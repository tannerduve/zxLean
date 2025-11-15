import ZxCalculus.AST
import ZxCalculus.Format.QGraph.Types

/-!
# QGraph serializer

Serialization of `ZxTerm n m` into QGraph data structures using a state monad.
-/

namespace ZxCalculus.Format.QGraph

/-- State for building QGraph data during serialization -/
structure SerializerState where
  nextId : Nat
  vertices : Array Vertex
  edges : Array Edge
  inputWires : Array Nat   -- Vertex IDs for current input wires
  outputWires : Array Nat  -- Vertex IDs for current output wires

/-- Serializer monad for stateful graph construction -/
abbrev SerializerM := StateM SerializerState

private def getInputWires : SerializerM (Array Nat) :=
  (·.inputWires) <$> get

private def getOutputWires : SerializerM (Array Nat) :=
  (·.outputWires) <$> get

private def setInputWires (wires : Array Nat) : SerializerM Unit :=
  modify fun s => { s with inputWires := wires }

private def setOutputWires (wires : Array Nat) : SerializerM Unit :=
  modify fun s => { s with outputWires := wires }

/-- Allocate a new vertex ID -/
def allocVertexId : SerializerM Nat :=
  modifyGet fun s => (s.nextId, { s with nextId := s.nextId + 1 })

/-- Add a vertex to the graph -/
def addVertex (v : Vertex) : SerializerM Unit := do
  modify fun s => { s with vertices := s.vertices.push v }

/-- Add an edge to the graph -/
def addEdge (e : Edge) : SerializerM Unit := do
  modify fun s => { s with edges := s.edges.push e }

/-- Create n boundary vertices at column z -/
def createBoundaries (n : ℕ) (z : ℤ) : SerializerM (Array Nat) := do
  ((List.range n).map fun i => (i : Int)).toArray.mapM fun i => do
    let vid ← allocVertexId
    addVertex {
      id := vid,
      vtype := .boundary,
      phase := 0,
      pos := some (z, i)
    }
    return vid

/-- Convert rational phase to string for .qgraph format -/
def phaseToString (r : ℚ) : String :=
  if r.den == 1 then
    toString r.num
  else
    s!"{r.num}/{r.den}"

private def createSpider (vtype : VertexType) (α : Rat) (n m : Nat)
    (col : Int) (startQubit : Int) : SerializerM Unit := do
  let inputWires ← getInputWires
  let vid ← allocVertexId
  addVertex {
    id := vid,
    vtype := vtype,
    phase := α,
    pos := some (col, startQubit + (n / 2))
  }
  -- Connect input wires to spider
  (inputWires.toList.take n).forM fun src =>
    addEdge { src := src, tgt := vid, etype := .simple }
  -- All outputs connect from this spider
  setOutputWires (Array.replicate m vid)

/-- Serialize a generator at a specific position -/
def serializeGenerator {n m : Nat} (g : Generator n m) (col : Int) (startQubit : Int) : SerializerM Unit := do
  let inputWires ← getInputWires

  match g with
  | .empty =>
    -- Empty diagram - no vertices, no wires
    setInputWires #[]
    setOutputWires #[]

  | .id => setOutputWires inputWires

  | .swap n m =>
    -- Swap wires - reverse the order
    let swapped := inputWires.reverse
    setOutputWires swapped

  | .H =>
    -- In PyZX, a Hadamard gate is encoded as a Z-spider with a Hadamard edge
    -- Here we create a Z-spider with phase 0 and attach a Hadamard edge
    let vid ← allocVertexId
    addVertex {
      id := vid,
      vtype := .z,
      phase := 0,
      pos := some (col, startQubit)
    }
    -- Connect input wire to Z-spider with HADAMARD edge
    if h : inputWires.size ≥ 1 then
      addEdge { src := inputWires[0], tgt := vid, etype := .hadamard }
    -- Output is the Z-spider
    setOutputWires #[vid]
  | .Z α n m => createSpider .z α n m col startQubit
  | .X α n m => createSpider .x α n m col startQubit
  | .cup =>
    -- Cup (2 → 0): connect two input wires
    if h : inputWires.size ≥ 2 then
      addEdge { src := inputWires[0], tgt := inputWires[1], etype := .simple }
    setOutputWires #[]

  | .cap =>
    -- Cap (0 → 2): create two new wires and connect them
    let vid1 ← allocVertexId
    let vid2 ← allocVertexId
    addVertex { id := vid1, vtype := .z, phase := 0, pos := some (col, startQubit) }
    addVertex { id := vid2, vtype := .z, phase := 0, pos := some (col, startQubit + 1) }
    addEdge { src := vid1, tgt := vid2, etype := .simple }
    setOutputWires #[vid1, vid2]

/-- Serialize a ZxTerm to QGraph structure
    col: horizontal position
    startQubit: vertical position offset (which qubit to start at)
-/
def serializeZxTermAux {n m : Nat} (term : ZxTerm n m) (col : Int) (startQubit : Int) : SerializerM Unit := do
  match term with
  | .gen g => serializeGenerator g col startQubit
  | .comp A B =>
    -- Serialize A first
    serializeZxTermAux A col startQubit
    -- Outputs of A become inputs of B
    let middleWires ← getOutputWires
    setInputWires middleWires
    -- Serialize B after A (same qubit offset)
    serializeZxTermAux B (col + 1) startQubit
  | .tens A B =>
    -- Save current input wires
    let currentInputs ← getInputWires
    -- Split inputs between A and B.
    -- This currently assumes an equal split and so only handles balanced tensors.
    let splitPoint := currentInputs.size / 2
    let inputsA := currentInputs.extract 0 splitPoint
    let inputsB := currentInputs.extract splitPoint currentInputs.size

    -- Serialize A (top qubits starting at qubit 0)
    setInputWires inputsA
    serializeZxTermAux A col startQubit
    let outputsA ← getOutputWires

    -- Serialize B (bottom qubits starting at qubit splitPoint)
    setInputWires inputsB
    serializeZxTermAux B col (startQubit + splitPoint)
    let outputsB ← getOutputWires

    -- Combine outputs
    setOutputWires (outputsA ++ outputsB)

/-- Main serialization function: ZxTerm → Data -/
def serialize {n m : Nat} (term : ZxTerm n m) : Data :=
  let initialState : SerializerState := {
    nextId := 0,
    vertices := #[],
    edges := #[],
    inputWires := #[],
    outputWires := #[]
  }

  let ((inputBoundaries, outputBoundaries), finalState) := (do
    -- Create input boundaries (column -1, before gates)
    let inputBoundaries ← createBoundaries n (-1)
    setInputWires inputBoundaries

    -- Serialize the term (starts at column 0, qubit 0)
    serializeZxTermAux term 0 0

    -- Create output boundaries (at column 1000, far to the right)
    let outputBoundaries ← createBoundaries m 1000

    -- Connect internal outputs to output boundaries
    let internalOuts ← getOutputWires
    internalOuts.zip outputBoundaries |>.forM fun (src, tgt) =>
      addEdge { src := src, tgt := tgt, etype := .simple }

    return (inputBoundaries, outputBoundaries)
  ).run initialState

  {
    version := 2,
    vertices := finalState.vertices,
    edges := finalState.edges,
    inputs := inputBoundaries,
    outputs := outputBoundaries,
    scalar := none
  }

end ZxCalculus.Format.QGraph
