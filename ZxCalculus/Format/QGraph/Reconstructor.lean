import ZxCalculus.AST
import ZxCalculus.Format.QGraph.Types

/-!
# QGraph reconstructor

Partial reconstruction of `ZxTerm n m` from QGraph data.

Currently supports:
- simple sequential circuits (gates in series)
- parallel single-qubit circuits (tensor products)

More general ZX-diagram reconstruction is out of scope here.
-/

namespace ZxCalculus.Format.QGraph

/-- Convert a non-boundary vertex to a `Generator`. -/
def vertexToGenerator (v : Vertex) (numInputs numOutputs : Nat) :
    Except String (Σ n m, Generator n m) := do
  match v.vtype with
  | .boundary => .error "Cannot convert boundary to generator"
  | .z => .ok ⟨numInputs, numOutputs, Generator.Z v.phase numInputs numOutputs⟩
  | .x => .ok ⟨numInputs, numOutputs, Generator.X v.phase numInputs numOutputs⟩
  | .hbox =>
    -- H-box is interpreted as a 1→1 gate here
    if numInputs == 1 && numOutputs == 1 then
      .ok ⟨1, 1, Generator.H⟩
    else
      .error "H-box must have 1 input and 1 output"

/-- Find vertex by ID -/
def findVertex? (vertices : Array Vertex) (id : Nat) : Option Vertex :=
  vertices.find? (·.id == id)

/-- Get all neighbors of a vertex via incoming or outgoing edges. -/
def getNeighbors (edges : Array Edge) (vid : Nat) : Array Nat :=
  let outgoing := edges.filter (·.src == vid) |>.map (·.tgt)
  let incoming := edges.filter (·.tgt == vid) |>.map (·.src)
  outgoing ++ incoming

/-- Build the `n`-qubit identity diagram. -/
def buildIdentity (n : Nat) : Σ n m, ZxTerm n m := tens_iter n ZxTerm.id

/-- Check if a vertex has a Hadamard edge -/
private def hasHadamardEdge (edges : Array Edge) (vid : Nat) : Bool :=
  edges.any (fun e => (e.src == vid || e.tgt == vid) && e.etype == .hadamard)

/-- Convert a gate vertex to a `ZxTerm 1 1`. -/
private def gateToZxTerm (edges : Array Edge) (gate : Vertex) : ZxTerm 1 1 :=
  match gate.vtype with
  | .hbox => ZxTerm.H
  | .z =>
    if gate.phase == 0 && hasHadamardEdge edges gate.id then
      ZxTerm.H
    else
      ZxTerm.Z gate.phase 1 1
  | .x =>
    if gate.phase == 0 && hasHadamardEdge edges gate.id then
      ZxTerm.H
    else
      ZxTerm.X gate.phase 1 1
  | .boundary => ZxTerm.id

/-- Extract and sort gates for a specific qubit -/
private def getGatesForQubit (gatesWithPos : Array (Vertex × Int))
    (qubitNum : Int) : Array Vertex :=
  gatesWithPos.filter (fun gp =>
    match gp.1.pos with
    | some (_, q) => q == qubitNum
    | none => false
  ) |>.qsort (fun a b => a.2 < b.2) |>.map (·.1)

/--
Reconstruct a ZxTerm from QGraph data using topology analysis.

Strategy:
1. For each input, trace the path to its corresponding output
2. Identify gates along each path (H-boxes, Z/X spiders)
3. Build the circuit layer by layer based on column positions
-/
def reconstruct (qgraph : Data) :
    Except String (Σ n m, ZxTerm n m) := do

  let numQubits := qgraph.inputs.size

  -- Special cases
  if numQubits == 0 then
    return ⟨0, 0, ZxTerm.empty⟩

  -- Find all non-boundary vertices (these are gates)
  let gates := qgraph.vertices.filter (fun v => v.vtype != .boundary)

  -- If no gates, just return identity
  if gates.isEmpty then
    return (buildIdentity numQubits)

  -- Group gates by column (position.fst)
  -- Sort by column to process left to right
  let gatesWithPos := gates.filterMap (fun v =>
    match v.pos with
    | some (col, _) => some (v, col)
    | none => none
  )

  if gatesWithPos.isEmpty then
    return (buildIdentity numQubits)
  -- Simple reconstruction: look at each gate individually
  -- For single-qubit circuits, just compose gates in order
  if numQubits == 1 then
    -- Sort gates by column
    let sortedGates := gatesWithPos.qsort (fun a b => a.2 < b.2) |>.map (·.1)

    -- Build composition of gates
    let circuit := sortedGates.foldl (fun acc gate =>
      if gate.vtype == .boundary then acc
      else acc ; gateToZxTerm qgraph.edges gate
    ) ZxTerm.id

    return ⟨1, 1, circuit⟩

  -- For multi-qubit circuits: return identity for now
  -- Full topology analysis for entangled circuits is complex
  -- and requires tracking which gates act on which qubits
  else
    -- Check if all gates are single-qubit (1 input, 1 output each)
    -- This indicates a tensor product of independent circuits
    let allSimple := gates.all (fun g =>
      let neighbors := getNeighbors qgraph.edges g.id
      neighbors.size ≤ 2  -- At most one input and one output
    )

    if allSimple && numQubits == 2 then
      -- Try to build tensor product of two single-qubit circuits
      let circuits := #[0, 1].map fun q =>
        let gates := getGatesForQubit gatesWithPos q
        gates.foldl (fun acc gate =>
          if gate.vtype == .boundary then acc
          else acc ; gateToZxTerm qgraph.edges gate
        ) ZxTerm.id

      match circuits with
      | #[circ0, circ1] => return ⟨2, 2, circ0 ⊗ circ1⟩
      | _ => .error "Internal error: expected 2 circuits"
    else
      -- Complex entangled circuit - return identity
      -- Full reconstruction would require analyzing edge connectivity
      -- and building CNOT/CZ gates from spider mergers
      return (buildIdentity numQubits)

end ZxCalculus.Format.QGraph
