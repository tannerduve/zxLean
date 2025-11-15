import Lean.Data.Json
import Parser
import ZxCalculus.Format.QGraph.Types

/-!
# QGraph JSON parser

Parsing of Quantomatic/PyZX `.qgraph` JSON into `QGraph.Data`.
-/

open Lean (Json)
open Parser Char

namespace ZxCalculus.Format.QGraph

/-- Parse vertex type from integer code -/
def parseVertexType (t : Int) : Except String VertexType :=
  match t with
  | 0 => .ok .boundary
  | 1 => .ok .z
  | 2 => .ok .x
  | 3 => .ok .hbox
  | _ => .error s!"Unknown vertex type code: {t}"

/-- Parse edge type from integer code -/
def parseEdgeType (t : Int) : Except String EdgeType :=
  match t with
  | 1 => .ok .simple
  | 2 => .ok .hadamard
  | _ => .ok .simple  -- Default to simple

/-- Parser for rational numbers in fraction form "n/d" or "-n/d" -/
def fractionParser : SimpleParser Substring Char Rat := do
  let n ← ASCII.parseInt
  drop 1 (char '/')
  let den ← ASCII.parseNat
  if den == 0 then
    throwUnexpected
  return mkRat n den

/-- Parser for decimal numbers like "0.25" or "-0.5" -/
def decimalParser : SimpleParser Substring Char Rat := do
  let neg ← test (char '-')
  if neg then drop 1 (char '-')
  let intPart ← ASCII.parseNat
  drop 1 (char '.')
  let fracDigits ← takeMany1 ASCII.digit
  let fracPart : Nat := fracDigits.foldl (fun acc d => acc * 10 + d.val) 0
  let denomPower : Nat := 10 ^ fracDigits.size
  let numerator : Int := (intPart : Int) * (denomPower : Int) + (fracPart : Int)
  return mkRat (if neg then -numerator else numerator) denomPower

/-- Parser for integer phases -/
def integerParser : SimpleParser Substring Char Rat := do
  let n ← ASCII.parseInt
  return Rat.ofInt n

/-- Combined phase string parser -/
def phaseStringParser : SimpleParser Substring Char Rat :=
  fractionParser <|> decimalParser <|> integerParser

/-- Parse rational phase from .qgraph (as string or number) -/
def parsePhase (j : Json) : Except String Rat :=
  match j with
  | .str s =>
    match phaseStringParser.run s.toSubstring with
    | .ok _ r => .ok r
    | .error _ e => .error s!"Invalid phase '{s}': {e}"
  | .num n => .ok (Rat.ofInt n.mantissa)
  | _ => .ok 0  -- Default to 0 if not provided

/-- Parse a single vertex from JSON object -/
def parseVertex (obj : Lean.Json) : Except String Vertex := do
  -- Get vertex ID (can be Nat or Int)
  let id ← match obj.getObjValAs? Nat "id" with
    | .ok n => .ok n
    | .error _ => match obj.getObjValAs? Int "id" with
      | .ok i => if i >= 0 then .ok i.toNat else .error "Negative vertex ID"
      | .error e => .error e

  -- Get vertex type (t field - can be Nat or Int)
  let t ← match obj.getObjValAs? Int "t" with
    | .ok i => .ok i
    | .error _ => match obj.getObjValAs? Nat "t" with
      | .ok n => .ok (n : Int)
      | .error e => .error e
  let vtype ← parseVertexType t

  -- Get phase (optional, default 0)
  let phase ← match obj.getObjValAs? Json "phase" |>.toOption with
    | some phaseJson => parsePhase phaseJson
    | none => .ok 0

  -- Get position (optional)
  let pos ← match obj.getObjValAs? Json "pos" |>.toOption with
    | some posJson => do
      let posArr ← posJson.getArr?
      match posArr with
      | #[xJson, yJson] =>
        -- x and y can be Int or Nat
        let x ← match xJson.getInt? with
          | .ok i => .ok i
          | .error _ => match xJson.getNat? with
            | .ok n => .ok (n : Int)
            | .error e => .error e
        let y ← match yJson.getInt? with
          | .ok i => .ok i
          | .error _ => match yJson.getNat? with
            | .ok n => .ok (n : Int)
            | .error e => .error e
        .ok (some (x, y))
      | _ => .ok none
    | none => .ok none

  pure { id, vtype, phase, pos }

/-- Parse edges from JSON -/
def parseEdges (json : Json) : Except String (Array Edge) := do
  let edgesArray ← json.getArr?
  let mut edges : Array Edge := #[]

  for edgeJson in edgesArray do
    let edgeArr ← edgeJson.getArr?
    match edgeArr with
    | #[srcJson, tgtJson, etypeJson] =>
      let src ← srcJson.getNat?
      let tgt ← tgtJson.getNat?
      let etypeInt ← etypeJson.getInt?
      let etype ← parseEdgeType etypeInt
      edges := edges.push { src, tgt, etype }
    | _ => .error "Edge must be [src, tgt, edgeType] triple"

  pure edges

/-- Main parser: .qgraph JSON → Data -/
def parse (json : Json) : Except String Data := do
  -- Parse version (can be Nat or Int)
  let version ← match json.getObjValAs? Nat "version" with
    | .ok n => .ok n
    | .error _ => match json.getObjValAs? Int "version" with
      | .ok i => if i >= 0 then .ok i.toNat else .error "Negative version"
      | .error e => .error e

  -- Parse vertices array
  let verticesJson ← json.getObjValAs? Json "vertices"
  let verticesArray ← verticesJson.getArr?
  let mut vertices : Array Vertex := #[]

  for vJson in verticesArray do
    let vertex ← parseVertex vJson
    vertices := vertices.push vertex

  -- Parse edges
  let edgesJson ← json.getObjValAs? Json "edges"
  let edges ← parseEdges edgesJson

  -- Parse inputs and outputs
  let inputsJson ← json.getObjValAs? Json "inputs"
  let inputsArr ← inputsJson.getArr?
  let mut inputs : Array Nat := #[]
  for iJson in inputsArr do
    -- Can be Nat or Int
    let i ← match iJson.getNat? with
      | .ok n => .ok n
      | .error _ => match iJson.getInt? with
        | .ok i => if i >= 0 then .ok i.toNat else .error "Negative input ID"
        | .error e => .error e
    inputs := inputs.push i

  let outputsJson ← json.getObjValAs? Json "outputs"
  let outputsArr ← outputsJson.getArr?
  let mut outputs : Array Nat := #[]
  for oJson in outputsArr do
    -- Can be Nat or Int
    let o ← match oJson.getNat? with
      | .ok n => .ok n
      | .error _ => match oJson.getInt? with
        | .ok i => if i >= 0 then .ok i.toNat else .error "Negative output ID"
        | .error e => .error e
    outputs := outputs.push o

  -- Parse scalar (optional)
  let scalar ← match json.getObjValAs? Json "scalar" |>.toOption with
    | some scalarJson => do
      -- power2 can be Int or Nat
      let power2 ← match scalarJson.getObjValAs? Int "power2" with
        | .ok i => .ok i
        | .error _ => match scalarJson.getObjValAs? Nat "power2" with
          | .ok n => .ok (n : Int)
          | .error e => .error e
      let phase ← scalarJson.getObjValAs? String "phase"
      .ok (some (power2, phase))
    | none => .ok none

  pure { version, vertices, edges, inputs, outputs, scalar }

/-- Read and parse a .qgraph file -/
def parseFile (path : System.FilePath) : IO Data := do
  let contents ← IO.FS.readFile path
  match Json.parse contents with
  | .error e => throw (IO.userError s!"JSON parse error: {e}")
  | .ok json =>
    match parse json with
    | .error e => throw (IO.userError s!"QGraph parse error: {e}")
    | .ok qgraph => pure qgraph

end ZxCalculus.Format.QGraph
