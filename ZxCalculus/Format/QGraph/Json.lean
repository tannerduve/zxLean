import Lean.Data.Json
import ZxCalculus.Format.QGraph.Types
import ZxCalculus.Format.QGraph.Serializer

/-!
# QGraph JSON export

Conversion from QGraph data to JSON and `.qgraph` files.
-/

open Lean (Json)

namespace ZxCalculus.Format.QGraph

/-- Convert Data to JSON -/
def toJson (qgraph : Data) : Json :=
  let verticesJson := qgraph.vertices.map fun v =>
    -- Explicitly cast to Int for JSON compatibility with PyZX
    let base := Json.mkObj [
      ("id", Lean.toJson (v.id : Int)),
      ("t", Lean.toJson (match v.vtype with
        | .boundary => (0 : Int)
        | .z => (1 : Int)
        | .x => (2 : Int)
        | .hbox => (3 : Int)))
    ]
    let withPhase := if v.phase != 0 then
      base.mergeObj (Json.mkObj [("phase", Json.str (phaseToString v.phase))])
    else base
    let withPos := match v.pos with
      | some (r, q) => withPhase.mergeObj (Json.mkObj [
          ("pos", Json.arr #[Lean.toJson r, Lean.toJson q])
        ])
      | none => withPhase
    withPos

  let edgesJson := qgraph.edges.map fun e =>
    Json.arr #[
      Lean.toJson (e.src : Int),
      Lean.toJson (e.tgt : Int),
      Lean.toJson (match e.etype with
        | .simple => (1 : Int)
        | .hadamard => (2 : Int))
    ]

  let inputsJson := qgraph.inputs.map (fun (i : Nat) => Lean.toJson (i : Int))
  let outputsJson := qgraph.outputs.map (fun (i : Nat) => Lean.toJson (i : Int))

  let base := Json.mkObj [
    ("version", Lean.toJson (qgraph.version : Int)),
    ("backend", Json.str "simple"),  -- PyZX requires this field
    ("vertices", Json.arr verticesJson),
    ("edges", Json.arr edgesJson),
    ("inputs", Json.arr inputsJson),
    ("outputs", Json.arr outputsJson)
  ]

  match qgraph.scalar with
  | some (power2, phase) => base.mergeObj (Json.mkObj [
      ("scalar", Json.mkObj [
        ("power2", Lean.toJson power2),
        ("phase", Json.str phase)
      ])
    ])
  | none => base

/-- Write Data to a .qgraph file -/
def writeFile (path : System.FilePath) (qgraph : Data) : IO Unit := do
  let json := toJson qgraph
  IO.FS.writeFile path (json.compress)

end ZxCalculus.Format.QGraph
