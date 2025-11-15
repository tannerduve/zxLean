import ZxCalculus.Format.QGraph.Types
import ZxCalculus.Format.QGraph.Parser
import ZxCalculus.Format.QGraph.Serializer
import ZxCalculus.Format.QGraph.Reconstructor
import ZxCalculus.Format.QGraph.Json


/-!
# QGraph format

Entry point for working with PyZX-style `.qgraph` diagrams.

This module re-exports:
- data structures (`Types`)
- JSON parsing (`Parser`)
- `ZxTerm` ↔ QGraph conversion (`Serializer`, `Reconstructor`)
- JSON export (`Json`)
-/
namespace ZxCalculus.Format.QGraph

/-! ## High-level convenience functions -/

/-- Read a .qgraph file and reconstruct it as a ZxTerm -/
def loadAsZxTerm (path : System.FilePath) :
    IO (Except String (Σ n m, ZxTerm n m)) := do
  let qgraph ← parseFile path
  pure (reconstruct qgraph)

/-- Serialize a ZxTerm and write it to a .qgraph file -/
def saveZxTerm {n m : Nat} (path : System.FilePath) (term : ZxTerm n m) : IO Unit := do
  let qgraph := serialize term
  writeFile path qgraph

end ZxCalculus.Format.QGraph
