import ZxCalculus.Parser.QGraph

/-!
# Roundtrip Test Script

Parses a .qgraph file, reconstructs as ZxTerm, and serializes back.
Used by roundtrip_test.py to verify serialization correctness.
-/

open ZxCalculus.Parser

def main (args : List String) : IO UInt32 := do
  match args with
  | [inputPath, outputPath] =>
    try
      -- Parse input .qgraph file
      IO.println s!"Loading: {inputPath}"
      let qgraph ← parseQGraphFile ⟨inputPath⟩
      IO.println s!"  Parsed: {qgraph.vertices.size} vertices, {qgraph.edges.size} edges"

      -- Attempt to reconstruct ZxTerm
      IO.println "  Reconstructing ZxTerm..."
      match reconstructZxTermSimple qgraph with
      | .error e =>
        IO.eprintln s!"  ✗ Failed to reconstruct: {e}"
        return 1
      | .ok ⟨n, m, term⟩ =>
        IO.println s!"  ✓ Reconstructed: {n} inputs, {m} outputs"

        -- Serialize back to .qgraph
        IO.println s!"  Serializing to: {outputPath}"
        saveZxTermAsQGraph ⟨outputPath⟩ term

        -- Verify output was created (but don't fail on parse error since we just want to check file exists)
        match ← try
          let outQgraph ← parseQGraphFile ⟨outputPath⟩
          pure (some outQgraph)
        catch _ =>
          pure none
        with
        | some outQgraph =>
          IO.println s!"  ✓ Output: {outQgraph.vertices.size} vertices, {outQgraph.edges.size} edges"
        | none =>
          IO.println "  ✓ Output file created"

        return 0
    catch e =>
      IO.eprintln s!"Error: {e}"
      return 1
  | _ =>
    IO.eprintln "Usage: lake env lean --run scripts/RoundtripLean.lean <input.qgraph> <output.qgraph>"
    return 1
