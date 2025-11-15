# QGraph format

Support for PyZX’s `.qgraph` (Quantomatic) format, split into small modules.

## Layout

```
ZxCalculus/Format/QGraph/
  Types.lean         -- core data types
  Parser.lean        -- JSON → QGraph.Data
  Serializer.lean    -- ZxTerm → QGraph.Data
  Reconstructor.lean -- QGraph.Data → ZxTerm
  Json.lean          -- QGraph.Data → JSON
  Basic.lean         -- convenient re-exports
```

## Basic use

```lean
import ZxCalculus.Format.QGraph.Basic
open ZxCalculus.Format.QGraph
```

### Read a `.qgraph` file and reconstruct a diagram

```lean
def load (path : System.FilePath) : IO (Except String (Σ n m, ZxTerm n m)) :=
  loadAsZxTerm path
```

### Serialize a diagram to `.qgraph`

```lean
def save {n m : Nat} (path : System.FilePath) (term : ZxTerm n m) : IO Unit :=
  saveZxTerm path term
```

## Data types

- `VertexType`   – boundary, Z, X, H-box
- `EdgeType`     – simple or Hadamard
- `Vertex`       – id, type, phase, optional position
- `Edge`         – source, target, type
- `Data`         – full `.qgraph` payload

## Core functions

- `parse : Json → Except String Data`
- `parseFile : FilePath → IO Data`
- `serialize : ZxTerm n m → Data`
- `reconstruct : Data → Except String (Σ n m, ZxTerm n m)`
- `toJson : Data → Json`
- `writeFile : FilePath → Data → IO Unit`
- `loadAsZxTerm : FilePath → IO (Except String (Σ n m, ZxTerm n m))`
- `saveZxTerm : FilePath → ZxTerm n m → IO Unit`

