import Mathlib.Data.Rat.Defs

/-!
# QGraph data types

Data structures for the Quantomatic `.qgraph` JSON format used by PyZX.

## Format

Example `.qgraph` structure:
```json
{
  "version": 2,
  "backend": "simple",
  "inputs": [0, 1],
  "outputs": [5, 6],
  "vertices": [
    {"id": 0, "t": 0, "pos": [0, 0]},  // t=0: boundary (input)
    {"id": 1, "t": 0, "pos": [0, 1]},  // t=0: boundary (input)
    {"id": 2, "t": 1, "pos": [1, 0], "phase": "0"},  // t=1: Z spider
    {"id": 3, "t": 2, "pos": [1, 1], "phase": "0"},  // t=2: X spider
    {"id": 5, "t": 0, "pos": [2, 0]},  // t=0: boundary (output)
    {"id": 6, "t": 0, "pos": [2, 1]}   // t=0: boundary (output)
  ],
  "edges": [[0, 2, 1], [1, 3, 1], [2, 5, 1], [3, 6, 1]]
  // [src, tgt, edgeType]: 1=simple, 2=hadamard
}
```

Vertex types (t):
- 0: Boundary (input/output)
- 1: Z spider (green)
- 2: X spider (red)
- 3: H-box (Hadamard)
-/

namespace ZxCalculus.Format.QGraph

/-- Vertex type in .qgraph format (encoded as integer "t") -/
inductive VertexType
  | boundary  -- t = 0
  | z         -- t = 1 (Z spider / green)
  | x         -- t = 2 (X spider / red)
  | hbox      -- t = 3 (H-box)
  deriving Repr, DecidableEq

/-- Edge type in .qgraph format -/
inductive EdgeType
  | simple    -- Regular edge
  | hadamard  -- H-edge (orange in diagrams)
  deriving Repr, DecidableEq

/-- A vertex from .qgraph JSON -/
structure Vertex where
  id : Nat
  vtype : VertexType
  phase : Rat  -- Phase as coefficient of π (optional, default 0)
  pos : Option (Int × Int)  -- Position [x, y] for layout
  deriving Repr

/-- An edge from .qgraph JSON -/
structure Edge where
  src : Nat
  tgt : Nat
  etype : EdgeType
  deriving Repr

/-- Complete parsed .qgraph data -/
structure Data where
  version : Nat
  vertices : Array Vertex
  edges : Array Edge
  inputs : Array Nat   -- Boundary vertex IDs marked as inputs
  outputs : Array Nat  -- Boundary vertex IDs marked as outputs
  scalar : Option (Int × String)  -- (power2, phase) - global scalar factor
  deriving Repr

end ZxCalculus.Format.QGraph
