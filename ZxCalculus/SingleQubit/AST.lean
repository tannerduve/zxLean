import ZxCalculus.AST
/-!
# Single-qubit ZX diagrams

This file defines the diagram syntax for the single-qubit fragment of the π / 4 ZX-calculus

The type `ZxDiagram n m` represents a diagram with strictly one or zero input wires, where `n` and `m` are booleans representing the presence of a wire.

* `false` = 0 wires
* `true`  = 1 wire

All non-empty generators are 1 → 1 maps:

* `id`, `H`: structural elements
* `Z α`, `X α` : phase gates with angle `α * π/4`

The only 0 → 0 diagram is `empty`, representing a scalar value.

Sequential composition is given by `comp`, with notation `A ; B`.

## References

Backens, M. (2014). The ZX-calculus is complete for the single-qubit Clifford+T group.
Department of Computer Science, University of Oxford. https://www.cs.ox.ac.uk/people/miriam.backens/Clifford_T.pdf
-/


namespace SingleQubit

/-- Single-qubit ZX diagrams with at most one input and one output wire. -/
inductive ZxDiagram : Bool → Bool → Type where
  /-- The empty diagram, interpreted as a scalar (0 → 0). -/
  | empty : ZxDiagram false false
  /-- Identity on a single wire (1 → 1) -/
  | id : ZxDiagram true true
  /-- Hadamard gate on a single wire (1 → 1) -/
  | H : ZxDiagram true true
  /-- Z-spider with phase `α * π/4` (1 → 1) -/
  | Z (α : ZMod 8) : ZxDiagram true true
  /-- X-spider with phase `α * π/4` (1 → 1) -/
  | X (α : ZMod 8) : ZxDiagram true true
  /-- Sequential composition of diagrams -/
  | comp {n m k : Bool} (A : ZxDiagram n m) (B : ZxDiagram m k) : ZxDiagram n k

@[inherit_doc] scoped infixl:90 " ∘ " => ZxDiagram.comp

/-! ### Smart constructors -/

/-- The empty scalar diagram (0 → 0). -/
def empty := ZxDiagram.empty
/-- Identity on a single wire. -/
def id := ZxDiagram.id
/-- Hadamard on a single wire. -/
def H := ZxDiagram.H
/-- Z-spider with phase `α * π/4`. -/
def Z (α : ZMod 8) := ZxDiagram.Z α
/-- X-spider with phase `α * π/4`. -/
def X (α : ZMod 8) := ZxDiagram.X α

/--
The dagger (adjoint) of a single-qubit ZX diagram.

It reverses the direction of the diagram and negates phases on spiders:
* inputs and outputs are swapped,
* `Z α` and `X α` become `Z (-α)` and `X (-α)`,
* sequential composition is reversed: `(A ; B)† = B† ; A†`.
-/
def dagger {n m : Bool} : ZxDiagram n m → ZxDiagram m n
  | .empty => .empty
  | .id => .id
  | .H => .H
  | .Z α => .Z (-α)
  | .X α => .X (-α)
  | .comp A B => (dagger B) ∘ (dagger A)

end SingleQubit
