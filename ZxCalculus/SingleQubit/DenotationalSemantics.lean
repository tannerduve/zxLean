import ZxCalculus.MultiQubit.DenotationalSemantics
import ZxCalculus.SingleQubit.AST

/-!
# Denotational semantics for single-qubit ZX diagrams

This file interprets single-qubit ZX diagrams as 2×2 complex matrices
(or scalars for 0→0 diagrams).

Single-qubit spiders have a particularly simple form:
- Z(α): |0⟩⟨0| + e^(iα·π/4) |1⟩⟨1| (diagonal in computational basis)
- X(α): |+⟩⟨+| + e^(iα·π/4) |-⟩⟨-| (diagonal in Hadamard basis)
-/

namespace SingleQubit

open Matrix Complex Real
open Braket SingleQubit

noncomputable section

/-! ### Type definitions -/

/-- Linear maps for single-qubit diagrams (2×2 complex matrices). -/
abbrev LinMap := Matrix (Fin 2) (Fin 2) ℂ

/-! ### Spider operators -/

/--
Z-spider with phase `α * π/4` (1 → 1).

Matrix: `|0⟩⟨0| + e^(i·α·π/4) |1⟩⟨1|`, diagonal in the computational basis.
-/
def Z_spider (α : ZMod 8) : LinMap :=
  let phase := Complex.exp (Complex.I * ((α.val : ℝ) * π) / 4)
  ![![(1 : ℂ), (0 : ℂ)], ![(0 : ℂ), phase]]

/--
X-spider with phase `α * π/4` (1 → 1).
-/
def X_spider (α : ZMod 8) : LinMap :=
  let phase := Complex.exp (Complex.I * ((α.val : ℝ) * π) / 4)
  ![![(1 + phase) / 2, (1 - phase) / 2],
    ![(1 - phase) / 2, (1 + phase) / 2]]

-- Interpret a single-qubit ZX diagram as a 2×2 complex matrix.
def interp {n m : Bool} (z : ZxDiagram n m) : LinMap :=
match z with
| .empty => 1
| .id => 1
| .Z α => Z_spider α
| .X α => X_spider α
| .H => H_gate.val
| .comp f g => interp g * interp f

end

end SingleQubit
