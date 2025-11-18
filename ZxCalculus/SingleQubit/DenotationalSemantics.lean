import ZxCalculus.DenotationalSemantics
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

/-- Linear maps for single-qubit diagrams (2×2 matrices). -/
abbrev LinMap := Matrix (Fin 2) (Fin 2) ℂ

/-! ### Spider operators -/

/--
Z-spider with phase `α * π/4` (1 → 1).

Matrix: `|0⟩⟨0| + e^(i·α·π/4) |1⟩⟨1|`

This is a diagonal matrix in the computational basis.
-/
def Z_spider (α : ZMod 8) : LinMap :=
  let phase := Complex.exp (Complex.I * ((α.val : ℝ) * π) / 4)
  ![![(1 : ℂ), (0 : ℂ)], ![(0 : ℂ), phase]]

def X_spider (α : ZMod 8) : LinMap :=
  let phase := Complex.exp (Complex.I * ((α.val : ℝ) * π) / 4)
  ![![(1 + phase) / 2, (1 - phase) / 2],
    ![(1 - phase) / 2, (1 + phase) / 2]]
/--
X-spider with phase `α * π/4` (1 → 1).

Matrix: `|+⟩⟨+| + e^(i·α·π/4) |-⟩⟨-|`

This is a diagonal matrix in the Hadamard basis.
-/
-- def X_spider (α : ZMod 8) : LinMap :=
--   let phase := ((α.val : ℝ) * π) / 4
--   let ketPlus_vec := ketToVec ketPlus
--   let ketMinus_vec := ketToVec ketMinus
--   let braPlus := ketPlus_vecᴴ
--   let braMinus := ketMinus_vecᴴ
--   -- Outer products: |+⟩⟨+| + e^(iαπ/4) |-⟩⟨-|
--   ketPlus_vec * braPlus + (Complex.exp (Complex.I * phase) • (ketMinus_vec * braMinus))

def interp {n m : Bool} (z : ZxDiagram n m) : LinMap :=
match z with
| .empty => 1
| .id => 1
| .Z α => Z_spider α
| .X α => X_spider α
| .H => H_gate.val
| .comp f g => interp g * interp f
