import ZxCalculus.SingleQubit.AST
import ZxCalculus.MultiQubit.AST

/-!
# Coercion from single-qubit to n-ary ZX diagrams

This file defines an embedding of single-qubit ZX diagrams into the full
n-ary ZX calculus. Since single-qubit diagrams have at most one wire,
they map naturally to 0-wire or 1-wire n-ary diagrams.
-/

open SingleQubit

/-- Convert a boolean wire count to a natural number. -/
def boolToNat : Bool → ℕ
  | false => 0
  | true => 1

/-- Coerce a single-qubit ZX diagram to an n-ary ZX term. -/
def toZxTerm : {n m : Bool} → ZxDiagram n m → ZxTerm (boolToNat n) (boolToNat m)
  | false, false, .empty => ZxTerm.empty
  | true, true, .id => ZxTerm.id
  | true, true, .H => ZxTerm.H
  | true, true, .Z α => ZxTerm.Z α 1 1
  | true, true, .X α => ZxTerm.X α 1 1
  | _, _, .comp A B => .comp (toZxTerm A) (toZxTerm B)

/-- Coercion instance for automatic conversion. -/
instance {n m : Bool} : Coe (ZxDiagram n m) (ZxTerm (boolToNat n) (boolToNat m)) where
  coe := toZxTerm

namespace Coercion

/-- The coercion preserves identity. -/
theorem toZxTerm_id : toZxTerm (.id : ZxDiagram true true) = ZxTerm.id := rfl

/-- The coercion preserves Hadamard. -/
theorem toZxTerm_H : toZxTerm (.H : ZxDiagram true true) = ZxTerm.H := rfl

/-- The coercion preserves Z-spiders. -/
theorem toZxTerm_Z (α : ZMod 8) :
    toZxTerm (.Z α : ZxDiagram true true) = ZxTerm.Z α 1 1 := rfl

/-- The coercion preserves X-spiders. -/
theorem toZxTerm_X (α : ZMod 8) :
    toZxTerm (.X α : ZxDiagram true true) = ZxTerm.X α 1 1 := rfl

/-- The coercion preserves composition. -/
theorem toZxTerm_comp {n m k : Bool} (A : ZxDiagram n m) (B : ZxDiagram m k) :
    toZxTerm (.comp A B) = .comp (toZxTerm A) (toZxTerm B) := by
  cases n <;> cases m <;> cases k <;> rfl

end Coercion
