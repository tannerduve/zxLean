import Mathlib.Data.Rat.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

inductive Generator : ℕ → ℕ → Type
| empty : Generator 0 0 -- the empty diagram
| id : {n : ℕ} → Generator n n -- the identity generator on n wires (type n → n)
| swap : (n m : ℕ) → Generator (n + m) (m + n) -- the swap generator (type (n + m) -> (m + n))
| H : Generator 1 1 -- the hadamard generator (type 1 → 1)
| Z     : (α : ℚ) → (n m : ℕ) → Generator n m -- Z spider with angle α*π (type n → m)
| X     : (α : ℚ) → (n m : ℕ) → Generator n m -- X spider with angle α*π (type n → m)
| cup   : Generator 0 2 -- bell state (cup) (type 0 → 2)
| cap   : Generator 2 0 -- bell effect (cap) (type 2 → 0)

/--
Recursive syntax for ZX diagrams/terms
- Generators are ZX diagrams
- If A, B are ZX diagrams, then A ⊗ B is a ZX diagram
- If A, B are ZX diagrams, then A ; B is a ZX diagram
-/
inductive ZxTerm : ℕ → ℕ → Type
| gen : {n m : ℕ} → Generator n m → ZxTerm n m
| seq   : {n k m : ℕ} → ZxTerm n k → ZxTerm k m → ZxTerm n m
| tens  : {n₁ m₁ n₂ m₂ : ℕ} → ZxTerm n₁ m₁ → ZxTerm n₂ m₂ → ZxTerm (n₁ + n₂) (m₁ + m₂)

-- Notation for ZX diagrams
infixl:90 " ; " => ZxTerm.seq   -- Sequential composition
infixl:80 " ⊗ " => ZxTerm.tens  -- Tensor product

-- Define the dagger (adjoint) of a ZX term
def dagger {n m : ℕ} : ZxTerm n m → ZxTerm m n
| .gen g => match g with
  | .empty         => ZxTerm.gen Generator.empty
  | .id            => ZxTerm.gen Generator.id
  | .swap n' m'    => ZxTerm.gen (Generator.swap m' n')
  | .H             => ZxTerm.gen Generator.H
  | .Z α n' m'     => ZxTerm.gen (Generator.Z (-α) m' n')
  | .X α n' m'     => ZxTerm.gen (Generator.X (-α) m' n')
  | .cup           => ZxTerm.gen Generator.cap
  | .cap           => ZxTerm.gen Generator.cup
| .seq f g   => dagger g ; dagger f
| .tens f g  => dagger f ⊗ dagger g
