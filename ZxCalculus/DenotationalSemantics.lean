import ZxCalculus.AST
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Cases
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.InnerProductSpace.PiL2

attribute [local simp] add_assoc add_comm mul_assoc mul_add add_mul

/-!
# Denotational Semantics for ZX-Calculus

We interpret ZX diagrams as linear maps between finite-dimensional complex vector spaces.
An n-wire diagram corresponds to ℂ^(2^n).
-/

open Complex ComplexConjugate InnerProductSpace


-- Helper: vector space for n qubits

abbrev Qubits (n : ℕ) := PiLp 2 (fun _ : Fin (2^n) => ℂ)

abbrev LinMap (n m : ℕ) := Qubits n →ₗ[ℂ] Qubits m

noncomputable section

def ket {n : ℕ} (a : Qubits n) : Qubits 0 →ₗ[ℂ] Qubits n := {
  toFun := fun s => s 0 • a
  map_add' := by intros; simp [add_smul]
  map_smul' := by intros; simp [smul_smul]
}

def bra {n : ℕ} (a : Qubits n) : Qubits n →ₗ[ℂ] Qubits 0 := {
  toFun := fun b => (WithLp.equiv 2 _).symm (fun _ => inner ℂ a b)
  map_add' := by intros; ext; simp [inner_add_right]
  map_smul' := by intros; ext; simp [inner_smul_right]
}

-- Decompose Fin (2^(n+m)) into (Fin (2^n), Fin (2^m))
def decompose {n m : ℕ} (i : Fin (2 ^ (n + m))) : Fin (2 ^ n) × Fin (2 ^ m) :=
  have h : 2 ^ (n + m) = 2 ^ n * 2 ^ m := by ring_nf
  let first := i.val / (2 ^ m)
  let second := i.val % (2 ^ m)
  (⟨first, sorry⟩, ⟨second, sorry⟩)

def recompose {n m : ℕ} (j : Fin (2 ^ m)) (i : Fin (2 ^ n)) : Fin (2 ^ (m + n)) :=
  have h : 2 ^ (m + n) = 2 ^ m * 2 ^ n := by ring_nf
  ⟨j.val * (2 ^ n) + i.val, sorry⟩

def swap_gen (n m : ℕ) : LinMap (n + m) (m + n) := {
  toFun := fun ψ =>
    WithLp.equiv 2 _ |>.symm fun i =>
      let i' : Fin (2 ^ (n + m)) := i.cast (by ring_nf)
      let (j, k) := decompose i'
      WithLp.equiv 2 _ ψ (recompose j k)
  map_add' := sorry
  map_smul' := sorry
}

-- Interpret generators
def interpGen (g : Generator') : (Σ n m : ℕ, LinMap n m) :=
match g with
  | .empty => ⟨0, 0, LinearMap.id⟩
  | .id n => ⟨n, n, LinearMap.id⟩
  | .swap n m => ⟨m, n, sorry⟩
  | _ => sorry

-- Main interpretation
def interp : ZxTerm' → (Σ n m : ℕ, LinMap n m)
  | .gen g => interpGen g
  | f ; g =>
      let ⟨nf, mf, φf⟩ := interp f
      let ⟨ng, mg, φg⟩ := interp g
      ⟨nf, mg, sorry⟩  -- φg.comp φf, need to handle mf = ng
  | f ⊗ g => sorry
end
