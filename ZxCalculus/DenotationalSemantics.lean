import ZxCalculus.AST
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Cases

attribute [local simp] add_assoc add_comm mul_assoc mul_add add_mul

/-!
# Denotational Semantics for ZX-Calculus

We interpret ZX diagrams as linear maps between finite-dimensional complex vector spaces.
An n-wire diagram corresponds to ℂ^(2^n).
-/

open Complex ComplexConjugate

-- Helper: vector space for n qubits

structure Qubits (n : ℕ) where
  toFun : Fin (2^n) → ℂ

instance {n} : CoeFun (Qubits n) (fun _ => Fin (2^n) → ℂ) where
  coe v := v.toFun

instance {n} : Add (Qubits n) where
  add x y := ⟨fun i => x.toFun i + y.toFun i⟩

instance {n} : Zero (Qubits n) where
  zero := ⟨fun _ => 0⟩

instance {n} : Neg (Qubits n) where
  neg a := ⟨fun i => - (a i)⟩

@[ext] lemma Qubits.ext {n : ℕ} {x y : Qubits n}
  (h : ∀ i, x i = y i) : x = y := by
  cases x
  cases y
  apply congrArg Qubits.mk
  funext i
  simpa using h i

@[simp] lemma coe_add {n : ℕ} (x y : Qubits n) (i) :
  (x + y : Qubits n) i = x i + y i := rfl

@[simp] lemma coe_zero {n : ℕ} (i) : (0 : Qubits n) i = 0 := rfl

@[simp] lemma coe_neg {n : ℕ} (x : Qubits n) (i) :
  (- x) i = - (x i) := by rfl

instance {n : ℕ} : AddCommGroup (Qubits n) := by
  refine {
    add_assoc a b c := ?_
    zero_add a := ?_
    add_zero a := ?_
    neg_add_cancel a := ?_
    add_comm a b := ?_
    nsmul := nsmulRec
    zsmul := zsmulRec
  } <;> (ext i; simp)

instance {n : ℕ} : SMul ℂ (Qubits n) where
  smul c q := ⟨fun i => c * q i⟩

@[simp] lemma coe_smul' {n : ℕ} (c : ℂ) (q : Qubits n) (i) :
  (c • q) i = c * q i := rfl

instance {n : ℕ} : Module ℂ (Qubits n) := by
  refine {
    one_smul a := ?_
    mul_smul a b c := ?_
    smul_zero a := ?_
    smul_add a b c := ?_
    add_smul a b c := ?_
    zero_smul a := ?_
  } <;> (ext i; simp)


-- Linear maps between qubit spaces
abbrev LinMap (n m : ℕ) := Qubits n →ₗ[ℂ] Qubits m

def ket {n : ℕ} (h : Qubits n) : LinMap 0 n :=
  { toFun := fun c => c 0 • h
    map_add' := by simp [add_smul]
    map_smul' := by simp [smul_smul] }

noncomputable section

def innerQ {n : ℕ} (ψ φ : Qubits n) : ℂ :=
  ∑ i : Fin (2^n), conj (ψ i) * φ i

def normQ {n : ℕ} (ψ : Qubits n) : ℝ :=
  Real.sqrt (innerQ ψ ψ).re

instance QNorm {n : ℕ} : Norm (Qubits n) where
  norm := normQ

@[simp] lemma norm_zero_qubits {n : ℕ} : ‖(0 : Qubits n)‖ = 0 := by
  unfold norm inner
  simp

instance {n : ℕ} : SeminormedAddCommGroup (Qubits n) where
  dist_self x := by
    simp only [sub_self]

instance {n : ℕ} : InnerProductSpace ℂ (Qubits n) where
  inner := innerQ
  norm_sq_eq_re_inner := by {
    intro x
    simp only [RCLike.re_to_complex, innerQ]
    unfold norm
  }

-- Interpret generators
def interpGen (g : Generator') : (Σ n m : ℕ, LinMap n m) :=
match g with
  | .empty => ⟨0, 0, LinearMap.id⟩
  | .id n => sorry
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
