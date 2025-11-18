import ZxCalculus.SingleQubit.MatrixLemmas

open Matrix

set_option linter.unusedTactic false
open SingleQubit

/-!
# Soundness of the single-qubit ZX-calculus

This file proves **soundness** of the single-qubit ZX rewrite system:
if two diagrams are related by the equational theory `ZxEquiv`, then
their denotational semantics as 2×2 complex matrices agree up to a
non-zero global phase.

The main ingredients are:

- `EqualUpToScalar`: a relation `A ≈ B` on matrices expressing equality
  up to a non-zero scalar factor.
- Low-level matrix facts from `MatrixLemmas` and `lemmas`, including an
  explicit Euler decomposition of the Hadamard gate.
- `soundness_euler_decomp`: the matrix-level counterpart of the
  Euler decomposition rewrite rule.
- `soundness`: the main theorem stating
  `ZxEquiv A B → interp A ≈ interp B`.
-/

def EqualUpToScalar {n m : Type*} [Fintype n] [Fintype m]
    (A B : Matrix n m ℂ) : Prop :=
  ∃ (c : ℂ), c ≠ 0 ∧ A = c • B

notation:50 A " ≈ " B => EqualUpToScalar A B

namespace EqualUpToScalar

@[refl]
lemma refl {n m : Type*} [Fintype n] [Fintype m] (A : Matrix n m ℂ) :
    A ≈ A := by
  use 1
  simp

@[symm]
lemma symm {n m : Type*} [Fintype n] [Fintype m] {A B : Matrix n m ℂ}
    (h : A ≈ B) : B ≈ A := by
  obtain ⟨c, hc, hab⟩ := h
  use c⁻¹
  constructor
  · exact inv_ne_zero hc
  · rw [hab]
    aesop

@[trans]
lemma trans {n m : Type*} [Fintype n] [Fintype m] {A B C : Matrix n m ℂ}
    (hab : A ≈ B) (hbc : B ≈ C) : A ≈ C := by
  obtain ⟨c₁, hc₁, hab⟩ := hab
  obtain ⟨c₂, hc₂, hbc⟩ := hbc
  use c₁ * c₂
  constructor
  · exact mul_ne_zero hc₁ hc₂
  · rw [hab, hbc, smul_smul]

end EqualUpToScalar

@[simp] lemma ket0_vec_apply (i : Fin 2) :
    ket0.vec i = if i = 0 then 1 else 0 := by
  simp [ket0, Ket.basis];
  split_ifs with h₁ h₂ h₃ <;> try rfl
  symm at h₁; contradiction
  symm at h₃; contradiction

@[simp] lemma ket1_vec_apply (i : Fin 2) :
    ket1.vec i = if i = 1 then 1 else 0 := by
  simp [ket1, Ket.basis]
  split_ifs with h₁ h₂ h₃ <;> try rfl
  symm at h₁; contradiction
  symm at h₃; contradiction

@[simp] lemma ketToVec_of_apply (ψ : Ket (Fin 2)) (i : Fin 2) :
    (ketToVec ψ) i 0 = ψ.vec i := by
  simp [ketToVec, Matrix.of_apply]; rfl

-- Simp lemmas for ZMod 8 values used in the calculus
@[simp] lemma zmod8_val_2 : ((2 : ZMod 8).val : ℝ) = 2 := rfl
@[simp] lemma zmod8_val_4 : ((4 : ZMod 8).val : ℝ) = 4 := rfl

-- `Z_spider 4` coincides with the usual Pauli Z gate on one qubit.
lemma z_spider_4_eq_pauliZ : SingleQubit.Z_spider 4 = Z_gate.val := by
  simp only [SingleQubit.Z_spider, Z_gate, Qubit.Z, zmod8_val_4]
  rw [Complex.exp_eq_exp_re_mul_sin_add_cos]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

-- `X_spider 4` coincides with the usual Pauli X gate on one qubit.
lemma x_spider_4_eq_pauliX : SingleQubit.X_spider 4 = X_gate.val := by
  simp only [SingleQubit.X_spider, X_gate, Qubit.X, zmod8_val_4]
  have h_exp : Complex.exp (Complex.I * (4 * Real.pi) / 4) = -1 := by
    convert Complex.exp_pi_mul_I using 2
    ring
  simp [h_exp]
  rfl

-- Z-spider with phase 0 is semantically the identity.
lemma soundness_z_id :
    interp (Z 0) = interp id := by
  simp only [Z, SingleQubit.interp, SingleQubit.Z_spider, Matrix.vecCons, Nat.succ_eq_add_one,
    Nat.reduceAdd, ZMod.val_zero, CharP.cast_eq_zero, Complex.ofReal_zero, zero_mul, mul_zero,
    zero_div, Complex.exp_zero, SingleQubit.id]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

-- X-spider with phase 0 is semantically the identity.
lemma soundness_x_id :
  interp (X 0) = interp id := by
  simp only [X, SingleQubit.interp, SingleQubit.X_spider, Matrix.vecCons, Nat.succ_eq_add_one,
    Nat.reduceAdd, ZMod.val_zero, CharP.cast_eq_zero, Complex.ofReal_zero, zero_mul, mul_zero,
    zero_div, Complex.exp_zero, add_self_div_two, sub_self, SingleQubit.id]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

-- Semantic version of the "colour-change" rule turning Z into X via H.
lemma soundness_color_change_z (α : ZMod 8):
  interp (ZxDiagram.comp (ZxDiagram.comp H (Z α)) H) = interp (X α) := by
  simp only [H, Z, X, SingleQubit.interp, H_gate, Qubit.H, SingleQubit.Z_spider, SingleQubit.X_spider]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.vecMul, Matrix.mul_apply]
  · ring_nf
    field_simp
    ring_nf
    exact Or.inl <| mod_cast by norm_num
  · ring_nf
    norm_num [← Complex.ofReal_pow]
    ring
  · ring_nf
    field_simp [Complex.ext_iff]
    ring_nf
    norm_num [sq, Complex.exp_re, Complex.exp_im]
    ring_nf
    norm_num
  · ring_nf
    norm_num [← Complex.ofReal_pow]
    rw [mul_comm]

-- Semantic version of the "colour-change" rule turning X into Z via H.
lemma soundness_color_change_x (α : ZMod 8):
  interp (ZxDiagram.comp (ZxDiagram.comp H (X α)) H) = interp (Z α) := by
  simp only [H, X, Z, SingleQubit.interp, H_gate, Qubit.H, SingleQubit.X_spider, SingleQubit.Z_spider]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Complex.ext_iff, Matrix.mul_apply] <;> ring_nf <;> norm_num [Complex.exp_re, Complex.exp_im]
  · norm_num [Matrix.vecMul, Matrix.mulVec]
    ring_nf
    trivial

-- Semantic version of Z-spider fusion: phases add.
lemma soundness_z_fus (α β : ZMod 8) :
    interp (ZxDiagram.comp (Z α) (Z β)) = interp (Z (α + β)) := by
  simp [SingleQubit.interp, Z, SingleQubit.Z_spider]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [ Matrix.mul_apply ] ; ring_nf;
  rw [←Complex.exp_add];
  have h_diff : ∃ k : ℤ, Complex.I * Real.pi * (β.cast + α.cast - (α + β).cast) * (1 / 4) = 2 * Real.pi * Complex.I * k := by
    use ((β.cast + α.cast - (α + β).cast) / 8)
    rw [ Int.cast_div ] <;> norm_num ; ring_nf;
    fin_cases α <;> fin_cases β <;> trivial;
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Complex.I * Real.pi * (β.cast + α.cast - (α + β).cast) * (1 / 4) = 2 * Real.pi * Complex.I * k := h_diff
  have h_exp_eq : Complex.exp (Complex.I * β.cast * Real.pi * (1 / 4) + Complex.I * Real.pi * α.cast * (1 / 4)) = Complex.exp (Complex.I * Real.pi * (α + β).cast * (1 / 4) + 2 * Real.pi * Complex.I * k) := by
    exact congr_arg Complex.exp ( by linear_combination hk )
  erw [h_exp_eq]
  convert Complex.exp_periodic.int_mul k _ using 2
  simp only [mul_comm, add_comm]
  abel

-- Semantic version of X-spider fusion: phases add.
lemma soundness_x_fus (α β : ZMod 8) :
    interp (ZxDiagram.comp (X α) (X β)) = interp (X (α + β)) := by
  simp [SingleQubit.interp, X, SingleQubit.X_spider]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply] <;> field_simp <;> ring_nf <;>
  have h := exp_add_zmod8 α β
  <;> aesop

-- Soundness of the `z_pi_copy` rule (π-phase copy through an X-spider).
lemma soundness_z_pi_copy (α : ZMod 8) :
    interp (ZxDiagram.comp (Z 4) (X α)) ≈ interp (ZxDiagram.comp (X (-α)) (Z 4)) := by
  simp only [SingleQubit.interp, X, SingleQubit.X_spider, ZMod.natCast_val, Z, SingleQubit.Z_spider]
  use Complex.exp (Complex.I * ↑α.cast * ↑Real.pi * (1 / 4))
  constructor
  · simp
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply] <;> field_simp <;> ring_nf <;> norm_cast
  · exact (z_pi_x_copy_entries α).1
  · exact (z_pi_x_copy_entries α).2.1
  · exact (z_pi_x_copy_entries α).2.2.1
  · exact (z_pi_x_copy_entries α).2.2.2

-- Soundness of the `x_pi_copy` rule (π-phase copy through a Z-spider).
lemma soundness_x_pi_copy (α : ZMod 8) :
    interp (ZxDiagram.comp (X 4) (Z α)) ≈ interp (ZxDiagram.comp (Z (-α)) (X 4)) := by
  simp [SingleQubit.interp, Z, X, SingleQubit.X_spider, SingleQubit.Z_spider, EqualUpToScalar]
  use Complex.exp (Complex.I * (α.cast * Real.pi) / 4)
  constructor
  · norm_num [Complex.exp_ne_zero]
  · have h4 : (↑((4 : ZMod 8).cast) : ℂ) = 4 := rfl
    erw [show ((ZMod.cast (4 : ZMod 8) : ℝ) : ℂ) = 4 by rfl]
    ext i j
    norm_cast
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.smul_apply, Complex.ext_iff, sq] <;>
      ring_nf <;>
      norm_num [Complex.exp_re, Complex.exp_im]
    field_simp
    have ⟨h1, h2⟩ := (x_pi_copy_remaining_goals α).1
    · exact ⟨h1, h2⟩
    · have ⟨h3, h4⟩ := (x_pi_copy_remaining_goals α).2
      exact ⟨h3, h4⟩

@[simp] lemma zmod_val_two :
  Complex.ofReal (@Nat.cast ℝ _ (ZMod.val (2 : ZMod 8))) = 2 := by
  rfl

section EulerDecomp
attribute [-instance] Pi.instMul

-- Soundness of the Euler decomposition rule for `H`:
-- the matrix of `H` agrees up to non-zero scalar with `Z 2 ∘ X 2 ∘ Z 2`.
lemma soundness_euler_decomp :
    interp H ≈ interp (ZxDiagram.comp (Z 2) (ZxDiagram.comp (X 2) (Z 2))) := by
  unfold EqualUpToScalar
  simp only [SingleQubit.interp, H, Z, X, SingleQubit.Z_spider, SingleQubit.X_spider, H_gate, Qubit.H]
  use (Real.sqrt 2 * (1 - Complex.I)) / 2
  constructor
  · norm_num [Complex.ext_iff]
  · -- Show the matrix equality
    let ⟨h00, h01, h10, h11⟩ := euler_matrix_entries
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, zmod_val_two] <;>
      norm_num [Complex.exp_re, Complex.exp_im, Real.sin_pi_div_two, Real.cos_pi_div_two]
    · exact h00
    · exact h01
    · exact h10
    · exact h11

end EulerDecomp

lemma eq_upTo_of_eq {n m : Type*} [Fintype n] [Fintype m]
    (A B : Matrix n m ℂ) (h : A = B) : A ≈ B := by
    use 1
    simp; apply h

/-! ### Main soundness theorem -/

theorem soundness {n m : Bool} {A B : ZxDiagram n m} (h : ZxEquiv A B) :
    interp A ≈ interp B := by
    induction h
    · case refl _ _ _ =>
      rfl
    · case symm n m f g ih₁ f' =>
      symm; exact f'
    · case trans n' m' f g h a₁ a₂ ih₁ ih₂ =>
      apply EqualUpToScalar.trans ih₁ ih₂
    · case seq_cong n k m f₁ f₂ g₁ g₂ a₁ a₂ ih₁ ih₂ =>
      cases' ih₁ with w₁ hw₁
      cases' ih₂ with w₂ hw₂
      simp [SingleQubit.interp];
      rw [hw₁.2, hw₂.2]
      use w₁ • w₂
      constructor
      · aesop
      · simp [Matrix.mul_smul, smul_mul_assoc, smul_smul]
    · case assoc_comp n k l m f g h =>
      simp [SingleQubit.interp, Matrix.mul_assoc];
      rfl
    · case unit_comp_l f =>
      simp [SingleQubit.interp]
      apply eq_upTo_of_eq
      rfl
    · case unit_comp_r f =>
      simp [SingleQubit.interp]
      apply eq_upTo_of_eq
      rfl
    · case empty_unit =>
      simp [SingleQubit.interp]
      apply eq_upTo_of_eq
      rfl
    · case z_id =>
      apply eq_upTo_of_eq
      apply soundness_z_id
    · case x_id =>
      apply eq_upTo_of_eq
      apply soundness_x_id
    · case z_fus α β =>
      apply eq_upTo_of_eq
      exact @soundness_z_fus α β
    · case x_fus α β =>
      apply eq_upTo_of_eq
      exact @soundness_x_fus α β
    · case z_pi_copy α =>
      exact @soundness_z_pi_copy α
    · case x_pi_copy α =>
      exact @soundness_x_pi_copy α
    · case color_change_z α =>
      apply eq_upTo_of_eq
      exact @soundness_color_change_z α
    · case color_change_x α =>
      apply eq_upTo_of_eq
      exact @soundness_color_change_x α
    · case euler_decomp => apply soundness_euler_decomp
