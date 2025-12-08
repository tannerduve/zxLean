import ZxCalculus.AST
import ZxCalculus.RewriteTerm
import ZxCalculus.DenotationalSemantics

set_option linter.unusedSimpArgs false

/-!
# Quantum Gates

Standard gates for quantum computing in ZX-calculus.

## Clifford+T Gates (Fault-Tolerant Universal Set)
* `T`: π/4 Z-rotation (non-Clifford, makes gate set universal)
* `S`: π/2 Z-rotation (Clifford gate)
* `CNOT`: Controlled-NOT (Clifford gate)

## Parameterized Rotations
* `Rz θ`: Z-rotation by angle θ·π
* `Rx θ`: X-rotation by angle θ·π
* `CRz θ`: Controlled Z-rotation by angle θ·π

Clifford+T is the standard for fault-tolerant quantum computing.
Parameterized rotations are essential for variational quantum algorithms (VQE, QAOA).
-/

open ZxTerm

/-! ## Parameterized Rotations -/

/-- Rz(θ): Z-rotation by angle θ·π -/
def Rz (θ : ZMod 8) : ZxTerm 1 1 := Z θ 1 1

/-- Rx(θ): X-rotation by angle θ·π -/
def Rx (θ : ZMod 8) : ZxTerm 1 1 := X θ 1 1

/-- CRz(θ): Controlled Z-rotation by angle θ·π.
    Generalizes controlled-S and controlled-T gates. -/
def CRz (θ : ZMod 8) : ZxTerm 2 2 := Z θ 2 2

/-! ## Clifford+T Gates -/

/-- T gate: π/4 Z-rotation. Non-Clifford gate required for universality. -/
def T : ZxTerm 1 1 := Rz 1

/-- S gate: π/2 Z-rotation. Clifford gate. -/
def S : ZxTerm 1 1 := Rz 2

/-- CNOT: Controlled-NOT gate.
    Copies control via Z-spider, XORs with target via X-spider. -/
def CNOT : ZxTerm 2 2 :=
  (Z 0 1 2 ⊗' id) ; (id ⊗' X 0 2 1)

/--
Pauli Z gate: A Z spider with phase π, 1 input, 1 output
-/
def PauliZ : ZxTerm 1 1 := Rz 4

/--
Paulix X gate: An X spider with phase π, 1 input, 1 output
-/
def PauliX : ZxTerm 1 1 := Rx 4

/-! Semantics proofs -/

/-
Want to show H, S, CNOT, and T diagrams map to the correct matrices via `interp`
This amounts to soundness of Clifford+T (i think?)
-/

theorem H_gate_sound : interp (ZxTerm.H) = H_gate := by
    simp only [H, interp, interpGen, unitaryToMatrix, Nat.reducePow]

theorem S_gate_sound : interp S = S_gate := by
  simp only [S, Rz, Z, interp, interpGen, Z_spider, qubitSpaceToVec]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [
    S_gate, Qubit.S, ket_pow, ket0, ket1,
    qubitSpaceEquiv, Ket.basis,
    Matrix.mul_apply
  ]
  have : Complex.I * (2⁻¹ * ↑Real.pi) = ↑Real.pi / 2 * Complex.I := by ring
  change (Complex.exp (Complex.I * (↑((2 : ZMod 8).val) * ↑Real.pi / 4)) = Complex.I)
    -- Simplify the angle using the fact that $2 * \pi / 4 = \pi / 2$.
  have h_angle : Complex.I * (2 * Real.pi / 4) = Complex.I * (Real.pi / 2) := by
    -- Simplify the expression $2 * \pi / 4$ to $\pi / 2$.
    ring_nf;
  have h_euler : Complex.exp (Complex.I * (Real.pi / 2)) =
    Complex.cos (Real.pi / 2) + Complex.sin (Real.pi / 2) * Complex.I := by
    rw [ ← Complex.exp_mul_I, mul_comm ];
  convert h_euler using 1 <;> norm_num [ h_angle ];
  congr! 1

open Real
lemma sqrt_two_over_two_mul_sqrt_two : sqrt 2 / 2 * sqrt 2 = (1 : ℝ) := by
  have hnonneg : (0 : ℝ) ≤ 2 := by norm_num
  calc
    sqrt 2 / 2 * sqrt 2
        = sqrt 2 * sqrt 2 / 2 := by
          field_simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    _   = 2 / 2 := by
          simp [Real.mul_self_sqrt hnonneg]
    _   = 1 := by norm_num

lemma sqrt_two_mul_sqrt_two_over_two : sqrt 2 * (sqrt 2 / 2) = (1 : ℝ) := by
  simpa [mul_comm] using sqrt_two_over_two_mul_sqrt_two

theorem T_gate_sound : interp T = T_gate := by
  simp only [T, Rz, Z, interp, interpGen, Z_spider, qubitSpaceToVec]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [
    T_gate, Qubit.T, ket_pow, ket0, ket1,
    Ket.basis, qubitSpaceEquiv, Matrix.mul_apply
  ]
  -- Apply Euler's formula to rewrite the exponential in terms of sine and cosine.
  have h_euler : Complex.exp (Complex.I * (1 * Real.pi / 4)) =
    Real.cos (Real.pi / 4) + Complex.I * Real.sin (Real.pi / 4) := by
    norm_num [ Complex.ext_iff ];
    simp [Complex.cos, Complex.sin, Complex.exp_re, Complex.exp_im];
  have h_cos_sin : Real.cos (Real.pi / 4) =
    1 / Real.sqrt 2 ∧ Real.sin (Real.pi / 4) = 1 / Real.sqrt 2 := by
    -- By definition of reciprocal, we know that $(\sqrt{2})^{-1} = \frac{1}{\sqrt{2}}$.
    field_simp;
    simp_all only [one_mul, Real.cos_pi_div_four, Complex.ofReal_div,
    Complex.ofReal_ofNat, Real.sin_pi_div_four]
    apply And.intro
    · apply sqrt_two_over_two_mul_sqrt_two
    · apply sqrt_two_mul_sqrt_two_over_two
  simp_all only [one_mul, one_div, Complex.ofReal_inv,
  Real.cos_pi_div_four, Real.sin_pi_div_four, and_self]
  ring_nf;
  convert h_euler using 1 <;> push_cast [ ZMod.cast ] <;> ring_nf!;
  norm_num [ ZMod.val ]

/-! ### CNOT Matrix Entry Lemmas

We break down the CNOT soundness proof into individual matrix entries.
The CNOT matrix is the standard controlled-NOT permutation matrix:
  [[1, 0, 0, 0],
   [0, 1, 0, 0],
   [0, 0, 0, 1],
   [0, 0, 1, 0]]
-/

-- ugly and incomplete proof of soundness for CNOT, not needed for now

-- Row 0 entries
lemma cnot_entry_00 : interp CNOT 0 0 = 1 := by
  unfold CNOT interp
  norm_num [interpGen, tensLin, Z_spider, X_spider, qubitSpaceToVec, ket_pow, ket0, ket1,
            ketPlus, ketMinus, Ket.normalize, qubitSpaceEquiv, Ket.basis,
            Matrix.mul_apply, Matrix.kroneckerMap, Matrix.reindex_apply,
            finProdFinEquiv, Equiv.prodCongr_apply, Equiv.cast_apply]
  sorry

lemma cnot_entry_01 : interp CNOT 0 1 = 0 := by
  unfold CNOT interp
  norm_num [interpGen, tensLin, Z_spider, X_spider, qubitSpaceToVec, ket_pow, ket0, ket1,
            ketPlus, ketMinus, Ket.normalize, qubitSpaceEquiv, Ket.basis,
            Matrix.mul_apply, Matrix.kroneckerMap, Matrix.reindex_apply,
            finProdFinEquiv, Equiv.prodCongr_apply, Equiv.cast_apply]
  sorry

lemma cnot_entry_02 : interp CNOT 0 2 = 0 := by
  unfold CNOT interp
  norm_num [interpGen, tensLin, Z_spider, X_spider, qubitSpaceToVec, ket_pow, ket0, ket1,
            ketPlus, ketMinus, Ket.normalize, qubitSpaceEquiv, Ket.basis,
            Matrix.mul_apply, Matrix.kroneckerMap, Matrix.reindex_apply,
            finProdFinEquiv, Equiv.prodCongr_apply, Equiv.cast_apply]
  sorry

lemma cnot_entry_03 : interp CNOT 0 3 = 0 := by
  unfold CNOT interp
  norm_num [interpGen, tensLin, Z_spider, X_spider, qubitSpaceToVec, ket_pow, ket0, ket1,
            ketPlus, ketMinus, Ket.normalize, qubitSpaceEquiv, Ket.basis,
            Matrix.mul_apply, Matrix.kroneckerMap, Matrix.reindex_apply,
            finProdFinEquiv, Equiv.prodCongr_apply, Equiv.cast_apply]
  sorry

-- Row 1 entries
lemma cnot_entry_10 : interp CNOT 1 0 = 0 := by
  unfold CNOT interp
  norm_num [interpGen, tensLin, Z_spider, X_spider, qubitSpaceToVec, ket_pow, ket0, ket1,
            ketPlus, ketMinus, Ket.normalize, qubitSpaceEquiv, Ket.basis,
            Matrix.mul_apply, Matrix.kroneckerMap, Matrix.reindex_apply,
            finProdFinEquiv, Equiv.prodCongr_apply, Equiv.cast_apply]
  sorry

lemma cnot_entry_11 : interp CNOT 1 1 = 1 := by
  unfold CNOT interp
  norm_num [interpGen, tensLin, Z_spider, X_spider, qubitSpaceToVec, ket_pow, ket0, ket1,
            ketPlus, ketMinus, Ket.normalize, qubitSpaceEquiv, Ket.basis,
            Matrix.mul_apply, Matrix.kroneckerMap, Matrix.reindex_apply,
            finProdFinEquiv, Equiv.prodCongr_apply, Equiv.cast_apply]
  sorry

lemma cnot_entry_12 : interp CNOT 1 2 = 0 := by
  unfold CNOT interp
  norm_num [interpGen, tensLin, Z_spider, X_spider, qubitSpaceToVec, ket_pow, ket0, ket1,
            ketPlus, ketMinus, Ket.normalize, qubitSpaceEquiv, Ket.basis,
            Matrix.mul_apply, Matrix.kroneckerMap, Matrix.reindex_apply,
            finProdFinEquiv, Equiv.prodCongr_apply, Equiv.cast_apply]
  sorry

lemma cnot_entry_13 : interp CNOT 1 3 = 0 := by
  unfold CNOT interp
  norm_num [interpGen, tensLin, Z_spider, X_spider, qubitSpaceToVec, ket_pow, ket0, ket1,
            ketPlus, ketMinus, Ket.normalize, qubitSpaceEquiv, Ket.basis,
            Matrix.mul_apply, Matrix.kroneckerMap, Matrix.reindex_apply,
            finProdFinEquiv, Equiv.prodCongr_apply, Equiv.cast_apply]
  sorry

-- Row 2 entries
lemma cnot_entry_20 : interp CNOT 2 0 = 0 := by
  unfold CNOT interp
  norm_num [interpGen, tensLin, Z_spider, X_spider, qubitSpaceToVec, ket_pow, ket0, ket1,
            ketPlus, ketMinus, Ket.normalize, qubitSpaceEquiv, Ket.basis,
            Matrix.mul_apply, Matrix.kroneckerMap, Matrix.reindex_apply,
            finProdFinEquiv, Equiv.prodCongr_apply, Equiv.cast_apply]
  sorry

lemma cnot_entry_21 : interp CNOT 2 1 = 0 := by
  unfold CNOT interp
  norm_num [interpGen, tensLin, Z_spider, X_spider, qubitSpaceToVec, ket_pow, ket0, ket1,
            ketPlus, ketMinus, Ket.normalize, qubitSpaceEquiv, Ket.basis,
            Matrix.mul_apply, Matrix.kroneckerMap, Matrix.reindex_apply,
            finProdFinEquiv, Equiv.prodCongr_apply, Equiv.cast_apply]
  sorry

lemma cnot_entry_22 : interp CNOT 2 2 = 0 := by
  unfold CNOT interp
  norm_num [interpGen, tensLin, Z_spider, X_spider, qubitSpaceToVec, ket_pow, ket0, ket1,
            ketPlus, ketMinus, Ket.normalize, qubitSpaceEquiv, Ket.basis,
            Matrix.mul_apply, Matrix.kroneckerMap, Matrix.reindex_apply,
            finProdFinEquiv, Equiv.prodCongr_apply, Equiv.cast_apply]
  sorry

lemma cnot_entry_23 : interp CNOT 2 3 = 1 := by
  unfold CNOT interp
  norm_num [interpGen, tensLin, Z_spider, X_spider, qubitSpaceToVec, ket_pow, ket0, ket1,
            ketPlus, ketMinus, Ket.normalize, qubitSpaceEquiv, Ket.basis,
            Matrix.mul_apply, Matrix.kroneckerMap, Matrix.reindex_apply,
            finProdFinEquiv, Equiv.prodCongr_apply, Equiv.cast_apply]
  sorry

-- Row 3 entries
lemma cnot_entry_30 : interp CNOT 3 0 = 0 := by
  unfold CNOT interp
  norm_num [interpGen, tensLin, Z_spider, X_spider, qubitSpaceToVec, ket_pow, ket0, ket1,
            ketPlus, ketMinus, Ket.normalize, qubitSpaceEquiv, Ket.basis,
            Matrix.mul_apply, Matrix.kroneckerMap, Matrix.reindex_apply,
            finProdFinEquiv, Equiv.prodCongr_apply, Equiv.cast_apply]
  sorry

lemma cnot_entry_31 : interp CNOT 3 1 = 0 := by
  unfold CNOT interp
  norm_num [interpGen, tensLin, Z_spider, X_spider, qubitSpaceToVec, ket_pow, ket0, ket1,
            ketPlus, ketMinus, Ket.normalize, qubitSpaceEquiv, Ket.basis,
            Matrix.mul_apply, Matrix.kroneckerMap, Matrix.reindex_apply,
            finProdFinEquiv, Equiv.prodCongr_apply, Equiv.cast_apply]
  sorry

lemma cnot_entry_32 : interp CNOT 3 2 = 1 := by
  unfold CNOT interp
  norm_num [interpGen, tensLin, Z_spider, X_spider, qubitSpaceToVec, ket_pow, ket0, ket1,
            ketPlus, ketMinus, Ket.normalize, qubitSpaceEquiv, Ket.basis,
            Matrix.mul_apply, Matrix.kroneckerMap, Matrix.reindex_apply,
            finProdFinEquiv, Equiv.prodCongr_apply, Equiv.cast_apply]
  sorry

lemma cnot_entry_33 : interp CNOT 3 3 = 0 := by
  unfold CNOT interp
  norm_num [interpGen, tensLin, Z_spider, X_spider, qubitSpaceToVec, ket_pow, ket0, ket1,
            ketPlus, ketMinus, Ket.normalize, qubitSpaceEquiv, Ket.basis,
            Matrix.mul_apply, Matrix.kroneckerMap, Matrix.reindex_apply,
            finProdFinEquiv, Equiv.prodCongr_apply, Equiv.cast_apply]
  sorry

/-- CNOT soundness: the ZX interpretation equals the standard matrix -/
theorem CNOT_gate_sound : interp CNOT = CNOT_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · -- case 0 0
    rw [CNOT_gate_matrix]
    simp only [Matrix.cons_val_zero, Matrix.head_cons]
    exact cnot_entry_00
  · -- case 0 1
    rw [CNOT_gate_matrix]
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Matrix.tail_cons]
    exact cnot_entry_01
  · -- case 0 2
    rw [CNOT_gate_matrix]
    simp only [Matrix.cons_val_fin_one, Matrix.head_cons]
    exact cnot_entry_02
  · -- case 0 3
    rw [CNOT_gate_matrix]
    simp only [Fin.mk_one, Matrix.cons_val_succ, Matrix.head_cons, Matrix.cons_val_zero,
               Matrix.tail_cons, Nat.succ_eq_add_one, Nat.reduceAdd]
    exact cnot_entry_03
  · -- case 1 0
    rw [CNOT_gate_matrix]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
    exact cnot_entry_10
  · -- case 1 1
    rw [CNOT_gate_matrix]
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
    exact cnot_entry_11
  · -- case 1 2
    rw [CNOT_gate_matrix]
    simp only [Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons]
    exact cnot_entry_12
  · -- case 1 3
    rw [CNOT_gate_matrix]
    simp only [Fin.mk_one, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons,
               Matrix.cons_val_zero, Matrix.tail_cons, Nat.succ_eq_add_one, Nat.reduceAdd]
    exact cnot_entry_13
  · -- case 2 0
    rw [CNOT_gate_matrix]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons]
    exact cnot_entry_20
  · -- case 2 1
    rw [CNOT_gate_matrix]
    simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons]
    exact cnot_entry_21
  · -- case 2 2
    rw [CNOT_gate_matrix]
    simp only [Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons]
    exact cnot_entry_22
  · -- case 2 3
    rw [CNOT_gate_matrix]
    simp only [Fin.mk_one, Matrix.cons_val_succ, Matrix.cons_val_fin_one, Matrix.head_cons,
               Matrix.cons_val_zero, Matrix.tail_cons, Nat.succ_eq_add_one, Nat.reduceAdd]
    exact cnot_entry_23
  · -- case 3 0
    rw [CNOT_gate_matrix]
    simp only [Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_succ, Matrix.head_cons,
               Matrix.tail_cons, Nat.succ_eq_add_one, Nat.reduceAdd]
    exact cnot_entry_30
  · -- case 3 1
    rw [CNOT_gate_matrix]
    simp only [Matrix.cons_val_one, Fin.mk_one, Matrix.cons_val_succ, Matrix.head_cons,
               Matrix.cons_val_zero, Matrix.tail_cons, Nat.succ_eq_add_one, Nat.reduceAdd]
    exact cnot_entry_31
  · -- case 3 2
    rw [CNOT_gate_matrix]
    simp only [Matrix.cons_val_fin_one, Fin.mk_one, Matrix.cons_val_succ, Matrix.head_cons,
               Matrix.tail_cons, Nat.succ_eq_add_one, Nat.reduceAdd]
    exact cnot_entry_32
  · -- case 3 3
    rw [CNOT_gate_matrix]
    simp only [Fin.mk_one, Matrix.cons_val_succ, Matrix.head_cons, Matrix.cons_val_zero,
               Matrix.tail_cons, Nat.succ_eq_add_one, Nat.reduceAdd]
    exact cnot_entry_33
