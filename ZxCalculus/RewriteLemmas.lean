import ZxCalculus.RewriteTerm
import ZxCalculus.Gates
open ZxTerm Real ZxEquiv

/-
Rewriting lemmas for the ZX-calculus.

This file collects a few small derived facts about `ZxEquiv` that are handy in
examples and tests, especially for single-qubit diagrams. It also provides
variants of some basic rules that avoid clutter from casts and from the
definition of `tensor_pow`.
-/

/-! ## Simplified Color Change Rules -/

/-- Specialized color change for single wires (Z to X) - avoids tensor_pow casts -/
lemma color_change_Z_1 (α : ℚ) :
    ZxEquiv (H ; Z α 1 1 ; H) (X α 1 1) := by
  have h := @color_change_Z α 1 1
  -- tensor_pow H 1 reduces to H definitionally after simpa
  unfold tensor_pow at h
  simpa using h

/-- Specialized color change for single wires (X to Z) -/
lemma color_change_X_1 (α : ℚ) :
    ZxEquiv (H ; X α 1 1 ; H) (Z α 1 1) := by
  have h := @color_change_X α 1 1
  unfold tensor_pow at h
  simpa using h

/-! ## Tensor Power Simplifications -/

@[simp] lemma tensor_pow_one {n m : ℕ} (d : ZxTerm n m) :
    tensor_pow d 1 = by simpa [mul_one] using d := by rfl

-- More specific version for H
@[simp] lemma tensor_pow_H_one : tensor_pow H 1 = H := by rfl

/-! ## Common Gate Identities -/

/-- Pauli X gate can be expressed as H ; PauliZ ; H -/
theorem pauliX_as_HZH : ZxEquiv PauliX (H ; PauliZ ; H) := by
  have h := by simpa [Nat.reduceMul, tensor_pow_H_one, eq_mpr_eq_cast, cast_eq] using @color_change_Z 1 1 1
  exact symm h

/-- Pauli Z gate can be expressed as H ; PauliX ; H -/
theorem pauliZ_as_HXH : ZxEquiv PauliZ (H ; PauliX ; H) := by
  have h := by simpa [Nat.reduceMul, tensor_pow_H_one, eq_mpr_eq_cast, cast_eq] using @color_change_X 1 1 1
  exact symm h

/-- Hadamard is self-inverse
TODO: This is currently unprovable but should be provable after adding Euler decomposition to our rewrite rules
 -/
theorem hadamard_involutive : ZxEquiv (H ; H) id := sorry

/-! ## Fusion Helpers -/

/-- Fusing two S gates gives Pauli Z -/
theorem s_s_is_pauliZ : ZxEquiv (S ; S) PauliZ := by
  simp only [S, PauliZ, Rz]
  have h := @z_fus 1 1 1 (1 / 2) (1 / 2)
  ring_nf at h ⊢
  exact h

/-! ## Phase Manipulations -/

/-- Z and -Z compose to identity -/
theorem z_cancel (α : ℚ) : ZxEquiv (Z α 1 1 ; Z (-α) 1 1) id := by
  have h := @z_fus 1 1 1 α (-α)
  have h' := ZxEquiv.z_id
  simp only [add_neg_cancel] at h
  exact ZxEquiv.trans h h'

/-- X and -X compose to identity -/
theorem x_cancel (α : ℚ) : ZxEquiv (X α 1 1 ; X (-α) 1 1) id := by
  have h := @x_fus 1 1 1 α (-α)
  have h' := ZxEquiv.x_id
  simp only [add_neg_cancel] at h
  exact ZxEquiv.trans h h'

/-! ## Clifford+T Gate Relations -/

/-- S is T squared - Fusing two π/4 Z-rotations gives a π/2 rotation (S gate) -/
theorem s_is_t_t : ZxEquiv (T ; T) S := by
  simp only [S, T, Rz]
  have h := @z_fus 1 1 1 (1 / 4) (1 / 4)
  ring_nf at h
  exact h

/-- Four T gates compose to Pauli Z -/
theorem t_t_t_t_is_pauliZ : ZxEquiv (T ; T ; T ; T) PauliZ := by
  -- T ; T ; T ; T = (T ; T) ; (T ; T) = S ; S = PauliZ
  have h1 : ZxEquiv (T ; T ; T ; T) ((T ; T) ; (T ; T)) :=
    assoc_comp (T ; T) T T
  have h2 : ZxEquiv ((T ; T) ; (T ; T)) (S ; S) :=
    seq_cong s_is_t_t s_is_t_t
  exact trans (trans h1 h2) s_s_is_pauliZ
