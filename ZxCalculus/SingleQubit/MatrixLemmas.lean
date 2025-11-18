import ZxCalculus.SingleQubit.RewriteTerm
import ZxCalculus.SingleQubit.DenotationalSemantics
import Mathlib.Data.Matrix.Mul

/-!
# Matrix and exponential lemmas for single-qubit ZX-calculus

This file is where I throw random lemmas that come up during proofs of soundness. Specifically these are
lemmas purely about matrices and complex numbers, and make no mention of anything ZX or quantum related.

Currently these are far too specific to be useful outside of where they were used, but maybe I can refactor and generalize
later to contribute to Mathlib
-/

namespace Matrix

set_option linter.unusedTactic false

lemma exp_add_zmod8 (α β : ZMod 8) :
  Complex.exp (Complex.I * ↑β.cast * ↑Real.pi * (1 / 4)) * Complex.exp (Complex.I * ↑Real.pi * ↑α.cast * (1 / 4)) =
  Complex.exp (Complex.I * ↑Real.pi * ↑(α + β).cast * (1 / 4)) := by
  rw [←Complex.exp_add]
  have h_diff : ∃ k : ℤ, Complex.I * Real.pi * (β.cast + α.cast - (α + β).cast) * (1 / 4) = 2 * Real.pi * Complex.I * k := by
    use ((β.cast + α.cast - (α + β).cast) / 8)
    rw [Int.cast_div] <;> norm_num ; ring_nf
    fin_cases α <;> fin_cases β <;> trivial
  obtain ⟨k, hk⟩ := h_diff
  have : Complex.exp (Complex.I * β.cast * Real.pi * (1 / 4) + Complex.I * Real.pi * α.cast * (1 / 4)) =
         Complex.exp (Complex.I * Real.pi * (α + β).cast * (1 / 4) + 2 * Real.pi * Complex.I * k) := by
    congr 1
    linear_combination hk
  erw [this]
  convert Complex.exp_periodic.int_mul k _ using 2
  ring

lemma z_pi_x_copy_entries (α : ZMod 8) :
  (1 + Complex.exp (Complex.I * ↑α.cast * ↑Real.pi * (1 / 4)) =
   Complex.exp (Complex.I * ↑Real.pi * α.cast * (1 / 4)) +
   Complex.exp (Complex.I * ↑Real.pi * α.cast * (1 / 4)) * Complex.exp (Complex.I * ↑Real.pi * ↑(-α).cast * (1 / 4))) ∧
  (-(Complex.exp (Complex.I * ↑α.cast * ↑Real.pi * (1 / 4)) *
      Complex.exp (Complex.I * ↑Real.pi * ↑(4 : ZMod 8).cast * (1 / 4))) +
   Complex.exp (Complex.I * ↑Real.pi * ↑(4 : ZMod 8).cast * (1 / 4)) =
   Complex.exp (Complex.I * ↑Real.pi * α.cast * (1 / 4)) -
   Complex.exp (Complex.I * ↑Real.pi * α.cast * (1 / 4)) * Complex.exp (Complex.I * ↑Real.pi * ↑(-α).cast * (1 / 4))) ∧
  (1 - Complex.exp (Complex.I * ↑α.cast * ↑Real.pi * (1 / 4)) =
   Complex.exp (Complex.I * ↑Real.pi * α.cast * (1 / 4)) *
     Complex.exp (Complex.I * ↑Real.pi * ↑(4 : ZMod 8).cast * (1 / 4)) -
   Complex.exp (Complex.I * ↑Real.pi * α.cast * (1 / 4)) *
     Complex.exp (Complex.I * ↑Real.pi * ↑(4 : ZMod 8).cast * (1 / 4)) *
     Complex.exp (Complex.I * ↑Real.pi * ↑(-α).cast * (1 / 4))) ∧
  (Complex.exp (Complex.I * ↑α.cast * ↑Real.pi * (1 / 4)) * Complex.exp (Complex.I * ↑Real.pi * ↑(4 : ZMod 8).cast * (1 / 4)) +
   Complex.exp (Complex.I * ↑Real.pi * ↑(4 : ZMod 8).cast * (1 / 4)) =
   Complex.exp (Complex.I * ↑Real.pi * ↑(4 : ZMod 8).cast * (1 / 4)) *
     Complex.exp (Complex.I * ↑Real.pi * α.cast * (1 / 4)) +
   Complex.exp (Complex.I * ↑Real.pi * ↑(4 : ZMod 8).cast * (1 / 4)) *
     Complex.exp (Complex.I * ↑Real.pi * α.cast * (1 / 4)) *
     Complex.exp (Complex.I * ↑Real.pi * ↑(-α).cast * (1 / 4))) := by
  apply And.intro
  · norm_num [ ← Complex.exp_add ] ; ring_nf;
    have h_exp : Complex.exp (Complex.I * α.cast * (Real.pi : ℂ) * (1 / 4) + Complex.I * (Real.pi : ℂ) * (-α).cast * (1 / 4)) = Complex.exp 0 := by
      fin_cases α <;> norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ];
      all_goals norm_num [ ZMod.cast, ZMod.val ] ; ring_nf ; norm_num;
      all_goals erw [ Nat.cast_succ ] ; norm_num ; ring_nf ;
      all_goals norm_num [ mul_two ] ;
    rw [ h_exp, Complex.exp_zero, add_comm ];
  ·
    have h_exp : Complex.exp (Complex.I * α.cast * (Real.pi : ℂ) * (1 / 4)) * Complex.exp (Complex.I * (Real.pi : ℂ) * (-α).cast * (1 / 4)) = 1 ∧ Complex.exp (Complex.I * α.cast * (Real.pi : ℂ) * (1 / 4)) * Complex.exp (Complex.I * (Real.pi : ℂ) * (-α).cast * (1 / 4)) = 1 := by
      norm_num [ ← Complex.exp_add ] ; ring_nf ; aesop;
      fin_cases α <;> norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ];
      all_goals norm_num [ ZMod.cast, ZMod.val ] ; ring_nf ; norm_num;
      all_goals erw [ Nat.cast_succ ] ; norm_num ; ring_nf ;
      all_goals norm_num [ mul_two ] ;
    apply And.intro (by
    norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] at *;
    erw [ show ( ZMod.cast 4 : ℂ ) = 4 by rfl ] ; norm_num [ mul_assoc, mul_comm Real.pi _, mul_div ] at * ; ring_nf at * ; aesop ( simp_config := { decide := true } ) ;
    · linarith;
    · linarith) (by
    erw [ show ( ZMod.cast 4 : ℂ ) = 4 by norm_cast ] ; ring_nf at * ; aesop;
    ·
      have h_exp_pi : Complex.exp (Complex.I * Real.pi) = -1 := by
        norm_num [ mul_comm Complex.I ];
      norm_num [ h_exp_pi ] at * ; ring_nf at * ; aesop;
      ring;
    · rw [ mul_right_comm, h_exp, one_mul ])

@[simp] lemma x_pi_copy_matrix_equality (α : ZMod 8) :
  ![![1, 0], ![0, Complex.exp (Complex.I * ↑α.cast * ↑Real.pi / 4)]] *
    ![![(1 + Complex.exp (Complex.I * ↑Real.pi)) / 2, (1 + -Complex.exp (Complex.I * ↑Real.pi)) / 2],
      ![(1 + -Complex.exp (Complex.I * ↑Real.pi)) / 2, (1 + Complex.exp (Complex.I * ↑Real.pi)) / 2]] =
  Complex.exp (Complex.I * ↑Real.pi * α.cast / 4) •
    (![![(1 + Complex.exp (Complex.I * ↑Real.pi)) / 2, (1 + -Complex.exp (Complex.I * ↑Real.pi)) / 2],
        ![(1 + -Complex.exp (Complex.I * ↑Real.pi)) / 2, (1 + Complex.exp (Complex.I * ↑Real.pi)) / 2]] *
      ![![1, 0], ![0, Complex.exp (Complex.I * ↑Real.pi * ↑(-α).cast / 4)]]) := by
  ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ Complex.ext_iff, sq ] <;> ring_nf <;> norm_num [Complex.exp_re, Complex.exp_im]

lemma x_pi_copy_remaining_goals (α : ZMod 8) :
  (2 = Real.exp (-(Real.pi * (α.cast : ℂ).im) / 4) * Real.cos (Real.pi * (α.cast : ℂ).re / 4) * Real.cos (Real.pi * (-α).cast / 4) +
        -(Real.sin (Real.pi * (-α).cast / 4) * (Real.exp (-(Real.pi * (α.cast : ℂ).im) / 4) * Real.sin (Real.pi * (α.cast : ℂ).re / 4))) +
      Real.exp (-(Real.pi * (α.cast : ℂ).im) / 4) * Real.cos (Real.pi * (α.cast : ℂ).re / 4) * Real.cos (Real.pi * (-α).cast / 4) +
      -(Real.sin (Real.pi * (-α).cast / 4) * (Real.exp (-(Real.pi * (α.cast : ℂ).im) / 4) * Real.sin (Real.pi * (α.cast : ℂ).re / 4))) ∧
    0 = Real.exp (-(Real.pi * (α.cast : ℂ).im) / 4) * Real.cos (Real.pi * (α.cast : ℂ).re / 4) * Real.sin (Real.pi * (-α).cast / 4) +
        Real.cos (Real.pi * (-α).cast / 4) * (Real.exp (-(Real.pi * (α.cast : ℂ).im) / 4) * Real.sin (Real.pi * (α.cast : ℂ).re / 4)) +
      Real.exp (-(Real.pi * (α.cast : ℂ).im) / 4) * Real.cos (Real.pi * (α.cast : ℂ).re / 4) * Real.sin (Real.pi * (-α).cast / 4) +
      Real.cos (Real.pi * (-α).cast / 4) * (Real.exp (-(Real.pi * (α.cast : ℂ).im) / 4) * Real.sin (Real.pi * (α.cast : ℂ).re / 4))) ∧
  (Real.cos (α.cast * Real.pi * (1 / 4)) = Real.exp (-(Real.pi * (α.cast : ℂ).im * (1 / 4))) * Real.cos (Real.pi * (α.cast : ℂ).re * (1 / 4)) ∧
   Real.sin (α.cast * Real.pi * (1 / 4)) = Real.exp (-(Real.pi * (α.cast : ℂ).im * (1 / 4))) * Real.sin (Real.pi * (α.cast : ℂ).re * (1 / 4)))
  := by
    fin_cases α <;> norm_num [ Complex.normSq, Complex.exp_re, Complex.exp_im, Complex.cos, Complex.sin ] <;> ring_nf <;> norm_num [ Real.pi_pos.ne' ] at *;
    all_goals norm_num [ ZMod.cast, ZMod.val ] ; ring_nf ; norm_num [ mul_div ] ;
    all_goals norm_num [ ( by ring : Real.pi * 3 / 4 = Real.pi - Real.pi / 4 ), ( by ring : Real.pi * 5 / 4 = Real.pi + Real.pi / 4 ), ( by ring : Real.pi * 7 / 4 = 2 * Real.pi - Real.pi / 4 ), Real.cos_add, Real.sin_add, Real.cos_sub, Real.sin_sub ] ; ring_nf ; norm_num [ mul_one_div ] ;
    all_goals repeat' erw [ Nat.cast_succ ] ; norm_num ; ring_nf ; norm_num [ mul_div ] ;
    norm_num [ show Real.pi * 7 / 4 = 2 * Real.pi - Real.pi / 4 by ring, show Real.pi * 5 / 4 = Real.pi + Real.pi / 4 by ring, show Real.pi * 3 / 4 = Real.pi - Real.pi / 4 by ring, Real.cos_add, Real.sin_add, Real.cos_sub, Real.sin_sub ] at *;
    all_goals norm_num [ show Real.pi * 3 / 2 = Real.pi + Real.pi / 2 by ring, show Real.pi * 5 / 4 = Real.pi + Real.pi / 4 by ring, show Real.pi * 3 / 4 = Real.pi - Real.pi / 4 by ring, Real.sin_add, Real.sin_sub, Real.cos_add, Real.cos_sub ] at * <;> ring_nf at * <;> norm_num at *;
    erw [ Nat.cast_succ ] ; norm_num ; ring_nf ; norm_num [ mul_div ] ;


lemma x_pi_copy_scalar_exists (α : ZMod 8) :
  ∃ c : ℂ, c ≠ 0 ∧
    ![![1, 0], ![0, Complex.exp (Complex.I * (↑α.cast * ↑Real.pi) / 4)]] *
      ![![(1 + Complex.exp (Complex.I * (↑(4 : ZMod 8).cast * ↑Real.pi) / 4)) / 2,
          (1 - Complex.exp (Complex.I * (↑(4 : ZMod 8).cast * ↑Real.pi) / 4)) / 2],
        ![(1 - Complex.exp (Complex.I * (↑(4 : ZMod 8).cast * ↑Real.pi) / 4)) / 2,
          (1 + Complex.exp (Complex.I * (↑(4 : ZMod 8).cast * ↑Real.pi) / 4)) / 2]] =
    c • (![![(1 + Complex.exp (Complex.I * (↑(4 : ZMod 8).cast * ↑Real.pi) / 4)) / 2,
            (1 - Complex.exp (Complex.I * (↑(4 : ZMod 8).cast * ↑Real.pi) / 4)) / 2],
          ![(1 - Complex.exp (Complex.I * (↑(4 : ZMod 8).cast * ↑Real.pi) / 4)) / 2,
            (1 + Complex.exp (Complex.I * (↑(4 : ZMod 8).cast * ↑Real.pi) / 4)) / 2]] *
        ![![1, 0], ![0, Complex.exp (Complex.I * (↑(-α).cast * ↑Real.pi) / 4)]]) := by
  use Complex.exp (Complex.I * (α.cast * Real.pi) / 4)
  norm_num [ Complex.exp_ne_zero, ← List.ofFn_inj ];
  erw [ show ( ZMod.cast 4 : ℂ ) = 4 by rfl ] ; ring_nf; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] ;


lemma euler_matrix_entries :
  ((↑√2)⁻¹ : ℂ) = ↑√2 * (1 - Complex.I) / 2 * ((1 + Complex.exp (Complex.I * (2 * ↑Real.pi) / 4)) / 2) ∧
  (↑√2)⁻¹ = ↑√2 * (1 - Complex.I) / 2 * ((1 - Complex.exp (Complex.I * (2 * ↑Real.pi) / 4)) / 2 * Complex.exp (Complex.I * (2 * ↑Real.pi) / 4)) ∧
  (↑√2)⁻¹ = ↑√2 * (1 - Complex.I) / 2 * (Complex.exp (Complex.I * (2 * ↑Real.pi) / 4) * ((1 - Complex.exp (Complex.I * (2 * ↑Real.pi) / 4)) / 2)) ∧
  -(↑√2)⁻¹ = ↑√2 * (1 - Complex.I) / 2 * (Complex.exp (Complex.I * (2 * ↑Real.pi) / 4) * ((1 + Complex.exp (Complex.I * (2 * ↑Real.pi) / 4)) / 2) * Complex.exp (Complex.I * (2 * ↑Real.pi) / 4)) := by
  field_simp [Complex.ext_iff]
  ring_nf;
  norm_num [ Complex.exp_re, Complex.exp_im, mul_div ] at *

end Matrix
