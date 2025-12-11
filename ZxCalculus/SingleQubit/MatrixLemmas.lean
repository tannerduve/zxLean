import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Rat.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Multiset.Functor
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.IsDiag

set_option linter.style.setOption false
set_option linter.style.multiGoal false
set_option maxHeartbeats 2000000

/-!
# Matrix and exponential lemmas for single-qubit ZX-calculus

This file is where I throw random lemmas that come up during proofs of soundness.
Specifically these are lemmas purely about matrices and complex numbers,
and make no mention of anything ZX or quantum related.

Currently these are far too specific to be useful outside of where they were used,
but maybe I can refactor and generalize
later to contribute to Mathlib
-/

namespace Matrix

set_option linter.unusedTactic false

lemma exp_add_zmod8 (α β : ZMod 8) :
  Complex.exp (Complex.I * ↑β.cast * ↑Real.pi * (1 / 4)) *
  Complex.exp (Complex.I * ↑Real.pi * ↑α.cast * (1 / 4)) =
  Complex.exp (Complex.I * ↑Real.pi * ↑(α + β).cast * (1 / 4)) := by
  rw [←Complex.exp_add]
  have h_diff : ∃ k : ℤ, Complex.I * Real.pi * (β.cast + α.cast - (α + β).cast) *
  (1 / 4) = 2 * Real.pi * Complex.I * k := by
    use ((β.cast + α.cast - (α + β).cast) / 8)
    rw [Int.cast_div] <;> norm_num ; ring_nf
    fin_cases α <;> fin_cases β <;> trivial
  obtain ⟨k, hk⟩ := h_diff
  have : Complex.exp (Complex.I * β.cast * Real.pi * (1 / 4) +
  Complex.I * Real.pi * α.cast * (1 / 4)) =
         Complex.exp (Complex.I * Real.pi * (α + β).cast * (1 / 4) +
         2 * Real.pi * Complex.I * k) := by
    congr 1
    linear_combination hk
  erw [this]
  convert Complex.exp_periodic.int_mul k _ using 2
  ring

-- Scalar equalities for the Z-π copy rule used in `soundness_z_pi_copy`.
lemma z_pi_x_copy_entries (α : ZMod 8) :
  (1 + Complex.exp (Complex.I * ↑α.cast * ↑Real.pi * (1 / 4)) =
   Complex.exp (Complex.I * ↑Real.pi * α.cast * (1 / 4)) +
   Complex.exp (Complex.I * ↑Real.pi * α.cast * (1 / 4)) *
   Complex.exp (Complex.I * ↑Real.pi * ↑(-α).cast * (1 / 4))) ∧
  (-(Complex.exp (Complex.I * ↑α.cast * ↑Real.pi * (1 / 4)) *
      Complex.exp (Complex.I * ↑Real.pi * ↑(4 : ZMod 8).cast * (1 / 4))) +
   Complex.exp (Complex.I * ↑Real.pi * ↑(4 : ZMod 8).cast * (1 / 4)) =
   Complex.exp (Complex.I * ↑Real.pi * α.cast * (1 / 4)) -
   Complex.exp (Complex.I * ↑Real.pi * α.cast * (1 / 4)) *
   Complex.exp (Complex.I * ↑Real.pi * ↑(-α).cast * (1 / 4))) ∧
  (1 - Complex.exp (Complex.I * ↑α.cast * ↑Real.pi * (1 / 4)) =
   Complex.exp (Complex.I * ↑Real.pi * α.cast * (1 / 4)) *
     Complex.exp (Complex.I * ↑Real.pi * ↑(4 : ZMod 8).cast * (1 / 4)) -
   Complex.exp (Complex.I * ↑Real.pi * α.cast * (1 / 4)) *
     Complex.exp (Complex.I * ↑Real.pi * ↑(4 : ZMod 8).cast * (1 / 4)) *
     Complex.exp (Complex.I * ↑Real.pi * ↑(-α).cast * (1 / 4))) ∧
  (Complex.exp (Complex.I * ↑α.cast * ↑Real.pi * (1 / 4)) *
  Complex.exp (Complex.I * ↑Real.pi * ↑(4 : ZMod 8).cast * (1 / 4)) +
   Complex.exp (Complex.I * ↑Real.pi * ↑(4 : ZMod 8).cast * (1 / 4)) =
   Complex.exp (Complex.I * ↑Real.pi * ↑(4 : ZMod 8).cast * (1 / 4)) *
     Complex.exp (Complex.I * ↑Real.pi * α.cast * (1 / 4)) +
   Complex.exp (Complex.I * ↑Real.pi * ↑(4 : ZMod 8).cast * (1 / 4)) *
     Complex.exp (Complex.I * ↑Real.pi * α.cast * (1 / 4)) *
     Complex.exp (Complex.I * ↑Real.pi * ↑(-α).cast * (1 / 4))) := by
  apply And.intro
  · norm_num [ ← Complex.exp_add ] ; ring_nf;
    have h_exp : Complex.exp (Complex.I * α.cast * (Real.pi : ℂ) *
    (1 / 4) + Complex.I * (Real.pi : ℂ) * (-α).cast * (1 / 4)) = Complex.exp 0 := by
      fin_cases α <;> norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ];
      all_goals norm_num [ ZMod.cast, ZMod.val ] ; ring_nf ; norm_num;
      all_goals erw [ Nat.cast_succ ] ; norm_num ; ring_nf ;
      all_goals norm_num [ mul_two ] ;
    rw [ h_exp, Complex.exp_zero, add_comm ];
  · have h_exp : Complex.exp (Complex.I * α.cast * (Real.pi : ℂ) *
    (1 / 4)) * Complex.exp (Complex.I * (Real.pi : ℂ) * (-α).cast * (1 / 4)) =
    1 ∧ Complex.exp (Complex.I * α.cast * (Real.pi : ℂ) * (1 / 4)) *
    Complex.exp (Complex.I * (Real.pi : ℂ) * (-α).cast * (1 / 4)) = 1 := by
      norm_num [ ← Complex.exp_add ] ; ring_nf ;
      simp_all only [one_div]
      fin_cases α <;> norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ];
      all_goals norm_num [ ZMod.cast, ZMod.val ] ; ring_nf ; norm_num;
      all_goals erw [ Nat.cast_succ ] ; norm_num ; ring_nf ;
      all_goals norm_num [ mul_two ] ;
    apply And.intro (by
    norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] at *;
    erw [ show ( ZMod.cast 4 : ℂ ) = 4 by rfl ] ;
    norm_num [ mul_assoc, mul_comm Real.pi _, mul_div ] at * ;
    refine And.intro ?h1 ?hrest
    · linarith;
    · linarith) (by
    erw [ show ( ZMod.cast 4 : ℂ ) = 4 by norm_cast ] ;
    have h_simp : Complex.exp (Complex.I * (Real.pi : ℂ) * 4 * (1 / 4)) = -1 := by
      norm_num [ mul_div, Complex.ext_iff, Complex.exp_re, Complex.exp_im ];
    grind)

-- Matrix identity for the X-π copy rule, used as a simp lemma.
@[simp] lemma x_pi_copy_matrix_equality (α : ZMod 8) :
  ![![1, 0], ![0, Complex.exp (Complex.I * ↑α.cast * ↑Real.pi / 4)]] *
    ![![(1 + Complex.exp (Complex.I * ↑Real.pi)) / 2,
    (1 + -Complex.exp (Complex.I * ↑Real.pi)) / 2],
      ![(1 + -Complex.exp (Complex.I * ↑Real.pi)) / 2,
      (1 + Complex.exp (Complex.I * ↑Real.pi)) / 2]] =
  Complex.exp (Complex.I * ↑Real.pi * α.cast / 4) •
    (![![(1 + Complex.exp (Complex.I * ↑Real.pi)) / 2,
    (1 + -Complex.exp (Complex.I * ↑Real.pi)) / 2],
        ![(1 + -Complex.exp (Complex.I * ↑Real.pi)) / 2,
        (1 + Complex.exp (Complex.I * ↑Real.pi)) / 2]] *
      ![![1, 0], ![0, Complex.exp (Complex.I * ↑Real.pi * ↑(-α).cast / 4)]]) := by
  ext i j ; fin_cases i <;> fin_cases j <;> norm_num [ Complex.ext_iff, sq ] <;> ring_nf <;>
  norm_num [Complex.exp_re, Complex.exp_im]

-- Remaining scalar goals for the X-π copy rule, discharged by heavy trig.
lemma x_pi_copy_remaining_goals (α : ZMod 8) :
  (2 = Real.exp (-(Real.pi * (α.cast : ℂ).im) / 4) * Real.cos (Real.pi * (α.cast : ℂ).re / 4) *
  Real.cos (Real.pi * (-α).cast / 4) +
        -(Real.sin (Real.pi * (-α).cast / 4) * (Real.exp (-(Real.pi * (α.cast : ℂ).im) / 4) *
        Real.sin (Real.pi * (α.cast : ℂ).re / 4))) +
      Real.exp (-(Real.pi * (α.cast : ℂ).im) / 4) * Real.cos (Real.pi * (α.cast : ℂ).re / 4) *
      Real.cos (Real.pi * (-α).cast / 4) +
      -(Real.sin (Real.pi * (-α).cast / 4) * (Real.exp (-(Real.pi * (α.cast : ℂ).im) / 4) *
      Real.sin (Real.pi * (α.cast : ℂ).re / 4))) ∧
    0 = Real.exp (-(Real.pi * (α.cast : ℂ).im) / 4) * Real.cos (Real.pi * (α.cast : ℂ).re / 4) *
    Real.sin (Real.pi * (-α).cast / 4) +
        Real.cos (Real.pi * (-α).cast / 4) * (Real.exp (-(Real.pi * (α.cast : ℂ).im) / 4) *
        Real.sin (Real.pi * (α.cast : ℂ).re / 4)) +
      Real.exp (-(Real.pi * (α.cast : ℂ).im) / 4) * Real.cos (Real.pi * (α.cast : ℂ).re / 4) *
      Real.sin (Real.pi * (-α).cast / 4) +
      Real.cos (Real.pi * (-α).cast / 4) * (Real.exp (-(Real.pi * (α.cast : ℂ).im) / 4) *
      Real.sin (Real.pi * (α.cast : ℂ).re / 4))) ∧
  (Real.cos (α.cast * Real.pi * (1 / 4)) = Real.exp (-(Real.pi * (α.cast : ℂ).im * (1 / 4))) *
  Real.cos (Real.pi * (α.cast : ℂ).re * (1 / 4)) ∧
   Real.sin (α.cast * Real.pi * (1 / 4)) = Real.exp (-(Real.pi * (α.cast : ℂ).im * (1 / 4))) *
   Real.sin (Real.pi * (α.cast : ℂ).re * (1 / 4)))
  := by
    fin_cases α <;> norm_num [ Complex.normSq, Complex.exp_re,
    Complex.exp_im, Complex.cos, Complex.sin ]
    <;> norm_num [ Real.pi_pos.ne' ] at *;
    · norm_num [ ZMod.cast, ZMod.val ] at *;
      erw [ Fin.coe_neg ] ; norm_num ; ring_nf ;
      norm_num [ mul_div ] ; ring_nf;
      norm_num [ show Real.pi * (7 / 4) = 2 * Real.pi - Real.pi / 4 by ring,
      Real.cos_two_pi_sub, Real.sin_two_pi_sub ] ;
      ring_nf ; norm_num
    · norm_num [ ZMod.cast, ZMod.val ] ; ring_nf ; norm_num [ mul_div ];
      erw [ Fin.coe_neg ] ; norm_num ; ring_nf ; norm_num [ mul_div ] ;
      norm_num [ show Real.pi * 3 / 2 = Real.pi + Real.pi / 2 by ring, Real.sin_add, Real.cos_add ]
    · norm_num [ ZMod.cast, ZMod.val ] at *;
      erw [ show ( -3 : ZMod 8 ) = 5 by decide ] ;
      norm_num [ ( by ring : Real.pi * 3 / 4 = Real.pi - Real.pi / 4 ),
      ( by ring : Real.pi * 5 / 4 = Real.pi + Real.pi / 4 ), Real.cos_add, Real.sin_add ] ;
      ring_nf ; norm_num
    · norm_num [ ZMod.cast, ZMod.val ];
      erw [ Nat.cast_succ ] ; norm_num ; ring_nf ; norm_num [ mul_div ] ;
    have h_cos : Real.cos (5 * Real.pi / 4) = -Real.cos (Real.pi / 4) := by
      rw [show 5 * Real.pi / 4 = Real.pi / 4 + Real.pi by ring, Real.cos_add_pi]
    have h_sin : Real.sin (5 * Real.pi / 4) = -Real.sin (Real.pi / 4) := by
      rw [show 5 * Real.pi / 4 = Real.pi + Real.pi / 4 by ring]
      rw [Real.sin_add]
      simp;
    simp_all [ Real.cos_pi_div_four, Real.sin_pi_div_four] ; ring_nf ;
    norm_num [ Real.exp_neg, Real.exp_mul, Real.exp_log ] at * ; aesop ;
    · norm_num [ ZMod.cast, ZMod.val ] ; ring_nf at * ; norm_num at * ;
      simp_all only [one_div, Nat.reduceAdd, neg_mul, mul_neg, sub_neg_eq_add]
      erw [ Fin.coe_neg ] ; norm_num ; ring_nf at * ; norm_num at * ;
      simp_all only [one_div]
      rw [ show Real.pi * ( 3 / 4 ) = Real.pi - Real.pi / 4 by ring,
      Real.cos_pi_sub, Real.sin_pi_sub ] ;
      norm_num ; ring_nf ; norm_num;
    · norm_num [ ZMod.cast, ZMod.val ] at * ; ring_nf at * ;
      simp_all only [Nat.reduceAdd, one_div]
      have h_trig : Real.sin (Real.pi * 3 * 4⁻¹) = Real.sqrt 2 / 2 ∧
      Real.cos (Real.pi * 3 * 4⁻¹) = -Real.sqrt 2 / 2 := by
        -- Using the angle addition formulas, we can simplify the sine and cosine terms.
        have h_trig : Real.sin (Real.pi * 3 / 4) = Real.sqrt 2 / 2 ∧
        Real.cos (Real.pi * 3 / 4) = -Real.sqrt 2 / 2 := by
          have h_sin : Real.sin (Real.pi - Real.pi / 4) = Real.sqrt 2 / 2 := by
            norm_num [ Real.sin_pi_sub ]
          have h_cos : Real.cos (Real.pi - Real.pi / 4) = -Real.sqrt 2 / 2 := by
            norm_num [ neg_div ] at *
          exact ⟨ by rw [ ← h_sin ] ; ring_nf, by rw [ ← h_cos ] ; ring_nf ⟩;
        exact h_trig;
      erw [ Fin.coe_neg ] ; norm_num ; ring_nf at * ;
      simp_all only [one_div]
      obtain ⟨left, right⟩ := h_trig
      ring
    · norm_num [ ZMod.cast, ZMod.val ] at *;
    · erw [ show ( ZMod.cast 5 : ℂ ) = 5 by rfl ] ; norm_num ;
      ring_nf ; norm_num [ mul_div ] ; aesop  ;
    · erw [ show ( ZMod.cast ( 6 : ZMod 8 ) : ℝ ) = 6 by norm_cast ] ;
      norm_num ; ring_nf ; norm_num [ mul_div ] ;
      erw [ show ( ⟨ 6, by decide ⟩ : ZMod 8 ) = 6 from rfl ] ;
      norm_num [ show Real.pi * 3 / 2 = Real.pi / 2 + Real.pi by ring,
      show Real.pi * 2 / 4 = Real.pi / 2 by ring ] ;
      erw [ show ( ZMod.cast 6 : ℂ ) = 6 by rfl ] ; norm_num
      [ show Real.pi * 6 / 4 = Real.pi / 2 + Real.pi by ring,
      show Real.pi * 2 / 4 = Real.pi / 2 by ring ] ;
      erw [ show ( ZMod.cast 2 : ℝ ) = 2 by rfl ] ; ring_nf; norm_num [ mul_div ] ;
    have h_cos_sin : Real.cos (Real.pi * 7 / 4) =
    Real.cos (Real.pi / 4) ∧ Real.sin (Real.pi * 7 / 4) =
    -Real.sin (Real.pi / 4) ∧ Real.cos (Real.pi * (-7) / 4) =
    Real.cos (Real.pi / 4) ∧ Real.sin (Real.pi * (-7) / 4) =
    Real.sin (Real.pi / 4) := by
      field_simp;
      norm_num [ ( by ring : Real.pi * 7 / 4 = 2 * Real.pi - Real.pi / 4 ) ];
    norm_num [ ZMod.cast, ZMod.val ] at * ; ring_nf at * ;
    simp_all only [one_div, Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue, and_self, and_true]
    obtain ⟨left, right⟩ := h_cos_sin
    obtain ⟨left_1, right⟩ := right
    obtain ⟨left_2, right⟩ := right
    apply And.intro
    · erw [ Nat.cast_succ ] ; norm_num ; ring_nf ;
      simp_all only [one_div]
      field_simp;
      simp at *;
    · erw [ Fin.coe_neg ] ; norm_num [ mul_assoc, mul_comm Real.pi _, mul_div ] ; ring;
      norm_num [ mul_div ]

-- Existence of the global phase used in the X-π copy soundness proof.
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
  erw [ show ( ZMod.cast 4 : ℂ ) = 4 by rfl ] ; ring_nf;
  norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im ] ;

-- Scalar equalities showing that H matches its Euler decomposition up to phase.
lemma euler_matrix_entries :
  ((↑√2)⁻¹ : ℂ) =
  ↑√2 * (1 - Complex.I) / 2 * ((1 + Complex.exp (Complex.I * (2 * ↑Real.pi) / 4)) / 2) ∧
  (↑√2)⁻¹ = ↑√2 * (1 - Complex.I) / 2 * ((1 - Complex.exp (Complex.I * (2 * ↑Real.pi) / 4)) /
  2 * Complex.exp (Complex.I * (2 * ↑Real.pi) / 4)) ∧
  (↑√2)⁻¹ = ↑√2 * (1 - Complex.I) / 2 * (Complex.exp (Complex.I * (2 * ↑Real.pi) / 4) *
   ((1 - Complex.exp (Complex.I * (2 * ↑Real.pi) / 4)) / 2)) ∧
  -(↑√2)⁻¹ = ↑√2 * (1 - Complex.I) / 2 * (Complex.exp (Complex.I * (2 * ↑Real.pi) / 4) *
  ((1 + Complex.exp (Complex.I * (2 * ↑Real.pi) / 4)) / 2) *
  Complex.exp (Complex.I * (2 * ↑Real.pi) / 4)) := by
  field_simp [Complex.ext_iff]
  ring_nf;
  norm_num [ Complex.exp_re, Complex.exp_im, mul_div,
  pow_three, Complex.ext_iff, Complex.exp_re, Complex.exp_im, sq  ] at *
end Matrix
