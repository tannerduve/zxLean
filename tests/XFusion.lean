import ZxCalculus.RewriteTerm
open ZxTerm Real

/-- X spider fusion adds phases -/
theorem x_fusion_basic :
  ZxEquiv (X 1 1 1 ; X 1 1 1) (X 2 1 1) := by
  have h := ZxEquiv.x_fus 1 1 (n := 1) (m := 1) (k := 1)
  apply ZxEquiv.trans h
  ring_nf
  exact ZxEquiv.refl _

/-- X fusion with zero phase -/
theorem x_fusion_with_zero :
  ZxEquiv (X 0 1 1 ; X 2 1 1) (X 2 1 1) := by
  have h := ZxEquiv.x_fus 0 2 (n := 1) (m := 1) (k := 1)
  apply ZxEquiv.trans h
  ring_nf
  exact ZxEquiv.refl _

/-- X fusion to full rotation -/
theorem x_fusion_full_rotation :
  ZxEquiv (X 2 1 1 ; X 6 1 1) (X 8 1 1) := by
  have h := ZxEquiv.x_fus 2 6 (n := 1) (m := 1) (k := 1)
  apply ZxEquiv.trans h
  ring_nf
  exact ZxEquiv.refl _

/-- X-0 is identity -/
theorem x_zero_is_id : ZxEquiv (X 0 1 1) id := ZxEquiv.x_id

#check x_fusion_basic
#check x_fusion_with_zero
#check x_zero_is_id
