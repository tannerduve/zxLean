import ZxCalculus.RewriteTerm
open ZxTerm Real

/-- X spider fusion adds phases -/
theorem x_fusion_basic :
  ZxEquiv (X (π/4) 1 1 ; X (π/4) 1 1) (X (π/2) 1 1) := by
  have h := ZxEquiv.x_fus (π/4) (π/4) (n := 1) (m := 1) (k := 1)
  apply ZxEquiv.trans h
  have : π/4 + π/4 = π/2 := by ring
  rw [this]
  exact ZxEquiv.refl _

/-- X fusion with zero phase -/
theorem x_fusion_with_zero :
  ZxEquiv (X 0 1 1 ; X (π/3) 1 1) (X (π/3) 1 1) := by
  have h := ZxEquiv.x_fus 0 (π/3) (n := 1) (m := 1) (k := 1)
  apply ZxEquiv.trans h
  have : 0 + π/3 = π/3 := by ring
  rw [this]
  exact ZxEquiv.refl _

/-- X fusion to full rotation -/
theorem x_fusion_full_rotation :
  ZxEquiv (X (π/2) 1 1 ; X (3*π/2) 1 1) (X (2*π) 1 1) := by
  have h := ZxEquiv.x_fus (π/2) (3*π/2) (n := 1) (m := 1) (k := 1)
  apply ZxEquiv.trans h
  have : π/2 + 3*π/2 = 2*π := by ring
  rw [this]
  exact ZxEquiv.refl _

/-- X-0 is identity -/
theorem x_zero_is_id : ZxEquiv (X 0 1 1) id := ZxEquiv.x_id

#check x_fusion_basic
#check x_fusion_with_zero
#check x_zero_is_id
