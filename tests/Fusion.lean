import ZxCalculus.MultiQubit.RewriteTerm
open ZxTerm Real

theorem z_fusion : ZxEquiv (Z 2 1 1 ; Z 2 1 1) (Z 4 1 1) := by
  have h := ZxEquiv.z_fus 2 2 (n := 1) (m := 1) (k := 1)
  apply ZxEquiv.trans h
  ring_nf
  exact ZxEquiv.refl _

#check z_fusion

-- Need a soundness check next
