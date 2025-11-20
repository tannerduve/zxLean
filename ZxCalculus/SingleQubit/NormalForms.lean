import ZxCalculus.SingleQubit.RewriteTerm

open SingleQubit

inductive W : {n m : Bool} → ZxDiagram n m → Prop
  | empty : W .empty
  | x_two : W (.X 2)
  | z_then_x : W (.comp (.Z 2) (.X 2))

inductive V : {n m : Bool} → ZxDiagram n m → Prop
  | z_one_x_two : V (.comp (.Z 1) (.X 2))
  | z_three_x_two : V (.comp (.Z 3) (.X 2))

lemma even_zmod8_cases (a : ZMod 8) (h : Even a.val) :
    a = 0 ∨ a = 2 ∨ a = 4 ∨ a = 6 := by
      have h_cases : a.val % 2 = 0 := by
        apply Nat.even_iff.mp h;
      fin_cases a <;> simp +decide at h_cases ⊢

-- Left normal form: either (Z α ∘ X β) or (X π/2 ∘ Z ±π/2 ∘ X γ)
inductive LeftForm : ZxDiagram true true → Prop
  | two_node (α β : ZMod 8) :
      Even α.val → Even β.val →
      LeftForm (ZxDiagram.comp (ZxDiagram.Z α) (ZxDiagram.X β))
  | three_node (γ s : ZMod 8) :
      Even γ.val → s ∈ ({2, 6} : Finset (ZMod 8)) →
      LeftForm (ZxDiagram.comp (ZxDiagram.X 2)
                (ZxDiagram.comp (ZxDiagram.Z s) (ZxDiagram.X γ)))

-- Right normal form: either (X β ∘ Z α) or (X γ ∘ Z ±π/2 ∘ X π/2)
inductive RightForm : ZxDiagram true true → Prop
  | two_node (β α : ZMod 8) :
      Even β.val → Even α.val →
      RightForm (ZxDiagram.comp (ZxDiagram.X β) (ZxDiagram.Z α))
  | three_node (γ s : ZMod 8) :
      Even γ.val → s ∈ ({2, 6} : Finset (ZMod 8)) →
      RightForm (ZxDiagram.comp (ZxDiagram.X γ)
                 (ZxDiagram.comp (ZxDiagram.Z s) (ZxDiagram.X 2)))

-- Lemma 1: Every Clifford+T operator has a unique representation in each form
theorem lemma1_unique_representation (C : ZxDiagram true true) :
  (∃! d, LeftForm d ∧ ZxEquiv C d) ∧ (∃! d, RightForm d ∧ ZxEquiv C d) :=
  sorry

-- instance {n m : Bool} : DecidablePred (@W n m) := fun d => by
--   cases d
--   · -- empty
--     exact isTrue W.empty
--   · -- id
--     exact isFalse (fun h => by cases h)
--   · -- H
--     exact isFalse (fun h => by cases h)
--   · -- Z
--     exact isFalse (fun h => by cases h)
--   · -- X
--     rename_i α
--     by_cases h : α = 2
--     · subst h
--       exact isTrue W.x_two
--     · exact isFalse (fun hw => by cases hw; contradiction)
--   · -- comp
--     rename_i d1 d2
--     cases d1
--     · exact isFalse (fun h => by cases h)  -- empty
--     · exact isFalse (fun h => by cases h)  -- id
--     · exact isFalse (fun h => by cases h)  -- H
--     · -- Z
--       rename_i α
--       cases d2
--       · exact isFalse (fun h => by cases h)  -- empty
--       · exact isFalse (fun h => by cases h)  -- id
--       · exact isFalse (fun h => by cases h)  -- H
--       · rename_i β
--         by_cases h : α = 2 ∧ β = 2
--         · case pos =>
--           obtain ⟨rfl, rfl⟩ := h
--           exact isTrue W.z_then_x
--         · case neg =>
--           exact isFalse (fun hw => by cases hw; contradiction)
--       · case comp.Z.comp m' A β =>
--         by_cases h : α = 2 ∧ m' = true
--         · obtain ⟨rfl, rfl⟩ := h
--           by_cases h₁ : m = true
--           · sorry
--           sorry
--         · sorry
--     · sorry
--     · sorry
