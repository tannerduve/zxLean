import ZxCalculus.SingleQubit.RewriteTerm
/-!
# Normal forms for single-qubit ZX diagrams

This file sets up the normal-form machinery for the single-qubit
Clifford+T fragment, following Backens' completeness proof.

We work with the syntax `SingleQubit.ZxDiagram` and the rewrite
relation `ZxEquiv` from `SingleQubit.RewriteTerm`.

The main ingredients are:

* basic combinators on angles and diagrams (`cliffordAngles`, `boolPiPhase`,
  `composeChain`);
* local classes of diagrams `W`, `V`, and `U`;
* left/right Clifford normal forms `LeftForm` and `RightForm`;
* a global normal form `NormalForm` built from `W`–`V`⋯`V`–`U` stacks.
-/
namespace SingleQubit

open ZxDiagram

/-! ### Clifford angles -/

/-- The set `{0, 2, 4, 6} ⊆ ℤ/8ℤ` of even angles (Clifford phases). -/
def cliffordAngles : Finset (ZMod 8) := {0, 2, 4, 6}

/-- An angle `a : ℤ/8ℤ` is *Clifford* if its representative is even. -/
def IsCliffordAngle (a : ZMod 8) : Prop := Even a.val

lemma even_zmod8_cases (a : ZMod 8) (h : Even a.val) :
    a = 0 ∨ a = 2 ∨ a = 4 ∨ a = 6 := by
  have h_cases : a.val % 2 = 0 := by
    exact Nat.even_iff.mp h
  fin_cases a <;> simp +decide at h_cases ⊢

lemma mem_cliffordAngles_of_even (a : ZMod 8) (h : IsCliffordAngle a) :
    a ∈ cliffordAngles := by
  have := even_zmod8_cases a h
  rcases this with rfl | rfl | rfl | rfl <;> simp [cliffordAngles]

/-! ### Boolean-controlled phases and composition utilities -/

/-- Boolean-controlled π phase (0 when `false`, π when `true`). -/
def boolPiPhase (b : Bool) : ZMod 8 :=
  if b then (4 : ZMod 8) else 0

@[simp] lemma boolPiPhase_eq_zero_iff {b} :
  boolPiPhase b = 0 ↔ b = false := by
  cases b <;> simp [boolPiPhase]; intro h; cases h

@[simp] lemma boolPiPhase_eq_four_iff {b} :
  boolPiPhase b = 4 ↔ b = true := by
  cases b <;> simp [boolPiPhase]; intro h; cases h

/-- Sequentially compose a list of single-qubit diagrams (head first). -/
def composeChain : List (ZxDiagram true true) → ZxDiagram true true
  | [] => .id
  | d :: ds => d ; composeChain ds

@[simp] lemma composeChain_nil :
  composeChain [] = (ZxDiagram.id) := rfl

@[simp] lemma composeChain_cons (d ds) :
  composeChain (d :: ds) = d ; composeChain ds := rfl

lemma composeChain_append_equiv (xs ys : List (ZxDiagram true true)) :
  ZxEquiv (composeChain (xs ++ ys))
          (composeChain xs ; composeChain ys) := by
  induction xs with
  | nil =>
      simpa [composeChain] using (ZxEquiv.symm (ZxEquiv.unit_comp_l (composeChain ys)))
  | cons d ds ih =>
      simp [composeChain]
      apply ZxEquiv.trans
      · exact ZxEquiv.seq_cong (ZxEquiv.refl d) ih
      · exact ZxEquiv.symm (ZxEquiv.assoc_comp d (composeChain ds) (composeChain ys))

/-! ### Clifford fragment -/

/-- Single-qubit Clifford diagrams:
all Z/X spiders carry even phases (angles in `cliffordAngles`). -/
inductive Clifford : ZxDiagram true true → Prop
  | id :
      Clifford .id
  | H :
      Clifford .H
  | Z (α : ZMod 8) (h : Even α.val) :
      Clifford (.Z α)
  | X (β : ZMod 8) (h : Even β.val) :
      Clifford (.X β)
  | comp {d₁ d₂} :
      Clifford d₁ → Clifford d₂ → Clifford (d₁ ; d₂)

/-- Number of Z/X spiders in a single-qubit diagram. -/
def spiderCount : {n m : Bool} → ZxDiagram n m → ℕ
  | _, _, .id        => 0
  | _, _, .empty     => 0
  | _, _, .H         => 0
  | _, _, .Z _       => 1
  | _, _, .X _       => 1
  | _, _, .comp d₁ d₂ => spiderCount d₁ + spiderCount d₂

/-! ### Local building blocks `W`, `V`, `U` -/

/-- The `W` component in Backens' normal form. -/
inductive W : {n m : Bool} → ZxDiagram n m → Prop
  | empty : W .empty
  | x_two : W (.X 2)
  | z_then_x : W (.comp (.Z 2) (.X 2))

/-- The `V` component in Backens' normal form. -/
inductive V : {n m : Bool} → ZxDiagram n m → Prop
  | z_one_x_two : V (.comp (.Z 1) (.X 2))
  | z_three_x_two : V (.comp (.Z 3) (.X 2))

/-- The `U` component in Backens' normal form. -/
inductive U : {n m : Bool} → ZxDiagram n m → Prop
  | z_then_x (α β : ZMod 8) :
      -- `Z(π/4 + β) ; X(α)` with α, β ∈ {0, π/2, π, -π/2}
      Even α.val → Even β.val →
      U (.comp (.Z (1 + β)) (.X α))
  | z_x_z (γ s : ZMod 8) :
      -- `Z(π/4 + γ) ; X(±π/2) ; Z(π/2)` with γ ∈ {0, π/2, π, -π/2}
      Even γ.val → s ∈ ({2, 6} : Finset (ZMod 8)) →
      U (.comp (.Z (1 + γ)) (.comp (.X s) (.Z 2)))

/-! ### Left and right Clifford normal forms -/

/-- Left normal form: either `Z α ∘ X β` or `X π/2 ∘ Z ±π/2 ∘ X γ`. -/
inductive LeftForm : ZxDiagram true true → Prop
  | two_node (α β : ZMod 8) :
      Even α.val → Even β.val →
      LeftForm (ZxDiagram.comp (ZxDiagram.Z α) (ZxDiagram.X β))
  | three_node (γ s : ZMod 8) :
      Even γ.val → s ∈ ({2, 6} : Finset (ZMod 8)) →
      LeftForm (ZxDiagram.comp (ZxDiagram.X 2)
                (ZxDiagram.comp (ZxDiagram.Z s) (ZxDiagram.X γ)))

/-- Right normal form: either `X β ∘ Z α` or `X γ ∘ Z ±π/2 ∘ X π/2`. -/
inductive RightForm : ZxDiagram true true → Prop
  | two_node (β α : ZMod 8) :
      Even β.val → Even α.val →
      RightForm (ZxDiagram.comp (ZxDiagram.X β) (ZxDiagram.Z α))
  | three_node (γ s : ZMod 8) :
      Even γ.val → s ∈ ({2, 6} : Finset (ZMod 8)) →
      RightForm (ZxDiagram.comp (ZxDiagram.X γ)
                 (ZxDiagram.comp (ZxDiagram.Z s) (ZxDiagram.X 2)))

inductive IsGreenRed : ZxDiagram true true → Prop
  | Z (α : ZMod 8) : IsGreenRed (.Z α)
  | X (β : ZMod 8) : IsGreenRed (.X β)
  | comp {d₁ d₂} : IsGreenRed d₁ → IsGreenRed d₂ → IsGreenRed (d₁ ; d₂)

private lemma even0 : Even (0 : ZMod 8).val := by decide
private lemma even2 : Even (2 : ZMod 8).val := by decide

/-- Any clifford operator can be written as one with only green and red nodes -/
lemma green_red_of_Clifford (d : ZxDiagram true true)
 (hc : Clifford d) : ∃ d' : ZxDiagram true true,
  Clifford d' ∧ ZxEquiv d d' ∧ IsGreenRed d' := by
  induction hc with
  | id =>
    use (.Z 0)
    constructor
    · apply Clifford.Z
      simp [Even, ZMod.val]
      use 0
    · constructor
      · apply ZxEquiv.symm
        apply ZxEquiv.z_id
      · apply IsGreenRed.Z
  | H =>
    use (.Z 2 ; .X 2 ; .Z 2)
    constructor
    · constructor
      · apply Clifford.comp
        · apply Clifford.Z
          simp [Even, ZMod.val]
          use 1
        apply Clifford.X
        simp [Even, ZMod.val]
        use 1
      · apply Clifford.Z
        simp [Even, ZMod.val]
        use 1
    · constructor
      · apply ZxEquiv.trans
        · apply ZxEquiv.euler_decomp
        · apply ZxEquiv.assoc_comp'
      · apply IsGreenRed.comp
        · apply IsGreenRed.comp
          · apply IsGreenRed.Z
          · apply IsGreenRed.X
        · apply IsGreenRed.Z
  | Z α hα => refine ⟨.Z α, Clifford.Z α hα, ZxEquiv.refl _, IsGreenRed.Z α⟩
  | X β hβ => refine ⟨.X β, Clifford.X β hβ, ZxEquiv.refl _, IsGreenRed.X β⟩
  | comp h₁ h₂ ih₁ ih₂ =>
      rcases ih₁ with ⟨d₁', hC₁, hEq₁, hGR₁⟩
      rcases ih₂ with ⟨d₂', hC₂, hEq₂, hGR₂⟩
      refine ⟨d₁' ; d₂', Clifford.comp hC₁ hC₂, ?_, IsGreenRed.comp hGR₁ hGR₂⟩
      exact ZxEquiv.seq_cong hEq₁ hEq₂

lemma LeftForm.comp {d₁ d₂ : ZxDiagram true true}
  (h₁ : LeftForm d₁) (h₂ : LeftForm d₂) :
  ∃ d, LeftForm d ∧ d₁ ; d₂ ≈ d := by
  sorry

lemma exists_leftForm (C : ZxDiagram true true) (hC : Clifford C) :
  ∃ d, LeftForm d ∧ C ≈ d := by
  induction hC with
  | id =>
      -- C = id
      -- find a simple LeftForm equivalent to id (e.g. Z 0 ; X 0)
      refine ⟨Z 0 ; X 0, ?_, ?_⟩
      · sorry
      · sorry
  | H =>
      -- C = H, use euler_decomp then simplify
      sorry
  | Z α hα =>
      -- C = Z α, choose LeftForm (Z α ; X 0)
      sorry
  | X β hβ =>
      -- C = X β, choose LeftForm (Z 0 ; X β)
      sorry
  | comp h₁ h₂ ih₁ ih₂ =>
      -- use ih₁, ih₂, and a lemma composing LeftForms
      rcases ih₁ with ⟨d₁, hL₁, hEq₁⟩
      rcases ih₂ with ⟨d₂, hL₂, hEq₂⟩
      -- we want a lemma:
      --   LeftForm d₁ → LeftForm d₂ → ∃ d, LeftForm d ∧ d₁ ; d₂ ≈ d
      have := LeftForm.comp hL₁ hL₂
      rcases this with ⟨d, hLd, hEq⟩
      refine ⟨d, hLd, ?_⟩
      -- chain the equivalences:
      -- C = C₁ ; C₂ ≈ d₁ ; d₂ ≈ d
      refine ZxEquiv.trans ?_ hEq
      exact ZxEquiv.seq_cong hEq₁ hEq₂

/-- Lemma 1 (Backens): every Clifford+T operator has a unique
representation in both left and right normal forms. -/
theorem lemma1_unique_representation (C : ZxDiagram true true) (hC : Clifford C) :
    (∃! d, LeftForm d ∧ ZxEquiv C d) ∧
      (∃! d, RightForm d ∧ ZxEquiv C d) :=
  by
  sorry

/-- Lemma 2 (Backens): every operator of the form `T ∘ C` has a unique
representation in `U`. -/
lemma lemma2_unique_representation (C : ZxDiagram true true) :
    ∃! d, U d ∧ ∃ t : ZMod 8, ZxEquiv (.comp (.Z t) C) d :=
  sorry

/-! ### Phase-shuffling lemmas (Backens Lemma 3–5) -/

lemma lemma3_push_V (C : ZxDiagram true true)
    (hC : LeftForm C) (Vd : ZxDiagram true true) (hV : V Vd) :
    ∃ (w v' : ZxDiagram true true) (a b : Bool),
      W w ∧ V v' ∧
        ZxEquiv (C ; Vd)
          (w ; (.Z (boolPiPhase a)) ; (.X (boolPiPhase b)) ; v') := by
  sorry

lemma lemma3_push_U (C : ZxDiagram true true)
    (hC : LeftForm C) (Ud : ZxDiagram true true) (hU : U Ud) :
    ∃ (w u' : ZxDiagram true true) (a b : Bool),
      W w ∧ U u' ∧
        ZxEquiv (C ; Ud)
          (w ; (.Z (boolPiPhase a)) ; (.X (boolPiPhase b)) ; u') := by
  sorry

lemma lemma4_phase_shuffle
    {n : ℕ} (hn : 0 < n)
    (Vs : Fin n → ZxDiagram true true)
    (hV : ∀ i, V (Vs i))
    (a b : Bool) :
    ∃ (Vs' : Fin n → ZxDiagram true true) (a' b' : Bool),
      (∀ i, V (Vs' i)) ∧
        ZxEquiv
          ((.Z (boolPiPhase a)) ; (composeChain (List.ofFn Vs)) ;
            (.X (boolPiPhase b)))
          ((composeChain (List.ofFn Vs')) ;
            (.Z (boolPiPhase a')) ; (.X (boolPiPhase b'))) := by
  sorry

/-! ### Stacked global normal form -/

/--
Normal-form stack used in Backens' Lemma 3–5:

`w ; V₁ ; … ; Vₙ ; u` with `w ∈ W`, each `Vᵢ ∈ V`, and `u ∈ U`.
We fix a concrete bracketing using `composeChain` so that the
normal form is an actual subset of diagrams (not just up to ≃).
-/

/- Shape of a stacked normal-form diagram `w ; V₁ ; … ; Vₙ ; u`. -/
def normalFormDiagram
    (w : ZxDiagram true true)
    (Vs : List (ZxDiagram true true))
    (u : ZxDiagram true true) : ZxDiagram true true :=
  w ; composeChain (Vs ++ [u])

/-- Global normal form: either Clifford (left form) or a W–V⋯V–U stack. -/
inductive NormalForm : ZxDiagram true true → Prop
  | clifford (d : ZxDiagram true true) :
      Clifford d → NormalForm d
  | stack (w u : ZxDiagram true true) (Vs : List (ZxDiagram true true)) :
      W w → U u → (∀ v ∈ Vs, V v) →
      NormalForm (normalFormDiagram w Vs u)

/-- Main global normal-form theorem (Backens Theorem 5). -/
theorem theorem5_normal_form
    (D : ZxDiagram true true) :
    LeftForm D ∨
      ∃ d, NormalForm d ∧ ZxEquiv D d := by
  sorry

end SingleQubit
