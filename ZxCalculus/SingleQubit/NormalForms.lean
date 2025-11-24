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

/-- Sequentially compose a list of single-qubit diagrams (head first). -/
def composeChain : List (ZxDiagram true true) → ZxDiagram true true
  | [] => .id
  | d :: ds => d ; composeChain ds

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

/-- Lemma 1 (Backens): every Clifford+T operator has a unique
representation in both left and right normal forms. -/
theorem lemma1_unique_representation (C : ZxDiagram true true) :
    (∃! d, LeftForm d ∧ ZxEquiv C d) ∧
      (∃! d, RightForm d ∧ ZxEquiv C d) :=
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
