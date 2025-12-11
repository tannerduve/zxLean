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

/-! ### Angle and composition utilities -/

/-- The set `{0, 2, 4, 6} ⊆ ℤ/8ℤ` of even angles (Clifford (π/2) phases). -/
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

/-- Syntactic Clifford fragment (1-qubit diagrams with only Clifford gates).

The even-phase side conditions are baked into the constructors, making this
type convenient for algorithms. The predicate `Clifford`
is a logical property on `ZxDiagram`s. -/
inductive Clifford' : Type where
  | id : Clifford'
  | H : Clifford'
  | Z (α : ZMod 8) (h : Even α.val) : Clifford'
  | X (β : ZMod 8) (h : Even β.val) : Clifford'
  | comp (d₁ : Clifford') (d₂ : Clifford') : Clifford'

/-- Interpret a syntactic Clifford diagram as a `ZxDiagram`. -/
def Clifford'.toZxDiagram : Clifford' → ZxDiagram true true
  | .id => .id
  | .H => .H
  | .Z α _ => .Z α
  | .X β _ => .X β
  | .comp d₁ d₂ => (Clifford'.toZxDiagram d₁) ; (Clifford'.toZxDiagram d₂)

/-- Coercion instance from the syntactic Clifford fragment to `ZxDiagram`. -/
instance : Coe (Clifford') (ZxDiagram true true) where
  coe := Clifford'.toZxDiagram

/-- The coercion image of a Clifford' diagram is Clifford -/
lemma coe_isClifford (d : Clifford') :
  Clifford (d : ZxDiagram true true) := by
  induction d with
  | id => exact Clifford.id
  | H => exact Clifford.H
  | Z α h => exact Clifford.Z α h
  | X β h => exact Clifford.X β h
  | comp d₁ d₂ ih₁ ih₂ =>
      exact Clifford.comp ih₁ ih₂

/-- If a diagram is Clifford it is the image of a Clifford' diagram -/
lemma exists_Clifford' (d : ZxDiagram true true)
    (hC : Clifford d) :
  ∃ d' : Clifford', (d' : ZxDiagram true true) = d := by
  induction hC with
  | id =>
      refine ⟨.id, ?_⟩
      rfl
  | H =>
      refine ⟨.H, ?_⟩
      rfl
  | Z α hα =>
      refine ⟨.Z α hα, ?_⟩
      rfl
  | X β hβ =>
      refine ⟨.X β hβ, ?_⟩
      rfl
  | comp h₁ h₂ ih₁ ih₂ =>
      rcases ih₁ with ⟨d₁', hd₁'⟩
      rcases ih₂ with ⟨d₂', hd₂'⟩
      refine ⟨.comp d₁' d₂', ?_⟩
      rename_i d₁ d₂
      simp [Clifford'.toZxDiagram, hd₁', hd₂']

/-- Number of nodes in a single-qubit diagram. -/
def nodeCount : {n m : Bool} → ZxDiagram n m → ℕ
  | _, _, .id        => 0
  | _, _, .empty     => 0
  | _, _, .H         => 1
  | _, _, .Z _       => 1
  | _, _, .X _       => 1
  | _, _, .comp d₁ d₂ => nodeCount d₁ + nodeCount d₂

/-! ### Green/red fragment -/

/-- Predicate: diagram built only from Z- and X-spiders and composition. -/
inductive IsGreenRed : ZxDiagram true true → Prop
  | Z (α : ZMod 8) : IsGreenRed (.Z α)
  | X (β : ZMod 8) : IsGreenRed (.X β)
  | comp {d₁ d₂} : IsGreenRed d₁ → IsGreenRed d₂ → IsGreenRed (d₁ ; d₂)

/-- Syntactic fragment containing only green (Z) and red (X) spiders. -/
inductive GreenRed : Type where
  | Z (α : ZMod 8) : GreenRed
  | X (β : ZMod 8) : GreenRed
  | comp (d₁ : GreenRed) (d₂ : GreenRed) : GreenRed

/-- Interpret a syntactic green/red diagram as a `ZxDiagram`. -/
def GreenRed.toZxDiagram : GreenRed → ZxDiagram true true
  | .Z α => .Z α
  | .X β => .X β
  | .comp d₁ d₂ => (GreenRed.toZxDiagram d₁) ; (GreenRed.toZxDiagram d₂)

/-- Coercion instance from the green/red fragment to `ZxDiagram`. -/
instance : Coe GreenRed (ZxDiagram true true) where
  coe := GreenRed.toZxDiagram

namespace GreenRed

/-- Number of green/red spiders in a diagram. -/
def nodes : GreenRed → ℕ := nodeCount ∘ (↑· : GreenRed → ZxDiagram true true)

lemma nodeCount_coe (d : GreenRed) :
  nodeCount (d : ZxDiagram true true) = nodes d := by
  rfl

/-- Local reduction cases from Backens' Lemma 1, viewed as global
diagrams with explicit left/right green–red contexts.

Each constructor corresponds to one of the four bullets in the proof:
1. two adjacent spiders of the same colour (`sameColourZ`/`sameColourX`);
2. a 0-phase spider (`zeroPhaseZ`/`zeroPhaseX`);
3. a π-phase spider next to an opposite-colour spider (`piZ_X`/`piX_Z`);
4. three adjacent spiders with phases in `{±π/2}` and alternating colours
   (`tripleZXZ`, `tripleXZX`). -/
inductive Case : ZxDiagram true true → Prop
  | sameColourZ
      (L R : ZxDiagram true true) (α β : ZMod 8) :
      Case (L ; .Z α ; .Z β ; R)
  | sameColourX
      (L R : ZxDiagram true true) (α β : ZMod 8) :
      Case (L ; .X α ; .X β ; R)
  | zeroPhaseZ
      (L R : ZxDiagram true true) :
      Case (L ; .Z 0 ; R)
  | zeroPhaseX
      (L R : ZxDiagram true true) :
      Case (L ; .X 0 ; R)
  | piZ_X
      (L R : ZxDiagram true true) (α : ZMod 8) :
      -- Z π followed by X α
      Case (L ; .Z 4 ; .X α ; R)
  | piX_Z
      (L R : ZxDiagram true true) (α : ZMod 8) :
      -- X π followed by Z α
      Case (L ; .X 4 ; .Z α ; R)
  | tripleZXZ
      (L R : ZxDiagram true true)
      (a b c : ZMod 8) :
      -- three adjacent spiders Z–X–Z, typically with a,b,c ∈ {2,6}
      Case (L ; .Z a ; .X b ; .Z c ; R)
  | tripleXZX
      (L R : ZxDiagram true true)
      (a b c : ZMod 8) :
      -- three adjacent spiders X–Z–X, typically with a,b,c ∈ {2,6}
      Case (L ; .X a ; .Z b ; .X c ; R)

/-- Syntactic fragment for the four local cases, built from green–red
contexts and concrete phases. -/
inductive Case' : Type where
  | sameColourZ
      (L : GreenRed) (α β : ZMod 8) (R : GreenRed)
  | sameColourX
      (L : GreenRed) (α β : ZMod 8) (R : GreenRed)
  | zeroPhaseZ
      (L R : GreenRed)
  | zeroPhaseX
      (L R : GreenRed)
  | piZ_X
      (L : GreenRed) (α : ZMod 8) (R : GreenRed)
  | piX_Z
      (L : GreenRed) (α : ZMod 8) (R : GreenRed)
  | tripleZXZ
      (L : GreenRed) (a b c : ZMod 8) (R : GreenRed)
  | tripleXZX
      (L : GreenRed) (a b c : ZMod 8) (R : GreenRed)

/-- Interpret a syntactic case as a `GreenRed` diagram. -/
def Case'.toGreenRed : Case' → GreenRed
  | .sameColourZ L α β R =>
      .comp L (.comp (.Z α) (.comp (.Z β) R))
  | .sameColourX L α β R =>
      .comp L (.comp (.X α) (.comp (.X β) R))
  | .zeroPhaseZ L R =>
      .comp L (.comp (.Z 0) R)
  | .zeroPhaseX L R =>
      .comp L (.comp (.X 0) R)
  | .piZ_X L α R =>
      .comp L (.comp (.Z 4) (.comp (.X α) R))
  | .piX_Z L α R =>
      .comp L (.comp (.X 4) (.comp (.Z α) R))
  | .tripleZXZ L a b c R =>
      .comp L (.comp (.Z a) (.comp (.X b) (.comp (.Z c) R)))
  | .tripleXZX L a b c R =>
      .comp L (.comp (.X a) (.comp (.Z b) (.comp (.X c) R)))

/-- Interpret a syntactic case as a `ZxDiagram`. -/
def Case'.toZxDiagram : Case' → ZxDiagram true true :=
  GreenRed.toZxDiagram ∘ Case'.toGreenRed

/-- Coercion from `Case'` to `ZxDiagram`. -/
instance : Coe Case' (ZxDiagram true true) where
  coe := Case'.toZxDiagram

/-- The coercion image of a `Case'` diagram satisfies the semantic
`Case` predicate. -/
lemma coe_isCase (c : Case') :
  Case (c : ZxDiagram true true) := by
  cases c with
  | sameColourZ L α β R =>
      -- goal: `Case ((L:ZxDiagram) ; Z α ; Z β ; (R:ZxDiagram))`
      sorry
  | sameColourX L α β R =>
      sorry
  | zeroPhaseZ L R =>
      sorry
  | zeroPhaseX L R =>
      sorry
  | piZ_X L α R =>
      sorry
  | piX_Z L α R =>
      sorry
  | tripleZXZ L a b c R =>
      sorry
  | tripleXZX L a b c R =>
      sorry

/-- If a `ZxDiagram` is in one of the four local green/red cases,
then it is the coercion image of a `Case'` diagram. -/
lemma exists_Case' {d : ZxDiagram true true}
    (h : Case d) :
  ∃ c : Case', (c : ZxDiagram true true) = d := by
  cases h with
  | sameColourZ L R α β =>
      refine ⟨Case'.sameColourZ (L := ?_) (α := α) (β := β) (R := ?_), ?_⟩
      <;> sorry
  | sameColourX L R α β =>
      sorry
  | zeroPhaseZ L R =>
      sorry
  | zeroPhaseX L R =>
      sorry
  | piZ_X L R α =>
      sorry
  | piX_Z L R α =>
      sorry
  | tripleZXZ L R a b c =>
      sorry
  | tripleXZX L R a b c =>
      sorry

/-- "Small" means at most 3 nodes. -/
def Small (d : ZxDiagram true true) : Prop :=
  nodeCount d ≤ 3

/-- A Clifford green/red diagram
either has at most three spiders, or can be presented in one of the
four local cases.
-/
lemma clifford_greenRed_small_or_case
    (g : GreenRed)
    (hC : Clifford (g : ZxDiagram true true)) :
    nodes g ≤ 3 ∨
      ∃ c : Case', (c : ZxDiagram true true) = (g : ZxDiagram true true) := by
  sorry

end GreenRed

private lemma even0 : Even (0 : ZMod 8).val := by decide
private lemma even2 : Even (2 : ZMod 8).val := by decide

/-- Any Clifford operator can be written as one with only green and red nodes. -/
lemma green_red_of_Clifford
    (d : ZxDiagram true true) (hc : Clifford d) :
  ∃ d' : ZxDiagram true true,
      Clifford d' ∧ ZxEquiv d d' ∧ IsGreenRed d' := by
  induction hc with
  | id =>
      refine ⟨.Z 0, ?_, ?_, ?_⟩
      · exact Clifford.Z 0 even0
      · exact ZxEquiv.symm ZxEquiv.z_id
      · exact IsGreenRed.Z 0
  | H =>
      have h2 : Even (2 : ZMod 8).val := even2
      refine ⟨.Z 2 ; .X 2 ; .Z 2, ?_, ?_, ?_⟩
      · exact
          Clifford.comp
            (Clifford.comp (Clifford.Z 2 h2) (Clifford.X 2 h2))
            (Clifford.Z 2 h2)
      · apply ZxEquiv.trans ZxEquiv.euler_decomp
        apply ZxEquiv.assoc_comp'
      · exact
          IsGreenRed.comp
            (IsGreenRed.comp (IsGreenRed.Z 2) (IsGreenRed.X 2))
            (IsGreenRed.Z 2)
  | Z α hα =>
      exact ⟨.Z α, Clifford.Z α hα, ZxEquiv.refl _, IsGreenRed.Z α⟩
  | X β hβ =>
      exact ⟨.X β, Clifford.X β hβ, ZxEquiv.refl _, IsGreenRed.X β⟩
  | comp _ _ ih₁ ih₂ =>
      rcases ih₁ with ⟨d₁', hC₁, hEq₁, hGR₁⟩
      rcases ih₂ with ⟨d₂', hC₂, hEq₂, hGR₂⟩
      refine ⟨d₁' ; d₂', Clifford.comp hC₁ hC₂, ?_, IsGreenRed.comp hGR₁ hGR₂⟩
      exact ZxEquiv.seq_cong hEq₁ hEq₂

/-- Rewrite a syntactic Clifford diagram into the green/red fragment. -/
def Clifford'.toGreenRed : Clifford' → GreenRed
  | .id => .Z 0
  | .H =>
      have _ : Even (2 : ZMod 8).val := even2
      .comp (.Z 2) (.comp (.X 2) (.Z 2))
  | .Z α _ => .Z α
  | .X β _ => .X β
  | .comp d₁ d₂ =>
      .comp (Clifford'.toGreenRed d₁) (Clifford'.toGreenRed d₂)

/-- The image of a syntactic Clifford diagram under `toGreenRed` is green/red. -/
lemma toGreenRed_isGreenRed (d : Clifford') :
  IsGreenRed (GreenRed.toZxDiagram (Clifford'.toGreenRed d)) := by
  induction d with
  | id =>
      simp [Clifford'.toGreenRed, GreenRed.toZxDiagram]
      exact IsGreenRed.Z 0
  | H =>
      simp [Clifford'.toGreenRed, GreenRed.toZxDiagram]
      have h2 : Even (2 : ZMod 8).val := even2
      apply IsGreenRed.comp
      · apply IsGreenRed.Z
      · apply IsGreenRed.comp
        · apply IsGreenRed.X
        · apply IsGreenRed.Z
  | Z α h =>
      simp [Clifford'.toGreenRed, GreenRed.toZxDiagram]
      exact IsGreenRed.Z α
  | X β h =>
      simp [Clifford'.toGreenRed, GreenRed.toZxDiagram]
      exact IsGreenRed.X β
  | comp d₁ d₂ ih₁ ih₂ =>
      simp [Clifford'.toGreenRed, GreenRed.toZxDiagram]
      exact IsGreenRed.comp ih₁ ih₂

/-- Clifford diagrams that are already made only of Z/X spiders. -/
def IsCliffordGreenRed (d : ZxDiagram true true) : Prop :=
  Clifford d ∧ IsGreenRed d

/-! ### Local building blocks `W`, `V`, `U` -/

/-- The `W` component in Backens' normal form. -/
inductive W : {n m : Bool} → ZxDiagram n m → Prop
  | empty : W .empty
  | x_two : W (.X 2)
  | z_then_x : W (.comp (.Z 2) (.X 2))

inductive W' : Bool → Bool → Type where
  | empty : W' false false
  | X2    : W' true true
  | ZX    : W' true true

/-- Interpret a `W'` diagram as a `ZxDiagram` -/
def W'.toZxDiagram : {n m : Bool} → W' n m → ZxDiagram n m
  | false, false, .empty => .empty
  | true,  true,  .X2    => .X 2
  | true,  true,  .ZX    => .comp (.Z 2) (.X 2)

/-- Coercion from `W'` to `ZxDiagram`. -/
instance {n m : Bool} : Coe (W' n m) (ZxDiagram n m) where
  coe := W'.toZxDiagram

/-- The coercion image of a W' diagram is W -/
lemma coe_isW {n m : Bool} (d : W' n m) :
  W (d : ZxDiagram n m) := by
  cases d <;> constructor

/-- If a Zx diagram is W, it is the coercion image of a W' diagram -/
lemma exists_W' {n m : Bool} (d : ZxDiagram n m)
    (hW : W d) :
  ∃ d' : W' n m, (d' : ZxDiagram n m) = d := by
  cases hW with
  | empty =>
      refine ⟨.empty, ?_⟩
      rfl
  | x_two =>
      refine ⟨.X2, ?_⟩
      rfl
  | z_then_x =>
      refine ⟨.ZX, ?_⟩
      rfl

/-- The `V` component in Backens' normal form. -/
inductive V : ZxDiagram true true → Prop
  | z_one_x_two : V (.comp (.Z 1) (.X 2))
  | z_three_x_two : V (.comp (.Z 3) (.X 2))

inductive V' : Type where
  | Z1X2 : V'
  | Z3X2 : V'

/-- Interpret a `V'` diagram as a `ZxDiagram`. -/
def V'.toZxDiagram : V' → ZxDiagram true true
  | .Z1X2 => .comp (.Z 1) (.X 2)
  | .Z3X2 => .comp (.Z 3) (.X 2)

/-- Coercion from `V'` to `ZxDiagram`. -/
instance : Coe V' (ZxDiagram true true) where
  coe := V'.toZxDiagram

/-- The coercion image of a V' diagram is V -/
lemma coe_isV (d : V') :
  V (d : ZxDiagram true true) := by
  cases d <;> constructor

/-- If a Zx diagram is V, it is the coercion image of a V' diagram -/
lemma exists_V' (d : ZxDiagram true true)
    (hV : V d) :
  ∃ d' : V', (d' : ZxDiagram true true) = d := by
  cases hV with
  | z_one_x_two =>
      refine ⟨.Z1X2, ?_⟩
      rfl
  | z_three_x_two =>
      refine ⟨.Z3X2, ?_⟩
      rfl

/-- The `U` component in Backens' normal form. -/
inductive U : ZxDiagram true true → Prop
  | z_then_x (α β : ZMod 8) :
      -- `Z(π/4 + β) ; X(α)` with α, β ∈ {0, π/2, π, -π/2}
      Even α.val → Even β.val →
      U (.comp (.Z (1 + β)) (.X α))
  | z_x_z (γ s : ZMod 8) :
      -- `Z(π/4 + γ) ; X(±π/2) ; Z(π/2)` with γ ∈ {0, π/2, π, -π/2}
      Even γ.val → s ∈ ({2, 6} : Finset (ZMod 8)) →
      U (.comp (.Z (1 + γ)) (.comp (.X s) (.Z 2)))

inductive U' : Type where
  | Z1Xα : (α : ZMod 8) → Even α.val → U'
  | Z1Xsz2 : (γ s : ZMod 8) → Even γ.val → s ∈ ({2, 6} : Finset (ZMod 8)) → U'

/-- Interpret a `U'` diagram as a `ZxDiagram`. -/
def U'.toZxDiagram : U' → ZxDiagram true true
  | .Z1Xα α _ => .comp (.Z (1 + α)) (.X α)
  | .Z1Xsz2 γ s _ _ => .comp (.Z (1 + γ)) (.comp (.X s) (.Z 2))

/-- Coercion from `U'` to `ZxDiagram`. -/
instance : Coe U' (ZxDiagram true true) where
  coe := U'.toZxDiagram

/-- The coercion image of a U' diagram is U -/
lemma coe_isU (d : U') :
  U (d : ZxDiagram true true) := by cases d <;> constructor <;> assumption

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
