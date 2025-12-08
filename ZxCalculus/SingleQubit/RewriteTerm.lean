import ZxCalculus.SingleQubit.AST

open SingleQubit

/-!
# Rewrite rules for single-qubit ZX diagrams

This file defines the equational theory of the single-qubit ZX calculus.
The `ZxEquiv` relation combines:
- Standard equivalence relation structure
- Congruence with respect to sequential composition
- Structural axioms (associativity, identity laws) "only topology matters"
- ZX-calculus specific rewrite rules
-/

inductive ZxEquiv : {n m : Bool} → ZxDiagram n m → ZxDiagram n m → Prop where
-- Equivalence relation
| refl : ∀ {n m} (f : ZxDiagram n m), ZxEquiv f f
| symm : ∀ {n m} {f g : ZxDiagram n m}, ZxEquiv f g → ZxEquiv g f
| trans : ∀ {n m} {f g h : ZxDiagram n m}, ZxEquiv f g → ZxEquiv g h → ZxEquiv f h

-- Congruence: equivalence respects composition
| seq_cong : ∀ {n k m} {f f' : ZxDiagram n k} {g g' : ZxDiagram k m},
    ZxEquiv f f' → ZxEquiv g g' → ZxEquiv (ZxDiagram.comp f g) (ZxDiagram.comp f' g')

-- Structural axioms: "only topology matters"
| assoc_comp : ∀ {n k l m} (f : ZxDiagram n k) (g : ZxDiagram k l) (h : ZxDiagram l m),
    ZxEquiv (ZxDiagram.comp (ZxDiagram.comp f g) h) (ZxDiagram.comp f (ZxDiagram.comp g h))
| unit_comp_l : ∀ (f : ZxDiagram true true), ZxEquiv (ZxDiagram.comp .id f) f
| unit_comp_r : ∀ (f : ZxDiagram true true), ZxEquiv (ZxDiagram.comp f .id) f
| empty_unit : ZxEquiv (ZxDiagram.comp .empty .empty) .empty

-- ZX-calculus specific rewrite rules
  -- Z/X identity rules (phase 0 is identity).
| z_id : ZxEquiv (.Z 0) .id
| x_id : ZxEquiv (.X 0) .id
-- Fusion rules: consecutive spiders of the same colour add their phases.
| z_fus : ∀ (α β : ZMod 8), ZxEquiv (ZxDiagram.comp (.Z α) (.Z β)) (.Z (α + β))
| x_fus : ∀ (α β : ZMod 8), ZxEquiv (ZxDiagram.comp (.X α) (.X β)) (.X (α + β))
-- π-copy rules: a phase-π spider can be copied through the opposite colour.
| z_pi_copy : ∀ (α : ZMod 8), ZxEquiv (ZxDiagram.comp (.Z 4) (.X α))
  (ZxDiagram.comp (.X (-α)) (.Z 4))
| x_pi_copy : ∀ (α : ZMod 8), ZxEquiv (ZxDiagram.comp (.X 4) (.Z α))
  (ZxDiagram.comp (.Z (-α)) (.X 4))
-- Colour-change: conjugation by H swaps Z and X.
| color_change_z : ∀ (α : ZMod 8), ZxEquiv (ZxDiagram.comp (ZxDiagram.comp .H (.Z α)) .H) (.X α)
| color_change_x : ∀ (α : ZMod 8), ZxEquiv (ZxDiagram.comp (ZxDiagram.comp .H (.X α)) .H) (.Z α)
-- Euler decomposition for H in the Clifford+T fragment.
| euler_decomp : ZxEquiv .H (ZxDiagram.comp (.Z 2) (ZxDiagram.comp (.X 2) (.Z 2)))
-- Hadamard gates are self-inverse
| h_involutive : ZxEquiv (ZxDiagram.comp .H .H) .id
