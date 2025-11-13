## Project Structure

```
ZxCalculus/
├── AST.lean                    # ZX diagram syntax (generators and terms)
├── RewriteTerm.lean            # Equational theory and rewrite rules
├── DenotationalSemantics.lean  # Interpretation as linear maps
├── Completeness.lean           # Soundness theorem and proofs
├── MatrixLemmas.lean           # Helper lemmas for matrix properties
├── Kronecker.lean              # Tensor product utilities
```

## Main Components

### AST (`ZxCalculus/AST.lean`)

Defines the syntax of ZX diagrams:
- **Generators**: Basic building blocks (empty, identity, swap, Hadamard, Z/X spiders, cup/cap)
- **ZxTerm**: Inductively defined diagrams with sequential (`;`) and parallel (`⊗`) composition
- **Dependent types**: Each diagram has a type `ZxTerm n m` representing n inputs and m outputs

### Rewrite Rules (`ZxCalculus/RewriteTerm.lean`)

Defines `ZxEquiv`, an inductive equivalence relation encoding:
- Symmetric monoidal category structure (associativity, units, interchange)
- ZX-calculus specific rules:
  - Spider fusion (composing spiders adds phases)
  - Color change (Hadamard conjugation swaps Z/X spiders)
  - π-copy rules (phase π spiders commute with opposite-color spiders)

### Denotational Semantics (`ZxCalculus/DenotationalSemantics.lean`)

Interprets ZX diagrams as linear maps (matrices):
- Maps n-wire diagrams to matrices representing linear operators on ℂ^(2^n)
- Uses Mathlib's matrix operations including Kronecker product for tensor composition
- Defines `interp : ZxTerm n m → LinMap n m` where `LinMap n m := Matrix (Fin (2^m)) (Fin (2^n)) ℂ`
- Implemented generators: identity, empty, swap, Hadamard gate, Z/X spiders

## Status

**Completed:**
- Core AST with dependent types
- Structural axioms (monoidal category laws)
- ZX rewrite rules: spider fusion, color change, π-copy, phase periodicity
- Matrix-based denotational semantics framework
- Generators: identity, empty, swap, Z/X spiders, Hadamard gate, cup/cap
- Sequential (`;`) and parallel (`⊗`) composition via matrix multiplication and Kronecker product
- Soundness theorem statement: `ZxEquiv A B → interp A = interp B`
- Proven soundness for: equivalence structure (refl/symm/trans), congruence rules, phase periodicity rules

**In Progress:**
- Additional rewrite rules (bialgebra, Euler decomposition, Hopf)
- Better diagram-like notation
- Soundness proofs for: spider fusion, color change, π-copy, identity axioms
- Helper lemmas in `MatrixLemmas.lean`: basis state properties, Hadamard conjugation, outer products
- Proof of `pow_tens_ket0_eq_basis` (tensor product of |0⟩ states)

**To Do:**
- Complete remaining soundness cases (requires matrix algebra lemmas)
- Completeness theorem: every representable linear map has a corresponding diagram
- Additional rewrite rules as needed (bialgebra, Euler decomposition)
