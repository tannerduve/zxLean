## Single-qubit ZX-calculus

This directory contains a self-contained development of the
single-qubit fragment of the π/4 ZX-calculus, including syntax,
rewrite system, and soundness proofs, built on top of the finite‑dimensional
quantum information framework from the `QuantumInfo` library
([`Lean-QuantumInfo`](https://github.com/Timeroot/Lean-QuantumInfo)).

### Main Reference
- M. Backens, *The ZX-calculus is complete for the single-qubit
  Clifford+T group*, 2014.  
  [`pdf`](https://www.cs.ox.ac.uk/people/miriam.backens/Clifford_T.pdf)

### File overview

- `AST.lean`  
  Defines the single-qubit ZX diagram syntax `SingleQubit.ZxDiagram`:
  generators (`empty`, `id`, `H`, `Z α`, `X α`), composition, and
  dagger. This is the core syntactic object for line graphs with at
  most one input and one output wire.

- `RewriteTerm.lean`  
  Defines the inductive relation `SingleQubit.ZxEquiv` capturing the
  equational theory of the single-qubit ZX-calculus: reflexivity,
  symmetry, transitivity, congruence for composition, structural
  axioms, colour-change rules, π-copy rules, and the Euler
  decomposition rule for `H`.

- `DenotationalSemantics.lean`  
  Interprets single-qubit diagrams as 2×2 complex matrices via
  `SingleQubit.interp`. Z- and X-spiders are given their standard
  matrix semantics, and all underlying quantum-related notions (Hilbert space,
  kets/bras, unitaries such as `H_gate`) are reused from the
  `QuantumInfo` library
  ([`Lean-QuantumInfo`](https://github.com/Timeroot/Lean-QuantumInfo)).

- `MatrixLemmas.lean`  
  Random collection of lemmas related to matrices and complex numbers that came up while proving soundness.
  Currently these are far too specific to be useful outside of where they were used, but maybe I can refactor and generalize later to contribute to Mathlib.

- `Soundness.lean`  
  Proves soundness of the single-qubit rewrite system:
  `ZxEquiv A B → interp A ≈ interp B`, where `≈` means equality of
  matrices up to a non-zero scalar factor. The proof proceeds by
  case analysis on `ZxEquiv` and uses the analytic facts from
  `MatrixLemmas`.

- `Coercion.lean`  
  Provides a coercion from single-qubit diagrams into the general
  `ZxTerm` syntax of the full ZX-calculus, preserving generators and
  composition.

- `Gates.lean`  
  Convenience definitions for standard single-qubit gates (`T`, `S`,
  `PauliX`, `PauliZ`) expressed as `SingleQubit.ZxDiagram`s.

### High-level picture

At a high level, this directory shows that the syntactic rewrite system
for single-qubit ZX diagrams is sound with respect to the usual
matrix semantics of qubit quantum mechanics. Together with the
completeness result of Backens [`Backens 2014`](https://www.cs.ox.ac.uk/people/miriam.backens/Clifford_T.pdf),
this places the formalisation within the broader story of the
Clifford+T ZX-calculus as a robust reasoning system for single-qubit
quantum circuits.

### Progress towards Backens' completeness theorem

The end goal for this directory is to formalise the entirety of
Backens' single-qubit Clifford+T result, including:

- a **normal form** for single-qubit Clifford+T diagrams; and
- a **completeness theorem** stating that two diagrams denote the same
  unitary (up to phase) if and only if they are related by `ZxEquiv`.

Current status:

- Diagram **syntax**, **rewrite system**, and **matrix semantics** are
  implemented (`AST`, `RewriteTerm`, `DenotationalSemantics`).
- All rewrite rules, including **π-copy**, **colour-change**, and the
  **Euler decomposition of H**, are proved **sound** with respect to
  the semantics (`MatrixLemmas`, `Soundness`).
- A coercion into the general `ZxTerm` calculus and basic gate
  definitions are in place (`Coercion`, `Gates`).

Planned work:

- Define and implement a **normal form** for single-qubit
  Clifford+T diagrams, following the structure in
  [`Backens 2014`](https://www.cs.ox.ac.uk/people/miriam.backens/Clifford_T.pdf).
- Prove **uniqueness** of the normal form and derive a full
  **completeness** theorem for the single-qubit ZX-calculus.



