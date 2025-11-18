# ZX-Calculus in Lean 4

In-progress formalization of the ZX-calculus in Lean 4.

[The ZX-calculus](https://zxcalculus.com/intro.html) is a graphical language for
reasoning about quantum circuits and linear maps. This repository currently
focuses on the **single-qubit π/4 ZX-calculus** (the Clifford+T fragment),
following Backens’ completeness result for the single-qubit Clifford+T group
[`Backens 2014`](https://www.cs.ox.ac.uk/people/miriam.backens/Clifford_T.pdf),
and builds on top of the finite-dimensional quantum information framework
from the `QuantumInfo` library
([`Lean-QuantumInfo`](https://github.com/Timeroot/Lean-QuantumInfo)).
See `ZxCalculus/SingleQubit/README.md` for a detailed overview of the
single-qubit development and current progress.

## What this project includes

- A dependently-typed abstract syntax tree (AST) for ZX diagrams
- An equational theory capturing the ZX-calculus rewrite rules
- Denotational semantics interpreting diagrams as linear maps between
  finite-dimensional Hilbert spaces (via `QuantumInfo`)
- A growing theorem library demonstrating verifiability of ZX diagrams in Lean,
  with the **single-qubit soundness theorem** already established
  (`ZxCalculus/SingleQubit`).

## Building

Requires [Lean 4 and Mathlib](https://lean-lang.org/install/). Build in this directory:

```bash
lake build
```

## Single-qubit development

The `ZxCalculus/SingleQubit/` directory contains:

- `AST.lean`: syntax for single-qubit ZX diagrams (`SingleQubit.ZxDiagram`)
- `RewriteTerm.lean`: the single-qubit ZX equational theory `ZxEquiv`
- `DenotationalSemantics.lean`: interpretation as 2×2 matrices, reusing
  qubit notions and gates from `QuantumInfo`
- `MatrixLemmas.lean`: matrix / exponential lemmas needed for soundness
- `Soundness.lean`: proof that `ZxEquiv A B → interp A ≈ interp B`
  (equality up to non-zero global phase)

The long-term goal is to extend this to a **normal form** and a full
**completeness theorem** for the single-qubit Clifford+T ZX-calculus, in line
with [`Backens 2014`](https://www.cs.ox.ac.uk/people/miriam.backens/Clifford_T.pdf).

## References

- Bob Coecke and Aleks Kissinger. *Picturing Quantum Processes: A First Course in Quantum Theory and Diagrammatic Reasoning.* Cambridge University Press, 2017.

- PennyLane. "Introduction to the ZX-calculus." https://pennylane.ai/qml/demos/tutorial_zx_calculus

- Chris Heunen and Jamie Vicary. *Categories for Quantum Theory: An Introduction.* Oxford University Press, 2019. https://doi.org/10.1093/oso/9780198739623.001.0001

- M. Backens. *The ZX-calculus is complete for the single-qubit Clifford+T group.*, 2014.  
  [`pdf`](https://www.cs.ox.ac.uk/people/miriam.backens/Clifford_T.pdf)

- A. Meiburg et al. *Quantum Information in Lean* (`QuantumInfo` library).  
  [`Lean-QuantumInfo`](https://github.com/Timeroot/Lean-QuantumInfo)
