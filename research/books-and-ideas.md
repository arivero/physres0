# Books and Ideas

Last updated: 2026-02-08

## Core Books (Quantum Theory)

1. J. J. Sakurai and J. Napolitano, *Modern Quantum Mechanics*.
2. R. Shankar, *Principles of Quantum Mechanics*.
3. M. A. Nielsen and I. L. Chuang, *Quantum Computation and Quantum Information*.
4. A. Altland and B. Simons, *Condensed Matter Field Theory*.

## Core Books (QFT and Particles)

1. M. E. Peskin and D. V. Schroeder, *An Introduction to Quantum Field Theory*.
2. M. D. Schwartz, *Quantum Field Theory and the Standard Model*.
3. S. Weinberg, *The Quantum Theory of Fields* (Vols. I-III).
4. P. A. Zyla et al. (Particle Data Group), *Review of Particle Physics* (living reference).

## Core Books (GR and Quantum Gravity)

1. R. M. Wald, *General Relativity*.
2. S. Carroll, *Spacetime and Geometry*.
3. C. Rovelli, *Quantum Gravity*.
4. J. Polchinski, *String Theory* (Vols. I-II).

## Formal Methods / Lean Track

1. Lean 4 documentation and community tutorials.
2. Mathlib documentation and theorem search workflows.
3. PhysLean as the physics specific formalization substrate.

## High Value Project Ideas

1. PhysLean-first canonical formalization:
Formalize short derivations in QM and QFT (commutators, conservation statements, Ward-identity style lemmas) and measure proof friction points.

2. CAS-to-Lean bridge:
Prototype a pipeline that exports symbolic identities from SymPy/Cadabra into Lean statement skeletons for human/agent completion.

3. Triple-check amplitude workflow:
For simple tree-level EFT processes, enforce three checks: symbolic derivation, numerical sampling, and known limit behavior.

4. QG consistency notebook series:
Build a set of notebooks testing minisuperspace or semiclassical toy models with explicit constraint and unit checks.

5. Agentic literature map:
Keep a continuously updated map of arXiv categories (`math.LO`, `math.AG`, `math-ph`, `hep-th`, `hep-ph`, `gr-qc`) with claim extraction + verification status.

## 12-Week Suggested Progression

1. Weeks 1-2: environment setup + first Lean and symbolic sanity tasks.
2. Weeks 3-5: QM and QFT derivation tasks with reproducibility reports.
3. Weeks 6-8: PhysLean formalization tasks and counterexample-first testing.
4. Weeks 9-10: particle theory mini-project with HEP data or EFT constraints.
5. Weeks 11-12: QG toy-model project + full report with assumptions and failure analysis.
