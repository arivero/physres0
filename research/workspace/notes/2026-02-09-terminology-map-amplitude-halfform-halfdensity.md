# Terminology Map: Amplitude vs Half-Form vs Half-Density

Date: 2026-02-09  
Scope: Goal 1 paper language standardization after literature check

## Decision Summary

There is no single universal replacement for `half-density`. The standard term depends on the technical layer.

Use this house style:

1. **Paper 1 (statics, QM-without-time-evolution):**
   primary term = `probability amplitude`; output layer = `Born density` / `Born probability`.
2. **Paper 2 (dynamics, path integral):**
   primary term = `transition amplitude` / `Feynman kernel`.
3. **Geometric quantization layer:**
   use `half-form` and `metaplectic correction`.
4. **Microlocal/FIO and groupoid kernel calculus:**
   use `half-density` or `1/2-density` precisely.
5. **BV odd-symplectic context (if used):**
   use `semidensity`.

## Why This Mapping (Source-Backed)

1. Feynman formalism uses the language of amplitudes whose modulus-square gives probabilities; this supports `probability amplitude` for physics-facing narrative.
2. Geometric quantization literature uses `half-form` and `metaplectic correction` for the square-root line-bundle correction.
3. Microlocal/FIO literature uses `Lagrangian half-densities` as the natural objects for oscillatory states.
4. Lie-groupoid pseudodifferential calculus defines convolution using the square-root density bundle \(D^{1/2}\), i.e., half-densities.
5. BV odd-symplectic literature standardizes `semidensity` terminology.

## Sources (Primary/Technical)

1. Feynman, *Space-Time Approach to Non-Relativistic Quantum Mechanics* (1948): https://journals.aps.org/rmp/abstract/10.1103/RevModPhys.20.367
2. Feynman Nobel lecture (historical Dirac-to-kernel thread): https://www.nobelprize.org/prizes/physics/1965/feynman/lecture/
3. Bates and Weinstein, *Lectures on the Geometry of Quantization* (half-forms, metaplectic correction, half-densities): https://www.math.berkeley.edu/~alanw/GofQ.pdf
4. Dyatlov, *Introduction to Microlocal Analysis* (Lagrangian half-densities): https://math.mit.edu/~dyatlov/19.136/lecture_notes.pdf
5. Lauter, Monthubert, Nistor, *Pseudodifferential Analysis on Continuous Family Groupoids* (bundle \(D^{1/2}\), groupoid half-density calculus): https://www.numdam.org/item/ASNSP_2000_4_29_4_681_0/
6. Khudaverdian, *Semidensities on odd symplectic supermanifolds* (BV terminology): https://research.manchester.ac.uk/en/publications/semidensities-on-odd-symplectic-supermanifolds
7. Hall and Kirwin, *Unitarity in “quantization commutes with reduction”* (half-form correction language): https://doi.org/10.1016/j.aim.2008.03.013
8. Hall and Mitchell, *The Segal-Bargmann transform for quantum mechanics on Lie groups. I. The basics* (half-form vs half-density quantization framing): https://doi.org/10.1016/j.geomphys.2022.104497

## Writing Rule for Current Drafts

1. Replace generic `half-density` in main text with `probability amplitude` (Paper 1) or `transition amplitude` (Paper 2).
2. Keep `half-density` only where the object is explicitly a section of \(D^{1/2}\) or groupoid kernel density.
3. Use `half-form/metaplectic correction` only in geometric quantization subsections.
4. Avoid mixing `semidensity` unless a BV odd-symplectic construction is actually introduced.

