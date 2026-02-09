# Claim 1 Phase AS (AN-4): \(d=3\) Intermediate Bridge Candidate Beyond Ultralocal

Date: 2026-02-09 (CET)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim1-d2-ultralocal-phi4-closure.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-d4-lift-obstruction-sheet.md`

## Goal

Define the next bridge class between:

1. closed \(d=2\) ultralocal interacting theorem (AP),
2. unresolved \(d=4\) local propagation frontier (AQ).

This note provides a theorem candidate in \(d=3\) with explicit proof obligations.

## Candidate \(d=3\) Local Lattice Class

On \(\Lambda_{a,L}\subset a\mathbb Z^3\) with periodic boundary, define
\[
S_{a,L}^{(\kappa)}(\phi)
=
a^3\sum_{x\in\Lambda_{a,L}}
\left[
\frac{m_0^2}{2}\phi_x^2+\frac{\lambda}{4}\phi_x^4
\right]
+
\frac{\kappa a^3}{2}\sum_{\langle x,y\rangle}\frac{(\phi_x-\phi_y)^2}{a^2},
\]
with \(m_0^2>0,\lambda>0,\kappa\ge0\).

For \(c\in\mathbb C\), \(\Re c>0\), define normalized states
\[
\omega_{c,a,L}^{(\kappa)}(F)=
\frac{\int e^{-cS_{a,L}^{(\kappa)}(\phi)}F(\phi)\,d\phi}
{\int e^{-cS_{a,L}^{(\kappa)}(\phi)}\,d\phi}.
\]

At \(\kappa=0\), this reduces to ultralocal product structure.

## Theorem Candidate (Bridge Form)

For local cylinders \(F\), under the hypotheses below, limits
\[
\omega_c^{(\kappa)}(F):=\lim_{a\to0,\ L\to\infty}\omega_{c,a,L}^{(\kappa)}(F)
\]
exist for \(\kappa\in[0,\kappa_*]\), and satisfy:

1. continuity at \(\kappa=0\) (bridge to AP closure),
2. SD pass-through for local insertions,
3. dependence only on \(c\) along \(\tau_\mu\)-orbits.

## Explicit Proof Obligations (Required Inputs)

To close the candidate, establish:

1. **B1: uniform local moment bounds** in \((a,L)\) for \(\kappa\in[0,\kappa_*]\),
2. **B2: local tightness / precompactness** of cylinder marginals,
3. **B3: denominator non-vanishing** on the working compact \(c\)-domain,
4. **B4: SD insertion control** for nearest-neighbor coupling terms,
5. **B5: \(\kappa\)-continuity estimate** near \(\kappa=0\) for local \(F\).

Without B1-B5, the bridge remains candidate-level.

## First Quantitative Target for Closure

A concrete next theorem target:

1. prove B5 with an explicit small-\(\kappa\) bound
   \[
   |\omega_{c,a,L}^{(\kappa)}(F)-\omega_{c,a,L}^{(0)}(F)|
   \le C_F\,\kappa
   \]
   uniformly on a restricted local observable class;
2. then use B1-B4 to pass to \((a,L)\to(0,\infty)\).

## Why \(d=3\) Here

\(d=3\) is the intended intermediate rung:

1. richer than AP ultralocal closure,
2. less boundary-critical than \(d=4\),
3. aligned with the dimension ladder in the roadmap.

## Reproducibility Hook

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_bridge_toy_coupling_scan.py
```

The script gives a finite-dimensional nearest-neighbor toy scan showing smooth weak-coupling departure from the \(\kappa=0\) ultralocal point.
