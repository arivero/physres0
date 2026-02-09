# Claim 1 Phase AT (AN-5): Small-\(\kappa\) Lipschitz Prototype for the \(d=3\) Bridge

Date: 2026-02-09 (CET)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim1-d3-intermediate-bridge-candidate.md`

## Goal

Prove the first quantitative B5-style estimate in a finite-dimensional nearest-neighbor surrogate:
a linear small-\(\kappa\) bound for local observable expectations.

## Two-Site Surrogate Setup

Fix \(c>0\), \(m_0^2>0\), \(\lambda>0\), and
\[
V(u)=\frac{m_0^2}{2}u^2+\frac{\lambda}{4}u^4.
\]
For \(\kappa\ge0\),
\[
S_\kappa(x,y)=V(x)+V(y)+\frac{\kappa}{2}(x-y)^2.
\]
Define probability measure
\[
d\mu_\kappa(x,y)=Z_\kappa^{-1}e^{-cS_\kappa(x,y)}\,dx\,dy.
\]
For bounded measurable \(F\),
\[
\omega_\kappa(F):=\int_{\mathbb R^2}F\,d\mu_\kappa.
\]
Let
\[
G(x,y):=(x-y)^2.
\]

## Proposition 1 (Derivative Formula)

For bounded \(F\), \(\kappa\mapsto\omega_\kappa(F)\) is \(C^1\) on \([0,\infty)\), and
\[
\frac{d}{d\kappa}\omega_\kappa(F)
=
-\frac{c}{2}\,\mathrm{Cov}_{\mu_\kappa}(F,G).
\]

### Proof

Write \(\omega_\kappa(F)=N_\kappa(F)/Z_\kappa\) with
\[
N_\kappa(F)=\int F e^{-cS_\kappa},\qquad Z_\kappa=\int e^{-cS_\kappa}.
\]
Differentiation under the integral is justified by quartic decay and bounded \(F\):
\[
N_\kappa'(F)= -\frac{c}{2}\int FG\,e^{-cS_\kappa},
\qquad
Z_\kappa'= -\frac{c}{2}\int G\,e^{-cS_\kappa}.
\]
Apply quotient rule:
\[
\omega_\kappa'(F)
=
\frac{N_\kappa'Z_\kappa-N_\kappa Z_\kappa'}{Z_\kappa^2}
=
-\frac{c}{2}\left(\omega_\kappa(FG)-\omega_\kappa(F)\omega_\kappa(G)\right).
\]
\(\square\)

## Theorem 2 (Small-\(\kappa\) Lipschitz Bound)

Fix \(\kappa_*>0\). Define
\[
M_{\kappa_*}:=\sup_{0\le\kappa\le\kappa_*}\omega_\kappa(G).
\]
Then \(M_{\kappa_*}<\infty\), and for every bounded \(F\),
\[
|\omega_\kappa(F)-\omega_0(F)|
\le
c\,\|F\|_\infty\,M_{\kappa_*}\,\kappa,
\qquad
0\le\kappa\le\kappa_*.
\]

### Proof

From Proposition 1 and \(|\mathrm{Cov}(F,G)|\le 2\|F\|_\infty\,\omega_\kappa(G)\),
\[
|\omega_\kappa'(F)|\le c\|F\|_\infty\,\omega_\kappa(G).
\]
Integrate from \(0\) to \(\kappa\):
\[
|\omega_\kappa(F)-\omega_0(F)|
\le
\int_0^\kappa |\omega_s'(F)|\,ds
\le
c\|F\|_\infty \int_0^\kappa \omega_s(G)\,ds
\le
c\|F\|_\infty M_{\kappa_*}\kappa.
\]
It remains to show \(M_{\kappa_*}<\infty\).  
For each fixed \(\kappa\), quartic confinement gives finite \(\omega_\kappa(G)\).  
Continuity in \(\kappa\) follows by dominated convergence on numerator and denominator integrals, so \(\kappa\mapsto\omega_\kappa(G)\) is continuous on compact \([0,\kappa_*]\), hence bounded. \(\square\)

## Corollary (B5 Prototype for the \(d=3\) Program)

The bridge obligation B5 from Phase AS has a concrete prototype:
small gradient coupling creates at most linear deformation of local bounded observables in this surrogate.

Programmatic translation:

1. replace \(G=(x-y)^2\) by local gradient-energy insertion on lattice blocks,
2. prove a uniform analog of \(M_{\kappa_*}<\infty\),
3. obtain a lattice-to-continuum B5 estimate.

## Reproducibility

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_lipschitz_prototype_check.py
```

The script reports numeric \(|\omega_\kappa(F)-\omega_0(F)|/\kappa\) ratios and verifies they stay below the theorem constant estimate.
