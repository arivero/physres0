# Claim 9 Phase AF: First-Principles Beyond-Window Transfer via Cluster-Shell Control

Date: 2026-02-09 (US)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim9-nonabelian-strong-coupling-window-derivation.md`
- `research/workspace/notes/theorems/2026-02-09-claim9-nonabelian-beyond-window-transfer-assumptions.md`
- `research/workspace/notes/theorems/2026-02-09-claim9-nonabelian-derivative-covariance-criterion.md`

## Goal

Replace the AD transfer lane's free channel bounds by a first-principles-style
criterion: a mass-gap/exponential-clustering shell estimate that implies
\((rT)\)-channel, \((r+T)\)-channel, and uniformly bounded residual control.

## Dependency Declaration

\[
\mathrm{C9\text{-}NA}(G,D)=\mathrm{C9\text{-}NA}(SU(N),D),\qquad N\ge2,\ D\ge3.
\]
All statements remain explicit in \((G,D)\), \(\beta\)-window, and
extraction window.

## Setup

Fix rectangular loop \(C(r,T)\) and lattice spacing \(a\), with
\[
A(C)=\frac{rT}{a^2},\qquad P(C)=\frac{2(r+T)}{a}.
\]
For \(\beta\in[\beta_0,\beta_1]\), write the derivative identity as
\[
\partial_\beta\log\langle W_C\rangle_\beta=\sum_p \Xi_{\beta,p}(C).
\]
Let \(\Sigma(C)\) be a fixed minimal plaquette filling of \(C\). For shell index
\(k\in\mathbb N_0\), denote by \(\mathcal S_k(C)\) the plaquettes at shell-distance
\(k\) from \(\partial\Sigma(C)\) in a fixed local lattice metric.

## First-Principles Assumption Package (AF)

Assume for all \(\beta\in[\beta_0,\beta_1]\):

1. **(AF-GAP)** uniform transfer-matrix gap:
   \[
   m_{\mathrm{gap}}(\beta)\ge m_*>0.
   \]
2. **(AF-BULK)** area-density channel:
   \[
   \sum_{p\in\Sigma(C)}\Xi_{\beta,p}(C)=-a_\beta A(C),\qquad |a_\beta|\le A_*.
   \]
3. **(AF-SHELL)** exponentially decaying shell profile with corner-defect control:
   there exist \(\nu_D(k)\ge0\), \(u_{\beta,k}\), \(Q_*>0\) such that
   \[
   \left|
   \sum_{p\in\mathcal S_k(C)}\Xi_{\beta,p}(C)
   -
   \nu_D(k)\,P(C)\,u_{\beta,k}
   \right|
   \le
   Q_*e^{-m_*k},
   \]
   with
   \[
   |u_{\beta,k}|\le U_*e^{-m_*k},\qquad 0\le \nu_D(k)\le \nu_*.
   \]
4. **(AF-SUM)** shell summability:
   \[
   M_0:=\sum_{k\ge0}e^{-m_*k}<\infty.
   \]

Interpretation:
AF-GAP + AF-SHELL is the first-principles bridge object, since exponential
clustering/mixing plus shell counting directly controls derivative transport.

## Theorem 1 (AF Implies AD Transfer Bounds)

Under AF assumptions, define
\[
b_\beta:=\frac{2}{a}\sum_{k\ge0}\nu_D(k)\,u_{\beta,k},
\]
\[
R_\beta(r,T):=
\sum_{k\ge0}
\left(
\sum_{p\in\mathcal S_k(C(r,T))}\Xi_{\beta,p}(C(r,T))
-\nu_D(k)\,P(C(r,T))\,u_{\beta,k}
\right).
\]
Then
\[
\partial_\beta\log\langle W(r,T)\rangle_\beta
=
-a_\beta\,rT+b_\beta\,(r+T)+R_\beta(r,T),
\]
and bounds
\[
|a_\beta|\le A_*,
\]
\[
|b_\beta|
\le
\frac{2}{a}\nu_*U_*\sum_{k\ge0}e^{-m_*k}
\,=:\,B_*,
\]
\[
|R_\beta(r,T)|
\le
Q_*\sum_{k\ge0}e^{-m_*k}
\,=:\,R_*.
\]
Hence AD assumptions (TB-DIFF)+(TB-BOUNDS) hold with explicit
\((A_*,B_*,R_*)\) generated from AF data.

### Proof sketch

Split \(\sum_p\Xi_{\beta,p}\) into \(\Sigma(C)\) plus shell sums. AF-BULK gives
the \((rT)\)-channel. AF-SHELL writes each shell contribution as
\(\nu_D(k)P(C)u_{\beta,k}\) plus bounded defect. Summing the principal shell part
and using \(P(C)=2(r+T)/a\) yields the \((r+T)\)-channel coefficient \(b_\beta\).
Summing defects and AF-SUM gives uniform residual bound \(R_*\). \(\square\)

## Corollary (AF -> AE -> AD -> AB Pipeline)

In the same \((SU(N),D)\) lane:

1. AF provides first-principles control of transfer-channel bounds,
2. AE becomes an explicit covariance-check realization of AF shells,
3. AD transfer theorem follows with explicit constants,
4. AB finite-\(T\) linear extraction bounds follow on \([\beta_0,\beta_1]\).

## Validation Contract

### Assumptions

1. explicit \((G,D)=(SU(N),D)\), \(N\ge2,\ D\ge3\),
2. explicit \(\beta\)-window and extraction window,
3. shell metric and shell decomposition are fixed.

### Units and dimensions check

1. \(a_\beta\) couples to \(rT\) (area channel),
2. \(b_\beta\) couples to \(r+T\) through \(P=2(r+T)/a\),
3. \(R_\beta\) is dimensionless as a log-derivative residual.

### Symmetry/conservation checks

1. all channels are built from gauge-invariant Wilson-loop derivatives,
2. shell decomposition is geometric and does not alter gauge invariance.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim9_nonabelian_first_principles_transfer_check.py
```

The script checks:

1. shell decomposition identity for \(\partial_\beta\log\langle W\rangle\),
2. derived \(a_\beta,b_\beta,R_\beta\) channel extraction,
3. AF-to-AD bound transfer \((A_*,B_*,R_*)\) across a \((r,T,\beta)\) grid.

### Confidence statement

AF is a scoped first-principles upgrade over pure transfer assumptions: channel
bounds are now generated from mass-gap/exponential-shell controls.
Open gap remains proving AF uniformly from continuum non-Abelian dynamics
outside scoped windows and closing dynamical-matter string-breaking rigor.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic seed printed by script,
3. date anchor: 2026-02-09 (US).
