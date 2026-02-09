# Claim 9 Phase AE: Covariance Criterion for \(\beta\)-Transfer Channel Bounds

Date: 2026-02-09 (US)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim9-nonabelian-beyond-window-transfer-assumptions.md`
- `research/workspace/notes/theorems/2026-02-09-claim9-nonabelian-strong-coupling-window-derivation.md`

## Goal

Make the AD transfer assumptions less free-form by giving an explicit
covariance-based sufficient criterion for the \(\beta\)-derivative channel split
\((rT)\) + \((r+T)\) + bounded remainder.

## Dependency Declaration

\[
\mathrm{C9\text{-}NA}(G,D)=\mathrm{C9\text{-}NA}(SU(N),D),\qquad N\ge2,\ D\ge3.
\]
No statement is promoted unless both \(G\) and \(D\) are explicit.

## Setup

For Wilson lattice action
\[
S_W(U)=-\frac{\beta}{N}\sum_p \Re\operatorname{Tr}(U_p),
\]
and rectangle \(C(r,T)\), define
\[
W_{r,T}:=W(C(r,T)).
\]
Using differentiation under the path-integral measure:
\[
\partial_\beta\log\langle W_{r,T}\rangle_\beta
=
\frac{1}{N}\sum_p
\operatorname{Cov}_\beta\!\left(\Re\operatorname{Tr}(U_p),\,\mathbf 1_{W_{r,T}}\right)
\Big/\langle W_{r,T}\rangle_\beta.
\]

Partition plaquettes into:

1. area class \(\mathcal A(r,T)\) with \(|\mathcal A|=rT/a^2\),
2. perimeter strip \(\mathcal P(r,T)\) with \(|\mathcal P|=2(r+T)/a\),
3. remainder class \(\mathcal R(r,T)\).

## Covariance-Bound Assumptions (AE)

Assume for \(\beta\in[\beta_0,\beta_1]\):

1. **(AE-A)** area-average covariance control:
   \[
   \left|
   \frac{1}{|\mathcal A|}\sum_{p\in\mathcal A}\Xi_{\beta,p}(r,T)
   \right|\le A_*,
   \]
2. **(AE-P)** perimeter-average covariance control:
   \[
   \left|
   \frac{1}{|\mathcal P|}\sum_{p\in\mathcal P}\Xi_{\beta,p}(r,T)
   \right|\le B_*,
   \]
3. **(AE-R)** bounded remainder covariance sum:
   \[
   \left|
   \sum_{p\in\mathcal R}\Xi_{\beta,p}(r,T)
   \right|\le R_*,
   \]
where \(\Xi_{\beta,p}(r,T)\) denotes the normalized covariance summand from the
derivative identity above.

## Theorem 1 (AE \(\Rightarrow\) AD Channel Assumptions)

Under (AE-A)+(AE-P)+(AE-R), one can define coefficients
\[
a_\beta(r,T):=
-\frac{a^2}{rT}\sum_{p\in\mathcal A}\Xi_{\beta,p}(r,T),\qquad
b_\beta(r,T):=
\frac{a}{2(r+T)}\sum_{p\in\mathcal P}\Xi_{\beta,p}(r,T),
\]
and remainder
\[
R_\beta(r,T):=\sum_{p\in\mathcal R}\Xi_{\beta,p}(r,T),
\]
so that
\[
\partial_\beta\log\langle W_{r,T}\rangle_\beta
=
-a_\beta(r,T)\,rT+b_\beta(r,T)\,(r+T)+R_\beta(r,T),
\]
with explicit bounds
\[
|a_\beta(r,T)|\le A_*,\qquad |b_\beta(r,T)|\le B_*,\qquad |R_\beta(r,T)|\le R_*.
\]
Hence AD assumptions (TB-DIFF)+(TB-BOUNDS) are discharged whenever these
covariance controls hold on the extraction window.

### Proof sketch

Write \(\partial_\beta\log\langle W\rangle\) as class-sum decomposition over
\(\mathcal A,\mathcal P,\mathcal R\). Rescale area and perimeter sums by class
sizes; apply (AE-A),(AE-P),(AE-R). \(\square\)

## Corollary (AE + AD + AB)

If AE holds on \([\beta_0,\beta_1]\) and AD anchor data holds at \(\beta_0\),
then AD transfer and AB finite-\(T\) extraction bounds follow on the same window.

This creates a concrete checklist:

1. prove covariance controls (AE),
2. transfer coefficients via AD,
3. read off potential bounds via AB.

## Validation Contract

### Assumptions

1. explicit \((SU(N),D)\) model class and \(\beta\)-window,
2. explicit plaquette-class partition \(\mathcal A,\mathcal P,\mathcal R\).

### Units and dimensions check

1. \(a_\beta\) scales with area channel \(rT\),
2. \(b_\beta\) scales with perimeter channel \(r+T\),
3. \(R_\beta\) is a bounded dimensionless residual contribution.

### Symmetry/conservation checks

1. decomposition uses only gauge-invariant Wilson-loop expectations,
2. plaquette-class partition preserves lattice translation/covariance structure
   up to explicit boundary terms.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim9_nonabelian_derivative_covariance_check.py
```

The script checks:

1. channel decomposition identity for \(\partial_\beta\log\langle W\rangle\),
2. recovered \((a_\beta,b_\beta,R_\beta)\) bounds against \((A_*,B_*,R_*)\),
3. compatibility of recovered channels with AD transfer estimates.

### Confidence statement

AE is theorem-grade as a sufficient-criterion layer under explicit covariance
controls. It reduces AD to a concrete bound-verification problem but does not yet
prove those covariance controls from first principles.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic seed printed by script,
3. date anchor: 2026-02-09 (US).
