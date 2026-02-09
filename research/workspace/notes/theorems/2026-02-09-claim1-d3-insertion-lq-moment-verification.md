# Claim 1 Phase BS (AN-26B): \(d=3\) Insertion \(L^{4/3}\)-Moment Verification

Date: 2026-02-09 (CET)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim1-d3-cutoff-lift-closure.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-d3-cb1-tail-insertion-closure.md`

## Goal

Close the AN-26 conditional gate by verifying, in the same scoped Euclidean
\(d=3\) branch, an explicit uniform insertion-moment bound
\[
\sup_{a,L,\kappa,c}\omega\!\left(|\partial_i S_{a,L}^{(\kappa)}|^q\right)<\infty
\]
for one exponent \(q>1\).

## Target/Model/Existence Declaration (Non-Drift Rule)

1. target dimension: \(d=3\),
2. model class: AN-24 nearest-neighbor lattice \(\phi^4\), Euclidean
   \(c\in[c_0,c_1]\subset(0,\infty)\), \(0<a\le1\), \(\kappa\in[0,\kappa_*]\),
3. existence notion: regulated finite-volume moment verification for the AN-26
   SD test-side extension gate,
4. geometric \(1/2\)-density role: interpretation only.

## Setup

Use finite-volume periodic action
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
with \(m_0^2>0,\lambda>0\). Let
\[
d\mu_{c,a,L}^{(\kappa)}(\phi)
=
\frac{1}{Z_{c,a,L}^{(\kappa)}}e^{-cS_{a,L}^{(\kappa)}(\phi)}\,d\phi,
\qquad c\in[c_0,c_1].
\]
Fix site \(i\in\Lambda_{a,L}\), and define insertion
\[
\mathcal D_i:=\partial_{\phi_i}S_{a,L}^{(\kappa)}
=
a^3\big(m_0^2\phi_i+\lambda\phi_i^3\big)
\kappa a\sum_{y\sim i}(\phi_i-\phi_y).
\]

## Proposition 1 (Uniform Site Moments Used by AN-26B)

Uniformly in \(a,L,\kappa,c\):
\[
\omega(\phi_i^2)\le \frac{1}{c_0m_0^2a^3},
\qquad
\omega(\phi_i^4)\le \frac{1}{c_0\lambda a^3}.
\]
For each neighbor \(y\sim i\):
\[
\omega\!\left(|\phi_i-\phi_y|^4\right)\le \frac{16}{c_0\lambda a^3}.
\]

### Proof sketch

Use the finite-volume integration-by-parts identity
\[
\sum_x\omega\!\left(\phi_x\,\partial_{\phi_x}S\right)=\frac{|\Lambda_{a,L}|}{c},
\]
expand \(\phi_x\partial_{\phi_x}S\), and drop nonnegative terms to isolate
second and fourth moments (as in AN-20).  
For edge differences, use \((u-v)^4\le 8(u^4+v^4)\). \(\square\)

## Theorem 2 (AN-26B Gate Closure with \(q=4/3\))

Set \(q:=4/3\). Then
\[
\sup_{0<a\le1,\ L,\ \kappa\in[0,\kappa_*],\ c\in[c_0,c_1]}
\omega\!\left(|\mathcal D_i|^{4/3}\right)
\le M_{i,4/3}<\infty,
\]
with explicit constant
\[
M_{i,4/3}
:=
3^{1/3}\!\left[
\left(\frac{m_0^2}{c_0}\right)^{2/3}
+
\frac{\lambda^{1/3}}{c_0}
+
\frac{6^{4/3}16^{1/3}\kappa_*^{4/3}}{(c_0\lambda)^{1/3}}
\right].
\]

### Proof

Write \(\mathcal D_i=T_1+T_2+T_3\) with
\[
T_1=a^3m_0^2\phi_i,\quad
T_2=a^3\lambda\phi_i^3,\quad
T_3=\kappa a\sum_{y\sim i}(\phi_i-\phi_y).
\]
For \(q=4/3\), \(|u+v+w|^q\le 3^{q-1}(|u|^q+|v|^q+|w|^q)\), so it is enough to
bound each term.

1. \(T_1\): by Holder/Lyapunov (\(q\le2\)),
   \[
   \omega(|T_1|^q)
   =(m_0^2)^q a^{3q}\omega(|\phi_i|^q)
   \le
   (m_0^2)^q a^{4}\omega(\phi_i^2)^{2/3}
   \le
   \left(\frac{m_0^2}{c_0}\right)^{2/3}.
   \]
2. \(T_2\):
   \[
   \omega(|T_2|^q)
   =\lambda^q a^4\omega(\phi_i^4)
   \le
   \frac{\lambda^{1/3}}{c_0}.
   \]
3. \(T_3\): with 6 neighbors and \(q=4/3\),
   \[
   \omega(|T_3|^q)
   \le
   \kappa_*^q a^q 6^{q-1}\sum_{y\sim i}\omega(|\phi_i-\phi_y|^q).
   \]
   By Lyapunov (\(q\le4\)),
   \[
   \omega(|\phi_i-\phi_y|^q)\le \omega(|\phi_i-\phi_y|^4)^{1/3}
   \le \left(\frac{16}{c_0\lambda a^3}\right)^{1/3}.
   \]
   Therefore
   \[
   \omega(|T_3|^q)
   \le
   \frac{6^{4/3}16^{1/3}\kappa_*^{4/3}}{(c_0\lambda)^{1/3}}\,a^{1/3}
   \le
   \frac{6^{4/3}16^{1/3}\kappa_*^{4/3}}{(c_0\lambda)^{1/3}}.
   \]

Combine with factor \(3^{q-1}=3^{1/3}\). \(\square\)

## Corollary (AN-26 Conditional Gate Discharged)

The AN-26 tail insertion-control theorem
(`2026-02-09-claim1-d3-cb1-tail-insertion-closure.md`) is now fully activated
in this scoped Euclidean branch by taking \(q=4/3\) and
\(M_{i,q}:=M_{i,4/3}\).

Hence AN-25 test-side \(C_c^1\to C_b^1\) extension is theorem-grade in this
branch, and AN-27 now closes oscillatory/de-regularized transfer in:
`research/workspace/notes/theorems/2026-02-09-claim1-d3-oscillatory-dereg-class-transfer.md`.
Next target is AN-28 nonlocal-cylinder extension.

## Validation Contract

### Assumptions

1. periodic finite-volume Euclidean branch, \(0<a\le1\),
2. \(c\in[c_0,c_1]\subset(0,\infty)\), \(\kappa\in[0,\kappa_*]\),
3. AN-24 setup and AN-26 tail framework.

### Units and dimensions check

1. insertion channel is exactly \(\partial_{\phi_i}S\) used in AN-26,
2. scaling in \(a\) is explicit in every bound term.

### Symmetry/conservation checks

1. periodic translation invariance is used for site-moment extraction,
2. neighbor-count factor (6 in \(d=3\)) is explicit in the insertion bound.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_an26b_insertion_lq_moment_check.py
```

The script checks:

1. empirical \(\omega(|\partial_i S|^{4/3})\) across an \((a,c,\kappa)\) grid,
2. empirical site/edge moments used in the analytic proof chain,
3. comparison against the explicit analytic \(M_{i,4/3}\) bound.

### Confidence statement

AN-26B closes the AN-26 insertion-moment gate in the scoped Euclidean branch.
Claims beyond that branch remain unverified.

### Reproducibility metadata

1. Python: `python3.12`,
2. seed and grid printed by script,
3. date anchor: 2026-02-09 (US).
