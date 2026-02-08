# Claim 1 Phase V: Intrinsic Sufficient Conditions for Quartic-Tail Assumptions

Date: 2026-02-09  
Depends on: `research/workspace/notes/theorems/2026-02-09-claim1-largeN-coupled-quartic-tail.md`, `research/workspace/notes/theorems/2026-02-09-claim1-partition-nonvanishing-bounds.md`

## Goal

Replace the external hypotheses in Phase T (non-vanishing and log-derivative bounds of \(I_j\)) by intrinsic moment conditions on the quartic one-mode blocks.

## One-Mode Block

For fixed \(j\), define
\[
S_{j,b}(t):=\Big(\frac{\lambda_j}{2}+b\Big)t^2+\gamma_j t^4,\qquad b\ge0,
\]
\[
I_j(b):=\int_{\mathbb R}e^{-cS_{j,b}(t)}dt,\qquad c=\eta-i/\varepsilon,\ \eta>0,\ \varepsilon>0,
\]
and positive reference measure
\[
\nu_{j,b}(dt):=\frac{e^{-\eta S_{j,b}(t)}}{\int e^{-\eta S_{j,b}}}\,dt.
\]

Define block moments
\[
M^{(1)}_{j,b}:=\mathbb E_{\nu_{j,b}}[S_{j,b}],\qquad
M^{(2)}_{j,b}:=\mathbb E_{\nu_{j,b}}[t^2].
\]

Set
\[
\overline M^{(1)}_j:=\sup_{b\ge0} M^{(1)}_{j,b},\qquad
\overline M^{(2)}_j:=\sup_{b\ge0} M^{(2)}_{j,b}.
\]

## Theorem 1 (Intrinsic Non-Vanishing Criterion)

If
\[
\varepsilon>\overline M^{(1)}_j,
\]
then \(I_j(b)\neq0\) for every \(b\ge0\), and
\[
|I_j(b)|
\ge
\left(\int e^{-\eta S_{j,b}}\right)
\left(1-\frac{\overline M^{(1)}_j}{\varepsilon}\right).
\]

### Proof

Apply the first-moment non-vanishing bound (Phase O) to each block \(S_{j,b}\):
\[
|I_j(b)|\ge A_{j,b}\left(1-\frac{M^{(1)}_{j,b}}{\varepsilon}\right),\qquad
A_{j,b}:=\int e^{-\eta S_{j,b}}>0.
\]
Since \(M^{(1)}_{j,b}\le\overline M^{(1)}_j\), the stated bound follows. \(\square\)

## Theorem 2 (Intrinsic Log-Derivative Bound)

Assume \(\varepsilon>\overline M^{(1)}_j\). Then for all \(b\ge0\),
\[
\left|\partial_b\log I_j(b)\right|
\le
\frac{|c|\,\overline M^{(2)}_j}
{1-\overline M^{(1)}_j/\varepsilon}
:
L_j^{\mathrm{int}}.
\]

### Proof

Differentiate under the integral:
\[
\partial_b I_j(b)
=
-c\int t^2 e^{-cS_{j,b}(t)}dt.
\]
Hence
\[
\left|\partial_b\log I_j(b)\right|
=
\frac{|\partial_b I_j(b)|}{|I_j(b)|}
\le
\frac{|c|\int t^2 e^{-\eta S_{j,b}}dt}
{A_{j,b}(1-\overline M^{(1)}_j/\varepsilon)}
=
\frac{|c|\,M^{(2)}_{j,b}}
{1-\overline M^{(1)}_j/\varepsilon}
\le
L_j^{\mathrm{int}}.
\]
\(\square\)

## Corollary (Intrinsic Replacement for Phase T Hypotheses)

In the Phase T large-\(N\) coupled quartic-tail theorem, assumptions
\[
I_j(b)\neq0,\qquad \sup_{b\ge0}|\partial_b\log I_j(b)|\le L_j
\]
are implied by the intrinsic conditions:

1. \(\varepsilon>\sup_j\overline M^{(1)}_j\),
2. \(\sum_{j>m} A_j\,L_j^{\mathrm{int}}<\infty\),

with
\[
L_j^{\mathrm{int}}
=
\frac{|c|\,\overline M^{(2)}_j}
{1-\overline M^{(1)}_j/\varepsilon}.
\]

So the former external assumptions are reduced to moment control of the block family.

## Scope

What remains is to derive sharp structural bounds for \(\overline M^{(1)}_j,\overline M^{(2)}_j\) directly from coefficient envelopes \((\lambda_j,\gamma_j)\) in broader interacting families.

## Reproducibility

Run:

```bash
python3.12 research/workspace/simulations/claim1_quartic_tail_intrinsic_conditions_check.py
```

The script estimates \(\overline M^{(1)}_j,\overline M^{(2)}_j\) on a sample family and confirms positivity/non-vanishing and summability diagnostics.
