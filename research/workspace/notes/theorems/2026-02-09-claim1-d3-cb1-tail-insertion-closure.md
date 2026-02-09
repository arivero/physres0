# Claim 1 Phase BR (AN-26): \(d=3\) SD Test-Side \(C_b^1\) Tail-Insertion Closure

Date: 2026-02-09 (CET)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim1-d3-class-extension-local-cb-channel.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-d3-cutoff-lift-closure.md`

## Goal

Close the AN-25 test-side gap by proving the tail insertion-control condition
needed to pass Schwinger-Dyson (SD) identities from compactly supported local
tests to bounded \(C_b^1\) local tests in the same \(d=3\) Euclidean branch.

## Target/Model/Existence Declaration (Non-Drift Rule)

1. target dimension: \(d=3\),
2. model class: AN-24 nearest-neighbor lattice \(\phi^4\), Euclidean \(c\in[c_0,c_1]\subset(0,\infty)\),
3. existence notion: class extension of already-built regulated/cutoff-lifted local states,
4. geometric \(1/2\)-density role: interpretation only.

## Setup

Fix a finite local block \(B\), and write renormalized local coordinates
\[
v_B=(\varphi_x)_{x\in B},\qquad \varphi_x=a^{3/2}\phi_x.
\]

For each \(i\in B\), denote lattice insertion channel
\[
\mathcal D_i:=\partial_i S_{a,L}^{(\kappa)}.
\]

AN-25 already closes observable-side extension \(C_c\to C_b\).
For test-side \(C_c^1\to C_b^1\), use compact cutoffs \(\chi_R\in C_c^\infty\)
on \(\mathbb R^{|B|}\), \(0\le \chi_R\le1\), with
\[
\chi_R\equiv1\text{ on }\|v_B\|\le R,\qquad
\|\nabla\chi_R\|_\infty\le \frac{C_\chi}{R}.
\]
For \(\psi\in C_b^1(\mathbb R^{|B|})\), set \(\psi_R:=\chi_R\psi\in C_c^1\).

## Tail-Control Assumption Package

Use:

1. AN-24 renormalized second moment:
   \[
   \sup_{a,L,\kappa,c}\omega(\|v_B\|^2)\le C_B<\infty.
   \]
2. insertion moment hypothesis for one exponent \(q>1\):
   \[
   \sup_{a,L,\kappa,c}\omega(|\mathcal D_i|^q)\le M_{i,q}<\infty.
   \]

This is the explicit AN-26 closure gate for SD test-side extension.

## Proposition 1 (Tail Insertion-Control)

Let \(q>1\), \(q'=q/(q-1)\). Under the package above,
\[
\sup_{a,L,\kappa,c}
\omega\!\left(|\mathcal D_i|\mathbf 1_{\|v_B\|>R}\right)
\le
M_{i,q}^{1/q}
\left(\frac{C_B}{R^2}\right)^{1/q'}
\xrightarrow[R\to\infty]{}0.
\]

### Proof

By Holder,
\[
\omega(|\mathcal D_i|\mathbf 1_{\|v_B\|>R})
\le
\omega(|\mathcal D_i|^q)^{1/q}
\omega(\|v_B\|>R)^{1/q'}.
\]
Bound first factor by \(M_{i,q}^{1/q}\).  
By Markov using AN-24 second moments,
\[
\omega(\|v_B\|>R)\le \frac{\omega(\|v_B\|^2)}{R^2}\le \frac{C_B}{R^2}.
\]
Insert and conclude. \(\square\)

## Theorem 2 (SD Extension \(C_c^1\to C_b^1\))

Assume Proposition 1 hypotheses. For any local \(\psi\in C_b^1(\mathbb R^{|B|})\),
the finite-volume SD identity extends from compact support to bounded \(C_b^1\):
\[
\omega(\partial_i\psi)=c\,\omega(\psi\,\mathcal D_i).
\]

### Proof sketch

For each \(R\), AN-24 gives SD for \(\psi_R=\chi_R\psi\):
\[
\omega(\partial_i\psi_R)=c\,\omega(\psi_R\mathcal D_i).
\]
Subtract target identity and split into
\[
E_{1,R}:=\omega(\partial_i\psi-\partial_i\psi_R),\qquad
E_{2,R}:=c\,\omega((\psi-\psi_R)\mathcal D_i).
\]
For \(E_{1,R}\), use
\[
\partial_i\psi_R
=
\chi_R\partial_i\psi+\psi\,\partial_i\chi_R,
\]
hence
\[
|E_{1,R}|
\le
\|\partial_i\psi\|_\infty\,\omega(\|v_B\|>R)
\;+\;
\|\psi\|_\infty\frac{C_\chi}{R}.
\]
For \(E_{2,R}\), use \(|\psi-\psi_R|\le \|\psi\|_\infty\mathbf 1_{\|v_B\|>R}\):
\[
|E_{2,R}|
\le
|c|\,\|\psi\|_\infty\,
\omega(|\mathcal D_i|\mathbf 1_{\|v_B\|>R}).
\]
Now \(E_{1,R}\to0\) by AN-24 second moments and cutoff-gradient bound, and
\(E_{2,R}\to0\) by Proposition 1. Pass \(R\to\infty\). \(\square\)

## Corollary (AN-25 Completion in This Branch)

In the AN-24 Euclidean local-renormalized branch, AN-25 is complete after
AN-26B verifies the insertion moment hypothesis in:
`research/workspace/notes/theorems/2026-02-09-claim1-d3-insertion-lq-moment-verification.md`.

1. observable-side \(C_c\to C_b\) extension (already closed in AN-25),
2. test-side \(C_c^1\to C_b^1\) SD extension (closed by Theorem 2).

AN-27 now closes oscillatory/de-regularized transfer of this widened class in:
`research/workspace/notes/theorems/2026-02-09-claim1-d3-oscillatory-dereg-class-transfer.md`.
Next branch target is AN-28: first nonlocal-cylinder extension.

## Validation Contract

### Assumptions

1. AN-24 Euclidean \(c\)-window and local-renormalized channel,
2. AN-24 renormalized second moments,
3. AN-26 insertion \(L^q\) moment hypothesis (verified in AN-26B for \(q=4/3\)).

### Units and dimensions check

1. tail event uses renormalized local coordinates \(v_B\),
2. SD identity keeps the same insertion channel \(\partial_i S\) as AN-24.

### Symmetry/conservation checks

1. periodic translation structure is unchanged,
2. no new symmetry-breaking regulator is introduced by cutoff approximation.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_an26_tail_insertion_control_check.py
python3.12 research/workspace/simulations/claim1_d3_an26b_insertion_lq_moment_check.py
```

The script checks:

1. empirical decay of \(\omega(|\mathcal D_i|\,\mathbf 1_{\|v_B\|>R})\),
2. Holder/Markov proxy bounds for the same tail channel,
3. SD residual behavior for cutoff approximants \(\psi_R\) of a bounded \(C_b^1\) test.

### Confidence statement

AN-26 closes the missing AN-25 test-side analytic gate in theorem form, with
its insertion-moment gate discharged by AN-26B. Claims beyond this branch
remain unverified.

### Reproducibility metadata

1. Python: `python3.12`,
2. seed printed by script,
3. date anchor: 2026-02-09 (US).
