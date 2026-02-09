# Claim 1 Phase BQ (AN-25): \(d=3\) Local-Class Extension Beyond Compact Support

Date: 2026-02-09 (CET)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim1-d3-cutoff-lift-closure.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-d3-scoped-continuum-branch-candidate.md`

## Goal

Start AN-25 by extending the AN-24 lifted branch from compact-support local
classes to broader local classes, while keeping the same \(d=3\) Euclidean
renormalized channel.

## Target/Model/Existence Declaration (Non-Drift Rule)

1. target dimension: \(d=3\),
2. model class: AN-24 nearest-neighbor lattice \(\phi^4\), Euclidean \(c\in[c_0,c_1]\subset(0,\infty)\),
3. existence notion: class-extension of already-built regulated/cutoff-lifted local states,
4. geometric \(1/2\)-density role: interpretation only.

## Extended Local Classes

Fix finite local block \(B\), renormalized coordinates
\[
v_B=(\varphi_x)_{x\in B},\qquad \varphi_x=a^{3/2}\phi_x.
\]

Start class extension with:

1. **Observable class**
   \[
   \mathcal A_{B,\mathrm{ext}}^{\mathrm{ren}}
   :=
   \{F(\phi)=f(v_B)\;:\; f\in C_b(\mathbb R^{|B|})\},
   \]
   i.e. bounded continuous local observables, not necessarily compactly supported.
2. **Test class (target extension)**
   \[
   \mathcal T_{B,\mathrm{ext}}^{\mathrm{ren}}
   :=
   \{\psi(\phi)=\tilde\psi(v_B)\;:\;\tilde\psi\in C_b^1(\mathbb R^{|B|})\}.
   \]

AN-24 covered \(C_c\) and \(C_c^1\) classes.

## Theorem A (Closed): Observable-Class Extension \(C_c\to C_b\)

In the AN-24 branch, expectations extend uniquely from compact-support local
observables to \(\mathcal A_{B,\mathrm{ext}}^{\mathrm{ren}}\), uniformly on the
working parameter window.

### Proof sketch

Let \(f\in C_b\), \(\|f\|_\infty\le M_f\), and choose cutoffs
\(\chi_R\in C_c^\infty\), \(0\le\chi_R\le1\), \(\chi_R\equiv1\) on \(\|v_B\|\le R\).
Set \(f_R:=\chi_R f\in C_c\). Then
\[
|\omega(f)-\omega(f_R)|
\le
M_f\,\omega(\|v_B\|>R).
\]
Using AN-24 renormalized second moments,
\[
\omega(\|v_B\|^2)\le \frac{|B|}{c_0m_0^2},
\]
Markov gives
\[
\omega(\|v_B\|>R)\le \frac{|B|}{c_0m_0^2\,R^2}.
\]
Hence \(\omega(f_R)\to\omega(f)\) uniformly as \(R\to\infty\).
Uniqueness follows because \(C_c\) approximants have vanishing tail error.
\(\square\)

## Proposition B (Closed via AN-26 + AN-26B): Test-Class Extension \(C_c^1\to C_b^1\)

For \(\psi\in\mathcal T_{B,\mathrm{ext}}^{\mathrm{ren}}\), finite-volume SD
identity extends from AN-24 by cutoff approximation
\(\psi_R=\chi_R\psi\in C_c^1\), once the AN-26 tail insertion-control condition
is available:
\[
\sup_{a,L,\kappa,c}
\omega\!\left(|\partial_i S_{a,L}^{(\kappa)}|\,\mathbf 1_{\|v_B\|>R}\right)
\xrightarrow[R\to\infty]{}0.
\]
This condition is reduced in:
`research/workspace/notes/theorems/2026-02-09-claim1-d3-cb1-tail-insertion-closure.md`,
and its insertion-moment gate is discharged in:
`research/workspace/notes/theorems/2026-02-09-claim1-d3-insertion-lq-moment-verification.md`.

## AN-25 Status (This Pass)

Closed now:

1. observable-side class extension \(C_c\to C_b\) with explicit tail rate
   \(O(R^{-2})\) from AN-24 moments,
2. SD test-side class extension \(C_c^1\to C_b^1\) closed via AN-26 + AN-26B
   in the same scoped branch.

AN-27 update:

1. widened local class transfer to oscillatory/de-regularized branch is now
   closed in
   `research/workspace/notes/theorems/2026-02-09-claim1-d3-oscillatory-dereg-class-transfer.md`.
2. next open step is AN-28: extend this transfer from strictly local blocks to
   first nonlocal-cylinder observables.

## Validation Contract

### Assumptions

1. AN-24 local-renormalized Euclidean branch,
2. uniform renormalized second-moment control from AN-24.
3. AN-26 insertion-moment gate verified by AN-26B for \(q=4/3\).

### Units and dimensions check

1. class extension uses renormalized coordinates \(v_B\), so tail estimates are
   dimensionally consistent with AN-24 bounds.

### Symmetry/conservation checks

1. local block structure and periodic symmetry assumptions are unchanged.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_an25_class_extension_check.py
python3.12 research/workspace/simulations/claim1_d3_an26_tail_insertion_control_check.py
python3.12 research/workspace/simulations/claim1_d3_an26b_insertion_lq_moment_check.py
python3.12 research/workspace/simulations/claim1_d3_an27_oscillatory_dereg_transfer_check.py
```

The script checks:

1. \(C_c\to C_b\) observable approximation error decay vs cutoff radius,
2. SD residual behavior for bounded noncompact \(C_b^1\)-type test probes,
3. tail insertion-control diagnostics used for AN-26 test-side closure,
4. insertion \(L^{4/3}\)-moment diagnostics closing the AN-26 gate.
5. oscillatory/de-regularized transfer diagnostics for the widened class.

### Confidence statement

Observable-side AN-25 extension is theorem-grade in the AN-24 channel.
Test-side \(C_b^1\) extension is theorem-grade in this scoped branch via
AN-26 + AN-26B.

### Reproducibility metadata

1. Python: `python3.12`,
2. seed printed by script,
3. date anchor: 2026-02-09 (US).
