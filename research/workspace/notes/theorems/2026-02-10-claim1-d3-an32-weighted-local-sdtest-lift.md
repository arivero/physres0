# Claim 1 Phase BY (AN-32): \(d=3\) Weighted-Local SD-Test Lift from AN-31 Exhaustion Families

Date: 2026-02-10 (US)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim1-d3-an31-exhaustion-summability-lift.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-d3-cb1-tail-insertion-closure.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-d3-insertion-lq-moment-verification.md`

## Goal

Execute AN-32: extend the AN-31 exhaustion-family lane from finite-cylinder
observables to weighted-local observable/SD-test classes with explicit
exhaustion-uniform insertion estimates.

## Target/Model/Existence Declaration (Non-Drift Rule)

1. target dimension: \(d=3\),
2. model class: AN-24/AN-31 nearest-neighbor lattice \(\phi^4\), scoped oscillatory/de-regularized branch,
3. existence notion: exhaustion-limit existence and SD pass-through for weighted-local classes,
4. geometric \(1/2\)-density role: interpretation only.

## Setup

Retain AN-31 exhaustion data:
\[
H_1\subset H_2\subset\cdots,\qquad \bigcup_{n\ge1}H_n=H_\infty,
\]
with summability weight \(w:V(H_\infty)\to(0,\infty)\) and
\[
\sum_{v\in V(H_\infty)}w(v)<\infty,\qquad
W_n^{\mathrm{tail}}:=\sum_{v\notin V(H_n)}w(v)\to0.
\]

For each \(n\), write AN-31 states as \(\omega_{\eta,\infty,H_n}^{(\kappa)}\).

Define weighted-local coefficient tails:
\[
T_\alpha(n):=\sum_{v\notin V(H_n)}|\alpha_v|\,w(v),
\qquad
T_\beta(n):=\sum_{v\notin V(H_n)}|\beta_v|\,w(v).
\]

## Weighted-Local Classes

Fix one local block \(B_v\) per graph vertex \(v\in V(H_\infty)\).

1. **Weighted-local observables**
   \[
   F=\sum_{v\in V(H_\infty)}\alpha_v F_v(v_{B_v}),
   \]
   with \(F_v\in C_b\), \(\|F_v\|_\infty\le1\), and
   \(\sum_v |\alpha_v|w(v)<\infty\).
2. **Weighted-local SD tests**
   \[
   \psi=\sum_{v\in V(H_\infty)}\beta_v\psi_v(v_{B_v}),
   \]
   with \(\psi_v\in C_b^1\),
   \(\|\psi_v\|_\infty+\|\nabla\psi_v\|_\infty\le1\), and
   \(\sum_v |\beta_v|w(v)<\infty\).

Use truncations
\[
F^{(n)}:=\sum_{v\in V(H_n)}\alpha_v F_v,
\qquad
\psi^{(n)}:=\sum_{v\in V(H_n)}\beta_v\psi_v.
\]

## Assumption Package (AN-32)

1. **(AN31-UNI)** AN-31 assumptions hold uniformly on \(\{H_n\}\).
2. **(LOC-CAUCHY)** each finite-support truncation satisfies AN-31-type
   exhaustion Cauchy control:
   \[
   |\omega_n(G)-\omega_m(G)|\le C_G(W_n^{\mathrm{tail}}+W_m^{\mathrm{tail}})
   \]
   for all finite-support local \(G\).
3. **(OBS-UNI)** local observable channels are uniformly bounded:
   \[
   \sup_{n,\eta,\kappa}\big|\omega_{\eta,\infty,H_n}^{(\kappa)}(F_v)\big|
   \le M_{\mathrm{obs}}\,w(v).
   \]
4. **(SD-LOC)** finite-support SD identity is already closed in-branch
   (from AN-26/AN-26B + AN-31 transfer) for all \(\psi^{(n)}\).
5. **(DER-UNI)** derivative-side weighted envelope:
   \[
   \sup_{n,\eta,\kappa}
   \big|\omega_{\eta,\infty,H_n}^{(\kappa)}(\partial\psi_v)\big|
   \le M_{\partial}\,w(v).
   \]
6. **(INS-UNI)** insertion-side weighted envelope:
   \[
   \sup_{n,\eta,\kappa}
   \omega_{\eta,\infty,H_n}^{(\kappa)}\!\big(|\psi_v\mathcal D_v|\big)
   \le M_{\mathrm{ins}}\,w(v),
   \]
   where \(\mathcal D_v\) is the chosen local SD insertion channel for block \(v\).

## Theorem 1 (Weighted-Local Exhaustion Cauchy Lift)

Under (AN31-UNI)+(LOC-CAUCHY)+(OBS-UNI), for any weighted-local observable \(F\),
\[
\left|
\omega_{\eta,\infty,H_n}^{(\kappa)}(F)
-\omega_{\eta,\infty,H_m}^{(\kappa)}(F)
\right|
\le
C_F(W_n^{\mathrm{tail}}+W_m^{\mathrm{tail}})
2M_{\mathrm{obs}}\,T_\alpha(\underline n),
\]
where \(\underline n:=\min\{n,m\}\), and \(C_F\) depends only on a finite
truncation envelope of \(F\).

Hence \(\omega_{\eta,\infty,H_n}^{(\kappa)}(F)\) is Cauchy, with exhaustion-limit
value \(\omega_{\eta,\infty,H_\infty}^{(\kappa)}(F)\).

### Proof sketch

Split with \(\underline n=\min\{n,m\}\):
\[
F=(F-F^{(\underline n)})+F^{(\underline n)}.
\]
Use (OBS-UNI) to bound both tail pieces by
\(M_{\mathrm{obs}}T_\alpha(\underline n)\), and apply (LOC-CAUCHY) to
\(F^{(\underline n)}\). Since \(T_\alpha(\underline n)\to0\), Cauchy follows.
\(\square\)

## Proposition 2 (Explicit Exhaustion-Uniform Insertion Tail Estimate)

Under (INS-UNI), for every \(n\):
\[
\sup_{\eta,\kappa}
\omega_{\eta,\infty,H_n}^{(\kappa)}
\!\left(
\left|(\psi-\psi^{(n)})\mathcal D\right|
\right)
\le
M_{\mathrm{ins}}\,T_\beta(n),
\]
where \((\psi-\psi^{(n)})\mathcal D\) is the weighted-local insertion-tail
pairing induced by \(\{\mathcal D_v\}\).

### Proof

Use absolute convergence and (INS-UNI):
\[
\omega_n\!\left(\left|\sum_{v\notin V(H_n)}\beta_v\psi_v\mathcal D_v\right|\right)
\le
\sum_{v\notin V(H_n)}|\beta_v|
\omega_n(|\psi_v\mathcal D_v|)
\le
M_{\mathrm{ins}}\sum_{v\notin V(H_n)}|\beta_v|w(v).
\]
\(\square\)

## Theorem 3 (Weighted-Local SD-Test Pass-Through on Exhaustion Limit)

Assume (SD-LOC)+(DER-UNI)+(INS-UNI) in addition to Theorem 1 hypotheses.
Then for every weighted-local \(\psi\),
\[
\omega_{\eta,\infty,H_\infty}^{(\kappa)}(\partial\psi)

=
c_\eta\,
\omega_{\eta,\infty,H_\infty}^{(\kappa)}(\psi\,\mathcal D).
\]

### Proof sketch

1. finite truncations satisfy SD by (SD-LOC):
   \[
   \omega_n(\partial\psi^{(r)})=c_\eta\,\omega_n(\psi^{(r)}\mathcal D).
   \]
2. pass \(r\to\infty\) at fixed \(n\) using:
   \[
   |\omega_n(\partial(\psi-\psi^{(r)}))|
   \le M_{\partial}T_\beta(r),
   \]
   and Proposition 2 for insertion tails.
3. pass \(n\to\infty\) via Theorem 1 lifted Cauchy control on both pairings.
\(\square\)

## Corollary (AN-32 Scoped Upgrade)

AN-32 upgrades AN-31 as follows:

1. exhaustion-limit existence now covers weighted-local observable classes,
2. SD-test pass-through extends from finite-cylinder/local truncations to
   weighted-local \(C_b^1\)-type tests,
3. insertion tails are controlled by explicit exhaustion-uniform bounds
   proportional to \(T_\beta(n)\).

Next target (AN-33): extend AN-32 weighted-local class from one-block channels
to graph-decay nonlocal weighted-local channels with explicit denominator-rate
bookkeeping in the same branch.

## Validation Contract

### Assumptions

1. AN-31 exhaustion assumptions remain active,
2. AN-26/AN-26B local SD + insertion machinery is available in-branch,
3. weighted envelopes (OBS-UNI/DER-UNI/INS-UNI) are explicit.

### Units and dimensions check

1. \(W_n^{\mathrm{tail}},T_\alpha(n),T_\beta(n)\) are dimensionless,
2. insertion channels \(\mathcal D_v\) are unchanged from the AN-26 lineage.

### Symmetry/conservation checks

1. exhaustion inclusions preserve local block algebra and restriction maps,
2. no new symmetry-breaking regulator is introduced in the weighted lift.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_an32_weighted_local_sdtest_check.py
```

The script checks:

1. weighted coefficient tails \(T_\alpha,T_\beta\to0\),
2. AN-32 weighted-local exhaustion Cauchy bound profile,
3. explicit insertion-tail bound proportional to \(T_\beta(n)\),
4. weighted-local SD residual stabilization along exhaustion levels.

### Confidence statement

AN-32 is theorem-grade in this scoped branch under explicit weighted-envelope
assumptions. It extends AN-31 from cylinder families to weighted-local classes
but does not yet close full reconstruction/global interacting existence.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic seed printed by script,
3. date anchor: 2026-02-10 (US).

