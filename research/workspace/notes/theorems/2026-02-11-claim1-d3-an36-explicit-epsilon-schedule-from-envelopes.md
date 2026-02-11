# Claim 1 Phase CE (AN-36): Explicit \(\varepsilon\)-Schedule from Concrete Envelopes

Date: 2026-02-11 (US)  
Depends on:

- `research/workspace/notes/theorems/2026-02-11-claim1-d3-an35-concrete-envelope-commuting-limit-integration.md`
- `research/workspace/notes/theorems/2026-02-10-claim1-d3-an34-firstprinciples-tail-rate-transmutation.md`
- `research/workspace/notes/theorems/2026-02-10-claim1-d3-an33l-c-commuting-limit-wrapper-lean.md`

## Goal

Upgrade AN-35 from existential joint convergence to an explicit quantitative
index schedule: for any target \(\varepsilon>0\), produce concrete
\((k_\varepsilon,n_\varepsilon)\) such that
\[
|u_{k,n}-L|\le\varepsilon\quad\text{for all }k\ge k_\varepsilon,\ n\ge n_\varepsilon.
\]

## Setup

From AN-35 and the commuting-limit wrapper lane, assume:
\[
|u_{k,n}-L|\le A\,t_n + B\,e_k,\qquad A,B>0.
\]

Use explicit envelope models:
\[
t_n\le C_t\,\rho^n,\qquad 0<\rho<1,
\]
\[
e_k=\eta_0^\alpha\,2^{-\alpha k}+\lambda^k,\qquad
\eta_0>0,\ \alpha>0,\ 0<\lambda<1.
\]
Define
\[
q:=\max\!\big(2^{-\alpha},\lambda\big),\qquad
C_e:=\eta_0^\alpha+1.
\]
Then \(e_k\le C_e q^k\).

## Theorem 1 (Closed-Form \(\varepsilon\)-Indices)

For any \(\varepsilon>0\), set
\[
n_\varepsilon:=
\left\lceil
\frac{\log\!\left(\frac{2AC_t}{\varepsilon}\right)}{|\log\rho|}
\right\rceil,
\qquad
k_\varepsilon:=
\left\lceil
\frac{\log\!\left(\frac{2BC_e}{\varepsilon}\right)}{|\log q|}
\right\rceil.
\]
Then for every \(n\ge n_\varepsilon\), \(k\ge k_\varepsilon\):
\[
|u_{k,n}-L|\le\varepsilon.
\]

### Proof

By definition of \(n_\varepsilon\):
\[
A t_n\le A C_t \rho^n\le A C_t \rho^{n_\varepsilon}\le \frac{\varepsilon}{2}.
\]
By definition of \(k_\varepsilon\):
\[
B e_k\le B C_e q^k\le B C_e q^{k_\varepsilon}\le \frac{\varepsilon}{2}.
\]
Summing gives \(|u_{k,n}-L|\le\varepsilon\). \(\square\)

## Corollary (Complexity Shape)

Index budgets scale logarithmically:
\[
n_\varepsilon,\ k_\varepsilon = O(\log(1/\varepsilon)).
\]
So the AN-35/AN-33L-C commuting-limit lane now has an explicit quantitative
cost profile for target precision.

## Scoped Numeric Instantiation

Using the AN-35 diagnostic constants:
\[
A=1.35,\quad B=0.92,\quad \eta_0=0.32,\quad \alpha=0.75,\quad \lambda=0.57,
\]
and geometric tail proxy \(t_n=C_t\rho^n\) with \(C_t=1/(1-\rho)\), \(\rho=0.66\),
the generated \((k_\varepsilon,n_\varepsilon)\) pass deterministic checks for a
grid of \(\varepsilon\)-targets.

## Validation Contract

### Assumptions

1. AN-35 envelope inequality \(|u_{k,n}-L|\le A t_n+B e_k\),
2. geometric-type exhaustion envelope dominance \(t_n\le C_t\rho^n\),
3. regularization schedule \(e_k=\eta_0^\alpha2^{-\alpha k}+\lambda^k\).

### Units and dimensions check

1. \(t_n,e_k\) dimensionless envelope quantities,
2. \(A,B,C_t,C_e\) dimensionless constants,
3. \(\varepsilon\) is dimensionless tolerance for normalized ratio/observable channel.

### Symmetry/conservation checks

1. no additional symmetry assumptions beyond AN-35 channel,
2. schedule extraction is purely quantitative and does not alter model symmetries.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_an36_explicit_epsilon_schedule_check.py
```

The script verifies:

1. closed-form \((k_\varepsilon,n_\varepsilon)\) formulas on a tolerance grid,
2. bound satisfaction for every \((k,n)\) in sampled tail blocks
   \(k\ge k_\varepsilon,\ n\ge n_\varepsilon\),
3. monotone growth of index budgets as \(\varepsilon\downarrow0\).

### Confidence statement

AN-36 closes the quantitative gap left by AN-35 in the scoped support lane:
commuting-limit convergence is now accompanied by explicit tolerance-to-index
budgets. Global interacting closure remains open.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic parameter grid and tolerance grid printed by script,
3. date anchor: 2026-02-11 (US).
