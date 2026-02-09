# Claim 1 Phase BP (AN-24): \(d=3\) Hard-Cutoff Lift \(R\to\infty\) in the Compact-Spin Branch

Date: 2026-02-09 (CET)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim1-d3-compact-spin-b1-b4-closure.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-d3-renormalized-moment-channel-proposition.md`

## Goal

Remove the hard compact-spin cutoff \(R\) from AN-23 while preserving the same
scoped B1-B4 control package in one interacting Euclidean \(d=3\) subclass.

## Target/Model/Existence Declaration (Non-Drift Rule)

1. target dimension: \(d=3\),
2. model class: nearest-neighbor lattice \(\phi^4\), Euclidean \(c\in[c_0,c_1]\subset(0,\infty)\),
3. existence notion: regulated finite-volume existence plus cutoff-removal limit inside the local renormalized observable channel,
4. geometric \(1/2\)-density role: interpretation only (not used as the core proof channel).

## Setup

For periodic \(\Lambda_{a,L}\subset a\mathbb Z^3\), \(0<a\le1\), let
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
with \(m_0^2>0\), \(\lambda>0\), \(\kappa\in[0,\kappa_*]\).

Truncated finite-volume states:
\[
d\mu_{c,a,L,R}^{(\kappa)}(\phi)=
\frac{1}{Z_{c,a,L,R}^{(\kappa)}}
e^{-cS_{a,L}^{(\kappa)}(\phi)}
\mathbf 1_{\{|\phi_x|\le R,\ \forall x\}}\,d\phi.
\]

Untruncated state:
\[
d\mu_{c,a,L,\infty}^{(\kappa)}(\phi)=
\frac{1}{Z_{c,a,L,\infty}^{(\kappa)}}e^{-cS_{a,L}^{(\kappa)}(\phi)}\,d\phi.
\]

Use renormalized local variables \(\varphi_x:=a^{3/2}\phi_x\), and local
renormalized observable class
\[
\mathcal A_{\mathrm{loc}}^{\mathrm{ren}}
=
\left\{F(\phi)=f((\varphi_x)_{x\in B})\;:\;
B\Subset\Lambda_{a,L},\ f\in C_b,\ \mathrm{supp}(f)\ \text{compact}\right\}.
\]

For SD, use compactly supported local tests in renormalized coordinates:
\[
\mathcal T_B^{\mathrm{ren}}
=
\left\{\psi(\phi)=\tilde\psi((\varphi_x)_{x\in B})\;:\;
\tilde\psi\in C_c^1(\mathbb R^{|B|})\right\}.
\]

## Proposition (Finite-Volume Cutoff Lift)

Fix \(a,L,\kappa,c\) in scope.

1. \(Z_{c,a,L,\infty}^{(\kappa)}\in(0,\infty)\), and \(Z_{c,a,L,R}^{(\kappa)}>0\) for all \(R\).
2. For each \(F\in\mathcal A_{\mathrm{loc}}^{\mathrm{ren}}\),
   \[
   \lim_{R\to\infty}\omega_{c,a,L,R}^{(\kappa)}(F)=\omega_{c,a,L,\infty}^{(\kappa)}(F).
   \]
3. For each \(\psi\in\mathcal T_B^{\mathrm{ren}}\), finite-volume SD identity
   \[
   \omega_{c,a,L,\infty}^{(\kappa)}(\partial_i\psi)
   =
   c\,\omega_{c,a,L,\infty}^{(\kappa)}\!\left(\psi\,\partial_iS_{a,L}^{(\kappa)}\right)
   \]
   holds for each \(i\in B\).
4. Local renormalized second moments obey
   \[
   \omega_{c,a,L,\infty}^{(\kappa)}(\varphi_x^2)\le \frac{1}{c_0m_0^2},
   \]
   uniformly in \(a,L,\kappa,c\).

### Proof sketch

1. Quartic coercivity gives \(e^{-cS}\in L^1(\mathbb R^{|\Lambda|})\); positivity gives \(Z>0\).
2. For compactly supported local \(F\), numerator and denominator converge by dominated convergence as truncation indicators increase to \(1\).
3. For \(\psi\in C_c^1\) in renormalized variables, integration by parts on \(\mathbb R^{|\Lambda|}\) has zero boundary term.
4. Multiply SD identity at \(i=x\) by \(\phi_x\), sum and use positivity of interaction terms:
   \[
   a^3m_0^2\,\omega(\phi_x^2)\le \frac1c\le\frac1{c_0}.
   \]
   Multiply by \(a^3\) to obtain the stated renormalized bound for \(\varphi_x^2=a^3\phi_x^2\).
\(\square\)

## Theorem (AN-24 Scoped Closure Without Hard Cutoff)

In the AN-23 compact-spin branch, replace finite \(R\) states by the \(R\to\infty\)
limit in \(\mathcal A_{\mathrm{loc}}^{\mathrm{ren}}\) and \(\mathcal T_B^{\mathrm{ren}}\).
Then B1-B4 remain closed in this lifted branch:

1. **B1:** uniform local renormalized moments from the proposition above,
2. **B2:** local tightness/precompactness in renormalized coordinates from uniform second moments,
3. **B3:** denominator non-vanishing from \(Z_{c,a,L,\infty}^{(\kappa)}>0\),
4. **B4:** SD pass-through in the same compactly supported local test class.

Combining with AN-21 renormalized B5 input yields the same scoped
\(\kappa\)-increment control theorem shape as AN-23, now without hard cutoff.

## Scope Boundary and Next Gap

Closed here:

1. AN-23 hard-cutoff artifact is removed in the Euclidean \(c>0\) lifted branch.

Still open:

1. extend this lifted branch from compact-support local test/observable classes to wider local classes,
2. oscillatory/de-regularized lift (\(\eta\to0^+\), \(c=\eta-i/h\)) for the same \(d=3\) branch.

## Validation Contract

### Assumptions

1. Euclidean compact \(c\)-window \([c_0,c_1]\subset(0,\infty)\),
2. local renormalized observable channel \(\mathcal A_{\mathrm{loc}}^{\mathrm{ren}}\),
3. compact-support SD test class \(\mathcal T_B^{\mathrm{ren}}\).

### Units and dimensions check

1. \(cS\) is dimensionless,
2. renormalized variables \(\varphi_x=a^{3/2}\phi_x\) remove explicit \(a^{-3}\) growth in local second moments.

### Symmetry/conservation checks

1. periodic translation invariance is unchanged by cutoff lift,
2. SD identity remains exact in finite volume for compactly supported local tests.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_an24_cutoff_lift_check.py
```

The script checks:

1. stabilization of local renormalized observables as \(R\) increases,
2. SD residuals in compact-support local tests after cutoff lift,
3. renormalized local moment boundedness and AN-21 renormalized insertion bounds.

### Confidence statement

Within the stated Euclidean local-renormalized channel, AN-24 is theorem-grade.
Any claim beyond that channel must be marked unverified.

### Reproducibility metadata

1. Python: `python3.12`,
2. seed and parameter grid printed by script,
3. date anchor: 2026-02-09 (US).
