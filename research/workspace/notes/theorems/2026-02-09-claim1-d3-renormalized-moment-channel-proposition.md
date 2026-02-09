# Claim 1 Phase BM (AN-21): \(d=3\) Renormalized Moment Channel for B5b

Date: 2026-02-09 (CET)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim1-d3-finite-volume-centered-moment-proposition.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-d3-intermediate-bridge-candidate.md`

## Goal

Replace AN-20's explicit finite-volume \(a^{-3}\) moment constant with a
continuum-safe renormalized channel that is uniform in lattice spacing.

## Setup

Use the AN-20 periodic \(d=3\) lattice class:
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
with \(m_0^2>0,\lambda>0,\kappa\in[0,\kappa_*]\), and Euclidean channel
\[
d\mu_{c,a,L}^{(\kappa)}(\phi)=
\frac{1}{Z_{c,a,L}^{(\kappa)}}e^{-cS_{a,L}^{(\kappa)}(\phi)}\,d\phi,
\quad c\in[c_0,c_1]\subset(0,\infty).
\]

For local edge set \(E_B\), define
\[
G_B(\phi):=\sum_{\langle x,y\rangle\in E_B}(\phi_x-\phi_y)^2.
\]
Introduce renormalized lattice field and insertion:
\[
\varphi_x:=a^{3/2}\phi_x,\qquad
G_{B,a}^{\mathrm{ren}}(\phi):=\sum_{\langle x,y\rangle\in E_B}(\varphi_x-\varphi_y)^2=a^3G_B(\phi).
\]

## Proposition (Renormalized B5b Constants)

Under the setup above, for every \(a>0\), \(L\), and \(\kappa\in[0,\kappa_*]\):

1. centered bound (same as AN-20):
   \[
   |F-\omega(F)|\le K_F,\qquad K_F:=2\|F\|_\infty,
   \]
   for bounded local cylinders \(F\);
2. renormalized local moment bound:
   \[
   \omega_{c,a,L}^{(\kappa)}\!\left(G_{B,a}^{\mathrm{ren}}\right)
   \le M_B^{\mathrm{ren}},
   \qquad
   M_B^{\mathrm{ren}}:=\frac{4|E_B|}{c_0m_0^2},
   \]
   which is uniform in \(a,L,\kappa\).

Hence B5b has an explicit finite-volume constant pair \((K_F,M_B^{\mathrm{ren}})\)
without explicit \(a^{-3}\) divergence.

## Proof

From AN-20:
\[
\omega_{c,a,L}^{(\kappa)}(G_B)\le \frac{4|E_B|}{c_0m_0^2a^3}.
\]
Multiply both sides by \(a^3\), use \(G_{B,a}^{\mathrm{ren}}=a^3G_B\), and obtain
\[
\omega_{c,a,L}^{(\kappa)}\!\left(G_{B,a}^{\mathrm{ren}}\right)
\le \frac{4|E_B|}{c_0m_0^2}=M_B^{\mathrm{ren}}.
\]
Centered bound is unchanged from AN-20. \(\square\)

## Mapping to AN-19 B5b

1. finite-volume B5b now has an \(a\)-uniform renormalized moment channel,
2. AN-18/AN-19 finite-model bridge can be fed using renormalized insertions,
3. B1-B4 remain independent and are still required for continuum closure.

## What Is Still Open

1. identify the continuum observable map corresponding to
   \(G_{B,a}^{\mathrm{ren}}\),
2. combine the renormalized B5b channel with B1-B4 tightness/SD/denominator
   controls to produce a scoped \(d=3\) continuum theorem.

## Validation Contract

### Assumptions

1. finite periodic volume and bounded local cylinders,
2. Euclidean channel \(c\in[c_0,c_1]\subset(0,\infty)\),
3. fixed local edge set \(E_B\).

### Units and dimensions check

1. \(G_B\) carries the explicit raw lattice scaling captured in AN-20,
2. \(G_{B,a}^{\mathrm{ren}}=a^3G_B\) is the renormalized channel used for
   \(a\)-uniform bounds.

### Symmetry/conservation checks

1. translation symmetry assumptions are exactly those used in AN-20,
2. edge-exchange symmetry is preserved by \(G_{B,a}^{\mathrm{ren}}\).

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_renormalized_moment_channel_check.py
```

The script scans several \(a\) values and checks both raw and renormalized
moment inequalities empirically.

### Confidence statement

Renormalized finite-volume channel is closed under AN-20 assumptions.
Continuum closure is still pending B1-B4 integration.

### Reproducibility metadata

1. Python: `python3.12`,
2. seed and parameter grid printed by script,
3. date anchor: 2026-02-09 (US).
