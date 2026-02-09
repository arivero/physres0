# Claim 1 Phase BL (AN-20): \(d=3\) Finite-Volume Centered/Moment Proposition for B5b

Date: 2026-02-09 (CET)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim1-d3-intermediate-bridge-candidate.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-d3-small-kappa-lipschitz-prototype.md`

## Goal

Provide a first explicit finite-volume \(d=3\) proposition that supplies the two
quantities needed in AN-19 B5b:

1. a uniform centered bound constant \(K_F\),
2. a uniform local gradient-moment bound constant \(M_{B,a}\).

This is a finite-volume theorem step, not yet continuum closure.

## Model and Observable Class

On periodic \(\Lambda_{a,L}\subset a\mathbb Z^3\), define
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
with \(m_0^2>0,\lambda>0,\kappa\in[0,\kappa_*]\).

Work in the Euclidean channel \(c\in[c_0,c_1]\subset(0,\infty)\):
\[
d\mu_{c,a,L}^{(\kappa)}(\phi)=
\frac{1}{Z_{c,a,L}^{(\kappa)}}e^{-cS_{a,L}^{(\kappa)}(\phi)}\,d\phi.
\]

Fix finite site block \(B\subset\Lambda_{a,L}\), local edge set
\(E_B:=\{\langle x,y\rangle:\ x\in B,\ y\sim x\}\), and local bounded cylinders
\[
F(\phi)=f\big(\phi|_B\big),\qquad \|F\|_\infty<\infty.
\]
Define local gradient insertion
\[
G_B(\phi):=\sum_{\langle x,y\rangle\in E_B}(\phi_x-\phi_y)^2.
\]

## Proposition (Finite-Volume B5b Input Pair)

Under the setup above, for every \(L\) and every \(\kappa\in[0,\kappa_*]\):

1. (**centered bound**) pointwise,
   \[
   |F(\phi)-\omega_{c,a,L}^{(\kappa)}(F)|\le 2\|F\|_\infty,
   \]
   so one can take \(K_F:=2\|F\|_\infty\), independent of \(L,\kappa\).
2. (**local moment bound**) uniformly in \(L,\kappa\),
   \[
   \omega_{c,a,L}^{(\kappa)}(G_B)\le M_{B,a},
   \qquad
   M_{B,a}:=\frac{4|E_B|}{c_0\,m_0^2\,a^3}.
   \]

Hence AN-19 B5b has an explicit finite-volume constant pair \((K_F,M_{B,a})\).

## Proof

### Step 1: Centered bound

For bounded \(F\),
\[
|F-\omega(F)|\le |F|+|\omega(F)|\le \|F\|_\infty+\|F\|_\infty=2\|F\|_\infty.
\]

### Step 2: Uniform one-site second moment bound

By periodic symmetry, \(\mu_{c,a,L}^{(\kappa)}\) is translation-invariant.
Using integration by parts and summing over all sites:
\[
\sum_{x\in\Lambda_{a,L}}\omega\!\left(\phi_x\,\partial_{\phi_x}S_{a,L}^{(\kappa)}\right)
=\frac{|\Lambda_{a,L}|}{c}.
\]
Direct expansion gives
\[
\sum_{x}\phi_x\,\partial_{\phi_x}S_{a,L}^{(\kappa)}
=
a^3\sum_x\!\left(m_0^2\phi_x^2+\lambda\phi_x^4\right)
+\kappa a\sum_{\langle x,y\rangle}(\phi_x-\phi_y)^2.
\]
All terms are nonnegative, so
\[
a^3m_0^2\sum_x\omega(\phi_x^2)\le \frac{|\Lambda_{a,L}|}{c}.
\]
Translation invariance yields
\[
\omega(\phi_x^2)\le \frac{1}{c\,m_0^2\,a^3}\le \frac{1}{c_0\,m_0^2\,a^3}.
\]

### Step 3: Local gradient moment bound

For each edge \(\langle x,y\rangle\),
\[
(\phi_x-\phi_y)^2\le 2\phi_x^2+2\phi_y^2.
\]
Taking expectation and using Step 2,
\[
\omega\!\left((\phi_x-\phi_y)^2\right)\le \frac{4}{c_0\,m_0^2\,a^3}.
\]
Sum over \(E_B\):
\[
\omega(G_B)\le \frac{4|E_B|}{c_0\,m_0^2\,a^3}=M_{B,a}.
\]
\(\square\)

## Mapping to AN-19 B5b

With \(K_F=2\|F\|_\infty\) and \(M_{B,a}\) above, the finite-volume \(d=3\)
B5b slot has explicit constants.

What remains open:

1. remove/renormalize explicit \(a^{-3}\) scaling in a continuum-safe way,
2. combine with B1-B4 and tightness to pass \(L\to\infty\) and then \(a\to0\).

## Validation Contract

### Assumptions

1. Euclidean channel \(c\in[c_0,c_1]\subset(0,\infty)\),
2. finite periodic volume,
3. bounded local cylinders \(F\),
4. fixed local edge set \(E_B\).

### Units and dimensions check

1. action terms have action dimension,
2. \(cS\) is dimensionless,
3. bound constant \(M_{B,a}\propto a^{-3}\) is explicit, not hidden.

### Symmetry/conservation checks

1. periodic-translation invariance used explicitly in Step 2,
2. edge symmetry \((x,y)\leftrightarrow(y,x)\) respected in \(G_B\).

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_finite_volume_centered_moment_bound_check.py
```

The script samples a small periodic \(d=3\) lattice Gibbs channel and checks:

1. empirical centered inequality against \(2\|F\|_\infty\),
2. empirical \(\omega(G_B)\) against \(M_{B,a}\).

### Confidence statement

Finite-volume Euclidean proposition is closed under stated assumptions.
Continuum upgrade remains open and is queued in AN-21.

### Reproducibility metadata

1. Python: `python3.12`,
2. seed fixed in script output,
3. date anchor: 2026-02-09 (US).
