# Claim 1 Phase BO (AN-23): \(d=3\) Scoped B1-B4 Closure in a Compact-Spin Interacting Subclass

Date: 2026-02-09 (CET)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim1-d3-scoped-continuum-branch-candidate.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-d3-renormalized-moment-channel-proposition.md`

## Goal

Discharge AN-22 open obligations B1-B4 in one explicit interacting \(d=3\)
subclass, so the AN-22 candidate is upgraded to a scoped closure theorem in that subclass.

## Scoped Model Class (Concrete)

Fix:

1. \(m_0^2>0\), \(\lambda>0\), \(\kappa\in[0,\kappa_*]\),
2. Euclidean \(c\in[c_0,c_1]\subset(0,\infty)\),
3. hard spin cutoff \(R>0\),
4. periodic lattice \(\Lambda_{a,L}\subset a\mathbb Z^3\), \(0<a\le 1\).

Action:
\[
S_{a,L}^{(\kappa)}(\phi)
=
a^3\sum_{x\in\Lambda_{a,L}}
\left[
\frac{m_0^2}{2}\phi_x^2+\frac{\lambda}{4}\phi_x^4
\right]
+
\frac{\kappa a^3}{2}\sum_{\langle x,y\rangle}\frac{(\phi_x-\phi_y)^2}{a^2}.
\]

State space is compact:
\[
\Omega_{a,L,R}:=[-R,R]^{|\Lambda_{a,L}|}.
\]
Define finite-volume Gibbs state
\[
d\mu_{c,a,L,R}^{(\kappa)}(\phi)=
\frac{1}{Z_{c,a,L,R}^{(\kappa)}}
e^{-cS_{a,L}^{(\kappa)}(\phi)}
\mathbf 1_{\Omega_{a,L,R}}(\phi)\,d\phi.
\]

Use bounded local cylinders \(F(\phi)=f(\phi|_B)\), and renormalized local edge insertion
\[
G_{B,a}^{\mathrm{ren}}:=a^3\sum_{\langle x,y\rangle\in E_B}(\phi_x-\phi_y)^2.
\]

For SD pass-through, use local test class
\[
\mathcal T_B:=\{\psi\in C^1([-R,R]^{|B|})\;:\;\psi=0 \text{ on a neighborhood of }\partial([-R,R]^{|B|})\}.
\]

## Proposition (B1-B4 Are Closed in This Subclass)

Under the setup above:

1. **B1 (uniform local moments):** for every \(p\ge1\), local site \(x\),
   \[
   \omega_{c,a,L,R}^{(\kappa)}(|\phi_x|^p)\le R^p,
   \]
   uniformly in \(a,L,\kappa,c\).
2. **B2 (local tightness/precompactness):** for each finite block \(B\), the
   family of marginals on \([-R,R]^{|B|}\) is tight; hence along any directed
   refinement net \((a,L)\to(0,\infty)\), extracted local subnet limits exist.
3. **B3 (denominator non-vanishing):**
   \[
   Z_{c,a,L,R}^{(\kappa)}=\int_{\Omega_{a,L,R}}e^{-cS_{a,L}^{(\kappa)}}\,d\phi>0
   \]
   for all \(a,L,\kappa,c\) in scope.
4. **B4 (SD insertion pass-through, scoped test class):** for each site \(i\in B\),
   \(\psi\in\mathcal T_B\), finite-volume identity
   \[
   \omega_{c,a,L,R}^{(\kappa)}(\partial_i\psi)
   =
   c\,\omega_{c,a,L,R}^{(\kappa)}\!\left(\psi\,\partial_i S_{a,L}^{(\kappa)}\right)
   \]
   holds exactly, and passes to extracted local limits.

## Proof

### Step 1 (B1)

On \(\Omega_{a,L,R}\), \(|\phi_x|\le R\) pointwise, so \(|\phi_x|^p\le R^p\).
Take expectation.

### Step 2 (B2)

Each block marginal is supported on compact \([-R,R]^{|B|}\), so tightness is automatic.
By compactness/diagonal extraction on a countable local-observable skeleton,
one gets extracted local limits along refinement nets.

### Step 3 (B3)

Integrand is strictly positive and continuous on compact \(\Omega_{a,L,R}\),
hence integral is strictly positive.

### Step 4 (B4 finite volume)

Because \(\psi\in\mathcal T_B\) vanishes near block boundary, boundary terms in
coordinatewise integration by parts vanish. Therefore
\[
\int \partial_i\psi\,e^{-cS}
=
c\int \psi\,(\partial_i S)\,e^{-cS},
\]
and dividing by \(Z>0\) gives finite-volume SD.

### Step 5 (B4 pass-through)

On \(\Omega_{a,L,R}\), \(\psi\) and \(\partial_i\psi\) are bounded.
Also, for \(0<a\le1\),
\[
|\partial_i S_{a,L}^{(\kappa)}|
\le
a^3\!\left(m_0^2R+\lambda R^3\right)+12\kappa_*R
\le
C_{R,\kappa_*,m_0,\lambda},
\]
uniform in \(a,L,\kappa\). Hence SD pairing terms are uniformly bounded, so
SD identities pass to extracted local limits by dominated convergence
along the extracted subnet.
\(\square\)

## Theorem (AN-23 Scoped Closure in the Compact-Spin Branch)

Fix \(R>0\) and the model class above. Combine:

1. B1-B4 closure from this note,
2. B5b renormalized constants from AN-21:
   \[
   |F-\omega(F)|\le K_F,\qquad
   \omega(G_{B,a}^{\mathrm{ren}})\le M_B^{\mathrm{ren}},
   \]
3. AN-22 increment template.

Then the \(d=3\) branch is closed at scoped level in this subclass:
for each local bounded \(F\), extracted local limit states satisfy
\[
|\omega_{c,R}^{(\kappa)}(F)-\omega_{c,R}^{(0)}(F)|\le C_{F,R}\kappa,
\]
and scoped SD identities hold in the limit for \(\psi\in\mathcal T_B\).

## Scope Boundary and Next Gap

Closed here:

1. AN-22 candidate -> scoped closure in one explicit interacting \(d=3\) subclass.

Still open:

1. remove hard cutoff \(R\to\infty\) while preserving B1-B4 in the same branch,
2. extend from Euclidean \(c>0\) to oscillatory/de-regularized branch where desired.

## Validation Contract

### Assumptions

1. hard cutoff \(R>0\),
2. Euclidean compact \(c\)-window \([c_0,c_1]\subset(0,\infty)\),
3. SD test class \(\mathcal T_B\) with boundary-vanishing support.

### Units and dimensions check

1. \(cS\) is dimensionless,
2. renormalized insertion uses \(G_{B,a}^{\mathrm{ren}}=a^3G_B\),
3. derivative bound constant is explicit in \(R,\kappa_*,m_0,\lambda\).

### Symmetry/conservation checks

1. periodic translation invariance remains available,
2. local SD identity is exact at finite volume in \(\mathcal T_B\).

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_an23_compact_spin_closure_check.py
```

The script checks:

1. compact-spin B1 and B3 facts numerically in finite volume,
2. finite-volume SD residuals for boundary-vanishing \(\psi\),
3. small-\(\kappa\) increment scaling for bounded local observables.

### Confidence statement

Within this compact-spin Euclidean subclass, AN-23 closure is theorem-grade.
Claims beyond this scope must be marked unverified.

### Reproducibility metadata

1. Python: `python3.12`,
2. seed printed by script,
3. date anchor: 2026-02-09 (US).
