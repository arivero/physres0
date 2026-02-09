# Claim 1 Phase AP: Closed \(d=2\) Interacting Field-Level Theorem (Ultralocal \(\phi^4\))

Date: 2026-02-09 (CET)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim1-d2-field-cylinder-candidate.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-fd-schwinger-dyson-identity.md`

## Goal

Close AN-1 with a fully proved field-indexed theorem in an explicit non-Gaussian interacting class in \(d=2\).

## Model (Explicit)

Fix \(m_0^2>0\), \(\lambda>0\), and
\[
V(u):=\frac{m_0^2}{2}u^2+\frac{\lambda}{4}u^4,\qquad u\in\mathbb R.
\]

For each \(c\in\mathbb C\) with \(\Re c>0\), define the one-site partition factor
\[
Z_1(c):=\int_{\mathbb R}e^{-cV(u)}\,du.
\]
Work on the domain
\[
\mathcal D:=\{c\in\mathbb C:\Re c>0,\ Z_1(c)\neq0\}.
\]

For \(d=2\), finite periodic lattice \(\Lambda_{a,L}\subset \mathbb T_L^2\) (spacing \(a\), side \(L\), \(N(a,L)=|\Lambda_{a,L}|\)):
\[
S_{a,L}(\phi):=\sum_{x\in\Lambda_{a,L}}V(\phi_x),
\qquad
\phi\in\mathbb R^{N(a,L)}.
\]
Define
\[
d\mu_{c,a,L}(\phi)=\frac{1}{Z_{c,a,L}}e^{-cS_{a,L}(\phi)}\prod_{x\in\Lambda_{a,L}}d\phi_x,
\quad
Z_{c,a,L}=\int e^{-cS_{a,L}}\prod_x d\phi_x.
\]

Because \(S_{a,L}\) is sitewise additive, \(\mu_{c,a,L}\) is a product measure:
\[
\mu_{c,a,L}=\bigotimes_{x\in\Lambda_{a,L}}\nu_c,\qquad
d\nu_c(u)=Z_1(c)^{-1}e^{-cV(u)}\,du.
\]

## Field-Indexed Cylinder Observables

Fix distinct points \(p_1,\dots,p_k\in\mathbb R^2\), and \(G\in C_b^1(\mathbb R^k)\).  
For each mesh \(a\), let \(x_i(a)\in\Lambda_{a,L}\) be the nearest-lattice representative of \(p_i\), with a deterministic tie-break.

Define lattice cylinder observable
\[
F_{a,L}(\phi):=G\!\left(\phi_{x_1(a)},\dots,\phi_{x_k(a)}\right).
\]

For small enough \(a\) (depending on minimum pairwise distance among \(p_i\)), the \(x_i(a)\) are distinct.

## Theorem 1 (Exact Cylinder Stabilization and Continuum Existence in \(d=2\))

Let \(c\in\mathcal D\), \(p_1,\dots,p_k\) distinct, \(G\in C_b^1(\mathbb R^k)\).  
Then there exists \(a_*(p_1,\dots,p_k)>0\) such that for all \(0<a<a_*\) and all \(L\) large enough to contain the selected representatives:
\[
\mathbb E_{\mu_{c,a,L}}[F_{a,L}]
=
\int_{\mathbb R^k}G(u_1,\dots,u_k)\prod_{j=1}^k d\nu_c(u_j)
:\Omega_c^{(k)}(G).
\]
Hence \(\mathbb E_{\mu_{c,a,L}}[F_{a,L}]\) is exactly independent of \((a,L)\) in that regime, and the continuum limit exists without further renormalization:
\[
\lim_{a\to0,\ L\to\infty}\mathbb E_{\mu_{c,a,L}}[F_{a,L}]
=
\Omega_c^{(k)}(G).
\]

### Proof

For \(0<a<a_*\), selected sites \(x_1(a),\dots,x_k(a)\) are distinct.  
Under product structure,
\[
\mathbb E_{\mu_{c,a,L}}[F_{a,L}]
=
\int_{\mathbb R^{N(a,L)}}G(\phi_{x_1(a)},\dots,\phi_{x_k(a)})
\prod_{x\in\Lambda_{a,L}}d\nu_c(\phi_x).
\]
Integrate out all sites not in \(\{x_1(a),\dots,x_k(a)\}\), each contributing factor \(1\).  
What remains is exactly
\[
\int_{\mathbb R^k}G(u_1,\dots,u_k)\prod_{j=1}^k d\nu_c(u_j),
\]
which has no dependence on \(a\) or \(L\). Therefore the directed limit exists and equals this value. \(\square\)

## Theorem 2 (Field-Level Schwinger-Dyson Identity in the Limit State)

Let \(G\in C_b^1(\mathbb R^k)\) with \(\partial_i G\) integrable against \(\nu_c^{\otimes k}\).  
For \(i\in\{1,\dots,k\}\),
\[
\Omega_c^{(k)}(\partial_i G)
=
c\,\Omega_c^{(k)}\!\big(G\,V'(\xi_i)\big),
\qquad
V'(u)=m_0^2u+\lambda u^3,
\]
where \(\xi_i\) denotes the \(i\)-th coordinate variable.

### Proof

Write \(\Omega_c^{(k)}\) as product integral. By Fubini, hold all variables except \(u_i\) fixed and apply one-dimensional integration by parts:
\[
\int_{\mathbb R}\partial_i G(\dots,u_i,\dots)e^{-cV(u_i)}\,du_i
=
c\int_{\mathbb R}G(\dots,u_i,\dots)V'(u_i)e^{-cV(u_i)}\,du_i,
\]
since \(\Re c>0\) and quartic growth gives boundary decay. Divide by \(Z_1(c)\), then integrate remaining coordinates. \(\square\)

## Corollary (Exact \(c\)-Invariance Along \(\tau_\mu\)-Orbits)

Let parameter triples \((\kappa,\eta,h)\) and \((\kappa',\eta',h')\) satisfy
\[
c=(\eta-i/h)\kappa=(\eta'-i/h')\kappa'\in\mathcal D.
\]
Then for every \(k\)-point cylinder \(G\),
\[
\Omega_{(\kappa,\eta,h)}^{(k)}(G)=\Omega_{(\kappa',\eta',h')}^{(k)}(G)=\Omega_c^{(k)}(G).
\]

So the field-level cylinder state depends only on \(c\), not on the representative triple.

## Interpretation and Scope

1. This is an explicit non-Gaussian interacting closure (\(\lambda>0\)) in \(d=2\).
2. It closes the field-indexed cylinder existence + SD + \(c\)-invariance chain in a rigorous model class.
3. It is ultralocal (no gradient coupling), so it is a controlled baseline, not yet the full relativistic local QFT target.

## Reproducibility

Run:

```bash
python3.12 research/workspace/simulations/claim1_d2_ultralocal_phi4_closure_check.py
```

The script verifies:

1. lattice-size invariance of selected cylinder expectations,
2. Schwinger-Dyson residuals near numerical zero,
3. equality for \(\tau_\mu\)-related parameter triples with identical \(c\).
