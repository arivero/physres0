# Claim 1 Phase AN-1 Draft: \(d=2\) Field-Indexed Cylinder Candidate and \(d=4\) Obstruction Checklist

Date: 2026-02-09 (CET)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim1-three-level-program.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-field-dimension-existence-roadmap.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-continuum-c-invariance-candidate.md`

## Scope

Draft a field-level upgrade path for Claim 1 in \(d=2\), still in theorem-candidate form.
This is a dimension-gated escalation note, not yet a full constructive proof.

## Lattice Field Setup (\(d=2\), Euclidean Signature)

Let \(\Lambda_{a,L}\subset a\mathbb{Z}^2\) be a periodic box of side \(L\), spacing \(a\).
Field variables are \(\phi=(\phi_x)_{x\in\Lambda_{a,L}}\in\mathbb{R}^{N(a,L)}\).

Use the renormalized lattice action family
\[
S_{a,L}(\phi)=a^2\sum_{x\in\Lambda_{a,L}}
\left[
\frac12 \phi_x(-\Delta_a+m^2_{a,L})\phi_x
+\frac{\lambda}{4}\phi_x^4
+\delta m^2_{a,L}\phi_x^2
+\delta E_{a,L}
\right],
\]
with \(\lambda\ge0\), and counterterms chosen by a fixed renormalization prescription.

Define, for \(\Re c>0\), cylinder observable \(F\) (depending on finitely many sites),
\[
\omega_{c,a,L}(F)=
\frac{\int_{\mathbb{R}^{N(a,L)}}e^{-cS_{a,L}(\phi)}F(\phi)\,d\phi}
{\int_{\mathbb{R}^{N(a,L)}}e^{-cS_{a,L}(\phi)}\,d\phi}.
\]

As in finite-dimensional phases, parameter triples \((\kappa,\eta,h)\) are mapped to
\[
c=(\eta-i/h)\kappa,
\]
and \(\tau_\mu\)-orbits preserve \(c\).

## Candidate Theorem (Dimension-Gated Claim 1 Lift in \(d=2\))

Assume:

1. (**A1: uniform integrability/tightness**) local polynomial cylinders are uniformly integrable along a directed limit \((a,L)\to(0,\infty)\);
2. (**A2: denominator non-vanishing**) partition factors in the normalization denominator stay nonzero in the working \(c\)-domain;
3. (**A3: local convergence**) \(\omega_{c,a,L}(F)\) converges for every local cylinder \(F\);
4. (**A4: SD pass-through bounds**) lattice SD pairings are uniformly controlled so discrete integration-by-parts identities pass to the limit.

Then:

1. \(\omega_c(F):=\lim_{(a,L)\to(0,\infty)}\omega_{c,a,L}(F)\) defines a local field cylinder state;
2. \(\omega_c\) is \(c\)-invariant along \(\tau_\mu\)-orbits;
3. local Schwinger-Dyson identities persist in the limit:
   \[
   \omega_c(\partial_i\psi)=c\,\omega_c(\psi\,\mathcal{G}_i),
   \]
   where \(\mathcal{G}_i\) is the continuum limit of lattice Euler-Lagrange channels in pairing sense.

This is the direct field-level analog of the finite-dimensional \(c\)-invariant SD chain.

## Half-Density Status in This Candidate

1. Core proof channel: correlator/cylinder state route (no mandatory half-density formalism).
2. Compatible interpretation: amplitude/half-density route remains admissible if one keeps composition/Jacobian control explicit.

## \(d=4\) Obstruction Checklist (Why AN-1 Does Not Auto-Lift)

To avoid overreach, the \(d=2\) candidate does not imply \(d=4\) closure unless one separately controls:

1. renormalization-counterterm hierarchy sufficient for continuum nontriviality;
2. uniform integrability/tightness analogs at \(d=4\) scaling;
3. denominator non-vanishing and SD pass-through under \(d=4\)-specific UV behavior;
4. nontriviality criterion excluding collapse to a Gaussian/trivial limit in the chosen model class.

These are explicit hypotheses, not currently proved in this workspace.

## Next Upgrade

Convert this candidate into a closed theorem in one explicit \(d=2\) interacting class
with fully written assumptions and verification hooks, then keep the \(d=4\) list as open gates.
