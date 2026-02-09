# Claim 1 Phase AQ (AN-2): \(d=4\) Lift-Obstruction Sheet from the \(d=2\) AP Closure

Date: 2026-02-09 (CET)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim1-d2-ultralocal-phi4-closure.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-field-dimension-existence-roadmap.md`

## Goal

State exactly why the AP theorem (closed in \(d=2\) ultralocal \(\phi^4\)) does not automatically lift to the physically central \(d=4\) local field setting.

## AP Proof Steps (What Was Used)

The AP closure used four structural ingredients:

1. **Sitewise factorization**:
   \[
   \mu_{c,a,L}=\bigotimes_{x\in\Lambda}\nu_c.
   \]
2. **Exact cylinder decoupling**:
   integrate out non-observed sites to obtain exact \((a,L)\)-independent value.
3. **One-site integration by parts**:
   SD identity reduced to a one-dimensional boundary-vanishing statement.
4. **\(c\)-parameter dependence only**:
   once normalized by \(Z_1(c)\), all observables depend only on \(c\).

## Obstructions After Restoring Local Propagation in \(d=4\)

Consider local lattice actions with gradient coupling, schematically:
\[
S_{a,L}^{\mathrm{loc}}(\phi)
=
a^4\sum_x\left[
\frac12\phi_x(-\Delta_a+m^2)\phi_x+\frac{\lambda}{4}\phi_x^4
+\text{counterterms}
\right].
\]

Then AP steps fail as follows:

1. **Loss of product structure**:
   nearest-neighbor coupling destroys exact factorization.
2. **No exact cylinder independence**:
   integrating out complement of observed sites induces nontrivial effective interactions (nonlocal kernels in general).
3. **SD hierarchy no longer one-site closed**:
   SD equations couple different coordinates/correlation orders.
4. **Renormalization dependence enters the limit**:
   continuum removal \(a\to0\) needs counterterm flow control; bare parameter choices are not stable.
5. **Potential triviality/open nontriviality issues in \(d=4\)**:
   even when limits exist along subsequences, nontrivial interacting continuum control requires extra hypotheses/proofs.

## Minimal Additional Hypotheses Needed for a \(d=4\) Lift

To promote AP-style conclusions in \(d=4\), one must add model-specific control for:

1. uniform tightness of local cylinders under regulator removal,
2. non-vanishing normalization in the target \(c\)-domain,
3. closed SD pass-through with renormalized insertions,
4. nontriviality criterion for the limiting state (not only existence),
5. compatibility of those bounds with \(c\)-invariance/\(\tau_\mu\)-orbit representation.

Without these items, AP cannot be cited as a \(d=4\) closure.

## Power-Counting Signal (Why \(d=4\) Is Boundary-Sensitive)

For \(\phi^4\)-type local interactions, superficial divergence degree scales as
\[
\omega \sim d-E
\]
(up to topology-dependent constants in standard graph counting conventions),
so \(d=4\) sits at the critical boundary where low-point functions remain UV-sensitive.

Program consequence:

1. \(d=2\): strongest closure candidate,
2. \(d=3\): intermediate,
3. \(d=4\): frontier requiring explicit renormalization and nontriviality input.

## Immediate AN-3 Link

Given these obstructions, the amplitude vs geometric \(1/2\)-density discussion must be split into:

1. kinematic composition/Jacobian statements (can hold widely),
2. dynamical continuum-existence statements (dimension/renormalization sensitive).

That split is the next deliverable.
