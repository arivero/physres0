# Claim 1 Phase AS (AN-4): \(d=3\) Intermediate Bridge Candidate Beyond Ultralocal

Date: 2026-02-09 (CET)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim1-d2-ultralocal-phi4-closure.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-d4-lift-obstruction-sheet.md`

## Goal

Define the next bridge class between:

1. closed \(d=2\) ultralocal interacting theorem (AP),
2. unresolved \(d=4\) local propagation frontier (AQ).

This note provides a theorem candidate in \(d=3\) with explicit proof obligations.

## Candidate \(d=3\) Local Lattice Class

On \(\Lambda_{a,L}\subset a\mathbb Z^3\) with periodic boundary, define
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
with \(m_0^2>0,\lambda>0,\kappa\ge0\).

For \(c\in\mathbb C\), \(\Re c>0\), define normalized states
\[
\omega_{c,a,L}^{(\kappa)}(F)=
\frac{\int e^{-cS_{a,L}^{(\kappa)}(\phi)}F(\phi)\,d\phi}
{\int e^{-cS_{a,L}^{(\kappa)}(\phi)}\,d\phi}.
\]

At \(\kappa=0\), this reduces to ultralocal product structure.

## Theorem Candidate (Bridge Form)

For local cylinders \(F\), under the hypotheses below, limits
\[
\omega_c^{(\kappa)}(F):=\lim_{a\to0,\ L\to\infty}\omega_{c,a,L}^{(\kappa)}(F)
\]
exist for \(\kappa\in[0,\kappa_*]\), and satisfy:

1. continuity at \(\kappa=0\) (bridge to AP closure),
2. SD pass-through for local insertions,
3. dependence only on \(c\) along \(\tau_\mu\)-orbits.

## Explicit Proof Obligations (Required Inputs)

To close the candidate, establish:

1. **B1: uniform local moment bounds** in \((a,L)\) for \(\kappa\in[0,\kappa_*]\),
2. **B2: local tightness / precompactness** of cylinder marginals,
3. **B3: denominator non-vanishing** on the working compact \(c\)-domain,
4. **B4: SD insertion control** for nearest-neighbor coupling terms,
5. **B5: \(\kappa\)-continuity estimate** near \(\kappa=0\) for local \(F\).

Without B1-B5, the bridge remains candidate-level.

## First Quantitative Target for Closure

A concrete next theorem target:

1. prove B5 with an explicit small-\(\kappa\) bound
   \[
   |\omega_{c,a,L}^{(\kappa)}(F)-\omega_{c,a,L}^{(0)}(F)|
   \le C_F\,\kappa
   \]
   uniformly on a restricted local observable class;
2. then use B1-B4 to pass to \((a,L)\to(0,\infty)\).

## AN-19 Alignment Update (Finite Lean Chain -> \(d=3\) B5)

Lean AN-18 now provides a finite-model wrapper theorem
`omegaExp_increment_bound_of_uniform_centered_control_auto`
in `research/workspace/proofs/Claim1lean/FiniteExponentialIncrementBound.lean`:
\[
|\omega(\kappa)-\omega(0)| \le (K\,M)\kappa
\]
under only:

1. \(\kappa\ge0\),
2. \(K\ge0\) and centered control \(|f_i-\omega(\kappa)|\le K\),
3. weighted-moment control \(\sum_i |p_i(\kappa)|\,|s_i|\le M\).

Regularity side-assumptions (differentiability, `derivWithin = deriv`, and
`Z\neq0`) are discharged automatically by
`research/workspace/proofs/Claim1lean/FiniteExponentialRegularity.lean`.

Implication for this \(d=3\) bridge note:

1. B5 can now be split into:
   - **B5a (reduced by AN-18):** no separate regularity bookkeeping is needed in the finite surrogate lane,
   - **B5b (remaining field task):** establish field-side analogues of centered and weighted-moment bounds uniformly in \((a,L)\), then pass limits.
2. B1-B4 remain independent obligations; AN-18 only collapses the B5 regularity part, not tightness/SD denominator/global limit controls.

## AN-20 Update (Finite-Volume B5b Constants Landed)

AN-20 now supplies the first explicit finite-volume B5b constants in:

- `research/workspace/notes/theorems/2026-02-09-claim1-d3-finite-volume-centered-moment-proposition.md`

For Euclidean \(c\in[c_0,c_1]\subset(0,\infty)\), bounded local cylinders \(F\),
and local edge insertion \(G_B\), it gives
\[
|F-\omega(F)|\le K_F,\qquad K_F=2\|F\|_\infty,
\]
and
\[
\omega(G_B)\le M_{B,a},\qquad
M_{B,a}=\frac{4|E_B|}{c_0m_0^2a^3},
\]
uniform in finite volume \(L\) and \(\kappa\in[0,\kappa_*]\).

Implication:

1. B5b is now closed at finite volume with explicit constants.
2. Remaining B5 work is continuum-safe renormalized passage \(a\to0\), coupled with B1-B4.

## AN-21 Update (Renormalized B5b Channel Landed)

AN-21 now upgrades AN-20's raw finite-volume moment channel to an
\(a\)-uniform renormalized channel in:

- `research/workspace/notes/theorems/2026-02-09-claim1-d3-renormalized-moment-channel-proposition.md`

Define
\[
G_{B,a}^{\mathrm{ren}}:=a^3G_B
=\sum_{\langle x,y\rangle\in E_B}(a^{3/2}(\phi_x-\phi_y))^2.
\]
Then AN-20 implies
\[
\omega_{c,a,L}^{(\kappa)}(G_{B,a}^{\mathrm{ren}})
\le M_B^{\mathrm{ren}},
\qquad
M_B^{\mathrm{ren}}=\frac{4|E_B|}{c_0m_0^2},
\]
uniform in \(a,L,\kappa\).

Implication:

1. B5b now has an explicit renormalized finite-volume channel without exposed
   \(a^{-3}\) constants.
2. Remaining bridge work is B1-B4 plus continuum identification of the
   renormalized insertion map.

## AN-22 Update (Scoped Continuum-Branch Candidate Landed)

AN-22 now integrates AN-21 B5b with B1-B4 in:

- `research/workspace/notes/theorems/2026-02-09-claim1-d3-scoped-continuum-branch-candidate.md`

Output of AN-22:

1. a scoped \(d=3\) continuum-branch theorem candidate statement is explicit,
2. extracted-limit \(\kappa\)-increment control is recorded at template level,
3. SD pass-through is tied to explicit B4 insertion-control hypotheses.

Implication:

1. bridge logic is now synchronized from AN-19 split through AN-22 theorem
   candidate level,
2. next closure lane is to discharge B1-B4 inside one concrete interacting
   model subclass.

## AN-23 Update (Concrete B1-B4 Closure Landed)

AN-23 now discharges B1-B4 in one explicit interacting compact-spin subclass:

- `research/workspace/notes/theorems/2026-02-09-claim1-d3-compact-spin-b1-b4-closure.md`

Output of AN-23:

1. B1 local moments close uniformly by compact support \(|\phi_x|\le R\),
2. B2 local tightness/precompactness closes from compact block marginals,
3. B3 denominator non-vanishing closes (\(Z>0\) in Euclidean \(c>0\) window),
4. B4 SD pass-through closes for boundary-vanishing local test class.

Implication:

1. AN-22 candidate is upgraded to scoped closure in this compact-spin Euclidean
   branch,
2. next gap is removal of hard cutoff \(R\to\infty\) while keeping B1-B4.

## AN-24 Update (Hard-Cutoff Lift Landed)

AN-24 now removes the AN-23 hard-spin cutoff in the same Euclidean branch:

- `research/workspace/notes/theorems/2026-02-09-claim1-d3-cutoff-lift-closure.md`

Output of AN-24:

1. finite-volume cutoff removal \(R\to\infty\) is proved for local renormalized
   compact-support observables/tests,
2. B1-B4 are preserved in that lifted channel (renormalized moments, tightness,
   \(Z>0\), SD pass-through),
3. AN-23 scoped closure now holds without hard cutoff in this same branch.

Implication:

1. next gap is no longer hard-cutoff removal,
2. next bridge lift is extension from compact-support local classes to wider
   local classes and then oscillatory/de-regularized branch transfer.

## Why \(d=3\) Here

\(d=3\) is the intended intermediate rung:

1. richer than AP ultralocal closure,
2. less boundary-critical than \(d=4\),
3. aligned with the dimension ladder in the roadmap.

## Reproducibility Hook

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_bridge_toy_coupling_scan.py
python3.12 research/workspace/simulations/claim1_d3_finite_volume_centered_moment_bound_check.py
python3.12 research/workspace/simulations/claim1_d3_renormalized_moment_channel_check.py
python3.12 research/workspace/simulations/claim1_d3_an22_continuum_branch_proxy_check.py
python3.12 research/workspace/simulations/claim1_d3_an23_compact_spin_closure_check.py
python3.12 research/workspace/simulations/claim1_d3_an24_cutoff_lift_check.py
```

The first script gives a nearest-neighbor toy weak-coupling scan.
The second script checks AN-20 finite-volume centered/moment inequalities.
The third script checks AN-21 renormalized moment bounds across \(a\).
The fourth script gives AN-22 continuum-branch proxy diagnostics.
The fifth script checks AN-23 compact-spin B1-B4 closure diagnostics.
The sixth script checks AN-24 hard-cutoff lift diagnostics across \(R\).
