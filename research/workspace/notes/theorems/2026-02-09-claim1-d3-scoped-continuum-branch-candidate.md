# Claim 1 Phase BN (AN-22): \(d=3\) Scoped Continuum-Branch Candidate

Date: 2026-02-09 (CET)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim1-d3-intermediate-bridge-candidate.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-d3-renormalized-moment-channel-proposition.md`
- `research/workspace/proofs/Claim1lean/FiniteExponentialIncrementBound.lean`

## Goal

Integrate AN-21's renormalized B5b input with B1-B4 into a scoped \(d=3\)
continuum-branch theorem candidate for local observables.

## Setup

For finite lattice spacing \(a>0\), periodic box size \(L\), coupling
\(\kappa\in[0,\kappa_*]\), and Euclidean \(c\in[c_0,c_1]\subset(0,\infty)\), let
\(\omega_{c,a,L}^{(\kappa)}\) be the finite-volume state from the \(d=3\) nearest
neighbor \(\phi^4\) action used in AN-20/AN-21.

For each local block \(B\), define:
\[
G_B(\phi)=\sum_{\langle x,y\rangle\in E_B}(\phi_x-\phi_y)^2,\qquad
G_{B,a}^{\mathrm{ren}}:=a^3G_B.
\]

## Inputs (B1-B5 in AN-19 Split Form)

Assume the following on a fixed local observable class \(\mathcal A_{\mathrm{loc}}\):

1. **B1 local bounds:** uniform finite-volume local moment controls compatible
   with local tightness.
2. **B2 tightness/precompactness:** local cylinder marginals are tight uniformly
   in \((a,L,\kappa)\), so extraction along \(a\to0\), \(L\to\infty\) is possible.
3. **B3 denominator non-vanishing:** normalized states are well-defined and
   uniformly non-singular on \(c\in[c_0,c_1]\).
4. **B4 SD insertion control:** Schwinger-Dyson insertion terms for local tests
   are uniformly controlled and pass to the extracted limit.
5. **B5 (AN-19 split):**
   - B5a is supplied by Lean-side regularity collapse (AN-18 style),
   - B5b is supplied by AN-21:
     \[
     |F-\omega(F)|\le K_F,\qquad
     \omega_{c,a,L}^{(\kappa)}(G_{B,a}^{\mathrm{ren}})\le M_B^{\mathrm{ren}}
     =\frac{4|E_B|}{c_0m_0^2},
     \]
     uniform in \(a,L,\kappa\).

## Theorem Candidate (Scoped \(d=3\) Continuum Branch)

Under B1-B5 above, for each fixed \(c\in[c_0,c_1]\) and \(\kappa\in[0,\kappa_*]\):

1. there exists an extracted continuum-branch state
   \(\omega_c^{(\kappa)}\) on \(\mathcal A_{\mathrm{loc}}\) obtained from a
   subnet \((a_n,L_n)\to(0,\infty)\),
2. for every bounded local \(F\in\mathcal A_{\mathrm{loc}}\),
   \[
   |\omega_c^{(\kappa)}(F)-\omega_c^{(0)}(F)|\le C_F\,\kappa
   \]
   with \(C_F\) controlled by the finite-volume B5 constants
   (\(K_F, M_B^{\mathrm{ren}}\)) through the AN-18/AN-22 increment template,
3. local SD identities pass to the extracted limit in the same scoped class.

## Proof Skeleton

1. AN-21 provides \(a\)-uniform renormalized B5b constants at finite volume.
2. B2 gives extraction of local limit points along \((a,L)\to(0,\infty)\).
3. Uniform finite-volume increment bounds (B5a+B5b) pass to the limit by
   limsup/liminf arguments, yielding the \(\kappa\)-increment inequality.
4. B3 prevents normalization singularities in the extracted channel.
5. B4 passes SD insertions to the same extracted limit.

This is the scoped template theorem. AN-23 and AN-24 now instantiate it in one
explicit interacting Euclidean subclass.

## Scope and Open Gap

Closed in this note:

1. dependency-level integration of AN-21 with the AN-19 bridge template,
2. explicit statement of the continuum-branch candidate and required inputs.

AN-23 update:

1. B1-B4 are now discharged in the compact-spin interacting Euclidean subclass
   in `research/workspace/notes/theorems/2026-02-09-claim1-d3-compact-spin-b1-b4-closure.md`,
   upgrading this AN-22 template from candidate to scoped closure in that branch.
2. the remaining lift gap is hard-cutoff removal \(R\to\infty\) with the same
   B1-B4 controls.

AN-24 update:

1. hard-cutoff removal \(R\to\infty\) is now discharged in the same subclass in
   `research/workspace/notes/theorems/2026-02-09-claim1-d3-cutoff-lift-closure.md`,
2. this AN-22 template is now realized as scoped closure in a lifted
   (no-hard-cutoff) Euclidean local-renormalized channel.

## Validation Contract

### Assumptions

1. finite-volume lattice model and observable class are explicit,
2. extraction topology and \(c\)-window are fixed.

### Units and dimensions check

1. renormalized insertion uses \(G_{B,a}^{\mathrm{ren}}=a^3G_B\),
2. finite-volume constants are dimensionally explicit.

### Symmetry/conservation checks

1. periodic translation symmetry assumptions remain as in AN-20/AN-21,
2. SD pass-through is only claimed under explicit insertion-control hypotheses.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim1_d3_an22_continuum_branch_proxy_check.py
python3.12 research/workspace/simulations/claim1_d3_an24_cutoff_lift_check.py
```

The script provides finite-volume diagnostics for:

1. renormalized moment boundedness across \(a\),
2. small-\(\kappa\) increment scaling proxies for local observables,
3. coarse Cauchy-style drift checks across spacing refinements.
4. hard-cutoff lift stabilization and SD residual checks across \(R\).

### Confidence statement

The dependency integration is theorem-grade, and a concrete AN-23/AN-24
subclass realization is now closed in the stated Euclidean local-renormalized channel.

### Reproducibility metadata

1. Python: `python3.12`,
2. fixed seed and parameter grid printed by script,
3. date anchor: 2026-02-09 (US).
