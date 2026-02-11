# Claim 8 Phase AE: Exterior-Branch Robustness with Horizon-Radius Uncertainty

Date: 2026-02-11 (US)
Depends on:
- `research/workspace/notes/theorems/2026-02-11-claim8-d6-multispin-regime-partition-tightening.md`
- `research/workspace/notes/theorems/2026-02-11-claim8-d6-multispin-discriminant-margin-robustness.md`

## Goal

Refine Claim 8 transfer control by adding a conservative exterior-orbit filter that
combines AC root classification with AD uncertainty margins and uncertain horizon radius.

## Setup

Use the AC surrogate roots for `Delta>0`:
\[
r_\pm = \frac{3M \pm \sqrt{\Delta}}{2L^2},
\qquad
\Delta = 9M^2 - 16L^2\Gamma.
\]

AD provides estimated discriminant `\widehat\Delta` with error radius `E_\Delta`:
\[
|\Delta-\widehat\Delta|\le E_\Delta.
\]

Assume estimated horizon radius `\widehat r_h` with uncertainty `E_h`:
\[
|r_h-\widehat r_h|\le E_h.
\]

Define conservative upper bound on discriminant in the positive branch:
\[
\Delta_{\max}:=\widehat\Delta + E_\Delta.
\]
For `\widehat\Delta>E_\Delta` (hence `\Delta>0`), define conservative inner-root lower bound
\[
r_-^{\mathrm{lb}}
:=
\frac{3M-\sqrt{\Delta_{\max}}}{2L^2}.
\]

## Theorem (Certified Exterior Stable-Root Filter)

If
\[
\widehat\Delta > E_\Delta
\quad\text{and}\quad
r_-^{\mathrm{lb}} > \widehat r_h + E_h,
\]
then the true system satisfies all of:

1. `\Delta>0` (two-root circular-candidate branch exists),
2. the inner candidate root is strictly exterior:
   \[
   r_- > r_h,
   \]
3. the AC surrogate stability sign at the inner root remains the stable branch marker.

### Proof

From AD sign-certification, `\widehat\Delta>E_\Delta` implies `\Delta>0`.
Since `\Delta\le\Delta_{\max}`, we have
\[
\sqrt{\Delta}\le\sqrt{\Delta_{\max}},
\]
thus
\[
r_- = \frac{3M-\sqrt\Delta}{2L^2}
\ge
\frac{3M-\sqrt{\Delta_{\max}}}{2L^2}
=
 r_-^{\mathrm{lb}}.
\]
By horizon uncertainty, `r_h <= \widehat r_h + E_h`. Therefore
\[
r_- \ge r_-^{\mathrm{lb}} > \widehat r_h + E_h \ge r_h,
\]
so the root is certified exterior. \(\square\)

## Corollary (Transfer Triage)

AE produces a strict subset of AD-certified circular-candidate points where an
inner stable candidate is guaranteed outside the uncertain horizon band. This
subset is a high-priority target for fuller Myers-Perry verification.

## Validation Contract

### Assumptions

1. AC root formulas and stability signatures,
2. AD discriminant error envelope,
3. deterministic horizon-radius uncertainty envelope.

### Units and dimensions check

1. `Delta`, `E_Delta` have matching dimensions,
2. all radii (`r_\pm`, `r_h`, `\widehat r_h`, `E_h`) have length units.

### Symmetry/conservation checks

1. classification depends only on scalar invariant channels,
2. no coordinate-gauge dependence introduced.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim8_d6_outer_branch_horizon_robustness_check.py
```

The script verifies zero false-positive exterior certificates against true
surrogate roots and true horizon model on a deterministic grid.

### Confidence statement

AE is a conservative transfer filter, not full global closure. It narrows the
physically relevant unresolved region to points with certified exterior stable
candidates under uncertainty.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic `(a1,a2)` scan and uncertainty profiles,
3. date anchor: 2026-02-11 (US).
