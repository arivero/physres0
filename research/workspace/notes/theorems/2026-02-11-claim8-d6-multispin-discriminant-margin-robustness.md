# Claim 8 Phase AD: Discriminant-Margin Robustness under Surrogate-to-Model Error

Date: 2026-02-11 (US)
Depends on:
- `research/workspace/notes/theorems/2026-02-11-claim8-d6-multispin-regime-partition-tightening.md`

## Goal

Transfer AC's discriminant partition into a perturbation-stable classification rule
that remains valid under bounded surrogate-to-physical model error.

## Setup

From AC, the surrogate classification is controlled by
\[
\Delta := 9M^2 - 16L^2\Gamma,
\qquad \Gamma\ge0,
\]
with sign classes:

1. `\Delta<0`: no-circular,
2. `\Delta=0`: marginal boundary,
3. `\Delta>0`: circular-candidate branch.

Assume only an estimated discriminant \(\widehat\Delta\), plus deterministic error
radius \(\mathcal E\ge0\) such that
\[
|\Delta-\widehat\Delta|\le \mathcal E.
\]

Define robust classes:

1. robust no-circular: \(\widehat\Delta < -\mathcal E\),
2. robust circular-candidate: \(\widehat\Delta > \mathcal E\),
3. uncertainty band: \(|\widehat\Delta|\le\mathcal E\).

## Theorem 1 (Sign-Certified Transfer)

Under \(|\Delta-\widehat\Delta|\le\mathcal E\):

1. \(\widehat\Delta < -\mathcal E \Rightarrow \Delta<0\) (certified no-circular),
2. \(\widehat\Delta > \mathcal E \Rightarrow \Delta>0\) (certified circular-candidate),
3. possible sign ambiguity occurs only inside \(|\widehat\Delta|\le\mathcal E\).

### Proof

From triangle inequality:
\[
\Delta \le \widehat\Delta + |\Delta-\widehat\Delta| < -\mathcal E + \mathcal E = 0,
\]
for case (1), and similarly
\[
\Delta \ge \widehat\Delta - |\Delta-\widehat\Delta| > \mathcal E-\mathcal E=0,
\]
for case (2). Case (3) is the complement where sign cannot be certified from
this bound alone. \(\square\)

## Corollary (Margin-Priority Map)

Define normalized robustness margin
\[
\mu := \frac{|\widehat\Delta|}{\mathcal E+\epsilon_0},\qquad \epsilon_0>0\text{ tiny}.
\]
Large-\(\mu\) points are classification-stable under surrogate/model mismatch;
small-\(\mu\) points define the only region requiring full Myers-Perry-resolution effort.
This creates a deterministic triage map for the unresolved Claim 8 sector.

## Validation Contract

### Assumptions

1. AC discriminant variable and sign classes,
2. explicit deterministic error envelope \(\mathcal E\) (from model mismatch budget),
3. fixed positive parameters `M,L` and `\Gamma>=0`.

### Units and dimensions check

1. `\Delta`, `\widehat\Delta`, and `\mathcal E` carry identical dimensions,
2. `\mu` is dimensionless.

### Symmetry/conservation checks

1. classification depends only on scalar invariants (`M,L,\Gamma`),
2. no coordinate-gauge structure is introduced.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim8_d6_multispin_margin_robustness_check.py
```

The script verifies that robust classes are sign-correct against true `\Delta` on a
deterministic grid and reports uncertainty-band contraction metrics.

### Confidence statement

AD does not complete full Myers-Perry geodesic closure; it provides a provably
safe transfer filter that contracts uncertainty to a bounded margin band.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic `(a1,a2)` scan and explicit error model,
3. date anchor: 2026-02-11 (US).
