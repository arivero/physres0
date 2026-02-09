# Claim 1 Phase AR (AN-3): Half-Density Kinematic vs Dynamical Split

Date: 2026-02-09 (CET)  
Depends on:

- `research/workspace/notes/theorems/2026-02-08-claim1-groupoid-halfdensity-theorem-pack.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-d4-lift-obstruction-sheet.md`

## Goal

Separate, in theorem form, what half-density formalism guarantees kinematically
from what still requires dynamical/renormalization existence control.

## Definitions

1. **Kinematic statement**:
   algebra/composition/invariance property that is valid at fixed regulator scale
   and does not require continuum limit existence.
2. **Dynamical statement**:
   existence/uniqueness/continuum claim that requires uniform bounds,
   non-vanishing normalization, and limit control.

## Theorem 1 (Kinematic Half-Density Closure)

On a smooth manifold pair groupoid, compactly supported smooth half-density kernels form a coordinate-free involutive convolution algebra:

1. convolution is globally well-defined,
2. associativity holds,
3. involution compatibility holds.

These results are independent of any choice of action functional or renormalization flow.

### Proof

Directly inherited from the groupoid half-density theorem pack:
Jacobian cancellation is geometric, and associativity/involution follow from
Fubini plus compact support. No continuum limit is used. \(\square\)

## Proposition 2 (Amplitude-to-Density Is Kinematic)

At fixed regulator \(\varepsilon>0\), an amplitude \(A_\varepsilon\) always induces a nonnegative density object \(|A_\varepsilon|^2\).  
This algebraic squaring step is kinematic and does not imply convergence as \(\varepsilon\to0\).

### Proof

Pointwise identity \(|z|^2=z\bar z\ge0\) for complex numbers/functions.  
No limiting argument appears. \(\square\)

## Theorem 3 (Dynamical Gate for Continuum Claims)

Let \(\{\omega_\rho\}_{\rho\downarrow0}\) be normalized oscillatory states
(\(\rho\) may represent \(a,\eta,\varepsilon,\) or a multi-parameter net).

Continuum conclusions (existence, SD pass-through, \(c\)-invariant limit state)
require all of:

1. uniform integrability/tightness on the observable class,
2. non-vanishing normalization denominators on the working parameter domain,
3. Cauchy/compactness control of \(\omega_\rho(F)\),
4. closure bounds for derivative insertions when passing SD identities to the limit.

Without these, half-density kinematics alone is insufficient.

### Proof

Each target conclusion needs a corresponding analytic passage to the limit:
ratios require denominator control, limit existence needs tightness/Cauchy control,
and SD pass-through needs derivative-insertion bounds.  
None of these follows from algebraic half-density composition by itself. \(\square\)

## Corollary (Programmatic Rule)

When reading Claim 1 status:

1. half-density/groupoid composition results certify kinematic consistency,
2. they do **not** by themselves certify continuum existence,
3. dimension-indexed renormalization analysis remains mandatory for field-level closure.

## Counterexample Pattern (Why the Split Is Necessary)

One can have:

1. perfectly valid fixed-scale amplitude algebra,
2. but non-convergent undamped oscillatory normalized sequences as regulator is removed.

Hence kinematic validity does not imply dynamical convergence.

## Reproducibility

Run:

```bash
python3.12 research/workspace/simulations/claim1_halfdensity_kinematic_dynamic_split_check.py
```

The script reports:

1. exact discrete associativity residuals near machine zero (kinematic success),
2. a toy undamped oscillatory normalized sequence that is not Cauchy (dynamical failure without extra hypotheses).
