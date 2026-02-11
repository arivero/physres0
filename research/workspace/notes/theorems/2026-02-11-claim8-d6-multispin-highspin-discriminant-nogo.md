# Claim 8 Phase AB: \(D=6,\ s=2\) High-Spin Discriminant No-Go Sector

Date: 2026-02-11 (US)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim8-multispin-dge6-regime-map.md`
- `research/workspace/notes/theorems/2026-02-08-claim8-beyond-tangherlini-asymptotic.md`

## Goal

Contract one unresolved \(D\ge 6\) multispin sector by proving an explicit
parameter region with no circular timelike orbit candidates in a scoped
effective-potential surrogate for \(D=6,\ s=2\) Myers-Perry geodesic channels.

## Scoped Model and Assumptions

Work in a reduced radial surrogate:
\[
V_{\mathrm{eff}}(r)
=
\frac{L^2}{2r^2}
-\frac{M}{r^3}
+\frac{\Gamma}{r^4},
\qquad
\Gamma:=a_1^2\ell_1^2+a_2^2\ell_2^2,\quad r>0,
\]
with \(M>0,\ L>0\), and \(a_i,\ell_i\) the two-spin channel parameters.

Interpretation:

1. \(-M/r^3\): \(D=6\) attractive tail (\(D-3=3\)),
2. \(+\Gamma/r^4\): multispin centrifugal correction in the reduced channel.

This note is explicitly scoped to the surrogate lane; it is not a full global
Myers-Perry theorem.

## Theorem 1 (High-Spin No-Circular Discriminant Sector)

Circular points satisfy \(V_{\mathrm{eff}}'(r)=0\), equivalently
\[
L^2 r^2 - 3Mr + 4\Gamma = 0.
\]
If
\[
16L^2\Gamma>9M^2,
\]
then this quadratic has negative discriminant and no real root. Hence no
circular timelike orbit candidate exists in this channel.

### Proof

Differentiate:
\[
V_{\mathrm{eff}}'(r)
=
-\frac{L^2}{r^3}
+\frac{3M}{r^4}
-\frac{4\Gamma}{r^5}.
\]
Setting \(V_{\mathrm{eff}}'(r)=0\) and multiplying by \(r^5\) gives
\[
L^2 r^2 -3Mr +4\Gamma=0.
\]
Discriminant
\[
\Delta = 9M^2 - 16L^2\Gamma.
\]
If \(\Delta<0\), there is no real \(r\), thus no circular point. \(\square\)

## Corollary (Explicit Excluded Spin Cone)

Any parameter tuple satisfying
\[
a_1^2\ell_1^2+a_2^2\ell_2^2>\frac{9M^2}{16L^2}
\]
belongs to an explicitly excluded no-circular sector in this \(D=6,\ s=2\)
surrogate channel.

For \(\ell_1=\ell_2=\ell\):
\[
a_1^2+a_2^2>\frac{9M^2}{16L^2\ell^2}.
\]

This gives a concrete region removal from the unresolved \(D=6,\ s=2\)
parameter map.

## Claim 8 Status Impact

The unresolved \(D=6,\ s=2\) map is tightened by a proved exclusion boundary in
the high-spin cone of the scoped surrogate model:

1. excluded region: \(16L^2\Gamma>9M^2\) (no circular candidates),
2. remaining open region: \(16L^2\Gamma\le 9M^2\) (requires fuller MP analysis).

## Validation Contract

### Assumptions

1. \(D=6,\ s=2\) reduced radial surrogate above,
2. constants \(M,L,\Gamma\) are positive and finite.

### Units and dimensions check

1. \(V_{\mathrm{eff}}\) terms share consistent radial scaling dimensions,
2. discriminant inequality compares dimensionless combination \(16L^2\Gamma/M^2\).

### Symmetry/conservation checks

1. reduced channel preserves radial effective-energy structure,
2. spin dependence enters through invariant combination \(\Gamma=a_1^2\ell_1^2+a_2^2\ell_2^2\).

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim8_d6_multispin_highspin_discriminant_check.py
```

The script verifies:

1. discriminant-sign classification matches root existence exactly,
2. excluded high-spin cone occupies a strictly positive fraction of scanned
   parameter space,
3. circular-root/stability diagnostics for the remaining region.

### Confidence statement

AB is a scoped no-go contraction result, not a full global \(D=6,\ s=2\)
Myers-Perry closure. It removes a concrete high-spin sub-sector from the open
set and sharpens the next target for full closure.
Phase AC now adds a surrogate partition tightening of the remaining AB-open set
in `research/workspace/notes/theorems/2026-02-11-claim8-d6-multispin-regime-partition-tightening.md`.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic grid and parameters printed by script,
3. date anchor: 2026-02-11 (US).
