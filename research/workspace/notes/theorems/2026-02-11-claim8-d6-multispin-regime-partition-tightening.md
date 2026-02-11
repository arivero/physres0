# Claim 8 Phase AC: \(D=6,\ s=2\) Surrogate Regime Partition Tightening

Date: 2026-02-11 (US)  
Depends on:

- `research/workspace/notes/theorems/2026-02-11-claim8-d6-multispin-highspin-discriminant-nogo.md`
- `research/workspace/notes/theorems/2026-02-09-claim8-multispin-dge6-regime-map.md`

## Goal

Tighten the \(D=6,\ s=2\) surrogate map beyond the AB no-circular cone by
partitioning the remaining region into explicit circular/stability classes.

## Scoped Model

Use the same reduced surrogate channel as AB:
\[
V_{\mathrm{eff}}(r)=\frac{L^2}{2r^2}-\frac{M}{r^3}+\frac{\Gamma}{r^4},
\qquad
\Gamma=a_1^2\ell_1^2+a_2^2\ell_2^2,\quad r>0.
\]

Stationary points satisfy:
\[
V_{\mathrm{eff}}'(r)=0
\iff
L^2r^2-3Mr+4\Gamma=0.
\]
Define discriminant:
\[
\Delta:=9M^2-16L^2\Gamma.
\]

## Theorem 1 (Existence Partition)

1. \(\Delta<0\): no real stationary radius (no circular candidate),
2. \(\Delta=0\): one double stationary radius
   \[
   r_*=\frac{3M}{2L^2},
   \]
3. \(\Delta>0\): two nonnegative stationary radii
   \[
   r_\pm=\frac{3M\pm\sqrt{\Delta}}{2L^2},\qquad 0\le r_-<r_+.
   \]
   More precisely, \(r_->0\) iff \(\Gamma>0\); at \(\Gamma=0\), \(r_-=0\) is a
   boundary root and only \(r_+\) is strictly positive.

### Proof

Direct quadratic classification of \(L^2r^2-3Mr+4\Gamma=0\). \(\square\)

## Theorem 2 (Stability Signature of Positive-Root Sectors)

At any stationary radius \(r\), one has
\[
V_{\mathrm{eff}}''(r)
=
\frac{3L^2}{r^4}-\frac{12M}{r^5}+\frac{20\Gamma}{r^6}
=
\frac{3M-2L^2r}{r^5}.
\]
Hence for \(\Delta>0\) and \(\Gamma>0\):
\[
V_{\mathrm{eff}}''(r_-)>0,\qquad V_{\mathrm{eff}}''(r_+)<0.
\]
So the inner branch is stable and the outer branch unstable in this surrogate
channel.

For the boundary case \((\Gamma=0,\Delta>0)\), only \(r_+=3M/L^2\) is positive
and it is unstable (\(V_{\mathrm{eff}}''(r_+)<0\)).

### Proof

Use the stationary relation \(L^2r^2-3Mr+4\Gamma=0\) to simplify \(V''\).
For \(r_\pm\), compute
\[
3M-2L^2r_\pm=\mp\sqrt{\Delta}.
\]
The sign statement then follows for the strictly positive roots in each case.
\(\square\)

## Corollary (Dimensionless Region Map)

Define
\[
\xi:=\frac{16L^2\Gamma}{9M^2}.
\]
Then the surrogate \(D=6,\ s=2\) sector partitions as:

1. \(\xi>1\): no-circular region (AB high-spin exclusion),
2. \(\xi=1\): marginal double-root boundary,
3. \(\xi=0\): boundary single-positive-root regime (\(r_-=0\), \(r_+\) unstable),
4. \(0<\xi<1\): two-positive-root regime with one stable (inner) and one
   unstable (outer) candidate branch.

This replaces a large previously "open" surrogate subset by explicit
subclassification, while full Myers-Perry global closure remains open.

## Validation Contract

### Assumptions

1. surrogate radial effective channel above,
2. \(M>0\), \(L>0\), \(\Gamma\ge0\).

### Units and dimensions check

1. discriminant ratio \(\xi\) is dimensionless,
2. \(V''\)-sign classification uses dimensionally consistent terms.

### Symmetry/conservation checks

1. spin dependence enters through invariant \(\Gamma=a_1^2\ell_1^2+a_2^2\ell_2^2\),
2. radial effective-energy structure preserved from AB lane.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim8_d6_multispin_regime_partition_check.py
```

The script verifies:

1. discriminant-to-root existence classification consistency,
2. stability-sign identities on two-root points,
3. deterministic fraction table for no-circular / marginal / two-root sectors,
4. strict contraction of "unclassified surrogate" region relative to AB framing.

### Confidence statement

AC is a scoped surrogate tightening step. It does not prove full global
Myers-Perry geodesic closure, but it materially contracts and structures the
remaining \(D=6,\ s=2\) surrogate map.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic grid specification in script output,
3. date anchor: 2026-02-11 (US).
