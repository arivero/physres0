# Claim 8 Phase AA: \(D\ge 6\) Multi-Spin Myers-Perry Regime Map

Date: 2026-02-09  
Primary external references:

1. J. P. A. Novo, *No-bound theorem for Myers-Perry null and timelike geodesics*, Phys. Rev. D **111**, 064060 (2025), DOI: `10.1103/PhysRevD.111.064060`
2. T. Igata, *Stable bound orbits in six-dimensional Myers-Perry black holes*, Phys. Rev. D **92**, 024002 (2015), DOI: `10.1103/PhysRevD.92.024002`

Internal reference:

- `research/workspace/notes/theorems/2026-02-08-claim8-beyond-tangherlini-asymptotic.md`

## Goal

Refine Claim 8 rotating closure by explicitly separating proven and unresolved sectors for \(D\ge 6\) Myers-Perry families.

## Parameterization

Let \(D\) be spacetime dimension and \(s\) the number of nonzero independent spin parameters (spin rank).

## Proposition 1 (Asymptotic Exclusion for \(D>5\))

Assume the far-zone radial effective potential has the asymptotic structure
\[
U_{\mathrm{eff}}(r)=\frac{L^2}{2r^2}-\frac{A}{r^p}+o(r^{-p}),
\qquad
p=D-3,\quad A>0.
\]
At an asymptotic circular point \(r_c\), the leading stability curvature is
\[
U_{\mathrm{eff}}''(r_c)\sim p(2-p)\,A\,r_c^{-p-2}.
\]
Hence for \(D>5\) (\(p>2\)), sufficiently large-radius circular orbits are unstable.

This is the shared far-zone obstruction used in the internal asymptotic Claim 8 extension.

## Proposition 2 (5D Rotating Baseline)

For \(D=5\), Novo (2025) proves no radially bound timelike/null geodesics outside the horizon for all regular spin configurations.

## Proposition 3 (6D Singly-Spinning Counter-Sector)

For \(D=6\), \(s=1\), Igata (2015) proves stable bound timelike and null branches exist above a critical spin.

## Corollary (Regime Map for \(D\ge 6\))

1. \(D=6,\;s=1\): stable-bound branch exists (high-spin regime), but far-zone stability is excluded by Proposition 1.
2. \(D=6,\;s=2\): far-zone stable circulars excluded; additionally, a scoped high-spin cone with no circular candidates is excluded by discriminant no-go (`research/workspace/notes/theorems/2026-02-11-claim8-d6-multispin-highspin-discriminant-nogo.md`), and the remaining surrogate lane is now explicitly partitioned into marginal / boundary-single-root / two-root (inner-stable, outer-unstable) sectors in `research/workspace/notes/theorems/2026-02-11-claim8-d6-multispin-regime-partition-tightening.md`.
3. \(D\ge 7,\;s\ge 1\): far-zone stable circulars excluded; full global theorem closure remains open.

Thus, in unresolved \(D\ge 6\) multi-spin sectors, any stable-bound branch (if it exists) must be confined to compact/intermediate radial regions, not asymptotic radii.

## Claim 8 Status Impact

This note sharpens the rotating gap from a generic uncertainty to a constrained regime map:

- proven no-bound sector (\(D=5\), all spins),
- proven stable-bound sector (\(D=6,\;s=1\), high spin),
- unresolved sectors explicitly isolated with a structured \(D=6,s=2\) surrogate partition and excluded high-spin cone (\(D\ge 6\) multi-spin global closure still open).

## Reproducibility

Run:

```bash
python3.12 research/workspace/simulations/claim8_multispin_dge6_regime_map_table.py
```

The script prints the \(D,s\)-map and the far-zone curvature sign coefficient \(p(2-p)\).
