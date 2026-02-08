# Claim 8 Phase Y: Rotating-Class Parameter Map (Myers-Perry Dimension Split)

Date: 2026-02-09  
Primary rotating references:

1. J. P. A. Novo, *No-bound theorem for Myers-Perry null and timelike geodesics*, Phys. Rev. D **111**, 064060 (2025), DOI: `10.1103/PhysRevD.111.064060`  
   URL: `https://journals.aps.org/prd/abstract/10.1103/PhysRevD.111.064060`
2. T. Igata, *Stable bound orbits in six-dimensional Myers-Perry black holes*, Phys. Rev. D **92**, 024002 (2015), DOI: `10.1103/PhysRevD.92.024002`  
   URL: `https://journals.aps.org/prd/abstract/10.1103/PhysRevD.92.024002?ft=1`

## Goal

Advance Claim 8 from a broad heuristic statement to a dimension/model-resolved rotating map.

## Baseline (Already Closed)

For static Tangherlini class (higher-dimensional Schwarzschild), the no-stable-circular result is already theoremized in this workspace.

## Proposition 1 (5D Rotating Myers-Perry: No-Bound Closure)

For 5D Myers-Perry black holes (all spin configurations with regular event horizon), the 2025 no-bound theorem establishes:

1. no radially bound timelike geodesics outside the event horizon,
2. no radially bound null geodesics outside the event horizon.

Hence the rotating 5D MP class inherits a strict no-bound geodesic closure. In particular, no stable circular bound timelike/null orbit can exist outside the horizon.

## Proposition 2 (6D Singly-Spinning Myers-Perry: Stable-Bound Existence at High Spin)

For 6D singly-spinning Myers-Perry black holes, Igata (2015) proves existence of stable bound orbits (massive and massless) for spin parameter above a critical value, with stable branches on the rotational axis.

Hence rotating higher-D behavior is not universally “no stable orbits”.

## Corollary (Claim 8 Refinement)

Claim 8 should be interpreted as a model-class map, not a single universal sentence:

1. Static Tangherlini (\(D>5\)): no stable circular timelike orbits (already closed).
2. Rotating MP in \(D=5\): no radially bound timelike/null geodesics (closed by 2025 theorem).
3. Rotating singly-spinning MP in \(D=6\): stable bound orbits can exist above a critical spin.

So the right global statement is:

- `no-stable` is robust in several key classes (static \(D>5\), rotating \(D=5\)),
- but rotating \(D\ge6\) can admit stable-bound sectors in specific parameter regimes.

## Status Impact

This substantially narrows the rotating-class uncertainty in Claim 8, while preserving a remaining open frontier:

full parameterized theorem closure across all Myers-Perry dimensions/spin sectors and other rotating families.

## Reproducibility

Run:

```bash
python3.12 research/workspace/simulations/claim8_rotating_parameter_map_table.py
```

The script prints the dimension/model split table used in this note.
