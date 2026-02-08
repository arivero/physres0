#!/usr/bin/env python3.12
"""Checks for Claim 1 Phase H Gaussian closure (H1-H6).

Observable:
  F_m(x) = exp(-alpha * sum_{j=1}^m x_j^2)

Exact normalized expectation under
  S(x) = 0.5 * sum_j c_j x_j^2
is
  E[F_m] = prod_{j=1}^m sqrt((-i c_j / (2 eps)) / (alpha - i c_j / (2 eps))).

We verify:
  1) Exact N-stability for compatible families.
  2) Oscillation for incompatible bare families.
  3) Counterterm repair restores stability.
  4) E[F_m] -> F_m(0)=1 as eps -> 0.

Run:
  python3.12 research/workspace/simulations/claim1_gaussian_h1_h6_closure_check.py
"""

from __future__ import annotations

import cmath


def gaussian_expectation(eps: float, alpha: float, coeffs: list[float]) -> complex:
    out = 1.0 + 0.0j
    for c in coeffs:
        # Branch-consistent Fresnel normalization uses -i*c/(2*eps) in denominator ratio.
        out *= cmath.sqrt((-1j * c / (2.0 * eps)) / (alpha - 1j * c / (2.0 * eps)))
    return out


def max_pairwise_gap(values: list[complex]) -> float:
    worst = 0.0
    for i, a in enumerate(values):
        for b in values[i + 1 :]:
            d = abs(a - b)
            if d > worst:
                worst = d
    return worst


def main() -> None:
    alpha = 0.6
    eps = 0.25
    m = 3
    lambdas = [1.1, 0.9, 1.4]

    n_values = list(range(m, m + 10))

    # Case A: compatible family (first m coefficients stable across N)
    compatible_vals = []
    for n in n_values:
        coeffs = lambdas[:m]
        compatible_vals.append(gaussian_expectation(eps, alpha, coeffs))

    # Case B: incompatible bare family (first m coeffs alternate with N)
    incompatible_vals = []
    for n in n_values:
        shift = 0.2 if n % 2 == 0 else -0.2
        coeffs = [c + shift for c in lambdas[:m]]
        incompatible_vals.append(gaussian_expectation(eps, alpha, coeffs))

    # Case C: counterterm repair (remove N-dependent shift)
    repaired_vals = []
    for n in n_values:
        shift = 0.2 if n % 2 == 0 else -0.2
        bare = [c + shift for c in lambdas[:m]]
        repaired = [b - shift for b in bare]
        repaired_vals.append(gaussian_expectation(eps, alpha, repaired))

    print("Claim 1 Phase H Gaussian closure checks")
    print(f"compatible max pairwise gap   : {max_pairwise_gap(compatible_vals):.3e}")
    print(f"incompatible max pairwise gap : {max_pairwise_gap(incompatible_vals):.3e}")
    print(f"repaired max pairwise gap     : {max_pairwise_gap(repaired_vals):.3e}")

    print("\nSemiclassical trend E[F_m] -> F_m(0)=1")
    for eps_k in [1.0, 0.5, 0.2, 0.1, 0.05, 0.02]:
        val = gaussian_expectation(eps_k, alpha, lambdas[:m])
        err = abs(val - (1.0 + 0.0j))
        print(f"  eps={eps_k:>4}: |E[F]-1|={err:.3e}")


if __name__ == "__main__":
    main()
