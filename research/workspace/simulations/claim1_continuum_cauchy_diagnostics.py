#!/usr/bin/env python3.12
"""Continuum-skeleton diagnostics for Claim 1 (Phase G).

This script tracks three toy diagnostics tied to the continuum template:
  1) Cauchy tail defect for cylinder expectations.
  2) Nondegeneracy proxy via |c_N| in 1D Gaussian blocks.
  3) Counterterm drift |delta c_N|.

Toy model:
  S_N(x) = 0.5 * c_N * x^2
  omega_N[x^2] = i * eps / c_N

Cases:
  - compatible: c_N = 1
  - incompatible: c_N = 1 + 0.5*(-1)^N
  - renormalized: start from incompatible and add counterterm
      delta c_N = -0.5*(-1)^N  => c_N^ren = 1

Run:
  python3.12 research/workspace/simulations/claim1_continuum_cauchy_diagnostics.py
"""

from __future__ import annotations


def expect_x2(eps: float, c_n: float) -> complex:
    return 1j * eps / c_n


def tail_cauchy_defect(values: list[complex], start_index: int) -> float:
    tail = values[start_index:]
    worst = 0.0
    for i, a in enumerate(tail):
        for b in tail[i + 1 :]:
            d = abs(a - b)
            if d > worst:
                worst = d
    return worst


def counterterm_drift(coeffs: list[float]) -> float:
    return max(abs(coeffs[k + 1] - coeffs[k]) for k in range(len(coeffs) - 1))


def summarize_case(name: str, eps: float, coeffs: list[float]) -> None:
    vals = [expect_x2(eps, c) for c in coeffs]
    defect = tail_cauchy_defect(vals, start_index=max(0, len(vals) // 2))
    min_abs_c = min(abs(c) for c in coeffs)
    drift = counterterm_drift(coeffs)
    print(f"{name}")
    print(f"  tail Cauchy defect : {defect:.3e}")
    print(f"  min |c_N|          : {min_abs_c:.3e}")
    print(f"  max |delta c_N|    : {drift:.3e}")


def main() -> None:
    eps = 0.2
    nmax = 24

    compatible = [1.0 for _ in range(1, nmax + 1)]
    incompatible = [1.0 + 0.5 * ((-1.0) ** n) for n in range(1, nmax + 1)]
    renormalized = [c + (-0.5 * ((-1.0) ** n)) for n, c in enumerate(incompatible, start=1)]

    print("Claim 1 continuum diagnostics (toy Gaussian block)")
    summarize_case("Case A: compatible family", eps, compatible)
    summarize_case("Case B: incompatible family", eps, incompatible)
    summarize_case("Case C: counterterm-renormalized family", eps, renormalized)


if __name__ == "__main__":
    main()
