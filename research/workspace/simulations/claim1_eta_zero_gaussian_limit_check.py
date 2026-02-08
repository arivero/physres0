#!/usr/bin/env python3.12
"""Check eta->0+ convergence for the Gaussian regularized Claim 1 sector.

For F(x)=exp(-sum_j alpha_j x_j^2),
  E_eta[F] = prod_j sqrt((lambda_j*(eta - i/eps)) /
                         (lambda_j*(eta - i/eps) + alpha_j)).

Run:
  python3.12 research/workspace/simulations/claim1_eta_zero_gaussian_limit_check.py
"""

from __future__ import annotations

import cmath


def expectation_eta(eps: float, eta: float, lambdas: list[float], alphas: list[float]) -> complex:
    out = 1.0 + 0.0j
    for lam, alpha in zip(lambdas, alphas):
        num = lam * (eta - 1j / eps)
        den = lam * (eta - 1j / eps) + alpha
        out *= cmath.sqrt(num / den)
    return out


def main() -> None:
    eps = 0.22
    lambdas = [1.0, 1.35, 0.85]
    alphas = [0.6, 0.2, 0.5]

    target = expectation_eta(eps=eps, eta=0.0, lambdas=lambdas, alphas=alphas)
    print("Claim 1 Phase J eta->0 Gaussian closure check")
    print(f"target at eta=0: {target.real:+.10f}{target.imag:+.10f}i")
    for eta in [0.50, 0.25, 0.10, 0.05, 0.02, 0.01, 0.005]:
        val = expectation_eta(eps=eps, eta=eta, lambdas=lambdas, alphas=alphas)
        err = abs(val - target)
        print(
            f"  eta={eta:>5}: E_eta={val.real:+.10f}{val.imag:+.10f}i, "
            f"|E_eta-E_0|={err:.3e}"
        )


if __name__ == "__main__":
    main()
