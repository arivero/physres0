#!/usr/bin/env python3.12
"""Numerical check for tangent-groupoid/tau/Schwinger-Dyson dependency sheet.

Run:
  python3.12 research/workspace/simulations/claim1_groupoid_tau_sd_dependency_check.py
"""

from __future__ import annotations

import cmath
import numpy as np


def S(x: np.ndarray) -> np.ndarray:
    return 0.5 * x**2 + 0.1 * x**4


def dS(x: np.ndarray) -> np.ndarray:
    return x + 0.4 * x**3


def psi(x: np.ndarray) -> np.ndarray:
    return x


def dpsi(x: np.ndarray) -> np.ndarray:
    return np.ones_like(x)


def trap(y: np.ndarray, x: np.ndarray) -> complex:
    t = getattr(np, "trapezoid", None)
    if t is None:
        t = np.trapz
    return t(y, x)


def tau_mu(kappa: float, eta: float, h: float, mu: float) -> tuple[float, float, float]:
    return (mu * kappa, eta / mu, mu * h)


def c_param(kappa: float, eta: float, h: float) -> complex:
    return (eta - 1j / h) * kappa


def sd_residual(c: complex, x: np.ndarray) -> complex:
    w = np.exp(-c * S(x))
    lhs = trap(dpsi(x) * w, x)
    rhs = c * trap(psi(x) * dS(x) * w, x)
    return lhs - rhs


def main() -> None:
    kappa = 1.7
    eta = 0.9
    h = 0.8
    mu = 2.3
    kp, etap, hp = tau_mu(kappa, eta, h, mu)

    c0 = c_param(kappa, eta, h)
    c1 = c_param(kp, etap, hp)

    print("Claim 1 groupoid/tau/SD dependency check")
    print()
    print(f"original params   : kappa={kappa}, eta={eta}, h={h}")
    print(f"tau_mu params     : kappa'={kp}, eta'={etap}, h'={hp}")
    print(f"c(original)       : {c0}")
    print(f"c(tau_mu)         : {c1}")
    print(f"|c-c'|            : {abs(c0-c1):.6e}")
    print()

    x = np.linspace(-7.0, 7.0, 12001)
    r0 = sd_residual(c0, x)
    r1 = sd_residual(c1, x)

    print("Schwinger-Dyson residuals (finite-dimensional test action):")
    print(f"  residual original : {r0.real:+.3e} + {r0.imag:+.3e}i")
    print(f"  residual tau_mu   : {r1.real:+.3e} + {r1.imag:+.3e}i")
    print(f"  |residual diff|   : {abs(r0-r1):.6e}")
    print()
    print("Interpretation: tau_mu preserves c, and SD identity residual is unchanged.")


if __name__ == "__main__":
    main()
