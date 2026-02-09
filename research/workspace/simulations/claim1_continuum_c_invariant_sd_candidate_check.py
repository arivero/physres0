#!/usr/bin/env python3.12
"""Continuum candidate check: large-N stabilization + c-invariant SD consistency.

Run:
  python3.12 research/workspace/simulations/claim1_continuum_c_invariant_sd_candidate_check.py
"""

from __future__ import annotations

import numpy as np


def P(u: np.ndarray) -> np.ndarray:
    return 0.25 * u**4 + 0.5 * u**2


def dP(u: np.ndarray) -> np.ndarray:
    return u**3 + u


def F(u: np.ndarray) -> np.ndarray:
    return u**2 / (1.0 + u**2)


def lam(j: int) -> float:
    return 1.0 + 0.3 * j


def acoef(j: int) -> float:
    return 0.5 / (j**2)


def trap(y: np.ndarray, x: np.ndarray) -> complex:
    t = getattr(np, "trapezoid", None)
    if t is None:
        t = np.trapz
    return t(y, x)


def phi_N(u: np.ndarray, N: int, m: int = 1) -> np.ndarray:
    idx = range(m + 1, N + 1)
    if N <= m:
        return np.ones_like(u, dtype=np.float64)
    logp = np.zeros_like(u, dtype=np.float64)
    for j in idx:
        logp += np.log(lam(j) + 2.0 * acoef(j) * u * u)
    return np.exp(-0.5 * logp)


def sum_term_N(u: np.ndarray, N: int, m: int = 1) -> np.ndarray:
    idx = range(m + 1, N + 1)
    s = np.zeros_like(u, dtype=np.float64)
    for j in idx:
        s += (2.0 * acoef(j) * u * u) / (lam(j) + 2.0 * acoef(j) * u * u)
    return s


def I_N(c: complex, N: int, fvals: np.ndarray, grid: np.ndarray) -> complex:
    w = np.exp(-c * P(grid)) * phi_N(grid, N)
    return trap(w * fvals, grid)


def omega_N(c: complex, N: int, grid: np.ndarray) -> complex:
    num = I_N(c, N, F(grid), grid)
    den = I_N(c, N, np.ones_like(grid), grid)
    return num / den


def sd_residual_N(c: complex, N: int, grid: np.ndarray) -> complex:
    # psi(u)=u, dpsi=1.
    lhs = I_N(c, N, np.ones_like(grid), grid)
    rhs_integrand = c * grid * dP(grid) + sum_term_N(grid, N)
    rhs = I_N(c, N, rhs_integrand, grid)
    return lhs - rhs


def tau_mu(kappa: float, eta: float, h: float, mu: float) -> tuple[float, float, float]:
    return (mu * kappa, eta / mu, mu * h)


def c_param(kappa: float, eta: float, h: float) -> complex:
    return (eta - 1j / h) * kappa


def main() -> None:
    grid = np.linspace(-6.0, 6.0, 8001)
    Ns = [8, 12, 16, 20, 24, 28]

    kappa = 1.3
    eta = 0.7
    h = 0.9
    mu = 1.8
    kp, etap, hp = tau_mu(kappa, eta, h, mu)

    c0 = c_param(kappa, eta, h)
    c1 = c_param(kp, etap, hp)

    print("Claim 1 continuum c-invariance candidate check")
    print(f"c(original)={c0}")
    print(f"c(tau_mu)  ={c1}")
    print(f"|c-c'|={abs(c0-c1):.6e}")
    print()

    vals0 = []
    vals1 = []
    print("Large-N omega_N(F) with c-invariant parameterization:")
    for N in Ns:
        w0 = omega_N(c0, N, grid)
        w1 = omega_N(c1, N, grid)
        vals0.append(w0)
        vals1.append(w1)
        print(
            f"N={N:>2d}  omega(c)={w0.real:.10f}+{w0.imag:.10f}i"
            f"   omega(tau)={w1.real:.10f}+{w1.imag:.10f}i   diff={abs(w0-w1):.3e}"
        )
    print()

    print("Successive large-N differences:")
    for i in range(len(Ns) - 1):
        d = abs(vals0[i + 1] - vals0[i])
        print(f"  N={Ns[i]:>2d}->{Ns[i+1]:>2d}: {d:.6e}")
    print()

    print("Schwinger-Dyson residuals across N:")
    for N in Ns:
        r = sd_residual_N(c0, N, grid)
        print(f"  N={N:>2d}: residual={r.real:+.3e}+{r.imag:+.3e}i")


if __name__ == "__main__":
    main()
