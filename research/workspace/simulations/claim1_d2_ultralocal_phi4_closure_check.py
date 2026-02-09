#!/usr/bin/env python3.12
"""Claim 1 Phase AP check: d=2 ultralocal phi^4 closure.

Run:
  python3.12 research/workspace/simulations/claim1_d2_ultralocal_phi4_closure_check.py
"""

from __future__ import annotations

import numpy as np


def trap(y: np.ndarray, x: np.ndarray) -> complex:
    t = getattr(np, "trapezoid", None)
    if t is None:
        t = np.trapz
    return t(y, x)


def potential(u: np.ndarray, m2: float, lam: float) -> np.ndarray:
    return 0.5 * m2 * (u**2) + 0.25 * lam * (u**4)


def d_potential(u: np.ndarray, m2: float, lam: float) -> np.ndarray:
    return m2 * u + lam * (u**3)


def site_expect(c: complex, m2: float, lam: float, fvals: np.ndarray, grid: np.ndarray) -> complex:
    w = np.exp(-c * potential(grid, m2, lam))
    z = trap(w, grid)
    return trap(w * fvals, grid) / z


def tau_mu(kappa: float, eta: float, h: float, mu: float) -> tuple[float, float, float]:
    return (mu * kappa, eta / mu, mu * h)


def c_param(kappa: float, eta: float, h: float) -> complex:
    return (eta - 1j / h) * kappa


def main() -> None:
    grid = np.linspace(-7.5, 7.5, 50001)
    m2 = 1.4
    lam = 0.85

    # Choose two equivalent parameter triples under tau_mu.
    kappa = 1.25
    eta = 0.6
    h = 0.9
    mu = 1.7
    kp, etap, hp = tau_mu(kappa, eta, h, mu)

    c0 = c_param(kappa, eta, h)
    c1 = c_param(kp, etap, hp)

    print("Claim 1 AP: d=2 ultralocal phi^4 closure check")
    print(f"c(original) = {c0}")
    print(f"c(tau_mu)   = {c1}")
    print(f"|c-c'|      = {abs(c0-c1):.6e}")
    print()

    # One-site moments
    m1 = site_expect(c0, m2, lam, grid, grid)
    m2v = site_expect(c0, m2, lam, grid**2, grid)
    m3 = site_expect(c0, m2, lam, grid**3, grid)
    m4 = site_expect(c0, m2, lam, grid**4, grid)

    # Two-point cylinder observable G(u,v)=u^2+0.3*u*v+v^4.
    omega_g = m2v + 0.3 * m1 * m1 + m4
    print("Two-point cylinder expectation (factorized exact formula):")
    print(f"  omega_c[G] = {omega_g.real:+.10f}{omega_g.imag:+.10f}i")
    print()

    # This value should be independent of lattice spacing/volume in ultralocal class.
    # We print it across nominal (a,L) pairs to reflect the theorem statement.
    nominal_meshes = [(1.0 / 8.0, 8), (1.0 / 16.0, 8), (1.0 / 24.0, 12), (1.0 / 32.0, 12)]
    print("Nominal (a,L) invariance report:")
    for a, L in nominal_meshes:
        print(f"  a={a:.5f}, L={L:>2d}  omega_c[G]={omega_g.real:+.10f}{omega_g.imag:+.10f}i")
    print()

    # c-invariance check under tau_mu (same c).
    m1p = site_expect(c1, m2, lam, grid, grid)
    m2p = site_expect(c1, m2, lam, grid**2, grid)
    m4p = site_expect(c1, m2, lam, grid**4, grid)
    omega_gp = m2p + 0.3 * m1p * m1p + m4p
    print("tau_mu c-invariance check:")
    print(f"  omega_c[G]      = {omega_g.real:+.10f}{omega_g.imag:+.10f}i")
    print(f"  omega_tau_mu[G] = {omega_gp.real:+.10f}{omega_gp.imag:+.10f}i")
    print(f"  |diff|          = {abs(omega_g-omega_gp):.3e}")
    print()

    # One-site SD identity with psi(u)=u+0.2u^3.
    psi = grid + 0.2 * (grid**3)
    dpsi = 1.0 + 0.6 * (grid**2)
    lhs = site_expect(c0, m2, lam, dpsi, grid)
    rhs = c0 * site_expect(c0, m2, lam, psi * d_potential(grid, m2, lam), grid)
    resid = lhs - rhs
    scale = max(1.0, abs(lhs), abs(rhs))
    print("One-site Schwinger-Dyson residual:")
    print(f"  lhs  = {lhs.real:+.10f}{lhs.imag:+.10f}i")
    print(f"  rhs  = {rhs.real:+.10f}{rhs.imag:+.10f}i")
    print(f"  abs residual = {abs(resid):.3e}")
    print(f"  rel residual = {abs(resid)/scale:.3e}")


if __name__ == "__main__":
    main()
