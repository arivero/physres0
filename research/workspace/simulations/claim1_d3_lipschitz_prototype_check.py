#!/usr/bin/env python3.12
"""Claim 1 AT check: small-kappa Lipschitz prototype bound.

Run:
  python3.12 research/workspace/simulations/claim1_d3_lipschitz_prototype_check.py
"""

from __future__ import annotations

import numpy as np


def trap(y: np.ndarray, x: np.ndarray):
    t = getattr(np, "trapezoid", None)
    if t is None:
        raise RuntimeError("numpy.trapezoid required")
    return t(y, x)


def onsite(u: np.ndarray, m2: float, lam: float) -> np.ndarray:
    return 0.5 * m2 * (u**2) + 0.25 * lam * (u**4)


def raw_integrals(kappa: float, c: float, m2: float, lam: float, grid: np.ndarray) -> tuple[float, float, float]:
    x = grid[:, None]
    y = grid[None, :]
    g = (x - y) ** 2
    s = onsite(x, m2, lam) + onsite(y, m2, lam) + 0.5 * kappa * g
    w = np.exp(-c * s)

    f = 1.0 / (1.0 + x**2) + 0.2 / (1.0 + y**2)  # bounded by 1.2
    z = trap(trap(w, grid), grid)
    wf = trap(trap(w * f, grid), grid)
    wg = trap(trap(w * g, grid), grid)
    return z, wf, wg


def main() -> None:
    grid = np.linspace(-6.0, 6.0, 1201)
    c = 1.0
    m2 = 1.2
    lam = 0.9
    kappas = [0.0, 0.01, 0.02, 0.04, 0.06, 0.08, 0.10]
    kappa_star = max(kappas)
    f_sup = 1.2

    omega_f = []
    omega_g = []
    for k in kappas:
        z, wf, wg = raw_integrals(k, c, m2, lam, grid)
        omega_f.append(wf / z)
        omega_g.append(wg / z)

    m_star = max(omega_g)
    c_bound = c * f_sup * m_star
    base = omega_f[0]

    print("Claim 1 AT: small-kappa Lipschitz prototype check")
    print(f"c={c}, m2={m2}, lambda={lam}, kappa_star={kappa_star}")
    print(f"Estimated M_kappa* = {m_star:.6f}")
    print(f"Theorem constant C = c * ||F||_inf * M_kappa* = {c_bound:.6f}")
    print()

    print("kappa scan:")
    for k, of, og in zip(kappas, omega_f, omega_g):
        print(f"  kappa={k:>4.2f}  omega_F={of:+.10f}  omega_G={og:.10f}")
    print()

    print("Lipschitz ratio check:")
    ok = True
    for k, of in zip(kappas[1:], omega_f[1:]):
        lhs = abs(of - base)
        rhs = c_bound * k
        ratio = lhs / k
        holds = lhs <= rhs + 1e-12
        ok = ok and holds
        print(
            f"  kappa={k:>4.2f}  |omega_k-omega_0|={lhs:.6e}  "
            f"ratio={ratio:.6e}  C*kappa={rhs:.6e}  holds={holds}"
        )

    print()
    print(f"Bound satisfied for all tested kappa: {ok}")


if __name__ == "__main__":
    main()
