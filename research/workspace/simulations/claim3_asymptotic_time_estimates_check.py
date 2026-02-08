#!/usr/bin/env python3.12
"""Asymptotic-time diagnostics for Claim 3 Phase X (SR Coulomb).

Checks:
  1) scattering branch: dr/dt -> v_inf as r -> infinity
  2) plunge branch L<K/c: dt/dr -> K/(c^2*sqrt(K^2/c^2-L^2)) as r -> 0
  3) critical branch L=K/c: (dt/dr)*sqrt(r) -> sqrt(K)/(c*sqrt(2E)) as r -> 0

Run:
  python3.12 research/workspace/simulations/claim3_asymptotic_time_estimates_check.py
"""

from __future__ import annotations

import math


def p_r(r: float, E: float, L: float, m: float, c: float, K: float) -> float:
    val = ((E + K / r) ** 2 - (m * c * c) ** 2) / (c * c) - (L * L) / (r * r)
    return math.sqrt(max(0.0, val))


def dt_dr(r: float, E: float, L: float, m: float, c: float, K: float) -> float:
    pr = p_r(r, E, L, m, c, K)
    return (E + K / r) / (c * c * pr)


def main() -> None:
    m = 1.0
    c = 1.0
    K = 1.0

    print("Claim 3 Phase X asymptotic-time checks")

    # 1) Scattering asymptotic
    E_s = 1.2
    L_s = 1.4
    v_inf = c * math.sqrt(1.0 - (m * c * c) ** 2 / (E_s * E_s))
    print("\nScattering branch (E>mc^2, L>K/c): dr/dt -> v_inf")
    print(f"theory v_inf = {v_inf:.10f}")
    for r in [20.0, 50.0, 100.0, 200.0]:
        val = 1.0 / dt_dr(r, E_s, L_s, m, c, K)
        print(f"  r={r:>6.1f}: dr/dt={val:.10f}, abs err={abs(val - v_inf):.3e}")

    # 2) Plunge branch L<K/c
    E_p = 1.2
    L_p = 0.8
    c0 = math.sqrt(K * K / (c * c) - L_p * L_p)
    kappa = K / (c * c * c0)
    print("\nPlunge branch (L<K/c): dt/dr -> kappa")
    print(f"theory kappa = {kappa:.10f}")
    for r in [1e-2, 5e-3, 2e-3, 1e-3]:
        val = dt_dr(r, E_p, L_p, m, c, K)
        print(f"  r={r:>7.1e}: dt/dr={val:.10f}, abs err={abs(val - kappa):.3e}")

    # 3) Critical branch L=K/c
    E_c = 1.2
    L_c = K / c
    kappa_c = math.sqrt(K) / (c * math.sqrt(2.0 * E_c))
    print("\nCritical branch (L=K/c): (dt/dr)*sqrt(r) -> kappa_c")
    print(f"theory kappa_c = {kappa_c:.10f}")
    for r in [1e-2, 5e-3, 2e-3, 1e-3]:
        val = dt_dr(r, E_c, L_c, m, c, K) * math.sqrt(r)
        print(f"  r={r:>7.1e}: scaled={val:.10f}, abs err={abs(val - kappa_c):.3e}")


if __name__ == "__main__":
    main()
