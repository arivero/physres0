#!/usr/bin/env python3.12
"""Unified SR/GR/gauge action-reduction diagnostics for the foundational narrative.

Run:
  python3.12 research/workspace/simulations/foundation_action_reduction_unification_check.py
"""

from __future__ import annotations

import math


def sr_coulomb_diagnostics(K: float, L: float, c: float, E: float, m: float) -> dict[str, float]:
    alpha2 = 1.0 - (K * K) / (L * L * c * c)
    A = (E * E - m * m * c**4) / (L * L * c * c)
    B = (K * E) / (c * c * L * L)
    disc = B * B + alpha2 * A
    return {"alpha2": alpha2, "A": A, "B": B, "disc": disc}


def schwarzschild_double_root_residual(r: float, M: float = 1.0) -> tuple[float, float, float]:
    l2 = (M * r * r) / (r - 3.0 * M)
    E2 = ((r - 2.0 * M) ** 2) / (r * (r - 3.0 * M))
    # R(r) = E^2 - (1-2M/r)(1+l^2/r^2)
    R = E2 - (1.0 - 2.0 * M / r) * (1.0 + l2 / (r * r))
    # derivative at fixed E,l
    dR = -(2.0 * M / (r * r)) * (1.0 + l2 / (r * r)) + (1.0 - 2.0 * M / r) * (2.0 * l2 / (r**3))
    return (l2, R, dR)


def gauge_phase_table() -> list[tuple[str, str]]:
    return [
        ("Coulomb phase", "V(r) ~ r^(3-D) / log r / r (low D cases)"),
        ("Confining phase", "V(r) ~ sigma r"),
        ("Screened/Higgs phase", "V(r) ~ exp(-m r) * r^(-(D-2)/2) -> saturation"),
    ]


def main() -> None:
    print("Foundational action-reduction unification check")
    print()

    print("SR Coulomb diagnostics (u'² = A + 2Bu - alpha² u²):")
    # For the first parameter set, E = sqrt(alpha^2) gives disc = 0 (double-root boundary).
    sr_cases = [
        ("double-root", dict(K=0.6, L=1.2, c=1.0, E=math.sqrt(0.75), m=1.0)),
        ("oscillatory", dict(K=0.6, L=1.2, c=1.0, E=0.95, m=1.0)),
        ("critical", dict(K=0.6, L=0.6, c=1.0, E=1.05, m=1.0)),
        ("hyperbolic", dict(K=0.6, L=0.5, c=1.0, E=1.05, m=1.0)),
    ]
    for label, p in sr_cases:
        d = sr_coulomb_diagnostics(**p)
        print(
            f"  {label:10s} alpha²={d['alpha2']:+.6f}  A={d['A']:+.6f}  B={d['B']:+.6f}  disc={d['disc']:+.6f}"
        )
    print()

    print("Schwarzschild circular-orbit double-root residuals:")
    for r in [6.0, 8.0, 12.0]:
        l2, R, dR = schwarzschild_double_root_residual(r=r, M=1.0)
        print(f"  r={r:>4.1f}  l²={l2:.8f}  R(r)={R:+.3e}  R'(r)={dR:+.3e}")
    print()

    print("Gauge phase -> asymptotic potential map:")
    for phase, asymp in gauge_phase_table():
        print(f"  {phase:18s}: {asymp}")
    print()
    print("Interpretation: same action-reduction skeleton, different V(r) by phase/model.")


if __name__ == "__main__":
    main()
