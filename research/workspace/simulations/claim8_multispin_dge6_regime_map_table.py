#!/usr/bin/env python3.12
"""Regime map table for Claim 8, D>=6 multi-spin Myers-Perry sectors.

Run:
  python3.12 research/workspace/simulations/claim8_multispin_dge6_regime_map_table.py
"""

from __future__ import annotations


def far_zone_curvature_coefficient(D: int) -> float:
    """Coefficient of leading far-zone circular-orbit curvature sign: p(2-p), p=D-3."""
    p = float(D - 3)
    return p * (2.0 - p)


def main() -> None:
    print("Claim 8: D>=6 multi-spin regime map")
    print()
    print("| D | spin rank s | proven status | far-zone sign p(2-p) | comment |")
    print("|---|---|---|---|---|")

    rows = [
        (6, 1, "stable-bound branch proven (high spin)", "Igata 2015"),
        (6, 2, "global bound-status open", "multi-spin unresolved in workspace"),
        (7, 1, "global bound-status open", "no full global closure"),
        (7, 2, "global bound-status open", "no full global closure"),
        (7, 3, "global bound-status open", "no full global closure"),
    ]

    for D, s, status, comment in rows:
        coeff = far_zone_curvature_coefficient(D)
        far_zone = "unstable" if coeff < 0 else ("neutral" if coeff == 0 else "stable")
        print(
            f"| {D} | {s} | {status} | {coeff:.1f} ({far_zone}) | {comment} |"
        )

    print()
    print("Interpretation:")
    print("  For D>5, p(2-p)<0, so asymptotic circular timelike stability is excluded.")
    print("  Any surviving stable branch must be non-asymptotic (compact/intermediate radius).")


if __name__ == "__main__":
    main()
