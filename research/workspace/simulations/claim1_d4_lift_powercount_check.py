#!/usr/bin/env python3.12
"""Claim 1 AQ check: simple phi^4 power-count diagnostics by dimension.

Run:
  python3.12 research/workspace/simulations/claim1_d4_lift_powercount_check.py
"""

from __future__ import annotations


def omega_phi4(d: int, external_legs: int) -> int:
    # Superficial divergence degree for connected phi^4 graphs:
    # omega = d - (d-2) * E / 2
    return int(d - ((d - 2) * external_legs) / 2)


def main() -> None:
    dims = [2, 3, 4]
    e_values = [0, 2, 4, 6, 8]

    print("Claim 1 AQ: superficial divergence trend for local phi^4")
    print("omega(d,E) = d - (d-2)E/2")
    print()

    for d in dims:
        print(f"d={d}")
        for e in e_values:
            om = omega_phi4(d, e)
            status = "UV-sensitive" if om >= 0 else "power-count suppressed"
            print(f"  E={e:>2d} -> omega={om:>3d}  ({status})")
        print()

    print("Interpretation:")
    print("  d=2: broad UV sensitivity by power counting (superrenormalizable context).")
    print("  d=3: reduced UV-sensitive sector (still superrenormalizable).")
    print("  d=4: marginal boundary where low-point sectors remain sensitive.")


if __name__ == "__main__":
    main()
