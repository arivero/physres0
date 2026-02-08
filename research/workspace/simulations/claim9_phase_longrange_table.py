#!/usr/bin/env python3.12
"""Asymptotic table for Claim 9 phase-split long-range potentials.

Run:
  python3.12 research/workspace/simulations/claim9_phase_longrange_table.py
"""

from __future__ import annotations


def coulomb_asymptotic(D: int) -> str:
    if D == 2:
        return "V(r) ~ r"
    if D == 3:
        return "V(r) ~ log r"
    return f"V(r) ~ r^({3 - D})"


def main() -> None:
    print("Coulomb phase (massless gauge mode):")
    for D in [2, 3, 4, 5, 6]:
        print(f"  D={D}: {coulomb_asymptotic(D)}")
    print()
    print("Screened/Higgs phase:")
    print("  V(r) ~ exp(-m r) * r^{-(D-2)/2}  (up to constants)")
    print("  => saturates at large r")
    print()
    print("Confining area-law sector:")
    print("  V(r) ~ sigma * r  (pure-gauge asymptotic regime)")
    print("  with dynamical matter: eventual string breaking -> saturation")


if __name__ == "__main__":
    main()
