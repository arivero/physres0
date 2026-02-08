#!/usr/bin/env python3.12
"""Model-class assumption/outcome table for Claim 9 (Phase E).

Run:
  python3.12 research/workspace/simulations/claim9_model_class_table.py
"""

from __future__ import annotations


def coulomb_form(D: int) -> str:
    if D == 2:
        return "V ~ r"
    if D == 3:
        return "V ~ log r"
    return f"V ~ r^({3 - D})"


def main() -> None:
    print("Model A: massless Abelian / Coulomb class")
    for D in [2, 3, 4, 5]:
        print(f"  D={D}: {coulomb_form(D)}")
    print()

    print("Model B: Abelian Higgs / screened")
    print("  V ~ r^{-(D-2)/2} exp(-m_V r)  -> saturation")
    print()

    print("Model C: pure YM confining (area law)")
    print("  V ~ sigma r  (asymptotic linear)")
    print()

    print("Model D: YM + dynamical fundamental matter")
    print("  intermediate: V ~ sigma r")
    print("  asymptotic : string breaking -> saturation")


if __name__ == "__main__":
    main()
