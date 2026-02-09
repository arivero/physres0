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
    print("Model A: (G=U(1), D) massless Abelian / Coulomb class")
    for D in [2, 3, 4, 5]:
        print(f"  (G=U(1), D={D}): {coulomb_form(D)}")
    print()

    print("Model B: (G=U(1), D) Abelian Higgs / screened")
    print("  (G=U(1), D): V ~ r^{-(D-2)/2} exp(-m_V r)  -> saturation")
    print()

    print("Model C: (G=SU(N), N>=2, N_f=0, D) pure YM confining")
    print("  (G=SU(N), D): V ~ sigma r  (asymptotic linear)")
    print()

    print("Model D: (G=SU(N), N>=2, N_f>0, D) YM + dynamical fundamentals")
    print("  (G=SU(N), D): intermediate V ~ sigma r")
    print("  (G=SU(N), D): asymptotic string breaking -> saturation")


if __name__ == "__main__":
    main()
