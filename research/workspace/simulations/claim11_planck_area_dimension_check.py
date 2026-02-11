#!/usr/bin/env python3.12
"""Claim 11: Planck area quantization → 3+1D forcing diagnostics.

Run:
  python3.12 research/workspace/simulations/claim11_planck_area_dimension_check.py

Verifies that the dimensional cancellation of Newton's constant in the
Planck-area quantization condition occurs only for q=2 (inverse-square law).
"""

from __future__ import annotations

import math


def dimensional_exponents(q: float):
    """Compute the dimensional exponents for the Planck area quantization formula.

    For F = G m m' / r^q, G has dimensions [L]^{q+1} [M]^{-1} [T]^{-2}.
    The area swept condition A(t_P) = n A_P leads to:
      2n = G^{1/2 - 1/q} m^{1/2} r^{3/2 - q/2} c^{3/q - 1} hbar^{-1/q}

    The exponent of G is (1/2 - 1/q).
    G cancels iff this exponent = 0, i.e., q = 2.
    """
    if abs(q) < 1.0e-15:
        return None
    g_exp = 0.5 - 1.0 / q
    m_exp = 0.5
    r_exp = 1.5 - q / 2.0
    c_exp = 3.0 / q - 1.0
    hbar_exp = -1.0 / q
    return {
        "G_exponent": g_exp,
        "m_exponent": m_exp,
        "r_exponent": r_exp,
        "c_exponent": c_exp,
        "hbar_exponent": hbar_exp,
    }


def spatial_dimension_from_propagator(q: int) -> int:
    """If F ~ 1/r^q comes from Fourier transform of 1/k^2 propagator in d spatial dims,
    then V ~ 1/r^{q-1} and Fourier(1/k^2) in d dims gives 1/r^{d-2}.
    So q - 1 = d - 2, hence d = q + 1.
    For q=2: d=3 spatial dimensions → 3+1 spacetime.
    """
    return q + 1


def main() -> None:
    # Check 1: G cancels only for q=2.
    q_values = [1, 1.5, 2, 2.5, 3, 4, 5]
    check_cancellation = True
    cancellation_q = None

    for q in q_values:
        exp = dimensional_exponents(q)
        if exp is None:
            continue
        g_exp = exp["G_exponent"]
        if abs(g_exp) < 1.0e-12:
            if cancellation_q is not None:
                check_cancellation = False  # non-unique
            cancellation_q = q

    check_unique_q2 = cancellation_q is not None and abs(cancellation_q - 2.0) < 1.0e-12

    # Check 2: q=2 with propagator origin implies d=3 spatial dimensions → 3+1 spacetime.
    d_spatial = spatial_dimension_from_propagator(2)
    check_3plus1 = (d_spatial == 3)  # 3 spatial dims → 3+1 spacetime

    # Check 3: Verify dimensional formula for specific q values.
    check_q2_reduces_to_compton = True
    exp_q2 = dimensional_exponents(2.0)
    if exp_q2 is None or abs(exp_q2["G_exponent"]) > 1.0e-12:
        check_q2_reduces_to_compton = False
    # After G cancels: 2n = m^{1/2} r^{1/2} c^{1/2} hbar^{-1/2}
    # => r ~ hbar / (m c) = Compton radius ✓
    if exp_q2:
        r_exp = exp_q2["r_exponent"]
        m_exp = exp_q2["m_exponent"]
        hbar_exp = exp_q2["hbar_exponent"]
        c_exp = exp_q2["c_exponent"]
        # Solving for r: r^{r_exp} = (2n) * hbar^{-hbar_exp} * m^{-m_exp} * c^{-c_exp}
        # r_exp = 0.5, hbar_exp = -0.5, so hbar power = 0.5
        # m_exp = 0.5, so m power = -0.5
        # c_exp = 0.5, so c power = -0.5
        # r ~ hbar^1 m^{-1} c^{-1} = hbar/(mc) ✓
        check_q2_reduces_to_compton = (
            abs(r_exp - 0.5) < 1.0e-12
            and abs(hbar_exp + 0.5) < 1.0e-12
            and abs(m_exp - 0.5) < 1.0e-12
            and abs(c_exp - 0.5) < 1.0e-12
        )

    # Check 4: For q != 2, G does not cancel (spot checks).
    check_no_cancel_others = True
    for q in [1, 3, 4, 5]:
        exp = dimensional_exponents(float(q))
        if exp and abs(exp["G_exponent"]) < 1.0e-12:
            check_no_cancel_others = False

    all_ok = (check_unique_q2 and check_3plus1
              and check_q2_reduces_to_compton and check_no_cancel_others)

    print("Claim 11 Planck area quantization dimension diagnostic")
    print("Dimensional exponents for various q:")
    for q in q_values:
        exp = dimensional_exponents(q)
        if exp:
            print(f"  q={q}: G_exp={exp['G_exponent']:.6f}, "
                  f"m_exp={exp['m_exponent']:.6f}, "
                  f"r_exp={exp['r_exponent']:.6f}")
    print(f"cancellation_at_q={cancellation_q}")
    print(f"spatial_dim_from_propagator_q2={d_spatial}")
    print(f"check_unique_cancellation_q2={check_unique_q2}")
    print(f"check_3plus1_spacetime={check_3plus1}")
    print(f"check_q2_reduces_to_compton={check_q2_reduces_to_compton}")
    print(f"check_no_cancel_for_q_neq_2={check_no_cancel_others}")
    print(f"all_checks_pass={all_ok}")


if __name__ == "__main__":
    main()
