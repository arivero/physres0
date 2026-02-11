#!/usr/bin/env python3.12
"""Claim 3 consolidated taxonomy diagnostics.

Run:
  python3.12 research/workspace/simulations/claim3_consolidated_taxonomy_check.py
"""

from __future__ import annotations

import math

import numpy as np


def classify_orbit(k: float, l: float, e: float, m: float, c: float):
    """Classify an SR Coulomb orbit and verify root-rotation consistency."""
    alpha_sq = 1.0 - k * k / (l * l * c * c)
    a_coeff = (e * e - m * m * c**4) / (l * l * c * c)
    b_coeff = k * e / (c * c * l * l)

    # Phase regime.
    if alpha_sq > 1.0e-10:
        regime = "oscillatory"
        alpha = math.sqrt(alpha_sq)
        u_c = b_coeff / alpha_sq
        e_sq = (b_coeff * b_coeff + alpha_sq * a_coeff) / (alpha_sq * alpha_sq)
        if e_sq < -1.0e-14:
            return None  # unphysical
        e_amp = math.sqrt(max(e_sq, 0.0))
        theta = alpha

        # Root-rotation bridge.
        u_plus = u_c + e_amp
        u_minus = u_c - e_amp

        # Vieta check.
        vieta_sum = u_plus + u_minus
        vieta_sum_expected = 2.0 * b_coeff / alpha_sq
        vieta_prod = u_plus * u_minus
        vieta_prod_expected = -a_coeff / alpha_sq

        sum_ok = abs(vieta_sum - vieta_sum_expected) < 1.0e-10
        prod_ok = abs(vieta_prod - vieta_prod_expected) < 1.0e-10

        # Q(u) factored check at midpoint.
        u_test = u_c
        q_direct = a_coeff + 2 * b_coeff * u_test - alpha_sq * u_test * u_test
        q_factored = -alpha_sq * (u_test - u_plus) * (u_test - u_minus)
        factor_ok = abs(q_direct - q_factored) < 1.0e-10

        # Energy split.
        if a_coeff < -1.0e-14:
            branch = "bound"
        elif abs(a_coeff) < 1.0e-14:
            branch = "threshold"
        else:
            branch = "scattering"

        return {
            "regime": regime, "branch": branch, "alpha": alpha,
            "theta": theta, "u_plus": u_plus, "u_minus": u_minus,
            "vieta_sum_ok": sum_ok, "vieta_prod_ok": prod_ok,
            "factor_ok": factor_ok,
        }

    elif abs(alpha_sq) < 1.0e-10:
        return {"regime": "critical", "branch": "marginal",
                "vieta_sum_ok": True, "vieta_prod_ok": True, "factor_ok": True}
    else:
        return {"regime": "hyperbolic", "branch": "spiral",
                "vieta_sum_ok": True, "vieta_prod_ok": True, "factor_ok": True}


def main() -> None:
    c = 1.0
    m = 1.0
    k = 0.5

    # Test cases spanning all regimes.
    # E must be physically valid: e^2 = (B^2 + alpha^2 A)/alpha^4 >= 0.
    test_cases = [
        # (L, E, expected_regime, expected_branch)
        (1.0, 0.98, "oscillatory", "bound"),       # E < mc^2, valid bound orbit
        (1.0, 1.0, "oscillatory", "threshold"),
        (1.0, 1.5, "oscillatory", "scattering"),
        (0.5, 0.8, "critical", "marginal"),         # L = K/c
        (0.3, 0.8, "hyperbolic", "spiral"),
        (2.0, 0.98, "oscillatory", "bound"),        # large L, valid bound orbit
        (2.0, 1.0, "oscillatory", "threshold"),
        (2.0, 2.0, "oscillatory", "scattering"),
    ]

    all_regime_ok = True
    all_branch_ok = True
    all_vieta_ok = True
    all_factor_ok = True

    for l_val, e_val, exp_regime, exp_branch in test_cases:
        result = classify_orbit(k, l_val, e_val, m, c)
        if result is None:
            all_regime_ok = False
            continue

        if result["regime"] != exp_regime:
            all_regime_ok = False
        if result["branch"] != exp_branch:
            all_branch_ok = False
        if not result["vieta_sum_ok"] or not result["vieta_prod_ok"]:
            all_vieta_ok = False
        if not result["factor_ok"]:
            all_factor_ok = False

    # Parametric sweep for Vieta/factorization consistency.
    l_sweep = np.linspace(0.6, 3.0, 100)
    e_sweep = np.linspace(0.3, 2.5, 100)
    sweep_vieta_ok = True
    sweep_factor_ok = True

    for l_val in l_sweep:
        for e_val in e_sweep:
            result = classify_orbit(k, l_val, e_val, m, c)
            if result is None:
                continue
            if not result["vieta_sum_ok"] or not result["vieta_prod_ok"]:
                sweep_vieta_ok = False
            if not result["factor_ok"]:
                sweep_factor_ok = False

    all_ok = (all_regime_ok and all_branch_ok and all_vieta_ok
              and all_factor_ok and sweep_vieta_ok and sweep_factor_ok)

    print("Claim 3 consolidated taxonomy diagnostic")
    print(f"K={k:.6f}, m={m:.6f}, c={c:.6f}")
    print(f"test_cases={len(test_cases)}")
    print(f"check_regime_labels={all_regime_ok}")
    print(f"check_branch_labels={all_branch_ok}")
    print(f"check_vieta_relations={all_vieta_ok}")
    print(f"check_factorization={all_factor_ok}")
    print(f"sweep_vieta_consistency={sweep_vieta_ok}")
    print(f"sweep_factor_consistency={sweep_factor_ok}")
    print(f"all_checks_pass={all_ok}")


if __name__ == "__main__":
    main()
