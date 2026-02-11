#!/usr/bin/env python3.12
"""Claim 8 AD discriminant-margin robustness diagnostics.

Run:
  python3.12 research/workspace/simulations/claim8_d6_multispin_margin_robustness_check.py
"""

from __future__ import annotations

import numpy as np


def main() -> None:
    # D=6, s=2 surrogate invariants (same normalized base as AC checks).
    m = 1.0
    ell = 1.0
    l1 = 1.0
    l2 = 1.0

    a_grid = np.linspace(0.0, 1.8, 361)

    # Deterministic mismatch model: estimated Gamma differs from true Gamma by
    # a bounded relative-absolute envelope. This emulates surrogate-to-model drift.
    rel = 0.06
    abs_floor = 0.010

    total = 0
    robust_no_circ = 0
    robust_circ = 0
    uncertain = 0

    mismatch_no_circ = 0
    mismatch_circ = 0

    margins = []

    for a1 in a_grid:
        for a2 in a_grid:
            total += 1

            gamma_true = a1 * a1 * l1 * l1 + a2 * a2 * l2 * l2
            delta_true = 9.0 * m * m - 16.0 * ell * ell * gamma_true

            # Deterministic signed estimator distortion.
            distortion = rel * np.sin(0.7 * a1 + 0.9 * a2 + 0.15)
            gamma_hat = gamma_true * (1.0 + distortion)
            delta_hat = 9.0 * m * m - 16.0 * ell * ell * gamma_hat

            # Certified error radius for discriminant.
            e_gamma = rel * gamma_true + abs_floor
            e_delta = 16.0 * ell * ell * e_gamma

            # Certified classes.
            if delta_hat < -e_delta:
                robust_no_circ += 1
                if not (delta_true < 0.0):
                    mismatch_no_circ += 1
            elif delta_hat > e_delta:
                robust_circ += 1
                if not (delta_true > 0.0):
                    mismatch_circ += 1
            else:
                uncertain += 1

            mu = abs(delta_hat) / (e_delta + 1.0e-15)
            margins.append(float(mu))

    robust_no_circ_frac = robust_no_circ / total
    robust_circ_frac = robust_circ / total
    uncertain_frac = uncertain / total

    # Reference AB/AC open fraction in this normalized grid is delta_true >= 0.
    # We report what fraction is now robustly sign-certified despite mismatch.
    certified_frac = robust_no_circ_frac + robust_circ_frac

    margins_arr = np.array(margins, dtype=float)

    all_ok = (
        mismatch_no_circ == 0
        and mismatch_circ == 0
        and abs((robust_no_circ_frac + robust_circ_frac + uncertain_frac) - 1.0) <= 1.0e-12
        and certified_frac > 0.90
    )

    print("Claim 8 AD discriminant-margin robustness diagnostic")
    print(f"grid_size={len(a_grid)}x{len(a_grid)}")
    print(f"M={m:.6f}, L={ell:.6f}, rel={rel:.6f}, abs_floor={abs_floor:.6f}")
    print(f"robust_no_circular_fraction={robust_no_circ_frac:.8f}")
    print(f"robust_circular_candidate_fraction={robust_circ_frac:.8f}")
    print(f"uncertainty_band_fraction={uncertain_frac:.8f}")
    print(f"certified_fraction={certified_frac:.8f}")
    print(f"mu_median={np.median(margins_arr):.6f}")
    print(f"mu_p10={np.quantile(margins_arr, 0.10):.6f}")
    print(f"mu_p90={np.quantile(margins_arr, 0.90):.6f}")
    print(f"mismatch_no_circular={mismatch_no_circ}")
    print(f"mismatch_circular_candidate={mismatch_circ}")
    print(f"check_partition_sum={abs((robust_no_circ_frac + robust_circ_frac + uncertain_frac) - 1.0) <= 1.0e-12}")
    print(f"check_sign_cert_no_circular={mismatch_no_circ == 0}")
    print(f"check_sign_cert_circular={mismatch_circ == 0}")
    print(f"check_certified_fraction_gt_0p90={certified_frac > 0.90}")
    print(f"all_checks_pass={all_ok}")


if __name__ == "__main__":
    main()
