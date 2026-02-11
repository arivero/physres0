#!/usr/bin/env python3.12
"""Claim 9 AK Lipschitz segment-budget diagnostics.

Run:
  python3.12 research/workspace/simulations/claim9_nonabelian_segment_lipschitz_budget_check.py
"""

from __future__ import annotations

import numpy as np


DRIFT_SCALE = 5.0


def a_beta(delta: float) -> float:
    return float(0.19 + 0.03 * np.sin(2.6 * delta + 0.2))


def b_beta(delta: float) -> float:
    return float(0.08 + 0.02 * np.cos(2.1 * delta + 0.4))


def r_beta(delta: float, r: float, t: float) -> float:
    return float(0.018 * np.sin(1.7 * delta + 0.13 * r + 0.09 * t))


def da_beta(delta: float) -> float:
    return float(0.03 * 2.6 * np.cos(2.6 * delta + 0.2))


def db_beta(delta: float) -> float:
    return float(-0.02 * 2.1 * np.sin(2.1 * delta + 0.4))


def dr_beta(delta: float, r: float, t: float) -> float:
    return float(0.018 * 1.7 * np.cos(1.7 * delta + 0.13 * r + 0.09 * t))


def D(beta_left: float, beta: float, r: float, t: float) -> float:
    d = beta - beta_left
    return DRIFT_SCALE * (-a_beta(d) * r * t + b_beta(d) * (r + t) + r_beta(d, r, t))


def D_prime_abs_bound(h: float, r: float, t: float) -> float:
    # Conservative analytic bound on sup |dD/dbeta| over segment length h.
    # dD/dbeta = DRIFT_SCALE * (-a'(d) r t + b'(d) (r+t) + r'(d,r,t)).
    sup_da = 0.03 * 2.6
    sup_db = 0.02 * 2.1
    sup_dr = 0.018 * 1.7
    return DRIFT_SCALE * (sup_da * r * t + sup_db * (r + t) + sup_dr)


def main() -> None:
    beta0 = 0.11
    beta1 = 0.24

    # Use the J*=2 partition from AJ stress lane.
    nodes = np.linspace(beta0, beta1, 3)

    r_values = np.array([2.0, 3.0, 4.0, 5.0, 6.0])
    t_values = np.array([6.0, 8.0, 10.0, 12.0, 16.0, 20.0])

    worst_sup_minus_lip = -np.inf
    worst_sample_minus_lip = -np.inf
    max_lip_over_sample_ratio = 0.0

    for seg in range(len(nodes) - 1):
        left = float(nodes[seg])
        right = float(nodes[seg + 1])
        h = right - left

        xs = np.linspace(left, right, 601)

        for r in r_values:
            for t in t_values:
                vals = np.array([abs(D(left, float(x), r, t)) for x in xs], dtype=float)
                sup_sample = float(np.max(vals))

                e_j = max(abs(D(left, left, r, t)), abs(D(left, right, r, t)))
                l_j = D_prime_abs_bound(h, r, t)
                lambda_lip = e_j + l_j * h

                worst_sup_minus_lip = max(worst_sup_minus_lip, sup_sample - lambda_lip)
                worst_sample_minus_lip = max(worst_sample_minus_lip, sup_sample - lambda_lip)
                max_lip_over_sample_ratio = max(max_lip_over_sample_ratio, lambda_lip / (sup_sample + 1.0e-15))

    check_sup_bound = worst_sup_minus_lip <= 1.0e-12
    # Ensure the Lipschitz envelope is not excessively loose in this deterministic lane.
    check_reasonable_tightness = max_lip_over_sample_ratio < 1.35

    all_ok = check_sup_bound and check_reasonable_tightness

    print("Claim 9 AK segment-Lipschitz budget diagnostic")
    print(f"beta0={beta0:.6f}, beta1={beta1:.6f}, drift_scale={DRIFT_SCALE:.6f}")
    print("partition=J2")
    print(f"worst_sup_minus_lambda_lip={worst_sup_minus_lip:.8e}")
    print(f"max_lambda_lip_over_sample_sup={max_lip_over_sample_ratio:.8f}")
    print(f"check_sup_bound={check_sup_bound}")
    print(f"check_reasonable_tightness={check_reasonable_tightness}")
    print(f"all_checks_pass={all_ok}")


if __name__ == "__main__":
    main()
