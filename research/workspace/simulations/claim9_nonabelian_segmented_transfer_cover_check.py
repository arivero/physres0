#!/usr/bin/env python3.12
"""Claim 9 AJ segmented transfer-cover diagnostics.

Run:
  python3.12 research/workspace/simulations/claim9_nonabelian_segmented_transfer_cover_check.py
"""

from __future__ import annotations

import numpy as np


def a_beta(delta: float) -> float:
    return float(0.19 + 0.03 * np.sin(2.6 * delta + 0.2))


def b_beta(delta: float) -> float:
    return float(0.08 + 0.02 * np.cos(2.1 * delta + 0.4))


def r_beta(delta: float, r: float, t: float) -> float:
    return float(0.018 * np.sin(1.7 * delta + 0.13 * r + 0.09 * t))


DRIFT_SCALE = 5.0


def deriv(beta0: float, beta: float, r: float, t: float) -> float:
    d = beta - beta0
    return DRIFT_SCALE * (
        -a_beta(d) * r * t + b_beta(d) * (r + t) + r_beta(d, r, t)
    )


def integrate_d(beta0: float, beta1: float, r: float, t: float, steps: int = 120) -> float:
    if beta1 == beta0:
        return 0.0
    xs = np.linspace(beta0, beta1, steps + 1)
    ys = np.array([deriv(beta0, float(x), r, t) for x in xs], dtype=float)
    return float(np.trapezoid(ys, xs))


def segment_budget(beta_left: float, beta_right: float, r: float, t: float) -> float:
    xs = np.linspace(beta_left, beta_right, 81)
    vals = np.array([abs(deriv(beta_left, float(x), r, t)) for x in xs], dtype=float)
    return float(np.max(vals))


def try_partition(J: int) -> tuple[bool, float, float, int, bool]:
    beta0 = 0.11
    beta1 = 0.24
    nodes = np.linspace(beta0, beta1, J + 1)

    r_values = np.array([2.0, 3.0, 4.0, 5.0, 6.0])
    t_values = np.array([6.0, 8.0, 10.0, 12.0, 16.0, 20.0])

    # Initial anchor profile at beta0.
    sigma0 = 0.21
    p0 = 0.028
    c0 = 0.012
    logw = np.zeros((len(r_values), len(t_values)))
    for i, r in enumerate(r_values):
        for j, t in enumerate(t_values):
            eps0 = 0.020 * np.sin(0.23 * r + 0.19 * t + 0.11 * (i + 1) * (j + 1))
            eps0 /= 1.0 + 0.25 * (r + t)
            logw[i, j] = -sigma0 * r * t + p0 * (r + t) + c0 + eps0

    min_ratio = float("inf")
    min_delta_j = float("inf")
    worst_segment = -1
    positivity_ok = True

    for seg in range(J):
        left = float(nodes[seg])
        right = float(nodes[seg + 1])
        h = right - left

        # Current anchor margins.
        m = -logw
        if np.any(m <= 0.0):
            positivity_ok = False
            return False, min_ratio, min_delta_j, seg, positivity_ok

        # Build local structured budget (segment-local sup envelope).
        lamb = np.zeros_like(logw)
        for i, r in enumerate(r_values):
            for j, t in enumerate(t_values):
                lamb[i, j] = segment_budget(left, right, r, t)

        delta_j = float(np.min(m / (2.0 * lamb)))
        ratio = h / delta_j

        if ratio < min_ratio:
            min_ratio = ratio
        if delta_j < min_delta_j:
            min_delta_j = delta_j

        if ratio > 1.0 + 1.0e-12:
            worst_segment = seg
            return False, min_ratio, min_delta_j, worst_segment, positivity_ok

        # Propagate to next anchor by true integral.
        for i, r in enumerate(r_values):
            for j, t in enumerate(t_values):
                drift = integrate_d(left, right, r, t)
                logw[i, j] += drift
                wilson = float(np.exp(logw[i, j]))
                if not (0.0 < wilson < 1.0):
                    positivity_ok = False

    return positivity_ok, min_ratio, min_delta_j, worst_segment, positivity_ok


def main() -> None:
    beta0 = 0.11
    beta1 = 0.24
    full_span = beta1 - beta0

    j_star = None
    result_rows = []

    for J in range(1, 25):
        ok, min_ratio, min_delta_j, worst_segment, positivity_ok = try_partition(J)
        result_rows.append((J, ok, min_ratio, min_delta_j, worst_segment, positivity_ok))
        if ok and j_star is None:
            j_star = J
            break

    full_cover_found = j_star is not None

    print("Claim 9 AJ segmented transfer-cover diagnostic")
    print(f"beta0={beta0:.6f}, beta1={beta1:.6f}, full_span={full_span:.6f}")
    print(f"drift_scale={DRIFT_SCALE:.6f}")
    print("J_scan_rows:")
    for J, ok, min_ratio, min_delta_j, worst_segment, positivity_ok in result_rows:
        print(
            f"  J={J:2d}: ok={ok}, min(h/delta_j)={min_ratio:.6f}, "
            f"min_delta_j={min_delta_j:.6e}, worst_segment={worst_segment}, "
            f"positivity_ok={positivity_ok}"
        )
    if full_cover_found:
        print(f"J_star={j_star}")
        print(f"segment_length_at_J_star={full_span / j_star:.8f}")
    else:
        print("J_star=None")

    all_ok = full_cover_found and (j_star is not None and j_star > 1)
    print(f"check_full_cover_found={full_cover_found}")
    print(f"check_requires_segmentation={(j_star is not None and j_star > 1)}")
    print(f"all_checks_pass={all_ok}")


if __name__ == "__main__":
    main()
