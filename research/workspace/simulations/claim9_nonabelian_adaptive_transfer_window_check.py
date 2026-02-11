#!/usr/bin/env python3.12
"""Claim 9 AH: adaptive transfer-budget window diagnostics."""

from __future__ import annotations

import numpy as np


def a_beta(delta: float) -> float:
    return 0.19 + 0.03 * np.sin(2.6 * delta + 0.2)


def b_beta(delta: float) -> float:
    return 0.08 + 0.02 * np.cos(2.1 * delta + 0.4)


def r_beta(delta: float, r: float, t: float) -> float:
    return 0.018 * np.sin(1.7 * delta + 0.13 * r + 0.09 * t)


def deriv(delta: float, r: float, t: float) -> float:
    return -a_beta(delta) * r * t + b_beta(delta) * (r + t) + r_beta(delta, r, t)


def integrate_deriv(delta_target: float, r: float, t: float, steps: int = 2400) -> float:
    if delta_target == 0.0:
        return 0.0
    xs = np.linspace(0.0, delta_target, steps + 1)
    ys = np.array([deriv(float(x), r, t) for x in xs], dtype=float)
    return float(np.trapezoid(ys, xs))


def main() -> None:
    gauge_group = "SU(3)"
    dimension = 4

    beta0 = 0.11
    beta1 = 0.24
    delta_max = beta1 - beta0

    a_star = 0.78
    b_star = 0.30
    r_star = 0.05

    r_values = np.array([2.0, 3.0, 4.0, 5.0, 6.0])
    t_values = np.array([6.0, 8.0, 10.0, 12.0, 16.0, 20.0])

    sigma0 = 0.21
    p0 = 0.028
    c0 = 0.012
    logw0 = np.zeros((len(r_values), len(t_values)))
    for i, r in enumerate(r_values):
        for j, t in enumerate(t_values):
            eps0 = 0.020 * np.sin(0.23 * r + 0.19 * t + 0.11 * (i + 1) * (j + 1))
            eps0 /= 1.0 + 0.25 * (r + t)
            logw0[i, j] = -sigma0 * r * t + p0 * (r + t) + c0 + eps0

    m0 = -logw0

    delta_scan = np.linspace(0.0, delta_max, 2001)

    lambda_coarse = np.zeros_like(logw0)
    lambda_adapt = np.zeros_like(logw0)
    max_adapt_minus_coarse = -np.inf
    for i, r in enumerate(r_values):
        for j, t in enumerate(t_values):
            lambda_coarse[i, j] = a_star * r * t + b_star * (r + t) + r_star
            dvals = np.array([abs(deriv(float(d), r, t)) for d in delta_scan], dtype=float)
            lambda_adapt[i, j] = float(np.max(dvals))
            max_adapt_minus_coarse = max(
                max_adapt_minus_coarse, lambda_adapt[i, j] - lambda_coarse[i, j]
            )

    delta_safe_coarse_raw = float(np.min(m0 / (2.0 * lambda_coarse)))
    delta_safe_adapt_raw = float(np.min(m0 / (2.0 * lambda_adapt)))
    delta_safe_coarse = min(delta_safe_coarse_raw, delta_max)
    delta_safe_adapt = min(delta_safe_adapt_raw, delta_max)
    gain = delta_safe_adapt / delta_safe_coarse

    beta_test_inside = beta0 + delta_safe_adapt * np.array([0.20, 0.45, 0.70, 0.92])
    positivity_inside_ok = True
    max_budget_gap = -np.inf
    for beta in beta_test_inside:
        delta = float(beta - beta0)
        for i, r in enumerate(r_values):
            for j, t in enumerate(t_values):
                drift = integrate_deriv(delta, r, t)
                logw_beta = logw0[i, j] + drift
                wilson = float(np.exp(logw_beta))
                if not (0.0 < wilson < 1.0):
                    positivity_inside_ok = False

                lhs = abs(drift)
                rhs = lambda_adapt[i, j] * abs(delta)
                max_budget_gap = max(max_budget_gap, lhs - rhs)

    print("Claim 9 AH adaptive transfer-window diagnostic")
    print(f"tagged_model: G={gauge_group}, D={dimension}")
    print(f"beta0={beta0:.6f}, beta1={beta1:.6f}")
    print(f"A*={a_star:.6f}, B*={b_star:.6f}, R*={r_star:.6f}")
    print(f"delta_safe_coarse_raw={delta_safe_coarse_raw:.8e}")
    print(f"delta_safe_adapt_raw={delta_safe_adapt_raw:.8e}")
    print(f"delta_safe_coarse_clipped={delta_safe_coarse:.8e}")
    print(f"delta_safe_adapt_clipped={delta_safe_adapt:.8e}")
    print(f"window_gain_factor={gain:.8f}")
    print(f"max_adapt_minus_coarse={max_adapt_minus_coarse:.8e}")
    print(f"max_adaptive_budget_gap={max_budget_gap:.8e}")
    print(f"check_adapt_le_coarse={max_adapt_minus_coarse <= 1.0e-12}")
    print(f"check_window_widening={delta_safe_adapt >= delta_safe_coarse - 1.0e-12}")
    print(f"check_adaptive_budget_bound={max_budget_gap <= 1.0e-12}")
    print(f"check_inside_window_positivity={positivity_inside_ok}")
    print(
        "all_checks_pass="
        f"{(max_adapt_minus_coarse <= 1.0e-12) and (delta_safe_adapt >= delta_safe_coarse - 1.0e-12) and (max_budget_gap <= 1.0e-12) and positivity_inside_ok}"
    )


if __name__ == "__main__":
    main()
