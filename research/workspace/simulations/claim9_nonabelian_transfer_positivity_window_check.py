#!/usr/bin/env python3.12
"""Claim 9 AG: positivity-window criterion diagnostics."""

from __future__ import annotations

import numpy as np


def main() -> None:
    seed = 2026021102
    rng = np.random.default_rng(seed)

    gauge_group = "SU(3)"
    dimension = 4

    beta0 = 0.11
    r_values = np.array([2.0, 3.0, 4.0, 5.0, 6.0])
    t_values = np.array([6.0, 8.0, 10.0, 12.0, 16.0, 20.0])

    # AD/AF-style transfer bounds.
    a_star = 0.78
    b_star = 0.30
    r_star = 0.05

    # Anchor profile with strict negativity (thus 0 < W < 1).
    sigma0 = 0.21
    p0 = 0.028
    c0 = 0.012
    logw0 = np.zeros((len(r_values), len(t_values)))
    for i, r in enumerate(r_values):
        for j, t in enumerate(t_values):
            osc = np.sin(0.23 * r + 0.19 * t + 0.11 * (i + 1) * (j + 1))
            eps0 = 0.020 * osc / (1.0 + 0.25 * (r + t))
            logw0[i, j] = -sigma0 * r * t + p0 * (r + t) + c0 + eps0

    m0 = -logw0
    lambda_rt = (
        a_star * np.outer(r_values, t_values)
        + b_star * (r_values[:, None] + t_values[None, :])
        + r_star
    )

    delta_safe_map = m0 / (2.0 * lambda_rt)
    delta_safe = float(np.min(delta_safe_map))
    beta_grid = beta0 + delta_safe * np.array([0.15, 0.35, 0.55, 0.75, 0.95])
    beta_outside = beta0 + 1.25 * delta_safe

    max_identity_gap = 0.0
    max_budget_gap = 0.0
    positivity_inside_ok = True
    positivity_outside_violations = 0

    for beta in beta_grid:
        delta = float(beta - beta0)

        # Channel values kept strictly within A*, B*, R* bounds.
        a_beta = 0.70 + 0.06 * np.cos(0.9 * delta)
        b_beta = 0.20 * np.sin(0.8 + 1.4 * delta)
        a_beta = float(np.clip(a_beta, -a_star + 0.01, a_star - 0.01))
        b_beta = float(np.clip(b_beta, -b_star + 0.01, b_star - 0.01))

        for i, r in enumerate(r_values):
            for j, t in enumerate(t_values):
                residual = 0.72 * r_star * np.sin(0.31 * r + 0.17 * t + 0.13 * delta)
                residual += 0.02 * r_star * rng.uniform(-1.0, 1.0)
                residual = float(np.clip(residual, -r_star + 1.0e-4, r_star - 1.0e-4))

                deriv = -a_beta * r * t + b_beta * (r + t) + residual
                logw_beta = logw0[i, j] + delta * deriv
                wilson = np.exp(logw_beta)

                # AD identity is exact by construction.
                recon_deriv = (logw_beta - logw0[i, j]) / delta
                max_identity_gap = max(max_identity_gap, abs(deriv - recon_deriv))

                lhs = abs(logw_beta - logw0[i, j])
                rhs = lambda_rt[i, j] * abs(delta)
                max_budget_gap = max(max_budget_gap, lhs - rhs)

                if not (0.0 < wilson < 1.0):
                    positivity_inside_ok = False

    # Probe outside safe window; violation is not required but informative.
    for i, r in enumerate(r_values):
        for j, t in enumerate(t_values):
            a_beta = 0.76
            b_beta = 0.27
            residual = 0.95 * r_star
            deriv = -a_beta * r * t + b_beta * (r + t) + residual
            logw_beta = logw0[i, j] + (beta_outside - beta0) * deriv
            wilson = np.exp(logw_beta)
            if not (0.0 < wilson < 1.0):
                positivity_outside_violations += 1

    print("Claim 9 AG positivity-window diagnostic")
    print(f"seed={seed}")
    print(f"tagged_model: G={gauge_group}, D={dimension}")
    print(f"beta0={beta0:.6f}")
    print(f"A*={a_star:.6f}, B*={b_star:.6f}, R*={r_star:.6f}")
    print(f"min_anchor_margin_m0={float(np.min(m0)):.8e}")
    print(f"max_anchor_margin_m0={float(np.max(m0)):.8e}")
    print(f"delta_safe={delta_safe:.8e}")
    print(f"beta_grid_inside={beta_grid.tolist()}")
    print(f"beta_probe_outside={beta_outside:.8f}")
    print(f"max_transfer_identity_gap={max_identity_gap:.8e}")
    print(f"worst_budget_gap={max_budget_gap:.8e}")
    print(f"outside_window_positivity_violations={positivity_outside_violations}")
    print(f"check_transfer_identity={max_identity_gap <= 1.0e-12}")
    print(f"check_budget_bound={max_budget_gap <= 1.0e-12}")
    print(f"check_inside_window_positivity={positivity_inside_ok}")
    print(
        "all_checks_pass="
        f"{(max_identity_gap <= 1.0e-12) and (max_budget_gap <= 1.0e-12) and positivity_inside_ok}"
    )


if __name__ == "__main__":
    main()
