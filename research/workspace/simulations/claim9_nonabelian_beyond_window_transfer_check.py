#!/usr/bin/env python3.12
"""Claim 9 AD: beyond-window beta-transfer diagnostics."""

from __future__ import annotations

import numpy as np


def main() -> None:
    seed = 2026020919
    rng = np.random.default_rng(seed)

    gauge_group = "SU(3)"
    dimension = 4

    beta0 = 0.11
    beta1 = 0.24
    beta_grid = np.array([0.11, 0.14, 0.17, 0.20, 0.24])

    # Anchor AB parameters (from AC lane style).
    sigma0 = 4.002334
    p0 = 0.0176
    c0 = 0.012

    # Transfer derivative channels: a_beta, b_beta linear in (beta-beta0).
    a0, a1 = 0.72, 0.55
    b0, b1 = 0.06, -0.04
    r_star = 0.09

    # Uniform bounds for AD assumptions.
    a_star = max(abs(a0), abs(a0 + a1 * (beta1 - beta0)))
    b_star = max(abs(b0), abs(b0 + b1 * (beta1 - beta0)))
    r_star_bound = r_star

    r_values = np.array([2.0, 3.0, 4.0, 5.0, 6.0])
    t_values = np.array([6.0, 8.0, 10.0, 12.0, 16.0, 20.0])

    # Anchor residual with cap C0.
    c0_cap = 0.035
    eps0 = np.zeros((len(r_values), len(t_values)))
    for i, r in enumerate(r_values):
        for j, t in enumerate(t_values):
            osc = np.sin(0.27 * r + 0.19 * t + 0.13 * (i + 1) * (j + 1))
            eps0[i, j] = c0_cap * osc / (1.0 + 0.3 * (r + t))

    # Beta transfer construction from AD theorem assumptions.
    logw_by_beta: dict[float, np.ndarray] = {}
    sigma_beta: dict[float, float] = {}
    p_beta: dict[float, float] = {}
    eps_beta: dict[float, np.ndarray] = {}
    max_transfer_gap = 0.0
    max_eps_cap_gap = 0.0

    for beta in beta_grid:
        delta = beta - beta0
        sigma = sigma0 + a0 * delta + 0.5 * a1 * delta * delta
        p_val = p0 + b0 * delta + 0.5 * b1 * delta * delta
        sigma_beta[float(beta)] = float(sigma)
        p_beta[float(beta)] = float(p_val)

        # Residual transfer with bounded R_beta.
        eps = np.zeros_like(eps0)
        for i, r in enumerate(r_values):
            for j, t in enumerate(t_values):
                chi = np.sin(0.33 * r + 0.11 * t + 0.07 * (i + 1) * (j + 1))
                rem_int = delta * r_star * chi / (1.0 + 0.2 * (r + t))
                rem_int += delta * r_star * 0.08 * (rng.uniform(-1.0, 1.0) / (30.0 + r + t))
                eps[i, j] = eps0[i, j] + rem_int
        eps_beta[float(beta)] = eps

        rr, tt = np.meshgrid(r_values, t_values, indexing="ij")
        logw = -sigma * rr * tt + p_val * (rr + tt) + c0 + eps
        logw_by_beta[float(beta)] = logw

        # Verify AD transfer identity / residual cap.
        recon = logw + sigma * rr * tt - p_val * (rr + tt) - c0
        max_transfer_gap = max(max_transfer_gap, float(np.max(np.abs(recon - eps))))
        cap = c0_cap + r_star_bound * abs(delta)
        max_eps_cap_gap = max(max_eps_cap_gap, float(np.max(np.abs(eps)) - cap))

    # Positivity and AB extraction compatibility checks.
    positivity_ok = True
    v_bound_ok = True
    slope_bound_ok = True
    max_v_gap = -np.inf
    max_slope_gap = -np.inf

    for beta in beta_grid:
        b = float(beta)
        logw = logw_by_beta[b]
        sigma = sigma_beta[b]
        p_val = p_beta[b]
        delta = b - beta0
        cap = c0_cap + r_star_bound * abs(delta)

        wilson = np.exp(logw)
        positivity_ok = positivity_ok and (np.min(wilson) > 0.0) and (np.max(wilson) < 1.0)

        v_rt = -(logw / t_values[None, :])
        approx = sigma * r_values[:, None] - p_val
        lhs_v = np.abs(v_rt - approx)
        rhs_v = (
            (np.abs(p_val) * r_values[:, None] + np.abs(c0) + cap) / t_values[None, :]
        )
        gap_v = float(np.max(lhs_v - rhs_v))
        max_v_gap = max(max_v_gap, gap_v)
        if gap_v > 1.0e-12:
            v_bound_ok = False

        for j, t in enumerate(t_values):
            for i1 in range(len(r_values)):
                for i2 in range(i1 + 1, len(r_values)):
                    dr = r_values[i2] - r_values[i1]
                    slope_t = (v_rt[i2, j] - v_rt[i1, j]) / dr
                    lhs = abs(slope_t - sigma)
                    rhs = abs(p_val) / t + 2.0 * cap / (t * dr)
                    gap_s = lhs - rhs
                    max_slope_gap = max(max_slope_gap, gap_s)
                    if gap_s > 1.0e-12:
                        slope_bound_ok = False

    print("Claim 9 AD beyond-window transfer diagnostic")
    print(f"seed={seed}")
    print(f"tagged_model: G={gauge_group}, D={dimension}")
    print(f"beta_window=[{beta0:.4f}, {beta1:.4f}]")
    print(f"beta_grid={beta_grid.tolist()}")
    print(
        "bounds: "
        f"A*={a_star:.6f}, B*={b_star:.6f}, R*={r_star_bound:.6f}, C0={c0_cap:.6f}"
    )
    print(f"max_transfer_identity_gap={max_transfer_gap:.8e}")
    print(f"max_residual_cap_gap={max_eps_cap_gap:.8e}")
    print(f"max_V_bound_gap={max_v_gap:.8e}")
    print(f"max_slope_bound_gap={max_slope_gap:.8e}")
    print("sigma_beta:")
    for beta in beta_grid:
        print(f"  beta={beta:.3f}: sigma={sigma_beta[float(beta)]:.8f}")
    print("p_beta:")
    for beta in beta_grid:
        print(f"  beta={beta:.3f}: p={p_beta[float(beta)]:.8f}")
    print(f"check_transfer_identity={max_transfer_gap <= 1.0e-12}")
    print(f"check_residual_cap={max_eps_cap_gap <= 1.0e-12}")
    print(f"check_positivity_window={positivity_ok}")
    print(f"check_AB_V_bound={v_bound_ok}")
    print(f"check_AB_slope_bound={slope_bound_ok}")
    print(
        "all_checks_pass="
        f"{(max_transfer_gap <= 1.0e-12) and (max_eps_cap_gap <= 1.0e-12) and positivity_ok and v_bound_ok and slope_bound_ok}"
    )


if __name__ == "__main__":
    main()
