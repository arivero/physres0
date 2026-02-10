#!/usr/bin/env python3.12
"""AN-33 graph-decay nonlocal weighted-local closure diagnostics."""

from __future__ import annotations

from itertools import combinations

import numpy as np


def tail_sum(weights: np.ndarray, n: int) -> float:
    return float(np.sum(weights[n:]))


def build_graph_decay_kernel(weights: np.ndarray, lam: float) -> np.ndarray:
    idx = np.arange(len(weights), dtype=float)
    dist = np.abs(idx[:, None] - idx[None, :])
    # Column-weighted kernel so column envelopes naturally scale with weights.
    return np.exp(-lam * dist) * (weights[None, :] / np.maximum(weights[:, None], 1.0e-14))


def weighted_l1(weights: np.ndarray, vec: np.ndarray) -> float:
    return float(np.sum(weights * np.abs(vec)))


def main() -> None:
    seed = 2026021003
    rng = np.random.default_rng(seed)

    num_blocks = 84
    levels = np.arange(8, 57)
    eta_grid = [0.30, 0.15, 0.08, 0.04, 0.02, 0.00]
    kappa_grid = [0.00, 0.10, 0.20]
    hbar = 1.25
    c_eta = complex(0.18, -1.0 / hbar)

    idx = np.arange(1, num_blocks + 1, dtype=float)
    weights = 0.63**idx + 0.018 / (idx**2)
    w_tail = np.array([tail_sum(weights, int(level)) for level in levels])

    # Weighted-local coefficients.
    alpha = 0.78 * weights * (1.0 + 0.04 * np.sin(0.31 * idx))
    beta = 0.66 * weights * (1.0 + 0.03 * np.cos(0.27 * idx))

    # Graph-decay nonlocal kernels.
    k_f = build_graph_decay_kernel(weights, lam=0.55)
    k_psi = build_graph_decay_kernel(weights, lam=0.48)

    # Column envelope constants from AN-33 assumptions.
    col_f = np.array([np.sum(np.abs(alpha) * np.abs(k_f[:, j])) for j in range(num_blocks)])
    col_psi = np.array([np.sum(np.abs(beta) * np.abs(k_psi[:, j])) for j in range(num_blocks)])
    c_gd_f = float(np.max(col_f / weights))
    c_gd_psi = float(np.max(col_psi / weights))

    # Check graph-decay operator inequality by randomized test vectors.
    op_f_ok = True
    op_psi_ok = True
    op_f_gap = 0.0
    op_psi_gap = 0.0
    for _ in range(64):
        x = rng.normal(size=num_blocks)
        lhs_f = float(np.sum(np.abs(alpha) * np.abs(k_f @ x)))
        rhs_f = c_gd_f * weighted_l1(weights, x)
        lhs_psi = float(np.sum(np.abs(beta) * np.abs(k_psi @ x)))
        rhs_psi = c_gd_psi * weighted_l1(weights, x)
        op_f_gap = max(op_f_gap, lhs_f - rhs_f)
        op_psi_gap = max(op_psi_gap, lhs_psi - rhs_psi)
        if lhs_f > rhs_f + 1.0e-10:
            op_f_ok = False
        if lhs_psi > rhs_psi + 1.0e-10:
            op_psi_ok = False

    # Truncation-tail checks from weighted-local tails.
    local_profile = 0.60 + 0.20 * np.sin(0.12 * idx)
    m_local = float(np.max(np.abs(local_profile)))
    tail_ok = True
    tail_gap = 0.0
    tail_values: list[tuple[int, float]] = []
    for r in levels:
        r_int = int(r)
        chi = np.zeros(num_blocks)
        chi[:r_int] = 1.0
        lhs = float(np.sum((1.0 - chi) * weights * np.abs(local_profile)))
        rhs = m_local * float(np.sum((1.0 - chi) * weights))
        tail_values.append((r_int, lhs))
        tail_gap = max(tail_gap, lhs - rhs)
        if lhs > rhs + 1.0e-12:
            tail_ok = False
    tail_monotone = all(
        tail_values[i + 1][1] <= tail_values[i][1] + 1.0e-12 for i in range(len(tail_values) - 1)
    )
    tail_small = tail_values[-1][1] < 3.5e-4

    # Exhaustion denominator/numerator channels with explicit rates.
    d_inf = complex(1.72, 0.23)
    d_coeff = complex(0.11, -0.05)
    a_d = abs(d_coeff)

    n_f_inf = complex(0.91, 0.18)
    n_f_coeff = complex(0.16, 0.07)
    a_f = abs(n_f_coeff)

    n_ins_inf = complex(0.52, -0.11)
    n_ins_coeff = complex(0.08, 0.03)
    a_ins = abs(n_ins_coeff)

    sd_coeff = complex(0.05, 0.02)
    n_deriv_inf = c_eta * n_ins_inf
    n_deriv_coeff = c_eta * n_ins_coeff + sd_coeff
    a_deriv = abs(n_deriv_coeff)

    ratio_data: dict[tuple[float, float], dict[str, dict[int, complex]]] = {}
    min_abs_den = float("inf")
    for eta in eta_grid:
        for kappa in kappa_grid:
            key = (eta, kappa)
            d_seq: dict[int, complex] = {}
            rf_seq: dict[int, complex] = {}
            rd_seq: dict[int, complex] = {}
            ri_seq: dict[int, complex] = {}
            for n in levels:
                n_int = int(n)
                wn = tail_sum(weights, n_int)

                # Mild parameter modulation while preserving rate constants.
                phase = complex(1.0 + 0.05 * kappa, 0.03 * eta)
                d_n = d_inf + d_coeff * wn + 0.01 * phase * wn
                n_f = n_f_inf + n_f_coeff * wn + 0.015 * phase * wn
                n_ins = n_ins_inf + n_ins_coeff * wn + 0.01 * phase * wn
                n_deriv = n_deriv_inf + n_deriv_coeff * wn + 0.01 * phase * wn

                d_seq[n_int] = d_n
                rf_seq[n_int] = n_f / d_n
                rd_seq[n_int] = n_deriv / d_n
                ri_seq[n_int] = n_ins / d_n
                min_abs_den = min(min_abs_den, abs(d_n))

            ratio_data[key] = {
                "D": d_seq,
                "R_F": rf_seq,
                "R_D": rd_seq,
                "R_I": ri_seq,
            }

    d0 = 1.20
    den_floor_ok = min_abs_den >= d0

    # Conservative denominator/numerator rate constants for bounds.
    a_d_eff = abs(d_coeff) + 0.02
    a_f_eff = abs(n_f_coeff) + 0.02
    a_deriv_eff = abs(n_deriv_coeff) + 0.02
    a_ins_eff = abs(n_ins_coeff) + 0.02

    b_f = abs(n_f_inf) + abs(n_f_coeff) * float(w_tail[0]) + 0.05
    b_deriv = abs(n_deriv_inf) + abs(n_deriv_coeff) * float(w_tail[0]) + 0.05
    b_ins = abs(n_ins_inf) + abs(n_ins_coeff) * float(w_tail[0]) + 0.05

    ratio_ok = True
    worst_ratio_gap = 0.0
    for key, data in ratio_data.items():
        d_seq = data["D"]
        for n, m in combinations(levels.tolist(), 2):
            n_int = int(n)
            m_int = int(m)
            wn = tail_sum(weights, n_int)
            wm = tail_sum(weights, m_int)
            tail_pair = wn + wm

            for channel, (a_x, b_x) in {
                "R_F": (a_f_eff, b_f),
                "R_D": (a_deriv_eff, b_deriv),
                "R_I": (a_ins_eff, b_ins),
            }.items():
                lhs = abs(data[channel][n_int] - data[channel][m_int])
                rhs = (a_x / d0 + b_x * a_d_eff / (d0 * d0)) * tail_pair
                gap = lhs - rhs
                worst_ratio_gap = max(worst_ratio_gap, gap)
                if gap > 1.0e-9:
                    ratio_ok = False

    # Nonlocal SD residual stabilization profile.
    sd_ok = True
    sd_profiles: dict[tuple[float, float], list[tuple[int, float]]] = {}
    for key, data in ratio_data.items():
        residuals = {n: abs(data["R_D"][n] - c_eta * data["R_I"][n]) for n in data["R_D"]}
        levels_list = sorted(residuals)
        profile: list[tuple[int, float]] = []
        for start in range(len(levels_list)):
            active = levels_list[start:]
            if len(active) < 2:
                continue
            max_abs = max(residuals[level] for level in active)
            profile.append((active[0], max_abs))
        sd_profiles[key] = profile
        vals = [v for _, v in profile]
        if any(vals[i + 1] > vals[i] + 1.0e-12 for i in range(len(vals) - 1)):
            sd_ok = False
        if vals and vals[-1] > 4.0e-4:
            sd_ok = False

    print("AN-33 graph-decay nonlocal weighted-local diagnostic")
    print(f"seed={seed}")
    print(f"num_blocks={num_blocks}")
    print(f"levels=[{int(levels[0])},...,{int(levels[-1])}]")
    print(f"eta_grid={eta_grid}")
    print(f"kappa_grid={kappa_grid}")
    print(f"min_abs_denominator={min_abs_den:.8f}")
    print(f"c_gd_f={c_gd_f:.8f}")
    print(f"c_gd_psi={c_gd_psi:.8f}")
    print(f"tail_last={tail_values[-1][1]:.8e}")
    print(f"worst_operator_gap_f={op_f_gap:.3e}")
    print(f"worst_operator_gap_psi={op_psi_gap:.3e}")
    print(f"worst_tail_gap={tail_gap:.3e}")
    print(f"worst_ratio_gap={worst_ratio_gap:.3e}")

    print("sd_tail_profiles:")
    for key in sorted(sd_profiles):
        eta, kappa = key
        prof = sd_profiles[key]
        stride = max(1, len(prof) // 6)
        body = ", ".join(f"n>={n}: {v:.6e}" for n, v in prof[::stride])
        print(f"  eta={eta:.2f}, kappa={kappa:.2f}: {body}")

    print(f"check_graph_decay_operator_f={op_f_ok}")
    print(f"check_graph_decay_operator_psi={op_psi_ok}")
    print(f"check_tail_bound={tail_ok}")
    print(f"check_tail_monotone={tail_monotone}")
    print(f"check_tail_small={tail_small}")
    print(f"check_denominator_floor={den_floor_ok}")
    print(f"check_ratio_denominator_rate_bound={ratio_ok}")
    print(f"check_nonlocal_sd_residual_stabilization={sd_ok}")
    print(
        "all_checks_pass="
        f"{op_f_ok and op_psi_ok and tail_ok and tail_monotone and tail_small and den_floor_ok and ratio_ok and sd_ok}"
    )


if __name__ == "__main__":
    main()
