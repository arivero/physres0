#!/usr/bin/env python3.12
"""AN-34 first-principles shell-tail to ratio-rate diagnostics."""

from __future__ import annotations

from itertools import combinations

import numpy as np


def tail_sum(weights: np.ndarray, n: int) -> float:
    return float(np.sum(weights[n:]))


def main() -> None:
    seed = 2026021004
    rng = np.random.default_rng(seed)

    num_shells = 140
    levels = np.arange(10, 81)
    eta_grid = [0.30, 0.15, 0.08, 0.04, 0.02, 0.00]
    kappa_grid = [0.00, 0.10, 0.20]
    hbar = 1.27
    c_eta = complex(0.17, -1.0 / hbar)

    idx = np.arange(1, num_shells + 1, dtype=float)
    sigma = 0.67**idx + 0.014 / (idx**2)
    w_tail = np.array([tail_sum(sigma, int(level)) for level in levels])

    c_d = 0.31
    c_f = 0.42
    c_ins = 0.27
    c_der = 0.36

    d_inf = complex(1.73, 0.21)
    n_f_inf = complex(0.95, 0.16)
    n_ins_inf = complex(0.47, -0.09)
    n_der_inf = c_eta * n_ins_inf

    # Shell increments with explicit envelope bounds.
    phase_d = np.exp(1j * (0.11 * idx))
    phase_f = np.exp(1j * (0.07 * idx + 0.3))
    phase_ins = np.exp(1j * (0.09 * idx + 0.2))
    phase_der = np.exp(1j * (0.08 * idx + 0.4))

    delta_d = 0.78 * c_d * sigma * phase_d
    delta_f = 0.73 * c_f * sigma * phase_f
    delta_ins = 0.69 * c_ins * sigma * phase_ins
    delta_der = 0.71 * c_der * sigma * phase_der

    # Reverse cumulative tails: sum_{j>=n} delta_j
    tail_d = np.flip(np.cumsum(np.flip(delta_d)))
    tail_f = np.flip(np.cumsum(np.flip(delta_f)))
    tail_ins = np.flip(np.cumsum(np.flip(delta_ins)))
    tail_der = np.flip(np.cumsum(np.flip(delta_der)))

    # Base one-sided shell-tail checks against first-principles constants.
    one_sided_ok = True
    worst_one_sided_gap = 0.0
    for n in levels:
        n_int = int(n)
        wn = tail_sum(sigma, n_int)
        for val, const in (
            (tail_d[n_int], c_d),
            (tail_f[n_int], c_f),
            (tail_ins[n_int], c_ins),
            (tail_der[n_int], c_der),
        ):
            gap = abs(val) - const * wn
            worst_one_sided_gap = max(worst_one_sided_gap, gap)
            if gap > 1.0e-10:
                one_sided_ok = False

    # Build parameter-dependent channels, preserving same tail constants.
    channels: dict[tuple[float, float], dict[str, dict[int, complex]]] = {}
    min_abs_den = float("inf")
    for eta in eta_grid:
        for kappa in kappa_grid:
            key = (eta, kappa)
            phase_mod = complex(1.0 + 0.03 * kappa, 0.02 * eta)
            d_seq: dict[int, complex] = {}
            rf_seq: dict[int, complex] = {}
            rd_seq: dict[int, complex] = {}
            ri_seq: dict[int, complex] = {}
            n_f_seq: dict[int, complex] = {}
            n_der_seq: dict[int, complex] = {}
            n_ins_seq: dict[int, complex] = {}
            for n in levels:
                n_int = int(n)
                wn = tail_sum(sigma, n_int)
                d_n = d_inf + tail_d[n_int] + 0.01 * phase_mod * wn
                n_f = n_f_inf + tail_f[n_int] + 0.012 * phase_mod * wn
                n_ins = n_ins_inf + tail_ins[n_int] + 0.008 * phase_mod * wn
                n_der = n_der_inf + tail_der[n_int] + 0.009 * phase_mod * wn

                d_seq[n_int] = d_n
                n_f_seq[n_int] = n_f
                n_der_seq[n_int] = n_der
                n_ins_seq[n_int] = n_ins
                rf_seq[n_int] = n_f / d_n
                rd_seq[n_int] = n_der / d_n
                ri_seq[n_int] = n_ins / d_n
                min_abs_den = min(min_abs_den, abs(d_n))

            channels[key] = {
                "D": d_seq,
                "N_F": n_f_seq,
                "N_D": n_der_seq,
                "N_I": n_ins_seq,
                "R_F": rf_seq,
                "R_D": rd_seq,
                "R_I": ri_seq,
            }

    d0 = 1.20
    den_floor_ok = min_abs_den >= d0

    # Effective constants include tiny parametric modulation terms.
    c_d_eff = c_d + 0.02
    c_f_eff = c_f + 0.02
    c_der_eff = c_der + 0.02
    c_ins_eff = c_ins + 0.02

    b_f = abs(n_f_inf) + c_f_eff * float(w_tail[0]) + 0.05
    b_der = abs(n_der_inf) + c_der_eff * float(w_tail[0]) + 0.05
    b_ins = abs(n_ins_inf) + c_ins_eff * float(w_tail[0]) + 0.05

    # Pairwise first-principles rate checks for numerator/denominator.
    pairwise_rate_ok = True
    worst_pairwise_gap = 0.0
    for key, data in channels.items():
        for n, m in combinations(levels.tolist(), 2):
            n_int = int(n)
            m_int = int(m)
            tail_pair = tail_sum(sigma, n_int) + tail_sum(sigma, m_int)
            for name, const in (
                ("D", c_d_eff),
                ("N_F", c_f_eff),
                ("N_D", c_der_eff),
                ("N_I", c_ins_eff),
            ):
                lhs = abs(data[name][n_int] - data[name][m_int])
                rhs = const * tail_pair
                gap = lhs - rhs
                worst_pairwise_gap = max(worst_pairwise_gap, gap)
                if gap > 1.0e-9:
                    pairwise_rate_ok = False

    # Normalized ratio bound using first-principles constants.
    ratio_ok = True
    worst_ratio_gap = 0.0
    for key, data in channels.items():
        for n, m in combinations(levels.tolist(), 2):
            n_int = int(n)
            m_int = int(m)
            tail_pair = tail_sum(sigma, n_int) + tail_sum(sigma, m_int)
            for channel, (c_x, b_x) in {
                "R_F": (c_f_eff, b_f),
                "R_D": (c_der_eff, b_der),
                "R_I": (c_ins_eff, b_ins),
            }.items():
                lhs = abs(data[channel][n_int] - data[channel][m_int])
                rhs = (c_x / d0 + b_x * c_d_eff / (d0 * d0)) * tail_pair
                gap = lhs - rhs
                worst_ratio_gap = max(worst_ratio_gap, gap)
                if gap > 1.0e-9:
                    ratio_ok = False

    # SD residual stabilization along exhaustion levels.
    sd_ok = True
    sd_profiles: dict[tuple[float, float], list[tuple[int, float]]] = {}
    for key, data in channels.items():
        residuals = {n: abs(data["R_D"][n] - c_eta * data["R_I"][n]) for n in data["R_D"]}
        level_list = sorted(residuals)
        profile: list[tuple[int, float]] = []
        for start in range(len(level_list)):
            active = level_list[start:]
            if len(active) < 2:
                continue
            max_abs = max(residuals[k] for k in active)
            profile.append((active[0], max_abs))
        sd_profiles[key] = profile
        vals = [v for _, v in profile]
        if any(vals[i + 1] > vals[i] + 1.0e-12 for i in range(len(vals) - 1)):
            sd_ok = False
        if vals and vals[-1] > 6.0e-4:
            sd_ok = False

    tail_monotone = bool(np.all(np.diff(w_tail) <= 1.0e-12))
    tail_small = bool(w_tail[-1] < 3.0e-4)

    print("AN-34 first-principles tail-rate diagnostic")
    print(f"seed={seed}")
    print(f"num_shells={num_shells}")
    print(f"levels=[{int(levels[0])},...,{int(levels[-1])}]")
    print(f"eta_grid={eta_grid}")
    print(f"kappa_grid={kappa_grid}")
    print(f"tail_first={w_tail[0]:.8e}")
    print(f"tail_last={w_tail[-1]:.8e}")
    print(f"min_abs_denominator={min_abs_den:.8f}")
    print(f"worst_one_sided_gap={worst_one_sided_gap:.3e}")
    print(f"worst_pairwise_gap={worst_pairwise_gap:.3e}")
    print(f"worst_ratio_gap={worst_ratio_gap:.3e}")

    print("sd_tail_profiles:")
    for key in sorted(sd_profiles):
        eta, kappa = key
        prof = sd_profiles[key]
        stride = max(1, len(prof) // 6)
        body = ", ".join(f"n>={n}: {v:.6e}" for n, v in prof[::stride])
        print(f"  eta={eta:.2f}, kappa={kappa:.2f}: {body}")

    print(f"check_one_sided_tail_bounds={one_sided_ok}")
    print(f"check_pairwise_tail_rates={pairwise_rate_ok}")
    print(f"check_denominator_floor={den_floor_ok}")
    print(f"check_ratio_from_first_principles={ratio_ok}")
    print(f"check_tail_monotone={tail_monotone}")
    print(f"check_tail_small={tail_small}")
    print(f"check_sd_residual_stabilization={sd_ok}")
    print(
        "all_checks_pass="
        f"{one_sided_ok and pairwise_rate_ok and den_floor_ok and ratio_ok and tail_monotone and tail_small and sd_ok}"
    )


if __name__ == "__main__":
    main()
