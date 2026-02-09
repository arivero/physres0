#!/usr/bin/env python3.12
"""Claim 9 non-Abelian area-law -> linear-potential scoped theorem check."""

from __future__ import annotations

import numpy as np


def fit_line(x: np.ndarray, y: np.ndarray) -> tuple[float, float]:
    a, b = np.polyfit(x, y, 1)
    return float(a), float(b)


def main() -> None:
    seed = 2026020914
    rng = np.random.default_rng(seed)

    # Explicit (G,D) tags for this executable proxy.
    gauge_group = "SU(3)"
    dimension = 4

    sigma_true = 0.42
    perimeter_coeff = 0.16
    constant_term = 0.40
    remainder_cap = 0.08

    r_values = np.array([1.0, 1.5, 2.0, 2.5, 3.0])
    t_values = np.array([8.0, 10.0, 12.0, 16.0, 20.0, 28.0])

    # Synthetic scoped-theorem model:
    # log W(r,T) = -(sigma r T) + perimeter*(r+T) + c + eps(r,T),
    # with |eps(r,T)| <= remainder_cap.
    logw = np.zeros((len(r_values), len(t_values)))
    eps = np.zeros((len(r_values), len(t_values)))
    for i, r in enumerate(r_values):
        for j, t in enumerate(t_values):
            oscillatory = np.sin(0.7 * r + 0.23 * t + 0.31 * (i + 1) * (j + 1))
            bounded_eps = remainder_cap * oscillatory / (1.0 + 0.18 * t)
            eps[i, j] = bounded_eps
            logw[i, j] = (
                -sigma_true * r * t
                + perimeter_coeff * (r + t)
                + constant_term
                + bounded_eps
            )

    v_rt = -(logw / t_values[None, :])
    v_large_t = np.mean(v_rt[:, -3:], axis=1)
    slope_fit, intercept_fit = fit_line(r_values, v_large_t)

    # Recover sigma by T->infinity extrapolation of slope(T) against 1/T.
    slope_by_t = np.array([fit_line(r_values, v_rt[:, j])[0] for j in range(len(t_values))])
    inv_t = 1.0 / t_values
    slope_inv_coeff, sigma_extrapolated = fit_line(inv_t, slope_by_t)
    rel_err_sigma = abs(sigma_extrapolated - sigma_true) / sigma_true

    # Theorem-bound checks from explicit remainder bookkeeping.
    # |V - (sigma*r - perimeter)| <= (|perimeter|*r + |c| + remainder_cap)/T
    approx = sigma_true * r_values[:, None] - perimeter_coeff
    lhs_v = np.abs(v_rt - approx)
    rhs_v = (
        (abs(perimeter_coeff) * r_values[:, None] + abs(constant_term) + remainder_cap)
        / t_values[None, :]
    )
    max_v_bound_gap = np.max(lhs_v - rhs_v)

    # Pairwise slope estimator:
    # |slope_T(r1,r2) - sigma| <= |perimeter|/T + 2*remainder_cap/(T*|r2-r1|)
    max_slope_bound_gap = -np.inf
    for j, t in enumerate(t_values):
        for i1 in range(len(r_values)):
            for i2 in range(i1 + 1, len(r_values)):
                dr = r_values[i2] - r_values[i1]
                slope_t = (v_rt[i2, j] - v_rt[i1, j]) / dr
                lhs = abs(slope_t - sigma_true)
                rhs = abs(perimeter_coeff) / t + 2.0 * remainder_cap / (t * dr)
                max_slope_bound_gap = max(max_slope_bound_gap, lhs - rhs)

    # Stabilization check across last three time slices.
    stabilization = np.max(np.abs(v_rt[:, -1] - v_rt[:, -3]))
    wilson = np.exp(logw)
    min_wilson = np.min(wilson)
    max_wilson = np.max(wilson)

    print("Claim 9 non-Abelian area-law scoped-theorem diagnostic")
    print(f"seed={seed}")
    print(f"tagged_model: G={gauge_group}, D={dimension}")
    print(
        "params: "
        f"sigma_true={sigma_true:.6f}, perimeter={perimeter_coeff:.6f}, "
        f"constant={constant_term:.6f}, remainder_cap={remainder_cap:.2e}"
    )
    print(f"r_grid={r_values.tolist()}")
    print(f"T_grid={t_values.tolist()}")
    print(f"wilson_range=[{min_wilson:.6e}, {max_wilson:.6e}]")
    print("V(r;T) sample rows:")
    for i, r in enumerate(r_values):
        vals = ", ".join(f"{v:.6f}" for v in v_rt[i, :])
        print(f"  r={r:.2f}: [{vals}]")

    print(f"fit_sigma_from_largeT_window={slope_fit:.8f}")
    print(f"fit_intercept_from_largeT={intercept_fit:.8f}")
    print("slope_by_T:")
    for t, s in zip(t_values, slope_by_t):
        print(f"  T={t:.1f}: slope={s:.8f}")
    print(f"slope_vs_invT_coeff={slope_inv_coeff:.8f}")
    print(f"sigma_extrapolated_T_to_inf={sigma_extrapolated:.8f}")
    print(f"relative_error_sigma={rel_err_sigma:.8e}")
    print(f"largeT_stabilization_max_abs={stabilization:.8e}")
    print(f"max_V_bound_gap={max_v_bound_gap:.8e}")
    print(f"max_slope_bound_gap={max_slope_bound_gap:.8e}")

    sigma_ok = rel_err_sigma < 2.0e-2
    stabilization_ok = stabilization < 6.0e-2
    wilson_ok = min_wilson > 0.0 and max_wilson < 1.0
    theorem_v_ok = max_v_bound_gap <= 1.0e-12
    theorem_slope_ok = max_slope_bound_gap <= 1.0e-12
    print(f"check_sigma_recovery={sigma_ok}")
    print(f"check_largeT_stabilization={stabilization_ok}")
    print(f"check_wilson_in_0_1={wilson_ok}")
    print(f"check_theorem_bound_V={theorem_v_ok}")
    print(f"check_theorem_bound_slope={theorem_slope_ok}")
    print(
        "all_checks_pass="
        f"{sigma_ok and stabilization_ok and wilson_ok and theorem_v_ok and theorem_slope_ok}"
    )


if __name__ == "__main__":
    main()
