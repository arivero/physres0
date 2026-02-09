#!/usr/bin/env python3.12
"""Claim 9 non-Abelian area-law -> linear-potential extraction check."""

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

    sigma_true = 0.37
    perimeter_coeff = 0.21
    constant_term = 0.5
    noise_scale = 2.0e-3

    r_values = np.array([1.0, 1.5, 2.0, 2.5, 3.0])
    t_values = np.array([6.0, 8.0, 10.0, 12.0, 16.0, 20.0])

    # Synthetic Wilson-loop log model:
    # log W(r,T) = -(sigma r T) + perimeter*(r+T) + c + noise.
    # Then V(r;T) = -(1/T) log W = sigma*r - perimeter - c/T + O(noise/T).
    logw = np.zeros((len(r_values), len(t_values)))
    for i, r in enumerate(r_values):
        for j, t in enumerate(t_values):
            noise = rng.normal(0.0, noise_scale)
            logw[i, j] = -sigma_true * r * t + perimeter_coeff * (r + t) + constant_term + noise

    v_rt = -(logw / t_values[None, :])
    v_large_t = np.mean(v_rt[:, -3:], axis=1)
    slope_fit, intercept_fit = fit_line(r_values, v_large_t)

    # Recover sigma by T->infinity extrapolation of slope(T) against 1/T.
    slope_by_t = np.array([fit_line(r_values, v_rt[:, j])[0] for j in range(len(t_values))])
    inv_t = 1.0 / t_values
    slope_inv_coeff, sigma_extrapolated = fit_line(inv_t, slope_by_t)
    rel_err_sigma = abs(sigma_extrapolated - sigma_true) / sigma_true

    # Stabilization check across last three time slices.
    stabilization = np.max(np.abs(v_rt[:, -1] - v_rt[:, -3]))

    print("Claim 9 non-Abelian area-law extraction diagnostic")
    print(f"seed={seed}")
    print(f"tagged_model: G={gauge_group}, D={dimension}")
    print(
        "params: "
        f"sigma_true={sigma_true:.6f}, perimeter={perimeter_coeff:.6f}, "
        f"constant={constant_term:.6f}, noise_scale={noise_scale:.2e}"
    )
    print(f"r_grid={r_values.tolist()}")
    print(f"T_grid={t_values.tolist()}")
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

    sigma_ok = rel_err_sigma < 2.0e-2
    stabilization_ok = stabilization < 6.0e-2
    print(f"check_sigma_recovery={sigma_ok}")
    print(f"check_largeT_stabilization={stabilization_ok}")
    print(f"all_checks_pass={sigma_ok and stabilization_ok}")


if __name__ == "__main__":
    main()
