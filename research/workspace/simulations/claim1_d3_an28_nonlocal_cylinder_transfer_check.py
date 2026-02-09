#!/usr/bin/env python3.12
"""AN-28 nonlocal-cylinder transfer diagnostics (two-block surrogate)."""

from __future__ import annotations

import math
from typing import Dict, List

import numpy as np


def integrate2_complex(values: np.ndarray, grid: np.ndarray) -> complex:
    real_part = np.trapezoid(np.trapezoid(np.real(values), grid, axis=1), grid, axis=0)
    imag_part = np.trapezoid(np.trapezoid(np.imag(values), grid, axis=1), grid, axis=0)
    return complex(real_part, imag_part)


def omega(weights: np.ndarray, observable: np.ndarray, grid: np.ndarray) -> complex:
    num = integrate2_complex(weights * observable, grid)
    den = integrate2_complex(weights, grid)
    return num / den


def bound_abs(weights: np.ndarray, observable_abs: np.ndarray, grid: np.ndarray) -> float:
    den_abs = abs(integrate2_complex(weights, grid))
    num_abs = np.trapezoid(
        np.trapezoid(np.abs(weights) * observable_abs, grid, axis=1), grid, axis=0
    )
    return float(num_abs / den_abs)


def chi_cutoff(radius_field: np.ndarray, radius: float) -> np.ndarray:
    return 1.0 / (1.0 + (radius_field / radius) ** 8)


def main() -> None:
    seed = 2026020911
    np.random.seed(seed)

    # Two-block surrogate parameters.
    mass_sq = 1.0
    lam = 0.7
    gamma = 0.16
    hbar = 1.2
    theta = -math.pi / 8.0
    eta_list = [0.40, 0.20, 0.10, 0.05, 0.02, 0.00]
    cutoff_radii = [1.4, 1.9, 2.5, 3.2]

    # Quadrature grid (kept moderate for low CPU).
    y_max = 4.8
    n_grid = 551
    y = np.linspace(-y_max, y_max, n_grid)
    y1, y2 = np.meshgrid(y, y, indexing="ij")
    y_norm = np.sqrt(y1**2 + y2**2)

    phase = np.exp(-1j * theta)
    jac = np.exp(-2j * theta)
    z1 = phase * y1
    z2 = phase * y2

    # Action and insertion channel (nonlocal via z1-z2 coupling).
    action = (
        0.5 * mass_sq * (z1**2 + z2**2)
        + 0.25 * lam * (z1**4 + z2**4)
        + gamma * z1 * z2
    )
    insertion_1 = mass_sq * z1 + lam * z1**3 + gamma * z2
    block_norm = np.sqrt(np.abs(z1) ** 2 + np.abs(z2) ** 2)

    # Two-block bounded observable/test.
    observable = np.tanh(z1) * np.tanh(0.9 * z2)
    psi = np.tanh(z1) * (1.0 + 0.25 * np.tanh(0.8 * z2))
    dpsi_dz1 = (1.0 / np.cosh(z1) ** 2) * (1.0 + 0.25 * np.tanh(0.8 * z2))

    denom_abs_list: List[float] = []
    observable_values: Dict[float, complex] = {}
    sd_residuals: Dict[float, float] = {}
    tail_bounds: Dict[float, List[float]] = {}
    cutoff_drifts: Dict[float, List[float]] = {}

    for eta in eta_list:
        c_param = complex(eta, -1.0 / hbar)
        weights = jac * np.exp(-c_param * action)

        den_abs = abs(integrate2_complex(weights, y))
        denom_abs_list.append(den_abs)

        observable_values[eta] = omega(weights, observable, y)
        lhs = omega(weights, dpsi_dz1, y)
        rhs = c_param * omega(weights, psi * insertion_1, y)
        sd_residuals[eta] = abs(lhs - rhs)

        per_radius_tail = []
        per_radius_drift = []
        for radius in cutoff_radii:
            tail = (block_norm > radius).astype(float)
            per_radius_tail.append(bound_abs(weights, np.abs(insertion_1) * tail, y))

            chi = chi_cutoff(y_norm, radius)
            psi_r = chi * psi
            dpsi_r = chi * dpsi_dz1
            drift_obs = abs(omega(weights, psi_r, y) - omega(weights, psi, y))
            drift_der = abs(omega(weights, dpsi_r, y) - omega(weights, dpsi_dz1, y))
            drift_ins = abs(
                omega(weights, psi_r * insertion_1, y)
                - omega(weights, psi * insertion_1, y)
            )
            per_radius_drift.append(max(drift_obs, drift_der, drift_ins))

        tail_bounds[eta] = per_radius_tail
        cutoff_drifts[eta] = per_radius_drift

    w0 = observable_values[0.0]
    de_reg_drift = {eta: abs(observable_values[eta] - w0) for eta in eta_list if eta > 0.0}

    min_den = min(denom_abs_list)
    tail_decay_ok = all(vals[-1] <= vals[0] for vals in tail_bounds.values())
    cutoff_decay_ok = all(vals[-1] <= vals[0] for vals in cutoff_drifts.values())
    sd_ok = max(sd_residuals.values()) < 5.0e-3
    dereg_ok = de_reg_drift[min(de_reg_drift.keys())] < 5.0e-3

    print("AN-28 nonlocal-cylinder transfer diagnostic")
    print(f"seed={seed}")
    print(
        "params: "
        f"mass_sq={mass_sq:.4f}, lambda={lam:.4f}, gamma={gamma:.4f}, "
        f"h={hbar:.4f}, theta={theta:.6f}, y_max={y_max:.2f}, n_grid={n_grid}"
    )
    print(f"eta_grid={eta_list}")
    print(f"cutoff_radii={cutoff_radii}")
    print(f"min_abs_denominator={min_den:.8e}")

    print("observable_de_regularization_drift_to_eta0:")
    for eta in sorted(de_reg_drift.keys(), reverse=True):
        print(f"  eta={eta:.2f}: drift={de_reg_drift[eta]:.8e}")

    print("full_test_sd_residuals:")
    for eta in eta_list:
        print(f"  eta={eta:.2f}: residual={sd_residuals[eta]:.8e}")

    print("tail_insertion_majorant_by_eta:")
    for eta in eta_list:
        vals = ", ".join(f"{v:.6e}" for v in tail_bounds[eta])
        print(f"  eta={eta:.2f}: [{vals}]")

    print("cutoff_approximant_drift_by_eta:")
    for eta in eta_list:
        vals = ", ".join(f"{v:.6e}" for v in cutoff_drifts[eta])
        print(f"  eta={eta:.2f}: [{vals}]")

    print(f"check_min_denominator_positive={min_den > 1.0e-4}")
    print(f"check_tail_majorant_decay={tail_decay_ok}")
    print(f"check_cutoff_approximant_decay={cutoff_decay_ok}")
    print(f"check_full_sd_residual_small={sd_ok}")
    print(f"check_de_regularization_drift_small={dereg_ok}")
    print(
        "all_checks_pass="
        f"{(min_den > 1.0e-4) and tail_decay_ok and cutoff_decay_ok and sd_ok and dereg_ok}"
    )


if __name__ == "__main__":
    main()
