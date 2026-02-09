#!/usr/bin/env python3.12
"""AN-27 oscillatory/de-regularized local-class transfer diagnostics.

This is a low-dimensional contour-rotation surrogate used to check:
1) denominator non-vanishing across eta in [0, eta_max],
2) de-regularization stabilization for a bounded local observable,
3) insertion-tail bound decay with cutoff radius,
4) Schwinger-Dyson residual behavior for bounded C_b^1 tests.
"""

from __future__ import annotations

import math
from typing import Dict, List

import numpy as np


def contour_data(y: np.ndarray, theta: float) -> np.ndarray:
    return np.exp(-1j * theta) * y


def action(z: np.ndarray, mass_sq: float, lam: float) -> np.ndarray:
    return 0.5 * mass_sq * z**2 + 0.25 * lam * z**4


def insertion(z: np.ndarray, mass_sq: float, lam: float) -> np.ndarray:
    return mass_sq * z + lam * z**3


def chi_cutoff(y: np.ndarray, radius: float) -> np.ndarray:
    # Real-line cutoff surrogate (smooth, bounded, radius-controlled).
    return 1.0 / (1.0 + (y / radius) ** 8)


def integrate_complex(values: np.ndarray, grid: np.ndarray) -> complex:
    real_part = np.trapezoid(np.real(values), grid)
    imag_part = np.trapezoid(np.imag(values), grid)
    return complex(real_part, imag_part)


def omega(
    z: np.ndarray,
    y: np.ndarray,
    jac: complex,
    c_param: complex,
    s_val: np.ndarray,
    g_val: np.ndarray,
) -> complex:
    weights = jac * np.exp(-c_param * s_val)
    numerator = integrate_complex(weights * g_val, y)
    denominator = integrate_complex(weights, y)
    return numerator / denominator


def abs_bound(
    z: np.ndarray,
    y: np.ndarray,
    jac: complex,
    c_param: complex,
    s_val: np.ndarray,
    g_abs: np.ndarray,
) -> float:
    weights = jac * np.exp(-c_param * s_val)
    denominator = abs(integrate_complex(weights, y))
    majorant = np.trapezoid(np.abs(weights) * g_abs, y)
    return float(majorant / denominator)


def main() -> None:
    seed = 20260209
    np.random.seed(seed)

    # Model/branch window.
    mass_sq = 1.1
    lam = 0.9
    hbar = 1.3
    theta = -math.pi / 8.0
    eta_list = [0.40, 0.20, 0.10, 0.05, 0.02, 0.00]
    radius_list = [1.3, 1.8, 2.4, 3.0]

    # Light but stable integration grid.
    y_max = 8.0
    n_grid = 12001
    y = np.linspace(-y_max, y_max, n_grid)
    z = contour_data(y, theta)
    jac = np.exp(-1j * theta)

    s_val = action(z, mass_sq, lam)
    d_val = insertion(z, mass_sq, lam)

    # Bounded observable/test probes.
    f_val = np.tanh(z)
    psi_val = np.tanh(z)
    dpsi_val = 1.0 / np.cosh(z) ** 2

    z_abs = np.abs(z)

    # Denominator non-vanishing and de-regularization stabilization.
    z_abs_list: List[float] = []
    f_values: Dict[float, complex] = {}
    full_sd_residuals: Dict[float, float] = {}

    for eta in eta_list:
        c_param = complex(eta, -1.0 / hbar)
        weights = jac * np.exp(-c_param * s_val)
        denom = integrate_complex(weights, y)
        z_abs_list.append(abs(denom))

        f_values[eta] = omega(z, y, jac, c_param, s_val, f_val)
        lhs = omega(z, y, jac, c_param, s_val, dpsi_val)
        rhs = c_param * omega(z, y, jac, c_param, s_val, psi_val * d_val)
        full_sd_residuals[eta] = abs(lhs - rhs)

    w0 = f_values[0.0]
    de_reg_drifts = {eta: abs(f_values[eta] - w0) for eta in eta_list if eta > 0.0}

    # Tail insertion majorant decay.
    tail_bounds_by_eta: Dict[float, List[float]] = {}
    for eta in eta_list:
        c_param = complex(eta, -1.0 / hbar)
        per_radius = []
        for radius in radius_list:
            tail = (z_abs > radius).astype(float)
            g_abs = np.abs(d_val) * tail
            per_radius.append(abs_bound(z, y, jac, c_param, s_val, g_abs))
        tail_bounds_by_eta[eta] = per_radius

    # C_b^1 cutoff-approximant convergence diagnostics.
    cutoff_drift_by_eta: Dict[float, List[float]] = {}
    for eta in eta_list:
        c_param = complex(eta, -1.0 / hbar)
        drifts = []
        for radius in radius_list:
            chi = chi_cutoff(y, radius)
            psi_r = chi * psi_val
            dpsi_r = chi * dpsi_val
            drift_obs = abs(
                omega(z, y, jac, c_param, s_val, psi_r)
                - omega(z, y, jac, c_param, s_val, psi_val)
            )
            drift_der = abs(
                omega(z, y, jac, c_param, s_val, dpsi_r)
                - omega(z, y, jac, c_param, s_val, dpsi_val)
            )
            drift_ins = abs(
                omega(z, y, jac, c_param, s_val, psi_r * d_val)
                - omega(z, y, jac, c_param, s_val, psi_val * d_val)
            )
            drifts.append(max(drift_obs, drift_der, drift_ins))
        cutoff_drift_by_eta[eta] = drifts

    # Simple pass/fail signals.
    min_denom = min(z_abs_list)
    tail_decay_ok = True
    for eta in eta_list:
        vals = tail_bounds_by_eta[eta]
        if vals[-1] > vals[0]:
            tail_decay_ok = False
            break
    cutoff_decay_ok = True
    for eta in eta_list:
        vals = cutoff_drift_by_eta[eta]
        if vals[-1] > vals[0]:
            cutoff_decay_ok = False
            break
    sd_small_ok = max(full_sd_residuals.values()) < 2.5e-2
    de_reg_ok = de_reg_drifts[min(de_reg_drifts.keys())] < 8.0e-3

    print("AN-27 oscillatory/de-regularized transfer diagnostic")
    print(f"seed={seed}")
    print(
        f"params: mass_sq={mass_sq:.4f}, lambda={lam:.4f}, h={hbar:.4f}, "
        f"theta={theta:.6f}, y_max={y_max:.2f}, n_grid={n_grid}"
    )
    print(f"eta_grid={eta_list}")
    print(f"radius_grid={radius_list}")
    print(f"min_abs_denominator={min_denom:.8e}")
    print("observable_de_regularization_drift_to_eta0:")
    for eta in sorted(de_reg_drifts.keys(), reverse=True):
        print(f"  eta={eta:.2f}: drift={de_reg_drifts[eta]:.8e}")
    print("full_test_sd_residuals:")
    for eta in eta_list:
        print(f"  eta={eta:.2f}: residual={full_sd_residuals[eta]:.8e}")
    print("tail_insertion_majorant_by_eta:")
    for eta in eta_list:
        vals = ", ".join(f"{v:.6e}" for v in tail_bounds_by_eta[eta])
        print(f"  eta={eta:.2f}: [{vals}]")
    print("cutoff_approximant_drift_by_eta:")
    for eta in eta_list:
        vals = ", ".join(f"{v:.6e}" for v in cutoff_drift_by_eta[eta])
        print(f"  eta={eta:.2f}: [{vals}]")

    print(f"check_min_denominator_positive={min_denom > 1.0e-4}")
    print(f"check_tail_majorant_decay={tail_decay_ok}")
    print(f"check_cutoff_approximant_decay={cutoff_decay_ok}")
    print(f"check_full_sd_residual_small={sd_small_ok}")
    print(f"check_de_regularization_drift_small={de_reg_ok}")
    print(
        "all_checks_pass="
        f"{(min_denom > 1.0e-4) and tail_decay_ok and cutoff_decay_ok and sd_small_ok and de_reg_ok}"
    )


if __name__ == "__main__":
    main()
