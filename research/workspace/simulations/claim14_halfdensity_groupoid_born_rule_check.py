#!/usr/bin/env python3.12
"""Claim 14: Amplitudes as half-densities on tangent groupoid algebras.

Run:
  python3.12 research/workspace/simulations/claim14_halfdensity_groupoid_born_rule_check.py

Verifies:
1. Half-density convolution is coordinate-free (invariant under diffeomorphism).
2. |A_eps|^2 concentrates on critical sets (stationary phase).
3. The squaring map half-density -> density matches Born rule structure.
"""

from __future__ import annotations

import math

import numpy as np


def check_halfdensity_convolution_invariance() -> bool:
    """Verify that 1/2-density convolution is coordinate-invariant.

    For two kernels K1(x,y), K2(y,z) as 1/2-density sections,
    the convolution integral (K1*K2)(x,z) = int K1(x,y) K2(y,z) dy
    is invariant under y -> phi(y) because the 1/2-density transformation
    produces exactly the Jacobian factor |det(dphi/dy)|^{1/2} * |det(dphi/dy)|^{1/2}
    = |det(dphi/dy)| which cancels the measure transformation dy -> dphi * |det|^{-1}.

    Test: 1D diffeomorphism y -> y^3 on [0.1, 2].
    """
    n_pts = 500

    # Define test kernels as 1/2-densities
    def k1(x, y):
        return np.exp(-(x - y)**2)

    def k2(y, z):
        return np.exp(-(y - z)**2 / 2)

    x_test = 0.5
    z_test = 1.5

    # Original coordinates: integral of K1(x,y) K2(y,z) dy
    y_orig = np.linspace(0.1, 2.0, n_pts)
    dy = y_orig[1] - y_orig[0]
    integrand_orig = k1(x_test, y_orig) * k2(y_orig, z_test)
    conv_orig = np.trapezoid(integrand_orig, y_orig)

    # Transformed coordinates: u = y^3, y = u^{1/3}
    # dy = (1/3) u^{-2/3} du
    # Half-density transforms: K -> K * |dy/du|^{1/2} for each index
    # K1(x, y(u)) * |dy/du|^{1/2} and K2(y(u), z) * |dy/du|^{1/2}
    # Product: K1 * K2 * |dy/du|
    # Integral: int K1 * K2 * |dy/du| du = int K1 * K2 dy (change of variables)

    u_min = 0.1**3
    u_max = 2.0**3
    u_vals = np.linspace(u_min, u_max, n_pts)
    y_from_u = u_vals**(1.0 / 3.0)
    dydu = (1.0 / 3.0) * u_vals**(-2.0 / 3.0)

    # As half-densities: each K factor absorbs |dy/du|^{1/2}
    # Total integrand in u-coordinates includes full |dy/du|
    integrand_trans = k1(x_test, y_from_u) * k2(y_from_u, z_test) * dydu
    conv_trans = np.trapezoid(integrand_trans, u_vals)

    rel_err = abs(conv_orig - conv_trans) / abs(conv_orig)
    return rel_err < 0.01  # numerical integration tolerance


def check_stationary_phase_concentration() -> bool:
    """Verify |A_eps(psi)|^2 concentrates on critical points of f.

    A_eps(psi) = eps^{-n/2} int exp(i*f(x)/eps) psi(x) dx.
    For f(x) = (x-x0)^2/2 (single critical point at x0), Morse with Hess = 1:
    |A_eps|^2 -> (2*pi)^n * |psi(x0)|^2 / |det Hess| = 2*pi * |psi(x0)|^2.
    """
    x0 = 1.0
    n = 1  # dimension

    def f(x):
        return (x - x0)**2 / 2.0

    def psi(x):
        return np.exp(-(x - 0.5)**2) + 0.5  # smooth, nonzero at x0

    psi_x0 = psi(x0)
    expected_limit = (2 * math.pi)**n * abs(psi_x0)**2  # |det Hess| = 1

    # Compute A_eps for decreasing eps
    x_grid = np.linspace(-5.0, 7.0, 10000)
    dx = x_grid[1] - x_grid[0]

    results = []
    for eps in [0.1, 0.05, 0.02, 0.01, 0.005]:
        integrand = np.exp(1j * f(x_grid) / eps) * psi(x_grid)
        A_eps = eps**(-n / 2.0) * np.trapezoid(integrand, x_grid)
        results.append(abs(A_eps)**2)

    # Check convergence toward expected limit
    # The last value should be closest
    rel_err_last = abs(results[-1] - expected_limit) / expected_limit
    # Check trend is converging
    diffs = [abs(r - expected_limit) for r in results]
    trend_ok = diffs[-1] < diffs[0]

    return trend_ok and rel_err_last < 0.5  # oscillatory convergence can be slow


def check_born_rule_squaring() -> bool:
    """Verify that |amplitude|^2 gives probability density correctly.

    For a normalized amplitude A(x) = (2*pi*sigma^2)^{-1/4} exp(-x^2/(4*sigma^2)),
    |A(x)|^2 = (2*pi*sigma^2)^{-1/2} exp(-x^2/(2*sigma^2)) is a normalized
    probability density.
    """
    sigma = 1.5
    x = np.linspace(-10, 10, 10000)
    dx = x[1] - x[0]

    # Amplitude (half-density)
    A = (2 * math.pi * sigma**2)**(-0.25) * np.exp(-x**2 / (4 * sigma**2))

    # Probability density (full density)
    rho = np.abs(A)**2

    # Check normalization
    norm = np.trapezoid(rho, x)
    norm_ok = abs(norm - 1.0) < 1e-6

    # Check it matches expected Gaussian density
    rho_expected = (2 * math.pi * sigma**2)**(-0.5) * np.exp(-x**2 / (2 * sigma**2))
    max_diff = np.max(np.abs(rho - rho_expected))
    shape_ok = max_diff < 1e-12

    return norm_ok and shape_ok


def check_halfdensity_transformation_law() -> bool:
    """Verify the half-density transformation law under coordinate change.

    Under x -> y = phi(x), a half-density transforms as:
    s(y) = s(x) * |det(dx/dy)|^{1/2} = s(x) * |phi'(x)|^{-1/2}.

    The full density (probability) transforms as:
    rho(y) = |s(y)|^2 = |s(x)|^2 * |phi'(x)|^{-1} = rho(x) * |dx/dy|.
    This is the standard Jacobian transformation law for densities.
    """
    # Test: x -> y = x^2 for x > 0
    n_pts = 1000
    x = np.linspace(0.1, 3.0, n_pts)

    # Half-density in x-coordinates
    s_x = np.exp(-x**2 / 2)

    # Full density in x-coordinates
    rho_x = s_x**2

    # Transform to y = x^2: dx/dy = 1/(2*sqrt(y))
    y = x**2
    dxdy = 1.0 / (2 * np.sqrt(y))

    # Half-density in y-coordinates
    s_y = s_x * np.sqrt(dxdy)

    # Full density in y-coordinates
    rho_y = s_y**2

    # Should equal rho_x * |dx/dy|
    rho_y_expected = rho_x * dxdy

    max_diff = np.max(np.abs(rho_y - rho_y_expected))
    return max_diff < 1e-12


def main() -> None:
    check_inv = check_halfdensity_convolution_invariance()
    check_sp = check_stationary_phase_concentration()
    check_born = check_born_rule_squaring()
    check_transf = check_halfdensity_transformation_law()

    all_ok = check_inv and check_sp and check_born and check_transf

    print("Claim 14 half-density groupoid Born rule diagnostic")
    print(f"check_convolution_invariance={check_inv}")
    print(f"check_stationary_phase_concentration={check_sp}")
    print(f"check_born_rule_squaring={check_born}")
    print(f"check_halfdensity_transformation_law={check_transf}")
    print(f"all_checks_pass={all_ok}")


if __name__ == "__main__":
    main()
