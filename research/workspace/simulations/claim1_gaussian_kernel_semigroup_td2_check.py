#!/usr/bin/env python3.12
"""Gaussian kernel semigroup + t^{-d/2} diagonal scaling diagnostic.

This script is an *independent numerical sanity check* for the Newton-limit paradox
support lane:

  1) The Euclidean Gaussian/heat kernel family forms a convolution semigroup:
       K_t * K_s = K_{t+s}.
  2) The diagonal normalization exponent is forced:
       K_t(0) ∝ t^{-d/2}.

We verify (1) by Monte Carlo integration:
  (K_t * K_s)(x) = ∫ K_t(x-y) K_s(y) dy = E_{Y~N(0,2s I)}[K_t(x-Y)].

We estimate (2) by a log-log least-squares fit of K_t(0) vs t.

Run:
  python3.12 research/workspace/simulations/claim1_gaussian_kernel_semigroup_td2_check.py
"""

from __future__ import annotations

import math
import sys
from dataclasses import dataclass

import numpy as np


def kernel_heat_gaussian(d: int, t: float, x: np.ndarray) -> float:
    """Heat kernel on R^d with variance 2t: (4πt)^(-d/2) exp(-|x|^2/(4t))."""
    if d <= 0:
        raise ValueError("d must be positive")
    if t <= 0.0:
        raise ValueError("t must be positive")
    x = np.asarray(x, dtype=float)
    if x.shape != (d,):
        raise ValueError(f"x must have shape ({d},), got {x.shape}")
    pref = (4.0 * math.pi * t) ** (-0.5 * d)
    return pref * math.exp(-float(x @ x) / (4.0 * t))


@dataclass(frozen=True)
class SemigroupCheck:
    d: int
    t: float
    s: float
    x: np.ndarray
    mc_n: int
    rel_err: float


def semigroup_mc_check(rng: np.random.Generator, d: int, t: float, s: float, x: np.ndarray, mc_n: int) -> SemigroupCheck:
    x = np.asarray(x, dtype=float).reshape(d)
    # Sample Y ~ N(0, 2s I_d)
    y = rng.normal(size=(mc_n, d)) * math.sqrt(2.0 * s)
    diff = x[None, :] - y
    sq = np.einsum("ij,ij->i", diff, diff)
    pref = (4.0 * math.pi * t) ** (-0.5 * d)
    kt_vals = pref * np.exp(-sq / (4.0 * t))
    conv_est = float(np.mean(kt_vals))

    target = kernel_heat_gaussian(d, t + s, x)

    denom = max(abs(target), 1e-300)
    rel_err = abs(conv_est - target) / denom
    return SemigroupCheck(d=d, t=t, s=s, x=x, mc_n=mc_n, rel_err=rel_err)


def fit_diagonal_exponent(d: int, t_grid: np.ndarray) -> float:
    ys = np.array([kernel_heat_gaussian(d, float(t), np.zeros(d)) for t in t_grid], dtype=float)
    xs = np.log(t_grid)
    zs = np.log(ys)
    slope = float(np.polyfit(xs, zs, deg=1)[0])
    return slope


def main() -> int:
    seed = 12345
    rng = np.random.default_rng(seed)

    print("Gaussian kernel semigroup + diagonal scaling diagnostic")
    print(f"python={sys.version.split()[0]} numpy={np.__version__} seed={seed}")
    print()

    # Semigroup tests: choose moderate t,s and a few points x in each dimension.
    t = 0.3
    s = 0.7
    mc_n = 200_000
    # Relative-error tolerance tuned for MC noise at this sample size.
    tol_rel = 1.5e-2

    checks: list[SemigroupCheck] = []
    for d in [1, 2, 3, 4]:
        points = [np.zeros(d), np.array([0.7] + [0.0] * (d - 1)), np.array([0.3] * d)]
        for x in points:
            checks.append(semigroup_mc_check(rng=rng, d=d, t=t, s=s, x=x, mc_n=mc_n))

    print("Semigroup MC checks (K_t * K_s ≈ K_{t+s})")
    ok = True
    for c in checks:
        x_str = "[" + ", ".join(f"{xi:.3g}" for xi in c.x.tolist()) + "]"
        status = "OK" if c.rel_err <= tol_rel else "FAIL"
        ok = ok and (c.rel_err <= tol_rel)
        print(f"  d={c.d} x={x_str:>18} rel_err={c.rel_err:.3e}  ({status})")
    print(f"  tolerance: rel_err <= {tol_rel:.1e} with mc_n={mc_n}")
    print()

    print("Diagonal scaling exponent fit (K_t(0) ∝ t^slope)")
    t_grid = np.array([0.08, 0.12, 0.18, 0.27, 0.41, 0.62, 0.93], dtype=float)
    for d in [1, 2, 3, 4]:
        slope = fit_diagonal_exponent(d=d, t_grid=t_grid)
        target = -0.5 * d
        err = slope - target
        print(f"  d={d}: fitted slope={slope:+.6f}  target={target:+.6f}  (delta={err:+.2e})")
        ok = ok and (abs(err) <= 2e-12)
    print()

    if not ok:
        print("FAIL: one or more checks exceeded tolerance.")
        return 1

    print("PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
