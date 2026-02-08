#!/usr/bin/env python3.12
"""Numerical check for Claim 1 non-factorized quadratic-mixing cylinder limit.

Run:
  python3.12 research/workspace/simulations/claim1_nonfactorized_quadratic_mixing_check.py
"""

from __future__ import annotations

import math
from typing import Iterable

import numpy as np


def P(u: np.ndarray) -> np.ndarray:
    return 0.25 * u**4 + 0.5 * u**2


def observable(u: np.ndarray) -> np.ndarray:
    return u**2 / (1.0 + u**2)


def lam(j: int) -> float:
    return 1.0 + 0.2 * j


def acoef(j: int) -> float:
    return 0.35 / (j**2)


def kappa(j: int, k: int) -> float:
    if j == k:
        return 0.0
    g = 0.12
    return g / ((j + k) ** 2)


def build_tail_matrix(indices: Iterable[int]) -> np.ndarray:
    idx = list(indices)
    n = len(idx)
    K = np.zeros((n, n), dtype=np.float64)
    for a, j in enumerate(idx):
        for b, k in enumerate(idx):
            K[a, b] = kappa(j, k)
    return K


def phi_N(u: float, N: int, m: int = 1) -> float:
    idx = list(range(m + 1, N + 1))
    n = len(idx)
    if n == 0:
        return 1.0

    d = np.array([lam(j) + 2.0 * acoef(j) * (u * u) for j in idx], dtype=np.float64)
    D = np.diag(d)
    K = build_tail_matrix(idx)
    A = D + K
    sign, logdet = np.linalg.slogdet(A)
    if sign <= 0:
        raise RuntimeError(f"non-positive determinant encountered for N={N}, u={u}")
    return math.exp(-0.5 * logdet)


def omega_N(N: int, eta: float = 1.0, u_max: float = 6.0, n_grid: int = 3201) -> float:
    grid = np.linspace(-u_max, u_max, n_grid)
    phi = np.array([phi_N(float(u), N) for u in grid], dtype=np.float64)
    base = np.exp(-eta * P(grid))
    w = base * phi
    trap = getattr(np, "trapezoid", None)
    if trap is None:
        trap = np.trapz
    num = trap(w * observable(grid), grid)
    den = trap(w, grid)
    return float(num / den)


def sigma_tail(N: int, j_max: int = 10000) -> float:
    return sum(acoef(j) / lam(j) for j in range(N + 1, j_max + 1))


def tau_tail_upper(N: int, j_max: int = 400) -> float:
    total = 0.0
    for j in range(2, j_max + 1):
        for k in range(2, j_max + 1):
            if max(j, k) > N:
                total += abs(kappa(j, k)) / math.sqrt(lam(j) * lam(k))
    return total


def spectral_radius_bound(j_max: int = 220) -> float:
    idx = list(range(2, j_max + 1))
    n = len(idx)
    B = np.zeros((n, n), dtype=np.float64)
    for a, j in enumerate(idx):
        for b, k in enumerate(idx):
            B[a, b] = kappa(j, k) / math.sqrt(lam(j) * lam(k))
    eig = np.linalg.eigvalsh(B)
    return float(np.max(np.abs(eig)))


def main() -> None:
    rho = spectral_radius_bound()
    print("Claim 1 non-factorized quadratic-mixing check")
    print(f"approx weighted operator-norm bound ||K~|| <= {rho:.6f}")
    if rho >= 1.0:
        raise RuntimeError("Smallness assumption violated: weighted norm >= 1")
    print()

    Ns = [8, 12, 16, 20, 24, 28]
    vals = []
    for N in Ns:
        w = omega_N(N)
        vals.append(w)
        print(f"N={N:>2d}  omega_N={w:.12f}")

    print()
    print("Successive differences vs mixed tail control (sigma_N + tau_N upper):")
    for i in range(len(Ns) - 1):
        N = Ns[i]
        Nn = Ns[i + 1]
        diff = abs(vals[i + 1] - vals[i])
        control = sigma_tail(N) + tau_tail_upper(N)
        print(
            f"N={N:>2d}->{Nn:>2d}  diff={diff:.6e}  control~={control:.6e}  ratio={diff/control:.6e}"
        )


if __name__ == "__main__":
    main()
