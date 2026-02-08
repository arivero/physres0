#!/usr/bin/env python3.12
"""Numerical check for Claim 1 first-order multi-mode quartic closure (Phase AC).

Run:
  python3.12 research/workspace/simulations/claim1_multimode_quartic_firstorder_check.py
"""

from __future__ import annotations

import numpy as np


def lam(j: int) -> float:
    return 1.0 + 0.2 * j


def acoef(j: int) -> float:
    return 0.35 / (j**2)


def bcoef(j: int, k: int) -> float:
    return 0.08 / ((j + k) ** 3)


def P(u: np.ndarray) -> np.ndarray:
    return 0.25 * u**4 + 0.5 * u**2


def F(u: np.ndarray) -> np.ndarray:
    return u**2 / (1.0 + u**2)


def trap(y: np.ndarray, x: np.ndarray) -> complex:
    t = getattr(np, "trapezoid", None)
    if t is None:
        t = np.trapz
    return t(y, x)


def phi_and_R(grid: np.ndarray, N: int, c: complex, m: int = 1) -> tuple[np.ndarray, np.ndarray]:
    idx = list(range(m + 1, N + 1))
    n = len(idx)
    if n == 0:
        return np.ones_like(grid), np.zeros_like(grid, dtype=np.complex128)

    d = np.array([lam(j) + 2.0 * acoef(j) * grid * grid for j in idx], dtype=np.float64)
    log_phi = -0.5 * np.sum(np.log(d), axis=0)
    phi = np.exp(log_phi)

    rsum = np.zeros_like(grid, dtype=np.float64)
    for a, j in enumerate(idx):
        dj = d[a]
        for b, k in enumerate(idx):
            if k <= j:
                continue
            rsum += bcoef(j, k) / (dj * d[b])

    R = rsum / (c * c)
    return phi, R


def first_order_state(
    N: int,
    c: complex,
    g: float,
    eta: float,
    grid: np.ndarray,
) -> complex:
    phase = np.exp(-c * P(grid))
    phi, R = phi_and_R(grid=grid, N=N, c=c)

    N0 = trap(phase * phi * F(grid), grid)
    D0 = trap(phase * phi, grid)
    A = trap(phase * phi * F(grid) * R, grid)
    B = trap(phase * phi * R, grid)

    omega0 = N0 / D0
    gamma = -c * (A / D0 - omega0 * (B / D0))
    return omega0 + g * gamma


def sigma_tail(N: int, j_max: int = 12000) -> float:
    return sum(acoef(j) / lam(j) for j in range(N + 1, j_max + 1))


def rho_tail(N: int, j_max: int = 600, m: int = 1) -> float:
    total = 0.0
    for j in range(m + 1, j_max + 1):
        for k in range(j + 1, j_max + 1):
            if max(j, k) > N:
                total += bcoef(j, k) / (lam(j) * lam(k))
    return total


def main() -> None:
    eta = 1.0
    eps = 2.0
    c = eta - 1j / eps
    g = 0.08
    grid = np.linspace(-6.0, 6.0, 3201)
    Ns = [8, 12, 16, 20, 24, 28, 32]

    print("Claim 1 first-order non-Gaussian multi-mode check")
    print(f"c={c}, g={g}")
    print()

    vals: list[complex] = []
    for N in Ns:
        w = first_order_state(N=N, c=c, g=g, eta=eta, grid=grid)
        vals.append(w)
        print(f"N={N:>2d}  omega1={w.real:.12f} + {w.imag:.12f}i")

    print()
    print("Successive differences vs mixed tail control (sigma_N + rho_N):")
    for i in range(len(Ns) - 1):
        N = Ns[i]
        Nn = Ns[i + 1]
        diff = abs(vals[i + 1] - vals[i])
        control = sigma_tail(N) + rho_tail(N)
        print(
            f"N={N:>2d}->{Nn:>2d}  diff={diff:.6e}  control~={control:.6e}  ratio={diff/control:.6e}"
        )


if __name__ == "__main__":
    main()
