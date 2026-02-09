#!/usr/bin/env python3.12
"""Numerical eta->0+ and large-N check for finite-g multimode quartic sector.

Run:
  python3.12 research/workspace/simulations/claim1_multimode_quartic_dereg_eta0_check.py
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


def build_B(indices: list[int]) -> np.ndarray:
    n = len(indices)
    B = np.zeros((n, n), dtype=np.float64)
    for a, j in enumerate(indices):
        for b, k in enumerate(indices):
            if j == k:
                continue
            B[a, b] = bcoef(j, k)
    return B


def estimate_R_N(
    u: float,
    N: int,
    kappa: complex,
    samples: int,
    rng: np.random.Generator,
    m: int = 1,
) -> complex:
    idx = list(range(m + 1, N + 1))
    n = len(idx)
    if n == 0:
        return 1.0 + 0.0j

    d = np.array([lam(j) + 2.0 * acoef(j) * (u * u) for j in idx], dtype=np.float64)
    std = np.sqrt(1.0 / d)
    y = rng.normal(loc=0.0, scale=std, size=(samples, n))
    t = y * y
    B = build_B(idx)
    W = 0.5 * np.einsum("bi,ij,bj->b", t, B, t, optimize=True)
    return complex(np.mean(np.exp(-kappa * W)))


def phi_N(u: float, N: int, m: int = 1) -> float:
    idx = list(range(m + 1, N + 1))
    if not idx:
        return 1.0
    d = np.array([lam(j) + 2.0 * acoef(j) * (u * u) for j in idx], dtype=np.float64)
    return float(np.exp(-0.5 * np.sum(np.log(d))))


def omega_N_eta(
    N: int,
    eta: float,
    eps: float,
    g: float,
    samples: int,
    u_max: float = 5.5,
    n_grid: int = 151,
    seed: int = 777,
) -> complex:
    c = eta - 1j / eps
    kappa = g / c
    rng = np.random.default_rng(seed + 1000 * N + int(1e6 * eta))

    grid = np.linspace(-u_max, u_max, n_grid)
    phase = np.exp(-c * P(grid))
    phi_vals = np.array([phi_N(float(u), N=N) for u in grid], dtype=np.float64)
    R_vals = np.array(
        [estimate_R_N(float(u), N=N, kappa=kappa, samples=samples, rng=rng) for u in grid],
        dtype=np.complex128,
    )

    w = phase * phi_vals * R_vals
    num = trap(w * F(grid), grid)
    den = trap(w, grid)
    return num / den


def sigma_tail(N: int, j_max: int = 12000) -> float:
    return sum(acoef(j) / lam(j) for j in range(N + 1, j_max + 1))


def rho_tail(N: int, j_max: int = 800, m: int = 1) -> float:
    total = 0.0
    for j in range(m + 1, j_max + 1):
        for k in range(j + 1, j_max + 1):
            if max(j, k) > N:
                total += bcoef(j, k) / (lam(j) * lam(k))
    return total


def main() -> None:
    eps = 2.0
    g = 0.35
    samples = 1200
    etas = [1.0, 0.5, 0.2, 0.1, 0.05, 0.02, 0.01, 0.005]
    Ns = [12, 20, 28]

    print("Claim 1 eta->0+ de-regularization check (finite-g multimode quartic)")
    print(f"eps={eps}, g={g}, samples={samples}")
    print()

    for N in Ns:
        print(f"N={N}")
        vals: list[complex] = []
        for eta in etas:
            w = omega_N_eta(N=N, eta=eta, eps=eps, g=g, samples=samples)
            vals.append(w)
            print(f"  eta={eta:>6.3f}  omega={w.real:.10f} + {w.imag:.10f}i")
        print("  successive eta-differences:")
        for i in range(len(etas) - 1):
            d = abs(vals[i + 1] - vals[i])
            print(f"    {etas[i]:>6.3f}->{etas[i+1]:>6.3f}: {d:.6e}")
        print()

    print("Large-N check at small positive eta:")
    for eta in [0.05, 0.005]:
        vals = [omega_N_eta(N=N, eta=eta, eps=eps, g=g, samples=samples) for N in Ns]
        print(f"  eta={eta:>6.3f}")
        for i in range(len(Ns) - 1):
            N = Ns[i]
            Nn = Ns[i + 1]
            diff = abs(vals[i + 1] - vals[i])
            control = sigma_tail(N) + rho_tail(N)
            print(
                f"    N={N:>2d}->{Nn:>2d}  diff={diff:.6e}  control~={control:.6e}  ratio={diff/control:.6e}"
            )


if __name__ == "__main__":
    main()
