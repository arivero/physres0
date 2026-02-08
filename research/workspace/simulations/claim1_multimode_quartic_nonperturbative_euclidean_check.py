#!/usr/bin/env python3.12
"""Monte Carlo check for non-perturbative Euclidean multi-mode quartic closure.

Run:
  python3.12 research/workspace/simulations/claim1_multimode_quartic_nonperturbative_euclidean_check.py
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


def trap(y: np.ndarray, x: np.ndarray) -> float:
    t = getattr(np, "trapezoid", None)
    if t is None:
        t = np.trapz
    return float(t(y, x))


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
    u: float, N: int, eta: float, g: float, samples: int, rng: np.random.Generator, m: int = 1
) -> float:
    idx = list(range(m + 1, N + 1))
    n = len(idx)
    if n == 0:
        return 1.0

    d = np.array([lam(j) + 2.0 * acoef(j) * (u * u) for j in idx], dtype=np.float64)
    std = np.sqrt(1.0 / (eta * d))
    z = rng.normal(loc=0.0, scale=std, size=(samples, n))
    t = z * z
    B = build_B(idx)
    # W = 1/2 * t^T B t, samplewise
    W = 0.5 * np.einsum("bi,ij,bj->b", t, B, t, optimize=True)
    return float(np.mean(np.exp(-eta * g * W)))


def phi_N(u: float, N: int, m: int = 1) -> float:
    idx = list(range(m + 1, N + 1))
    if not idx:
        return 1.0
    d = np.array([lam(j) + 2.0 * acoef(j) * (u * u) for j in idx], dtype=np.float64)
    return float(np.exp(-0.5 * np.sum(np.log(d))))


def omega_N(
    N: int,
    eta: float,
    g: float,
    samples: int,
    u_max: float = 5.5,
    n_grid: int = 151,
    seed: int = 12345,
) -> float:
    rng = np.random.default_rng(seed + 1000 * N)
    grid = np.linspace(-u_max, u_max, n_grid)
    base = np.exp(-eta * P(grid))

    R_vals = np.array(
        [estimate_R_N(float(u), N=N, eta=eta, g=g, samples=samples, rng=rng) for u in grid],
        dtype=np.float64,
    )
    phi_vals = np.array([phi_N(float(u), N=N) for u in grid], dtype=np.float64)
    w = base * phi_vals * R_vals

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
    eta = 1.0
    g = 0.35
    samples = 1200
    Ns = [8, 12, 16, 20, 24]

    print("Claim 1 non-perturbative Euclidean multi-mode quartic check")
    print(f"eta={eta}, g={g}, samples={samples}")
    print()

    vals = []
    for N in Ns:
        w = omega_N(N=N, eta=eta, g=g, samples=samples)
        vals.append(w)
        print(f"N={N:>2d}  omega_N={w:.10f}")

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
