#!/usr/bin/env python3.12
"""Claim 1 AR check: half-density kinematic success vs dynamical failure.

Run:
  python3.12 research/workspace/simulations/claim1_halfdensity_kinematic_dynamic_split_check.py
"""

from __future__ import annotations

import numpy as np


def discrete_convolution(k1: np.ndarray, k2: np.ndarray, w: np.ndarray) -> np.ndarray:
    n = k1.shape[0]
    out = np.zeros((n, n), dtype=np.complex128)
    for i in range(n):
        for k in range(n):
            out[i, k] = np.sum(k1[i, :] * k2[:, k] * w)
    return out


def trap(y: np.ndarray, x: np.ndarray) -> complex:
    t = getattr(np, "trapezoid", None)
    if t is None:
        raise RuntimeError("numpy.trapezoid required")
    return t(y, x)


def oscillatory_ratio(eps: float) -> complex:
    # Undamped oscillatory toy ratio on [0,1].
    # This sequence need not be Cauchy as eps->0.
    x = np.linspace(0.0, 1.0, 20001)
    phase = np.exp(1j * x / eps)
    den = trap(phase, x)
    num = trap(phase * x, x)
    return num / den


def main() -> None:
    print("Claim 1 AR: kinematic vs dynamical split check")
    print()

    # Kinematic part: discrete kernel associativity.
    rng = np.random.default_rng(20260209)
    n = 7
    w = np.ones(n, dtype=np.float64)
    k1 = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))
    k2 = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))
    k3 = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))

    lhs = discrete_convolution(discrete_convolution(k1, k2, w), k3, w)
    rhs = discrete_convolution(k1, discrete_convolution(k2, k3, w), w)
    assoc_resid = np.max(np.abs(lhs - rhs))
    print("Kinematic associativity check (discrete analogue):")
    print(f"  max residual = {assoc_resid:.3e}")
    print()

    # Dynamical part: no guaranteed convergence without extra hypotheses.
    eps_list = [1.0 / n for n in [20, 30, 40, 50, 60, 70, 80, 90, 100]]
    vals = [oscillatory_ratio(eps) for eps in eps_list]
    print("Undamped oscillatory normalized sequence:")
    for eps, z in zip(eps_list, vals):
        print(f"  eps={eps:.5f}  ratio={z.real:+.8f}{z.imag:+.8f}i")
    print()

    diffs = [abs(vals[i + 1] - vals[i]) for i in range(len(vals) - 1)]
    print("Successive differences:")
    for i, d in enumerate(diffs):
        print(f"  step {i+1}: {d:.6e}")
    print()
    print(f"max successive diff = {max(diffs):.6e}")
    print("Interpretation: kinematic algebra can hold while continuum convergence fails.")


if __name__ == "__main__":
    main()
