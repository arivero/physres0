#!/usr/bin/env python3.12
"""Claim 1 AN-20 check: d=3 finite-volume centered/moment bounds.

Run:
  python3.12 research/workspace/simulations/claim1_d3_finite_volume_centered_moment_bound_check.py
"""

from __future__ import annotations

import math
from dataclasses import dataclass

import numpy as np


@dataclass(frozen=True)
class Params:
    a: float
    m2: float
    lam: float
    kappa: float
    c: float
    lbox: int


def sites(lbox: int) -> list[tuple[int, int, int]]:
    return [(i, j, k) for i in range(lbox) for j in range(lbox) for k in range(lbox)]


def plus_neighbor(x: tuple[int, int, int], axis: int, lbox: int) -> tuple[int, int, int]:
    coords = list(x)
    coords[axis] = (coords[axis] + 1) % lbox
    return (coords[0], coords[1], coords[2])


def unique_edges(lbox: int) -> list[tuple[tuple[int, int, int], tuple[int, int, int]]]:
    edges: list[tuple[tuple[int, int, int], tuple[int, int, int]]] = []
    for x in sites(lbox):
        for axis in range(3):
            y = plus_neighbor(x, axis, lbox)
            edges.append((x, y))
    return edges


def local_edges(b_sites: set[tuple[int, int, int]], lbox: int) -> list[tuple[tuple[int, int, int], tuple[int, int, int]]]:
    edges: list[tuple[tuple[int, int, int], tuple[int, int, int]]] = []
    for x in b_sites:
        for axis in range(3):
            y = plus_neighbor(x, axis, lbox)
            edges.append((x, y))
    return edges


def onsite(u: float, m2: float, lam: float) -> float:
    return 0.5 * m2 * (u * u) + 0.25 * lam * (u**4)


def total_action(field: dict[tuple[int, int, int], float], p: Params) -> float:
    pot = 0.0
    for x, value in field.items():
        pot += onsite(value, p.m2, p.lam)
    grad = 0.0
    for x, y in unique_edges(p.lbox):
        diff = field[x] - field[y]
        grad += diff * diff
    return (p.a**3) * pot + 0.5 * p.kappa * (p.a**3) * grad / (p.a**2)


def local_observable(field: dict[tuple[int, int, int], float]) -> float:
    x0 = (0, 0, 0)
    x1 = (1, 0, 0)
    return 1.0 / (1.0 + field[x0] * field[x0]) + 0.2 / (1.0 + field[x1] * field[x1])


def local_gradient(field: dict[tuple[int, int, int], float], e_local: list[tuple[tuple[int, int, int], tuple[int, int, int]]]) -> float:
    total = 0.0
    for x, y in e_local:
        diff = field[x] - field[y]
        total += diff * diff
    return total


def metropolis_samples(
    p: Params,
    rng: np.random.Generator,
    n_therm: int,
    n_keep: int,
    stride: int,
    proposal_sigma: float,
) -> tuple[np.ndarray, np.ndarray]:
    all_sites = sites(p.lbox)
    field = {x: 0.0 for x in all_sites}
    current_s = total_action(field, p)

    b_sites = {(0, 0, 0), (1, 0, 0)}
    e_local = local_edges(b_sites, p.lbox)

    obs_f: list[float] = []
    obs_g: list[float] = []
    n_steps = n_therm + n_keep * stride

    for step in range(n_steps):
        x = all_sites[rng.integers(0, len(all_sites))]
        old_val = field[x]
        new_val = old_val + proposal_sigma * rng.normal()
        field[x] = new_val
        new_s = total_action(field, p)
        delta = p.c * (new_s - current_s)

        if delta <= 0.0 or rng.random() < math.exp(-delta):
            current_s = new_s
        else:
            field[x] = old_val

        if step >= n_therm and (step - n_therm) % stride == 0:
            obs_f.append(local_observable(field))
            obs_g.append(local_gradient(field, e_local))

    return np.array(obs_f), np.array(obs_g)


def main() -> None:
    seed = 20260209
    rng = np.random.default_rng(seed)

    p = Params(
        a=0.8,
        m2=1.2,
        lam=0.7,
        kappa=0.2,
        c=0.9,
        lbox=2,
    )

    n_therm = 6000
    n_keep = 5000
    stride = 3
    proposal_sigma = 0.55

    obs_f, obs_g = metropolis_samples(p, rng, n_therm, n_keep, stride, proposal_sigma)

    f_sup = 1.2
    centered_bound = 2.0 * f_sup
    f_mean = float(obs_f.mean())
    max_centered = float(np.max(np.abs(obs_f - f_mean)))

    b_sites = {(0, 0, 0), (1, 0, 0)}
    e_local = local_edges(b_sites, p.lbox)
    m_bound = 4.0 * len(e_local) / (p.c * p.m2 * (p.a**3))
    g_mean = float(obs_g.mean())

    print("Claim 1 AN-20 finite-volume d=3 check")
    print(f"seed={seed}")
    print(f"params: a={p.a}, m2={p.m2}, lambda={p.lam}, kappa={p.kappa}, c={p.c}, L={p.lbox}")
    print(f"samples={len(obs_f)}, therm={n_therm}, stride={stride}")
    print()
    print("Centered bound check:")
    print(f"  empirical max |F-mean(F)| = {max_centered:.6f}")
    print(f"  theorem bound 2||F||_inf  = {centered_bound:.6f}")
    print(f"  holds = {max_centered <= centered_bound + 1e-12}")
    print()
    print("Local moment bound check:")
    print(f"  empirical omega(G_B) = {g_mean:.6f}")
    print(f"  theorem M_B,a        = {m_bound:.6f}")
    print(f"  holds = {g_mean <= m_bound + 1e-12}")


if __name__ == "__main__":
    main()
