#!/usr/bin/env python3.12
"""Claim 1 AN-21 check: d=3 renormalized moment channel.

Run:
  python3.12 research/workspace/simulations/claim1_d3_renormalized_moment_channel_check.py
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
            edges.append((x, plus_neighbor(x, axis, lbox)))
    return edges


def local_edges(
    b_sites: set[tuple[int, int, int]],
    lbox: int,
) -> list[tuple[tuple[int, int, int], tuple[int, int, int]]]:
    edges: list[tuple[tuple[int, int, int], tuple[int, int, int]]] = []
    for x in b_sites:
        for axis in range(3):
            edges.append((x, plus_neighbor(x, axis, lbox)))
    return edges


def onsite(u: float, m2: float, lam: float) -> float:
    return 0.5 * m2 * (u * u) + 0.25 * lam * (u**4)


def total_action(field: dict[tuple[int, int, int], float], p: Params) -> float:
    pot = 0.0
    for value in field.values():
        pot += onsite(value, p.m2, p.lam)
    grad = 0.0
    for x, y in unique_edges(p.lbox):
        diff = field[x] - field[y]
        grad += diff * diff
    return (p.a**3) * pot + 0.5 * p.kappa * (p.a**3) * grad / (p.a**2)


def local_gradient_raw(
    field: dict[tuple[int, int, int], float],
    e_local: list[tuple[tuple[int, int, int], tuple[int, int, int]]],
) -> float:
    total = 0.0
    for x, y in e_local:
        diff = field[x] - field[y]
        total += diff * diff
    return total


def metropolis_gradient_samples(
    p: Params,
    rng: np.random.Generator,
    n_therm: int,
    n_keep: int,
    stride: int,
    proposal_sigma: float,
) -> np.ndarray:
    all_sites = sites(p.lbox)
    field = {x: 0.0 for x in all_sites}
    current_s = total_action(field, p)

    b_sites = {(0, 0, 0), (1, 0, 0)}
    e_local = local_edges(b_sites, p.lbox)

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
            obs_g.append(local_gradient_raw(field, e_local))

    return np.array(obs_g)


def main() -> None:
    seed = 20260209
    rng = np.random.default_rng(seed)

    m2 = 1.2
    lam = 0.7
    kappa = 0.2
    c = 0.9
    lbox = 2
    a_grid = [1.0, 0.8, 0.65, 0.5]

    n_therm = 3500
    n_keep = 2800
    stride = 3

    b_sites = {(0, 0, 0), (1, 0, 0)}
    e_local = local_edges(b_sites, lbox)
    edge_count = len(e_local)

    ren_bound = 4.0 * edge_count / (c * m2)
    all_raw_ok = True
    all_ren_ok = True

    print("Claim 1 AN-21 d=3 renormalized moment channel check")
    print(f"seed={seed}")
    print(f"params: m2={m2}, lambda={lam}, kappa={kappa}, c={c}, L={lbox}")
    print(f"samples={n_keep}, therm={n_therm}, stride={stride}")
    print(f"|E_B|={edge_count}")
    print()

    for a in a_grid:
        p = Params(a=a, m2=m2, lam=lam, kappa=kappa, c=c, lbox=lbox)
        proposal_sigma = 0.55 / (a ** 1.5)
        raw = metropolis_gradient_samples(
            p=p,
            rng=rng,
            n_therm=n_therm,
            n_keep=n_keep,
            stride=stride,
            proposal_sigma=proposal_sigma,
        )

        raw_mean = float(raw.mean())
        raw_bound = 4.0 * edge_count / (c * m2 * (a**3))
        ren_mean = (a**3) * raw_mean

        raw_ok = raw_mean <= raw_bound + 1e-12
        ren_ok = ren_mean <= ren_bound + 1e-12
        all_raw_ok = all_raw_ok and raw_ok
        all_ren_ok = all_ren_ok and ren_ok

        print(f"a={a:.2f}")
        print(f"  empirical omega(G_B)          = {raw_mean:.6f}")
        print(f"  raw theorem bound M_B,a       = {raw_bound:.6f}")
        print(f"  raw bound holds               = {raw_ok}")
        print(f"  empirical omega(a^3 G_B)      = {ren_mean:.6f}")
        print(f"  renormalized bound M_B^ren    = {ren_bound:.6f}")
        print(f"  renormalized bound holds      = {ren_ok}")
        print()

    print(f"all raw bounds hold: {all_raw_ok}")
    print(f"all renormalized bounds hold: {all_ren_ok}")


if __name__ == "__main__":
    main()
