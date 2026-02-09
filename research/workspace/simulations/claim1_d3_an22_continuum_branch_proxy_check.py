#!/usr/bin/env python3.12
"""Claim 1 AN-22 check: d=3 scoped continuum-branch proxy diagnostics.

Run:
  python3.12 research/workspace/simulations/claim1_d3_an22_continuum_branch_proxy_check.py
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


def local_observable(field: dict[tuple[int, int, int], float]) -> float:
    x0 = (0, 0, 0)
    x1 = (1, 0, 0)
    return 1.0 / (1.0 + field[x0] * field[x0]) + 0.2 / (1.0 + field[x1] * field[x1])


def local_gradient_raw(
    field: dict[tuple[int, int, int], float],
    e_local: list[tuple[tuple[int, int, int], tuple[int, int, int]]],
) -> float:
    total = 0.0
    for x, y in e_local:
        diff = field[x] - field[y]
        total += diff * diff
    return total


def metropolis_stats(
    p: Params,
    rng: np.random.Generator,
    n_therm: int,
    n_keep: int,
    stride: int,
    proposal_sigma: float,
) -> tuple[float, float, float]:
    all_sites = sites(p.lbox)
    field = {x: 0.0 for x in all_sites}
    current_s = total_action(field, p)

    b_sites = {(0, 0, 0), (1, 0, 0)}
    e_local = local_edges(b_sites, p.lbox)

    obs_f: list[float] = []
    obs_gren: list[float] = []
    obs_phi2_ren: list[float] = []

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
            raw_grad = local_gradient_raw(field, e_local)
            phi0 = field[(0, 0, 0)]
            obs_f.append(local_observable(field))
            obs_gren.append((p.a**3) * raw_grad)
            obs_phi2_ren.append((p.a**3) * phi0 * phi0)

    return float(np.mean(obs_f)), float(np.mean(obs_gren)), float(np.mean(obs_phi2_ren))


def main() -> None:
    seed = 20260209
    rng = np.random.default_rng(seed)

    m2 = 1.2
    lam = 0.7
    c = 0.9
    lbox = 2
    a_grid = [1.00, 0.80, 0.65, 0.50]
    kappa0 = 0.0
    kappa1 = 0.15

    n_therm = 3500
    n_keep = 2600
    stride = 3

    b_sites = {(0, 0, 0), (1, 0, 0)}
    edge_count = len(local_edges(b_sites, lbox))
    m_ren_bound = 4.0 * edge_count / (c * m2)

    means0: list[float] = []
    means1: list[float] = []
    grens1: list[float] = []

    print("Claim 1 AN-22 d=3 scoped continuum-branch proxy check")
    print(f"seed={seed}")
    print(f"params: m2={m2}, lambda={lam}, c={c}, L={lbox}, kappa in {{{kappa0}, {kappa1}}}")
    print(f"samples={n_keep}, therm={n_therm}, stride={stride}")
    print(f"M_B^ren bound = {m_ren_bound:.6f}")
    print()

    for a in a_grid:
        p0 = Params(a=a, m2=m2, lam=lam, kappa=kappa0, c=c, lbox=lbox)
        p1 = Params(a=a, m2=m2, lam=lam, kappa=kappa1, c=c, lbox=lbox)
        sigma = 0.55 / (a ** 1.5)

        f0, gren0, phi2ren0 = metropolis_stats(p0, rng, n_therm, n_keep, stride, sigma)
        f1, gren1, phi2ren1 = metropolis_stats(p1, rng, n_therm, n_keep, stride, sigma)

        lipschitz_est = abs(f1 - f0) / kappa1
        gren_ok = gren1 <= m_ren_bound + 1e-12

        means0.append(f0)
        means1.append(f1)
        grens1.append(gren1)

        print(f"a={a:.2f}")
        print(f"  mean F(kappa=0)              = {f0:.6f}")
        print(f"  mean F(kappa={kappa1})       = {f1:.6f}")
        print(f"  |Delta F|/kappa              = {lipschitz_est:.6f}")
        print(f"  mean a^3 G_B (kappa={kappa1})= {gren1:.6f}")
        print(f"  renormalized bound holds     = {gren_ok}")
        print(f"  mean a^3 phi_0^2 (kappa=0)   = {phi2ren0:.6f}")
        print(f"  mean a^3 phi_0^2 (kappa={kappa1}) = {phi2ren1:.6f}")
        print()

    cauchy_f = [abs(means1[i + 1] - means1[i]) for i in range(len(means1) - 1)]
    cauchy_g = [abs(grens1[i + 1] - grens1[i]) for i in range(len(grens1) - 1)]
    all_gren_ok = all(g <= m_ren_bound + 1e-12 for g in grens1)

    print("Cross-a drift proxies (kappa=0.15):")
    print(f"  |Delta_a mean F| sequence    = {[round(v, 6) for v in cauchy_f]}")
    print(f"  |Delta_a mean a^3 G_B| seq   = {[round(v, 6) for v in cauchy_g]}")
    print()
    print(f"all renormalized bounds hold across a: {all_gren_ok}")


if __name__ == "__main__":
    main()
