#!/usr/bin/env python3.12
"""Claim 1 AN-26B check: d=3 insertion L^(4/3)-moment diagnostics.

Run:
  python3.12 research/workspace/simulations/claim1_d3_an26b_insertion_lq_moment_check.py
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np


Site = tuple[int, int, int]


@dataclass(frozen=True)
class BaseParams:
    m2: float
    lam: float
    lbox: int


def sites(lbox: int) -> list[Site]:
    return [(i, j, k) for i in range(lbox) for j in range(lbox) for k in range(lbox)]


def shift(x: Site, axis: int, step: int, lbox: int) -> Site:
    i, j, k = x
    coords = [i, j, k]
    coords[axis] = (coords[axis] + step) % lbox
    return (coords[0], coords[1], coords[2])


def unique_edges(lbox: int) -> list[tuple[Site, Site]]:
    edges: list[tuple[Site, Site]] = []
    for x in sites(lbox):
        for axis in range(3):
            edges.append((x, shift(x, axis, +1, lbox)))
    return edges


def build_index_map(lbox: int) -> dict[Site, int]:
    return {x: idx for idx, x in enumerate(sites(lbox))}


def weighted_expectation(values: np.ndarray, logw: np.ndarray) -> float:
    pivot = float(np.max(logw))
    w = np.exp(logw - pivot)
    return float(np.sum(w * values) / np.sum(w))


def evaluate_combo(
    base: BaseParams,
    a: float,
    c: float,
    kappa: float,
    n_samples: int,
    sample_radius: float,
    rng: np.random.Generator,
    idx_map: dict[Site, int],
) -> tuple[float, float, float, float]:
    n_sites = base.lbox**3
    fields = rng.uniform(-sample_radius, sample_radius, size=(n_samples, n_sites))

    pot = 0.5 * base.m2 * np.sum(fields * fields, axis=1) + 0.25 * base.lam * np.sum(fields**4, axis=1)
    grad = np.zeros(n_samples, dtype=np.float64)
    for sx, sy in unique_edges(base.lbox):
        ix = idx_map[sx]
        iy = idx_map[sy]
        diff = fields[:, ix] - fields[:, iy]
        grad += diff * diff
    action = (a**3) * pot + 0.5 * kappa * a * grad
    logw = -c * action

    x0 = idx_map[(0, 0, 0)]
    phi0 = fields[:, x0]

    dgrad = np.zeros(n_samples, dtype=np.float64)
    x0_site = (0, 0, 0)
    for axis in range(3):
        ip = idx_map[shift(x0_site, axis, +1, base.lbox)]
        im = idx_map[shift(x0_site, axis, -1, base.lbox)]
        dgrad += (phi0 - fields[:, ip]) + (phi0 - fields[:, im])

    dsi = (a**3) * (base.m2 * phi0 + base.lam * phi0**3) + kappa * a * dgrad
    p = 4.0 / 3.0

    d_moment = weighted_expectation(np.abs(dsi) ** p, logw)
    phi2 = weighted_expectation(phi0 * phi0, logw)
    phi4 = weighted_expectation(phi0**4, logw)

    x_plus = idx_map[shift(x0_site, 0, +1, base.lbox)]
    delta = phi0 - fields[:, x_plus]
    edge4 = weighted_expectation(delta**4, logw)
    return d_moment, phi2, phi4, edge4


def main() -> None:
    seed = 2026020902
    rng = np.random.default_rng(seed)

    base = BaseParams(m2=1.1, lam=0.8, lbox=2)
    c0 = 0.8
    kappa_star = 0.2
    a_grid = [1.0, 0.7, 0.5]
    c_grid = [0.8, 1.1]
    kappa_grid = [0.0, 0.1, 0.2]
    n_samples = 60000
    sample_radius = 3.8
    idx_map = build_index_map(base.lbox)

    analytic_bound = (3.0 ** (1.0 / 3.0)) * (
        (base.m2 / c0) ** (2.0 / 3.0)
        + (base.lam ** (1.0 / 3.0)) / c0
        + ((6.0 ** (4.0 / 3.0)) * (16.0 ** (1.0 / 3.0)) * (kappa_star ** (4.0 / 3.0)))
        / ((c0 * base.lam) ** (1.0 / 3.0))
    )

    print("Claim 1 AN-26B d=3 insertion L^(4/3)-moment diagnostics")
    print(f"seed={seed}")
    print(
        "params: "
        f"m2={base.m2}, lambda={base.lam}, L={base.lbox}, "
        f"c0={c0}, kappa_star={kappa_star}"
    )
    print(f"grids: a={a_grid}, c={c_grid}, kappa={kappa_grid}")
    print(f"importance samples/combo={n_samples}, sampling cube radius={sample_radius}")
    print(f"analytic M_(i,4/3) bound={analytic_bound:.6f}")
    print()

    max_d_moment = -1.0
    max_row: tuple[float, float, float] | None = None
    all_bounds_ok = True

    for a in a_grid:
        for c in c_grid:
            for kappa in kappa_grid:
                d_moment, phi2, phi4, edge4 = evaluate_combo(
                    base, a, c, kappa, n_samples, sample_radius, rng, idx_map
                )
                max_d_moment = max(max_d_moment, d_moment)
                if max_d_moment == d_moment:
                    max_row = (a, c, kappa)

                phi2_bound = 1.0 / (c0 * base.m2 * (a**3))
                phi4_bound = 1.0 / (c0 * base.lam * (a**3))
                edge4_bound = 16.0 / (c0 * base.lam * (a**3))

                bounds_ok = (phi2 <= phi2_bound + 1e-12) and (phi4 <= phi4_bound + 1e-12) and (
                    edge4 <= edge4_bound + 1e-12
                )
                all_bounds_ok = all_bounds_ok and bounds_ok

                print(f"a={a:.2f}, c={c:.2f}, kappa={kappa:.2f}")
                print(f"  E[|d_i S|^(4/3)]               = {d_moment:.6f}")
                print(f"  E[phi_i^2] <= 1/(c0 m2 a^3):     {phi2:.6f} <= {phi2_bound:.6f}")
                print(f"  E[phi_i^4] <= 1/(c0 lam a^3):    {phi4:.6f} <= {phi4_bound:.6f}")
                print(f"  E[(phi_i-phi_j)^4] <= edge bound:{edge4:.6f} <= {edge4_bound:.6f}")
                print(f"  moment-support bounds hold:      {bounds_ok}")
                print()

    assert max_row is not None
    print("Summary:")
    print(f"  max empirical E[|d_i S|^(4/3)] = {max_d_moment:.6f} at (a,c,kappa)={max_row}")
    print(f"  analytic bound M_(i,4/3)       = {analytic_bound:.6f}")
    print(f"  empirical/analytic ratio       = {max_d_moment / analytic_bound:.6f}")
    print(f"  all support bounds respected   = {all_bounds_ok}")


if __name__ == "__main__":
    main()
