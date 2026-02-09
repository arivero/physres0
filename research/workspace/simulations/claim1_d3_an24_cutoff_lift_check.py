#!/usr/bin/env python3.12
"""Claim 1 AN-24 check: d=3 hard-cutoff lift diagnostics.

Run:
  python3.12 research/workspace/simulations/claim1_d3_an24_cutoff_lift_check.py
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np


Site = tuple[int, int, int]


@dataclass(frozen=True)
class Params:
    a: float
    m2: float
    lam: float
    kappa: float
    c: float
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


def local_edges(b_sites: set[Site], lbox: int) -> list[tuple[Site, Site]]:
    edges: list[tuple[Site, Site]] = []
    for x in b_sites:
        for axis in range(3):
            edges.append((x, shift(x, axis, +1, lbox)))
    return edges


def build_index_map(lbox: int) -> dict[Site, int]:
    return {x: idx for idx, x in enumerate(sites(lbox))}


def weighted_expectation(values: np.ndarray, logw: np.ndarray) -> float:
    pivot = float(np.max(logw))
    w = np.exp(logw - pivot)
    return float(np.sum(w * values) / np.sum(w))


def compact_bump(v: np.ndarray, m: float) -> np.ndarray:
    t = 1.0 - (v / m) ** 2
    return np.where(np.abs(v) < m, t * t, 0.0)


def compact_psi(v: np.ndarray, m: float) -> np.ndarray:
    return v * compact_bump(v, m)


def d_compact_psi(v: np.ndarray, m: float) -> np.ndarray:
    z = (v / m) ** 2
    return np.where(np.abs(v) < m, (1.0 - z) * (1.0 - 5.0 * z), 0.0)


def evaluate_for_cutoff(
    p: Params,
    rcut: float,
    n_samples: int,
    rng: np.random.Generator,
    idx_map: dict[Site, int],
) -> tuple[float, float, float, float]:
    n_sites = p.lbox**3
    fields = rng.uniform(-rcut, rcut, size=(n_samples, n_sites))

    pot = 0.5 * p.m2 * np.sum(fields * fields, axis=1) + 0.25 * p.lam * np.sum(fields**4, axis=1)
    grad = np.zeros(n_samples, dtype=np.float64)
    for sx, sy in unique_edges(p.lbox):
        ix = idx_map[sx]
        iy = idx_map[sy]
        diff = fields[:, ix] - fields[:, iy]
        grad += diff * diff
    action = (p.a**3) * pot + 0.5 * p.kappa * p.a * grad
    logw = -p.c * action

    x0 = idx_map[(0, 0, 0)]
    x1 = idx_map[(1, 0, 0)]
    v0 = (p.a ** 1.5) * fields[:, x0]
    v1 = (p.a ** 1.5) * fields[:, x1]

    m_obs = 1.1
    obs_f = compact_bump(v0, m_obs) * compact_bump(v1, m_obs)
    mean_f = weighted_expectation(obs_f, logw)

    m_psi = 0.5
    psi = compact_psi(v0, m_psi)
    dpsi_dphi = (p.a ** 1.5) * d_compact_psi(v0, m_psi)

    dgrad = np.zeros(n_samples, dtype=np.float64)
    x0_site = (0, 0, 0)
    for axis in range(3):
        ip = idx_map[shift(x0_site, axis, +1, p.lbox)]
        im = idx_map[shift(x0_site, axis, -1, p.lbox)]
        dgrad += (fields[:, x0] - fields[:, ip]) + (fields[:, x0] - fields[:, im])

    dsi = (p.a**3) * (p.m2 * fields[:, x0] + p.lam * fields[:, x0] ** 3) + p.kappa * p.a * dgrad
    sd_residual = weighted_expectation(dpsi_dphi, logw) - weighted_expectation(p.c * psi * dsi, logw)

    mean_varphi2 = weighted_expectation(v0 * v0, logw)

    b_sites = {(0, 0, 0), (1, 0, 0)}
    gren_raw = np.zeros(n_samples, dtype=np.float64)
    for sx, sy in local_edges(b_sites, p.lbox):
        ix = idx_map[sx]
        iy = idx_map[sy]
        diff = fields[:, ix] - fields[:, iy]
        gren_raw += diff * diff
    mean_g_ren = weighted_expectation((p.a**3) * gren_raw, logw)

    return mean_f, sd_residual, mean_varphi2, mean_g_ren


def main() -> None:
    seed = 20260209
    rng = np.random.default_rng(seed)

    p = Params(a=0.7, m2=1.1, lam=0.8, kappa=0.12, c=0.9, lbox=2)
    r_grid = [1.2, 1.6, 2.0, 2.4, 2.8, 3.2]
    n_samples = 120000

    idx_map = build_index_map(p.lbox)
    b_sites = {(0, 0, 0), (1, 0, 0)}
    edge_count = len(local_edges(b_sites, p.lbox))
    m_ren_bound = 4.0 * edge_count / (p.c * p.m2)
    varphi2_bound = 1.0 / (p.c * p.m2)

    print("Claim 1 AN-24 d=3 hard-cutoff lift diagnostics")
    print(f"seed={seed}")
    print(
        "params: "
        f"a={p.a}, m2={p.m2}, lambda={p.lam}, kappa={p.kappa}, c={p.c}, L={p.lbox}"
    )
    print(f"R grid={r_grid}")
    print(f"importance samples per R={n_samples}")
    print(f"renormalized moment bound 1/(c m2)={varphi2_bound:.6f}")
    print(f"AN-21 insertion bound M_B^ren={m_ren_bound:.6f}")
    print()

    mean_f_values: list[float] = []

    for rcut in r_grid:
        mean_f, sd_residual, mean_varphi2, mean_g_ren = evaluate_for_cutoff(
            p, rcut, n_samples, rng, idx_map
        )
        mean_f_values.append(mean_f)
        print(f"R={rcut:.1f}")
        print(f"  E[F_R]                         = {mean_f:.6f}")
        print(f"  SD residual                    = {sd_residual:.6e}")
        print(f"  E[varphi_0^2]                  = {mean_varphi2:.6f}")
        print(f"  renorm moment bound holds      = {mean_varphi2 <= varphi2_bound + 1e-12}")
        print(f"  E[a^3 G_B]                     = {mean_g_ren:.6f}")
        print(f"  AN-21 insertion bound holds    = {mean_g_ren <= m_ren_bound + 1e-12}")
        print()

    drifts = [abs(mean_f_values[i + 1] - mean_f_values[i]) for i in range(len(mean_f_values) - 1)]
    print("Cutoff-lift stabilization proxy:")
    print(f"  |Delta_R E[F_R]| sequence      = {[round(x, 6) for x in drifts]}")


if __name__ == "__main__":
    main()
