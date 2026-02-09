#!/usr/bin/env python3.12
"""Claim 1 AN-25 check: d=3 local class-extension diagnostics.

Run:
  python3.12 research/workspace/simulations/claim1_d3_an25_class_extension_check.py
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


def weighted_probability(mask: np.ndarray, logw: np.ndarray) -> float:
    return weighted_expectation(mask.astype(np.float64), logw)


def radial_compact_cutoff(radius: np.ndarray, rcut: float) -> np.ndarray:
    t = 1.0 - (radius / rcut) ** 2
    return np.where(radius < rcut, t * t, 0.0)


def one_dim_compact_cutoff(v: np.ndarray, rcut: float) -> np.ndarray:
    t = 1.0 - (v / rcut) ** 2
    return np.where(np.abs(v) < rcut, t * t, 0.0)


def d_one_dim_compact_cutoff(v: np.ndarray, rcut: float) -> np.ndarray:
    z = (v / rcut) ** 2
    return np.where(np.abs(v) < rcut, (-4.0 * v / (rcut * rcut)) * (1.0 - z), 0.0)


def main() -> None:
    seed = 20260209
    rng = np.random.default_rng(seed)

    p = Params(a=0.7, m2=1.1, lam=0.8, kappa=0.12, c=0.9, lbox=2)
    idx_map = build_index_map(p.lbox)

    n_sites = p.lbox**3
    n_samples = 180000
    sample_radius = 3.6
    fields = rng.uniform(-sample_radius, sample_radius, size=(n_samples, n_sites))

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
    varphi0 = (p.a ** 1.5) * fields[:, x0]
    varphi1 = (p.a ** 1.5) * fields[:, x1]
    radius = np.sqrt(varphi0 * varphi0 + varphi1 * varphi1)

    observable = np.tanh(varphi0) + 0.2 * np.arctan(varphi1)
    mean_observable = weighted_expectation(observable, logw)
    max_abs_observable = float(np.max(np.abs(observable)))
    mean_radius_sq = weighted_expectation(radius * radius, logw)

    print("Claim 1 AN-25 d=3 local class-extension diagnostics")
    print(f"seed={seed}")
    print(
        "params: "
        f"a={p.a}, m2={p.m2}, lambda={p.lam}, kappa={p.kappa}, c={p.c}, L={p.lbox}"
    )
    print(f"importance samples={n_samples}, sampling cube radius={sample_radius}")
    print()
    print("Observable-side C_c -> C_b approximation (radial compact cutoffs):")
    print(f"  mean E[F] (noncompact bounded F) = {mean_observable:.6f}")
    print(f"  max |F| on sample                = {max_abs_observable:.6f}")
    print(f"  E[||v_B||^2]                     = {mean_radius_sq:.6f}")

    cutoff_grid = [0.8, 1.2, 1.6, 2.0, 2.4, 2.8]
    for rcut in cutoff_grid:
        chi = radial_compact_cutoff(radius, rcut)
        observable_cut = chi * observable
        mean_cut = weighted_expectation(observable_cut, logw)
        err = abs(mean_observable - mean_cut)

        tail_prob = weighted_probability(radius > rcut, logw)
        coarse_bound = max_abs_observable * tail_prob
        markov_bound = max_abs_observable * mean_radius_sq / (rcut * rcut)

        print(f"  R={rcut:.1f}  |E[F]-E[F_R]|={err:.6e}  M*P(||v||>R)={coarse_bound:.6e}  M*E[||v||^2]/R^2={markov_bound:.6e}")

    print()
    print("SD residual behavior for bounded noncompact C_b^1 probe psi(v)=tanh(v):")

    psi = np.tanh(varphi0)
    dpsi_dvarphi = 1.0 / np.cosh(varphi0) ** 2
    dpsi_dphi = (p.a ** 1.5) * dpsi_dvarphi

    dgrad = np.zeros(n_samples, dtype=np.float64)
    x0_site = (0, 0, 0)
    for axis in range(3):
        ip = idx_map[shift(x0_site, axis, +1, p.lbox)]
        im = idx_map[shift(x0_site, axis, -1, p.lbox)]
        dgrad += (fields[:, x0] - fields[:, ip]) + (fields[:, x0] - fields[:, im])

    dsi = (p.a**3) * (p.m2 * fields[:, x0] + p.lam * fields[:, x0] ** 3) + p.kappa * p.a * dgrad
    residual_noncompact = weighted_expectation(dpsi_dphi, logw) - weighted_expectation(
        p.c * psi * dsi, logw
    )
    print(f"  residual (noncompact psi)       = {residual_noncompact:.6e}")

    print("  cutoff-approximant residuals psi_R = chi_R * psi:")
    for rcut in cutoff_grid:
        chi1 = one_dim_compact_cutoff(varphi0, rcut)
        dchi1 = d_one_dim_compact_cutoff(varphi0, rcut)
        psi_r = chi1 * psi
        dpsi_r_dvarphi = dchi1 * psi + chi1 * dpsi_dvarphi
        dpsi_r_dphi = (p.a ** 1.5) * dpsi_r_dvarphi

        residual_r = weighted_expectation(dpsi_r_dphi, logw) - weighted_expectation(
            p.c * psi_r * dsi, logw
        )
        print(f"    R={rcut:.1f}  residual={residual_r:.6e}")

    print()
    print("Renormalized moment/insertion checks (AN-24 compatibility):")
    mean_varphi2 = weighted_expectation(varphi0 * varphi0, logw)
    b_sites = {(0, 0, 0), (1, 0, 0)}
    edge_count = len(local_edges(b_sites, p.lbox))
    m2_bound = 1.0 / (p.c * p.m2)
    insertion_bound = 4.0 * edge_count / (p.c * p.m2)

    g_raw = np.zeros(n_samples, dtype=np.float64)
    for sx, sy in local_edges(b_sites, p.lbox):
        ix = idx_map[sx]
        iy = idx_map[sy]
        diff = fields[:, ix] - fields[:, iy]
        g_raw += diff * diff
    mean_g_ren = weighted_expectation((p.a**3) * g_raw, logw)

    print(f"  E[varphi_0^2]                   = {mean_varphi2:.6f}  <= 1/(c m2)={m2_bound:.6f}")
    print(f"  E[a^3 G_B]                      = {mean_g_ren:.6f}  <= M_B^ren={insertion_bound:.6f}")


if __name__ == "__main__":
    main()
