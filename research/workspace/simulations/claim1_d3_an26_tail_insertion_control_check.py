#!/usr/bin/env python3.12
"""Claim 1 AN-26 check: d=3 SD-test tail insertion-control diagnostics.

Run:
  python3.12 research/workspace/simulations/claim1_d3_an26_tail_insertion_control_check.py
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


def build_index_map(lbox: int) -> dict[Site, int]:
    return {x: idx for idx, x in enumerate(sites(lbox))}


def weighted_expectation(values: np.ndarray, logw: np.ndarray) -> float:
    pivot = float(np.max(logw))
    w = np.exp(logw - pivot)
    return float(np.sum(w * values) / np.sum(w))


def weighted_probability(mask: np.ndarray, logw: np.ndarray) -> float:
    return weighted_expectation(mask.astype(np.float64), logw)


def radial_compact_cutoff(v0: np.ndarray, v1: np.ndarray, rcut: float) -> np.ndarray:
    z = (v0 * v0 + v1 * v1) / (rcut * rcut)
    return np.where(z < 1.0, (1.0 - z) * (1.0 - z), 0.0)


def d_radial_compact_cutoff_dv0(v0: np.ndarray, v1: np.ndarray, rcut: float) -> np.ndarray:
    z = (v0 * v0 + v1 * v1) / (rcut * rcut)
    return np.where(z < 1.0, (-4.0 * v0 / (rcut * rcut)) * (1.0 - z), 0.0)


def main() -> None:
    seed = 2026020901
    rng = np.random.default_rng(seed)

    p = Params(a=0.7, m2=1.1, lam=0.8, kappa=0.12, c=0.9, lbox=2)
    idx_map = build_index_map(p.lbox)

    n_sites = p.lbox**3
    n_samples = 220000
    sample_radius = 3.8
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

    psi = np.tanh(varphi0) + 0.2 * np.tanh(varphi1)
    dpsi_dvarphi0 = 1.0 / np.cosh(varphi0) ** 2
    dpsi_dphi0 = (p.a ** 1.5) * dpsi_dvarphi0

    dgrad = np.zeros(n_samples, dtype=np.float64)
    x0_site = (0, 0, 0)
    for axis in range(3):
        ip = idx_map[shift(x0_site, axis, +1, p.lbox)]
        im = idx_map[shift(x0_site, axis, -1, p.lbox)]
        dgrad += (fields[:, x0] - fields[:, ip]) + (fields[:, x0] - fields[:, im])

    dsi = (p.a**3) * (p.m2 * fields[:, x0] + p.lam * fields[:, x0] ** 3) + p.kappa * p.a * dgrad
    residual_noncompact = weighted_expectation(dpsi_dphi0, logw) - weighted_expectation(
        p.c * psi * dsi, logw
    )

    tail_moment_q2 = weighted_expectation(dsi * dsi, logw)
    tail_moment_q1 = weighted_expectation(np.abs(dsi), logw)
    block_second_moment = weighted_expectation(radius * radius, logw)

    print("Claim 1 AN-26 d=3 SD-test tail insertion-control diagnostics")
    print(f"seed={seed}")
    print(
        "params: "
        f"a={p.a}, m2={p.m2}, lambda={p.lam}, kappa={p.kappa}, c={p.c}, L={p.lbox}"
    )
    print(f"importance samples={n_samples}, sampling cube radius={sample_radius}")
    print()
    print("Global proxy moments for Holder/Markov tail bounds:")
    print(f"  E[|d_i S|]                      = {tail_moment_q1:.6f}")
    print(f"  E[|d_i S|^2]                    = {tail_moment_q2:.6f}")
    print(f"  E[||v_B||^2]                    = {block_second_moment:.6f}")
    print()
    print("SD residual for bounded noncompact test:")
    print(f"  residual (noncompact psi)       = {residual_noncompact:.6e}")
    print()
    print("Tail insertion-control and cutoff-approximant diagnostics:")

    cutoff_grid = [0.8, 1.2, 1.6, 2.0, 2.4, 2.8]
    for rcut in cutoff_grid:
        chi = radial_compact_cutoff(varphi0, varphi1, rcut)
        dchi_dv0 = d_radial_compact_cutoff_dv0(varphi0, varphi1, rcut)

        psi_r = chi * psi
        dpsi_r_dvarphi0 = dchi_dv0 * psi + chi * dpsi_dvarphi0
        dpsi_r_dphi0 = (p.a ** 1.5) * dpsi_r_dvarphi0

        residual_r = weighted_expectation(dpsi_r_dphi0, logw) - weighted_expectation(
            p.c * psi_r * dsi, logw
        )

        tail_mask = radius > rcut
        tail_prob = weighted_probability(tail_mask, logw)
        insertion_tail = weighted_expectation(np.abs(dsi) * tail_mask.astype(np.float64), logw)
        holder_from_prob = np.sqrt(tail_moment_q2) * np.sqrt(tail_prob)
        markov_prob = block_second_moment / (rcut * rcut)
        holder_markov = np.sqrt(tail_moment_q2) * np.sqrt(markov_prob)

        deriv_tail = weighted_expectation(np.abs(dpsi_dphi0 - dpsi_r_dphi0), logw)
        sd_term_tail = p.c * weighted_expectation(np.abs(psi - psi_r) * np.abs(dsi), logw)

        print(f"  R={rcut:.1f}")
        print(f"    insertion tail E[|d_iS| 1_tail]   = {insertion_tail:.6e}")
        print(f"    Holder(sqrt(E[d_iS^2]P_tail))     = {holder_from_prob:.6e}")
        print(f"    Holder+Markov proxy               = {holder_markov:.6e}")
        print(f"    derivative-tail error             = {deriv_tail:.6e}")
        print(f"    SD insertion-tail term            = {sd_term_tail:.6e}")
        print(f"    residual(psi_R)                   = {residual_r:.6e}")


if __name__ == "__main__":
    main()
