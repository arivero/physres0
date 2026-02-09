#!/usr/bin/env python3.12
"""Claim 1 AN-23 check: compact-spin d=3 scoped B1-B4 closure diagnostics.

Run:
  python3.12 research/workspace/simulations/claim1_d3_an23_compact_spin_closure_check.py
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
    rcut: float


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


def psi_boundary_vanishing(u: np.ndarray, rcut: float) -> np.ndarray:
    t = 1.0 - (u / rcut) ** 2
    return u * t * t


def d_psi_boundary_vanishing(u: np.ndarray, rcut: float) -> np.ndarray:
    z = (u / rcut) ** 2
    return (1.0 - z) * (1.0 - 5.0 * z)


def weighted_expectation(values: np.ndarray, logw: np.ndarray) -> float:
    pivot = float(np.max(logw))
    w = np.exp(logw - pivot)
    return float(np.sum(w * values) / np.sum(w))


def evaluate_for_kappa(
    fields: np.ndarray,
    p_base: Params,
    kappa: float,
    idx_map: dict[Site, int],
) -> tuple[float, float, float, float]:
    n_samples = fields.shape[0]
    assert n_samples > 0

    x0 = idx_map[(0, 0, 0)]
    x1 = idx_map[(1, 0, 0)]
    phi0 = fields[:, x0]
    phi1 = fields[:, x1]

    pot = 0.5 * p_base.m2 * np.sum(fields * fields, axis=1) + 0.25 * p_base.lam * np.sum(
        fields**4, axis=1
    )

    grad = np.zeros(n_samples, dtype=np.float64)
    for sx, sy in unique_edges(p_base.lbox):
        ix = idx_map[sx]
        iy = idx_map[sy]
        diff = fields[:, ix] - fields[:, iy]
        grad += diff * diff

    action = (p_base.a**3) * pot + 0.5 * kappa * p_base.a * grad
    logw = -p_base.c * action

    obs_f = np.tanh(phi0) + 0.3 * np.tanh(phi1)
    mean_f = weighted_expectation(obs_f, logw)

    psi = psi_boundary_vanishing(phi0, p_base.rcut)
    dpsi = d_psi_boundary_vanishing(phi0, p_base.rcut)

    dgrad = np.zeros(n_samples, dtype=np.float64)
    x0_site = (0, 0, 0)
    for axis in range(3):
        y_plus = idx_map[shift(x0_site, axis, +1, p_base.lbox)]
        y_minus = idx_map[shift(x0_site, axis, -1, p_base.lbox)]
        dgrad += (phi0 - fields[:, y_plus]) + (phi0 - fields[:, y_minus])

    dsi = (p_base.a**3) * (p_base.m2 * phi0 + p_base.lam * phi0**3) + kappa * p_base.a * dgrad
    sd_residual = weighted_expectation(dpsi, logw) - weighted_expectation(p_base.c * psi * dsi, logw)

    b_sites = {(0, 0, 0), (1, 0, 0)}
    gren_raw = np.zeros(n_samples, dtype=np.float64)
    for sx, sy in local_edges(b_sites, p_base.lbox):
        ix = idx_map[sx]
        iy = idx_map[sy]
        diff = fields[:, ix] - fields[:, iy]
        gren_raw += diff * diff
    mean_g_ren = weighted_expectation((p_base.a**3) * gren_raw, logw)

    mean_phi2 = weighted_expectation(phi0 * phi0, logw)
    return mean_f, sd_residual, mean_g_ren, mean_phi2


def main() -> None:
    seed = 20260209
    rng = np.random.default_rng(seed)

    p_base = Params(a=0.7, m2=1.1, lam=0.8, kappa=0.0, c=0.9, lbox=2, rcut=2.0)
    kappa0 = 0.0
    kappa1 = 0.12
    n_samples = 180000

    idx_map = build_index_map(p_base.lbox)
    n_sites = p_base.lbox**3
    fields = rng.uniform(-p_base.rcut, p_base.rcut, size=(n_samples, n_sites))

    f0, sd0, gren0, phi20 = evaluate_for_kappa(fields, p_base, kappa0, idx_map)
    f1, sd1, gren1, phi21 = evaluate_for_kappa(fields, p_base, kappa1, idx_map)

    lipschitz_est = abs(f1 - f0) / kappa1
    b1_bound = p_base.rcut * p_base.rcut

    b_sites = {(0, 0, 0), (1, 0, 0)}
    edge_count = len(local_edges(b_sites, p_base.lbox))
    m_ren_bound = 4.0 * edge_count / (p_base.c * p_base.m2)

    print("Claim 1 AN-23 compact-spin d=3 closure diagnostics")
    print(f"seed={seed}")
    print(
        "params: "
        f"a={p_base.a}, m2={p_base.m2}, lambda={p_base.lam}, c={p_base.c}, "
        f"L={p_base.lbox}, R={p_base.rcut}"
    )
    print(f"kappa values: {kappa0}, {kappa1}")
    print(f"importance samples={n_samples}")
    print(f"AN-21 renormalized moment bound M_B^ren={m_ren_bound:.6f}")
    print()

    print("B1 compact-spin moment check:")
    print(f"  E[phi_0^2] at kappa=0      = {phi20:.6f} <= R^2={b1_bound:.6f}")
    print(f"  E[phi_0^2] at kappa={kappa1} = {phi21:.6f} <= R^2={b1_bound:.6f}")
    print()

    print("B3 positivity check (analytic):")
    print("  integrand exp(-c S) is strictly positive on compact domain [-R,R]^N")
    print("  therefore finite-volume partition factor Z is strictly positive")
    print()

    print("B4 SD identity residuals for boundary-vanishing psi:")
    print(f"  residual at kappa=0         = {sd0:.6e}")
    print(f"  residual at kappa={kappa1}  = {sd1:.6e}")
    print()

    print("B5 proxy (small-kappa increment + renormalized insertion):")
    print(f"  mean F(kappa=0)             = {f0:.6f}")
    print(f"  mean F(kappa={kappa1})      = {f1:.6f}")
    print(f"  |Delta F|/kappa             = {lipschitz_est:.6f}")
    print(f"  mean a^3 G_B (kappa=0)      = {gren0:.6f}")
    print(f"  mean a^3 G_B (kappa={kappa1}) = {gren1:.6f}")
    print(f"  bound check kappa=0         = {gren0 <= m_ren_bound + 1e-12}")
    print(f"  bound check kappa={kappa1}  = {gren1 <= m_ren_bound + 1e-12}")


if __name__ == "__main__":
    main()
