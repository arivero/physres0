#!/usr/bin/env python3.12
"""AN-37 field-tail calibrated epsilon-schedule diagnostics."""

from __future__ import annotations

import math

import numpy as np


def tail_weight(weights: np.ndarray, n: int) -> float:
    return float(np.sum(weights[n:]))


def n_eps_geometric(eps: float, a_env: float, c_t: float, rho: float) -> int:
    return int(math.ceil(math.log((2.0 * a_env * c_t) / eps) / abs(math.log(rho))))


def k_eps_formula(eps: float, b_env: float, c_e: float, q: float) -> int:
    return int(math.ceil(math.log((2.0 * b_env * c_e) / eps) / abs(math.log(q))))


def main() -> None:
    # AN-35 constants.
    a_env = 1.35
    b_env = 0.92
    eta0 = 0.32
    alpha = 0.75
    lam = 0.57

    # AN-31 deterministic tail model.
    num_blocks = 480
    idx = np.arange(1, num_blocks + 1, dtype=float)
    weights = 0.58**idx + 0.015 / (idx**2)

    n_grid = np.arange(6, 241)
    w_tail = np.array([tail_weight(weights, int(n)) for n in n_grid])

    # Regularization envelope summary constants.
    q = max(2.0 ** (-alpha), lam)
    c_e = eta0**alpha + 1.0

    # AN-36 geometric proxy reference.
    rho = 0.66
    c_t = 1.0 / (1.0 - rho)

    eps_grid = [1.0e-1, 5.0e-2, 2.0e-2, 1.0e-2, 5.0e-3, 2.0e-3, 1.0e-3, 5.0e-4]

    monotone_tail = bool(np.all(np.diff(w_tail) <= 1.0e-14))
    tail_decay = bool(w_tail[-1] < 1.0e-3 * w_tail[0])

    monotone_n_field = True
    monotone_n_geo = True
    monotone_k = True
    has_field_better = False
    has_field_worse = False
    bound_ok = True
    worst_gap = 0.0

    prev_nf = -1
    prev_ng = -1
    prev_k = -1

    rows: list[tuple[float, int, int, int, float]] = []
    for eps in eps_grid:
        # Field-calibrated n: first index where A*W_tail <= eps/2.
        thresh = eps / (2.0 * a_env)
        candidates = np.where(w_tail <= thresh)[0]
        if len(candidates) == 0:
            raise RuntimeError(f"no field n found for eps={eps}")
        n_field = int(n_grid[candidates[0]])
        n_geo = n_eps_geometric(eps, a_env, c_t, rho)
        k_eps = k_eps_formula(eps, b_env, c_e, q)

        if prev_nf > n_field:
            monotone_n_field = False
        if prev_ng > n_geo:
            monotone_n_geo = False
        if prev_k > k_eps:
            monotone_k = False
        prev_nf, prev_ng, prev_k = n_field, n_geo, k_eps

        if n_field < n_geo:
            has_field_better = True
        if n_field > n_geo:
            has_field_worse = True

        max_bound = 0.0
        for n in range(n_field, n_field + 20):
            t_n = tail_weight(weights, n)
            for k in range(k_eps, k_eps + 20):
                e_k = eta0**alpha * (2.0 ** (-alpha * k)) + lam**k
                err_bound = a_env * t_n + b_env * e_k
                max_bound = max(max_bound, err_bound)
                gap = err_bound - eps
                worst_gap = max(worst_gap, gap)
                if gap > 1.0e-12:
                    bound_ok = False

        rows.append((eps, n_field, n_geo, k_eps, max_bound))

    print("AN-37 field-tail schedule diagnostic")
    print(f"A={a_env:.6f}, B={b_env:.6f}")
    print(f"eta0={eta0:.6f}, alpha={alpha:.6f}, lambda={lam:.6f}")
    print(f"q={q:.6f}, C_e={c_e:.6f}")
    print(f"num_blocks={num_blocks}")
    print(f"n_grid=[{int(n_grid[0])},...,{int(n_grid[-1])}]")
    print(f"tail_first={w_tail[0]:.8e}")
    print(f"tail_last={w_tail[-1]:.8e}")
    print("epsilon_schedule_rows:")
    for eps, n_field, n_geo, k_eps, max_bound in rows:
        print(
            f"  eps={eps:.1e}: n_field={n_field:3d}, n_geo={n_geo:3d}, "
            f"k_eps={k_eps:3d}, max_bound={max_bound:.8e}"
        )
    print(f"worst_gap={worst_gap:.8e}")
    print(f"check_tail_monotone={monotone_tail}")
    print(f"check_tail_decay={tail_decay}")
    print(f"check_monotone_n_field={monotone_n_field}")
    print(f"check_monotone_n_geo={monotone_n_geo}")
    print(f"check_monotone_k={monotone_k}")
    print(f"check_has_field_better_regime={has_field_better}")
    print(f"check_has_field_worse_regime={has_field_worse}")
    print(f"check_tail_block_bound={bound_ok}")
    print(
        "all_checks_pass="
        f"{monotone_tail and tail_decay and monotone_n_field and monotone_n_geo and monotone_k and has_field_better and has_field_worse and bound_ok}"
    )


if __name__ == "__main__":
    main()
