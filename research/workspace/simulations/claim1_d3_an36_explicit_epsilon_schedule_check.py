#!/usr/bin/env python3.12
"""AN-36 explicit epsilon-index schedule diagnostics."""

from __future__ import annotations

import math

import numpy as np


def n_epsilon(eps: float, a_env: float, c_t: float, rho: float) -> int:
    return int(math.ceil(math.log((2.0 * a_env * c_t) / eps) / abs(math.log(rho))))


def k_epsilon(eps: float, b_env: float, c_e: float, q: float) -> int:
    return int(math.ceil(math.log((2.0 * b_env * c_e) / eps) / abs(math.log(q))))


def main() -> None:
    # AN-35/AN-36 scoped constants.
    a_env = 1.35
    b_env = 0.92
    rho = 0.66
    c_t = 1.0 / (1.0 - rho)

    eta0 = 0.32
    alpha = 0.75
    lam = 0.57
    q = max(2.0 ** (-alpha), lam)
    c_e = eta0**alpha + 1.0

    eps_grid = [1.0e-1, 5.0e-2, 2.0e-2, 1.0e-2, 5.0e-3, 2.0e-3, 1.0e-3, 5.0e-4]

    monotone_n = True
    monotone_k = True
    bound_ok = True
    worst_gap = 0.0

    prev_n = -1
    prev_k = -1

    rows: list[tuple[float, int, int, float]] = []
    for eps in eps_grid:
        n_eps = n_epsilon(eps, a_env, c_t, rho)
        k_eps = k_epsilon(eps, b_env, c_e, q)

        if prev_n > n_eps:
            monotone_n = False
        if prev_k > k_eps:
            monotone_k = False
        prev_n, prev_k = n_eps, k_eps

        max_error = 0.0
        # Sample a deterministic tail block beyond the schedule indices.
        for n in range(n_eps, n_eps + 20):
            t_n = c_t * (rho**n)
            for k in range(k_eps, k_eps + 20):
                e_k = eta0**alpha * (2.0 ** (-alpha * k)) + lam**k
                err_bound = a_env * t_n + b_env * e_k
                max_error = max(max_error, err_bound)
                gap = err_bound - eps
                worst_gap = max(worst_gap, gap)
                if gap > 1.0e-12:
                    bound_ok = False
        rows.append((eps, n_eps, k_eps, max_error))

    print("AN-36 explicit epsilon schedule diagnostic")
    print(f"A={a_env:.6f}, B={b_env:.6f}")
    print(f"rho={rho:.6f}, C_t={c_t:.6f}")
    print(f"eta0={eta0:.6f}, alpha={alpha:.6f}, lambda={lam:.6f}")
    print(f"q={q:.6f}, C_e={c_e:.6f}")
    print("epsilon_schedule_rows:")
    for eps, n_eps, k_eps, max_error in rows:
        print(
            f"  eps={eps:.1e}: n_eps={n_eps:3d}, k_eps={k_eps:3d}, "
            f"max_bound_in_tail_block={max_error:.8e}"
        )
    print(f"worst_gap={worst_gap:.8e}")
    print(f"check_monotone_n_schedule={monotone_n}")
    print(f"check_monotone_k_schedule={monotone_k}")
    print(f"check_tail_block_bound={bound_ok}")
    print(f"all_checks_pass={monotone_n and monotone_k and bound_ok}")


if __name__ == "__main__":
    main()
