#!/usr/bin/env python3.12
"""AN-38 hybrid robust epsilon-schedule diagnostics."""

from __future__ import annotations

import math

import numpy as np


def tail_weight(weights: np.ndarray, n: int) -> float:
    return float(np.sum(weights[n:]))


def n_eps_proxy(eps: float, a_env: float, c_t: float, rho: float) -> int:
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

    # AN-31 deterministic tail proxy used in existing diagnostics.
    num_blocks = 480
    idx = np.arange(1, num_blocks + 1, dtype=float)
    weights = 0.58**idx + 0.015 / (idx**2)

    n_grid = np.arange(6, 301)
    w_tail = np.array([tail_weight(weights, int(n)) for n in n_grid])

    # AN-36 constants for proxy schedule.
    rho = 0.66
    c_t = 1.0 / (1.0 - rho)

    # Regularization envelope constants.
    q = max(2.0 ** (-alpha), lam)
    c_e = eta0**alpha + 1.0

    eps_grid = [1.0e-1, 5.0e-2, 2.0e-2, 1.0e-2, 5.0e-3, 2.0e-3, 1.0e-3, 5.0e-4]

    monotone_proxy = True
    monotone_field = True
    monotone_hybrid = True
    monotone_k = True
    safe_hybrid_vs_proxy = True
    safe_hybrid_vs_field = True
    has_proxy_dominant = False
    has_field_dominant = False
    bound_ok = True
    worst_gap = 0.0

    prev_np = -1
    prev_nf = -1
    prev_nh = -1
    prev_k = -1

    rows: list[tuple[float, int, int, int, int, float]] = []
    for eps in eps_grid:
        n_proxy = n_eps_proxy(eps, a_env, c_t, rho)

        thresh = eps / (2.0 * a_env)
        candidates = np.where(w_tail <= thresh)[0]
        if len(candidates) == 0:
            raise RuntimeError(f"no field schedule index found for eps={eps}")
        n_field = int(n_grid[candidates[0]])

        n_hybrid = max(n_proxy, n_field)
        k_eps = k_eps_formula(eps, b_env, c_e, q)

        monotone_proxy = monotone_proxy and (prev_np <= n_proxy or prev_np < 0)
        monotone_field = monotone_field and (prev_nf <= n_field or prev_nf < 0)
        monotone_hybrid = monotone_hybrid and (prev_nh <= n_hybrid or prev_nh < 0)
        monotone_k = monotone_k and (prev_k <= k_eps or prev_k < 0)
        prev_np, prev_nf, prev_nh, prev_k = n_proxy, n_field, n_hybrid, k_eps

        safe_hybrid_vs_proxy = safe_hybrid_vs_proxy and (n_hybrid >= n_proxy)
        safe_hybrid_vs_field = safe_hybrid_vs_field and (n_hybrid >= n_field)

        has_proxy_dominant = has_proxy_dominant or (n_proxy > n_field)
        has_field_dominant = has_field_dominant or (n_field > n_proxy)

        max_bound = 0.0
        for n in range(n_hybrid, n_hybrid + 20):
            t_n = tail_weight(weights, n)
            for k in range(k_eps, k_eps + 20):
                e_k = eta0**alpha * (2.0 ** (-alpha * k)) + lam**k
                err_bound = a_env * t_n + b_env * e_k
                max_bound = max(max_bound, err_bound)
                gap = err_bound - eps
                worst_gap = max(worst_gap, gap)
                if gap > 1.0e-12:
                    bound_ok = False

        rows.append((eps, n_proxy, n_field, n_hybrid, k_eps, max_bound))

    print("AN-38 hybrid robust schedule diagnostic")
    print(f"A={a_env:.6f}, B={b_env:.6f}")
    print(f"eta0={eta0:.6f}, alpha={alpha:.6f}, lambda={lam:.6f}")
    print(f"rho={rho:.6f}, C_t={c_t:.6f}, q={q:.6f}, C_e={c_e:.6f}")
    print(f"num_blocks={num_blocks}")
    print("epsilon_schedule_rows:")
    for eps, n_proxy, n_field, n_hybrid, k_eps, max_bound in rows:
        print(
            f"  eps={eps:.1e}: n_proxy={n_proxy:3d}, n_field={n_field:3d}, "
            f"n_hybrid={n_hybrid:3d}, k_eps={k_eps:3d}, max_bound={max_bound:.8e}"
        )
    print(f"worst_gap={worst_gap:.8e}")
    print(f"check_monotone_proxy={monotone_proxy}")
    print(f"check_monotone_field={monotone_field}")
    print(f"check_monotone_hybrid={monotone_hybrid}")
    print(f"check_monotone_k={monotone_k}")
    print(f"check_hybrid_safety_vs_proxy={safe_hybrid_vs_proxy}")
    print(f"check_hybrid_safety_vs_field={safe_hybrid_vs_field}")
    print(f"check_has_proxy_dominant_regime={has_proxy_dominant}")
    print(f"check_has_field_dominant_regime={has_field_dominant}")
    print(f"check_tail_block_bound={bound_ok}")
    print(
        "all_checks_pass="
        f"{monotone_proxy and monotone_field and monotone_hybrid and monotone_k and safe_hybrid_vs_proxy and safe_hybrid_vs_field and has_proxy_dominant and has_field_dominant and bound_ok}"
    )


if __name__ == "__main__":
    main()
