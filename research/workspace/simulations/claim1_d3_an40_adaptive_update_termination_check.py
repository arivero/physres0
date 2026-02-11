#!/usr/bin/env python3.12
"""AN-40 adaptive-update stabilization diagnostics.

Run:
  python3.12 research/workspace/simulations/claim1_d3_an40_adaptive_update_termination_check.py
"""

from __future__ import annotations

import math

import numpy as np


def tail_weight(weights: np.ndarray, n: int) -> float:
    return float(np.sum(weights[n:]))


def k_eps_formula(eps: float, b_env: float, c_e: float, q: float) -> int:
    return int(math.ceil(math.log((2.0 * b_env * c_e) / eps) / abs(math.log(q))))


def min_index(values: np.ndarray, threshold: float, n_grid: np.ndarray) -> int:
    ids = np.where(values <= threshold)[0]
    if len(ids) == 0:
        raise RuntimeError("no admissible schedule index")
    return int(n_grid[ids[0]])


def main() -> None:
    # Envelope constants.
    a_env = 1.35
    b_env = 0.92
    eta0 = 0.32
    alpha = 0.75
    lam = 0.57

    q = max(2.0 ** (-alpha), lam)
    c_e = eta0**alpha + 1.0

    # Deterministic true tails.
    num_blocks = 520
    idx = np.arange(1, num_blocks + 1, dtype=float)
    w_blocks_true = 0.58**idx + 0.015 / (idx**2)

    n_grid = np.arange(6, 340)
    w_true = np.array([tail_weight(w_blocks_true, int(n)) for n in n_grid], dtype=float)

    # Update envelope model: U^(j) = w_true + C_n * rho^j
    rho = 0.70
    c_n = 0.20 * np.exp(-0.045 * n_grid) + 3.0e-5

    # Update depth budget for empirical stabilization check.
    j_max = 40

    eps_grid = [1.0e-2, 7.5e-3, 5.0e-3, 2.5e-3, 1.0e-3]

    all_mono = True
    all_stable = True
    all_bound_ok = True
    all_safe = True

    rows: list[tuple[float, int, int, int, int, int, int, float]] = []

    for eps in eps_grid:
        threshold = eps / (2.0 * a_env)
        k_eps = k_eps_formula(eps, b_env, c_e, q)
        e_k = eta0**alpha * (2.0 ** (-alpha * k_eps)) + lam**k_eps

        # Build schedule trajectory over updates.
        n_seq = []
        for j in range(j_max + 1):
            u_j = w_true + c_n * (rho**j)
            n_j = min_index(u_j, threshold, n_grid)
            n_seq.append(n_j)

            # Per-update safety check at selected schedule.
            tail_true = tail_weight(w_blocks_true, n_j)
            err_bound = a_env * tail_true + b_env * e_k
            if err_bound > eps + 1.0e-12:
                all_safe = False

        # Monotonicity and finite stabilization checks.
        mono = all(n_seq[t + 1] <= n_seq[t] for t in range(len(n_seq) - 1))
        all_mono = all_mono and mono

        # Observed stabilization index.
        j_obs = 0
        for j in range(len(n_seq) - 1):
            if all(n_seq[t] == n_seq[j] for t in range(j, len(n_seq))):
                j_obs = j
                break

        n_inf = n_seq[-1]
        n_inf_pos = int(np.where(n_grid == n_inf)[0][0])
        g_eps = threshold - w_true[n_inf_pos]
        c_inf = c_n[n_inf_pos]

        if g_eps <= 0.0:
            raise RuntimeError("strict asymptotic gap not satisfied")

        j_bound = max(0, int(math.ceil(math.log(c_inf / g_eps) / abs(math.log(rho)))))
        bound_ok = j_obs <= j_bound

        all_stable = all_stable and (j_obs <= j_max)
        all_bound_ok = all_bound_ok and bound_ok

        rows.append((eps, n_seq[0], n_inf, j_obs, j_bound, k_eps, int(n_seq[j_obs]), g_eps))

    all_ok = all_mono and all_stable and all_bound_ok and all_safe

    print("AN-40 adaptive-update stabilization diagnostic")
    print(f"A={a_env:.6f}, B={b_env:.6f}, q={q:.6f}, C_e={c_e:.6f}")
    print(f"rho={rho:.6f}, j_max={j_max}, num_blocks={num_blocks}")
    print("epsilon_rows:")
    for eps, n0, ninf, jobs, jbound, keps, njobs, geps in rows:
        print(
            f"  eps={eps:.1e}: n0={n0:3d}, n_inf={ninf:3d}, "
            f"j_obs={jobs:2d}, j_bound={jbound:2d}, k_eps={keps:3d}, "
            f"n_at_j_obs={njobs:3d}, gap={geps:.3e}"
        )
    print(f"check_schedule_monotone={all_mono}")
    print(f"check_finite_stabilization={all_stable}")
    print(f"check_geometric_bound={all_bound_ok}")
    print(f"check_per_update_safety={all_safe}")
    print(f"all_checks_pass={all_ok}")


if __name__ == "__main__":
    main()
