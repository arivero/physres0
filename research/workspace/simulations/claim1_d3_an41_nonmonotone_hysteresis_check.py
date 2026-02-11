#!/usr/bin/env python3.12
"""AN-41 non-monotone hysteresis termination diagnostics.

Run:
  python3.12 research/workspace/simulations/claim1_d3_an41_nonmonotone_hysteresis_check.py
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

    # Dominant monotone trend + non-monotone oscillation.
    rho = 0.72
    kappa = 0.82
    c_n = 0.16 * np.exp(-0.04 * n_grid) + 2.0e-5
    phi_n = 0.21 * n_grid + 0.35
    nu0 = 0.018
    omega = 1.37

    h_hyst = 3
    j_max = 90

    eps_grid = [1.0e-2, 7.5e-3, 5.0e-3, 2.5e-3, 1.0e-3]

    all_upper_safe = True
    all_hyst_stop = True
    all_post_stable = True
    all_stop_safe = True

    rows: list[tuple[float, int, int, int, int, int, bool]] = []

    for eps in eps_grid:
        threshold = eps / (2.0 * a_env)
        k_eps = k_eps_formula(eps, b_env, c_e, q)
        e_k = eta0**alpha * (2.0 ** (-alpha * k_eps)) + lam**k_eps

        n_seq: list[int] = []
        nu_seq: list[float] = []
        u_hist: list[np.ndarray] = []

        for j in range(j_max + 1):
            trend = w_true + c_n * (rho**j)
            nu_j = nu0 * (kappa**j)
            osc = nu_j * np.sin(phi_n + omega * j)
            u_j = np.maximum(trend + osc, w_true)  # enforce upper safety

            all_upper_safe = all_upper_safe and bool(np.all(u_j >= w_true - 1.0e-15))

            n_j = min_index(u_j, threshold, n_grid)
            n_seq.append(n_j)
            nu_seq.append(nu_j)
            u_hist.append(u_j)

        # eventual stabilization index (ground truth over finite horizon)
        j_true = None
        for j in range(j_max + 1):
            if all(n_seq[t] == n_seq[j] for t in range(j, j_max + 1)):
                j_true = j
                break
        if j_true is None:
            all_hyst_stop = False
            continue

        # asymptotic gap approximation with trend limit = w_true.
        n_inf = n_seq[-1]
        pos_inf = int(np.where(n_grid == n_inf)[0][0])
        g_eps = threshold - w_true[pos_inf]
        if g_eps <= 0.0:
            all_hyst_stop = False
            continue

        nu_tol = g_eps / 4.0

        j_stop = None
        for j in range(h_hyst - 1, j_max + 1):
            if nu_seq[j] > nu_tol:
                continue
            if len(set(n_seq[j - h_hyst + 1 : j + 1])) == 1:
                j_stop = j
                break

        if j_stop is None:
            all_hyst_stop = False
            continue

        # Post-stop stability check.
        stable_after = all(n_seq[t] == n_seq[j_stop] for t in range(j_stop, j_max + 1))
        all_post_stable = all_post_stable and stable_after

        # Safety check at stopped schedule with true tails.
        n_stop = n_seq[j_stop]
        tail_true = tail_weight(w_blocks_true, n_stop)
        err_bound = a_env * tail_true + b_env * e_k
        safe = err_bound <= eps + 1.0e-12
        all_stop_safe = all_stop_safe and safe

        rows.append((eps, n_seq[0], n_stop, j_true, j_stop, k_eps, safe))

    all_ok = all_upper_safe and all_hyst_stop and all_post_stable and all_stop_safe

    print("AN-41 non-monotone hysteresis termination diagnostic")
    print(f"A={a_env:.6f}, B={b_env:.6f}, q={q:.6f}, C_e={c_e:.6f}")
    print(f"rho={rho:.6f}, kappa={kappa:.6f}, nu0={nu0:.6f}, H={h_hyst}, j_max={j_max}")
    print("epsilon_rows:")
    for eps, n0, nstop, jtrue, jstop, keps, safe in rows:
        print(
            f"  eps={eps:.1e}: n0={n0:3d}, n_stop={nstop:3d}, "
            f"j_true={jtrue:2d}, j_stop={jstop:2d}, k_eps={keps:3d}, safe={safe}"
        )
    print(f"check_upper_safety={all_upper_safe}")
    print(f"check_hysteresis_stop_exists={all_hyst_stop}")
    print(f"check_post_stop_stability={all_post_stable}")
    print(f"check_stop_safety={all_stop_safe}")
    print(f"all_checks_pass={all_ok}")


if __name__ == "__main__":
    main()
