#!/usr/bin/env python3.12
"""AN-35 concrete envelope commuting-limit diagnostics."""

from __future__ import annotations

from itertools import combinations

import numpy as np


def tail_weight(weights: np.ndarray, n: int) -> float:
    return float(np.sum(weights[n:]))


def main() -> None:
    seed = 2026021101
    rng = np.random.default_rng(seed)

    num_blocks = 180
    n_levels = np.arange(12, 121)  # exhaustion index n
    k_levels = np.arange(0, 23)  # regularization index k

    eta0 = 0.32
    alpha = 0.75
    lam = 0.57

    a_env = 1.35
    b_env = 0.92

    idx = np.arange(1, num_blocks + 1, dtype=float)
    weights = 0.66**idx + 0.012 / (idx**2)
    t_n = np.array([tail_weight(weights, int(n)) for n in n_levels])

    eta_k = eta0 * (2.0 ** (-k_levels))
    e_k = eta_k**alpha + lam**k_levels

    # Synthetic channel meeting wrapper assumptions by construction.
    limit = complex(0.81, -0.17)
    phase_k = np.exp(1j * (0.19 * k_levels))
    l_k = limit + 0.74 * b_env * e_k * phase_k

    u_kn = np.zeros((len(k_levels), len(n_levels)), dtype=np.complex128)
    for i, k in enumerate(k_levels):
        for j, n in enumerate(n_levels):
            modulation = np.exp(1j * (0.11 * k + 0.07 * n))
            noise = 0.02 * (rng.uniform(-1.0, 1.0) + 1j * rng.uniform(-1.0, 1.0))
            psi = (1.0 + noise) * modulation
            psi /= max(1.0, abs(psi))
            u_kn[i, j] = l_k[i] + 0.82 * a_env * t_n[j] * psi

    # Envelope assumption checks.
    max_gap_exhaustion = 0.0
    check_exhaustion_env = True
    for i, _ in enumerate(k_levels):
        for j, _ in enumerate(n_levels):
            lhs = abs(u_kn[i, j] - l_k[i])
            rhs = a_env * t_n[j]
            gap = lhs - rhs
            max_gap_exhaustion = max(max_gap_exhaustion, gap)
            if gap > 1.0e-10:
                check_exhaustion_env = False

    max_gap_regularization = 0.0
    check_regularization_env = True
    for i, j in combinations(range(len(k_levels)), 2):
        lhs = abs(l_k[i] - l_k[j])
        rhs = b_env * (e_k[i] + e_k[j])
        gap = lhs - rhs
        max_gap_regularization = max(max_gap_regularization, gap)
        if gap > 1.0e-10:
            check_regularization_env = False

    # Direct derived residual bound.
    max_gap_joint_bound = 0.0
    check_joint_bound = True
    residual = np.abs(u_kn - limit)
    for i, _ in enumerate(k_levels):
        for j, _ in enumerate(n_levels):
            lhs = residual[i, j]
            rhs = a_env * t_n[j] + b_env * e_k[i]
            gap = lhs - rhs
            max_gap_joint_bound = max(max_gap_joint_bound, gap)
            if gap > 1.0e-10:
                check_joint_bound = False

    # Sup-tail residual profile:
    # R(k,n) := sup_{k'>=k, n'>=n} |u_{k',n'} - L|
    sup_tail = np.zeros_like(residual)
    for i in range(len(k_levels)):
        for j in range(len(n_levels)):
            sup_tail[i, j] = float(np.max(residual[i:, j:]))

    # Monotonicity of R(k,n) along k and n.
    check_sup_tail_monotone_k = bool(np.all(np.diff(sup_tail, axis=0) <= 1.0e-12))
    check_sup_tail_monotone_n = bool(np.all(np.diff(sup_tail, axis=1) <= 1.0e-12))

    # Envelope decay checks.
    check_t_monotone = bool(np.all(np.diff(t_n) <= 1.0e-12))
    check_e_monotone = bool(np.all(np.diff(e_k) <= 1.0e-12))
    check_t_small = bool(t_n[-1] < 2.5e-4)
    check_e_small = bool(e_k[-1] < 3.5e-4)
    check_joint_small = bool(sup_tail[-1, -1] < 4.5e-4)

    print("AN-35 concrete envelope commuting-limit diagnostic")
    print(f"seed={seed}")
    print(f"num_blocks={num_blocks}")
    print(f"n_levels=[{int(n_levels[0])},...,{int(n_levels[-1])}]")
    print(f"k_levels=[{int(k_levels[0])},...,{int(k_levels[-1])}]")
    print(f"eta0={eta0:.6f}, alpha={alpha:.6f}, lambda={lam:.6f}")
    print(f"A={a_env:.6f}, B={b_env:.6f}")
    print(f"t_first={t_n[0]:.8e}")
    print(f"t_last={t_n[-1]:.8e}")
    print(f"e_first={e_k[0]:.8e}")
    print(f"e_last={e_k[-1]:.8e}")
    print(f"sup_tail_first={sup_tail[0,0]:.8e}")
    print(f"sup_tail_last={sup_tail[-1,-1]:.8e}")
    print(f"worst_exhaustion_gap={max_gap_exhaustion:.3e}")
    print(f"worst_regularization_gap={max_gap_regularization:.3e}")
    print(f"worst_joint_bound_gap={max_gap_joint_bound:.3e}")
    print(f"check_exhaustion_envelope={check_exhaustion_env}")
    print(f"check_regularization_envelope={check_regularization_env}")
    print(f"check_joint_bound={check_joint_bound}")
    print(f"check_sup_tail_monotone_k={check_sup_tail_monotone_k}")
    print(f"check_sup_tail_monotone_n={check_sup_tail_monotone_n}")
    print(f"check_t_monotone={check_t_monotone}")
    print(f"check_e_monotone={check_e_monotone}")
    print(f"check_t_small={check_t_small}")
    print(f"check_e_small={check_e_small}")
    print(f"check_joint_small={check_joint_small}")
    print(
        "all_checks_pass="
        f"{check_exhaustion_env and check_regularization_env and check_joint_bound and check_sup_tail_monotone_k and check_sup_tail_monotone_n and check_t_monotone and check_e_monotone and check_t_small and check_e_small and check_joint_small}"
    )


if __name__ == "__main__":
    main()
