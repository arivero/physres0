#!/usr/bin/env python3.12
"""AN-30 multi-block nonlocal refinement/projective-consistency diagnostics."""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations


@dataclass(frozen=True)
class GraphSpec:
    name: str
    num_vertices: int
    num_edges: int


@dataclass(frozen=True)
class StateData:
    level: int
    rho: float
    denominator: complex
    numerator: complex
    ratio: complex
    graph_shift: complex


def rho_of_level(level: int) -> float:
    lattice_spacing = 2.0 ** (-level)
    box_scale = 5.0 + level
    return lattice_spacing + 1.0 / box_scale


def graph_shift(spec: GraphSpec, eta: float) -> complex:
    base = complex(0.013 * spec.num_vertices, 0.007 * spec.num_edges)
    eta_term = complex(0.0025 * spec.num_vertices, -0.0015 * spec.num_edges) * eta
    return base + eta_term


def build_state(spec: GraphSpec, level: int, eta: float, hbar: float) -> StateData:
    rho = rho_of_level(level)
    c_eta = complex(eta, -1.0 / hbar)

    den_base = complex(1.74, 0.19)
    den_eta = complex(0.15, -0.06) * eta
    den_rho = complex(-0.018 * spec.num_vertices - 0.010 * spec.num_edges, 0.004 * spec.num_edges) * rho
    denominator = den_base + den_eta + den_rho

    omega_base = complex(0.49, 0.10) + complex(0.05, -0.02) * eta
    shift = graph_shift(spec, eta)
    residual = complex(0.07 + 0.02 * spec.num_edges, 0.03 + 0.01 * spec.num_vertices) * rho
    residual += complex(0.01, -0.005) * rho * c_eta.real
    numerator = denominator * (omega_base + shift) + residual
    ratio = numerator / denominator
    return StateData(
        level=level,
        rho=rho,
        denominator=denominator,
        numerator=numerator,
        ratio=ratio,
        graph_shift=shift,
    )


def pairwise_rate_constant(values: dict[int, complex], rhos: dict[int, float]) -> float:
    max_ratio = 0.0
    for i, j in combinations(sorted(values), 2):
        rho_sum = rhos[i] + rhos[j]
        if rho_sum == 0.0:
            continue
        ratio = abs(values[i] - values[j]) / rho_sum
        max_ratio = max(max_ratio, ratio)
    return max_ratio


def tail_cauchy(values: dict[int, complex]) -> list[tuple[int, float]]:
    levels = sorted(values)
    out: list[tuple[int, float]] = []
    for idx in range(len(levels)):
        active = levels[idx:]
        if len(active) < 2:
            continue
        max_diff = 0.0
        for i, j in combinations(active, 2):
            max_diff = max(max_diff, abs(values[i] - values[j]))
        out.append((active[0], max_diff))
    return out


def main() -> None:
    seed = 2026020916
    hbar = 1.3
    eta_grid = [0.30, 0.15, 0.08, 0.04, 0.02, 0.00]
    levels = list(range(3, 11))

    graphs = {
        "g2": GraphSpec("g2", num_vertices=2, num_edges=1),
        "path3": GraphSpec("path3", num_vertices=3, num_edges=2),
        "star4": GraphSpec("star4", num_vertices=4, num_edges=3),
        "k4": GraphSpec("k4", num_vertices=4, num_edges=6),
    }

    projective_pairs = [
        ("path3", "g2"),
        ("star4", "g2"),
        ("k4", "path3"),
        ("k4", "g2"),
    ]

    all_data: dict[str, dict[float, dict[int, StateData]]] = {}
    for g_name, spec in graphs.items():
        eta_data: dict[float, dict[int, StateData]] = {}
        for eta in eta_grid:
            eta_data[eta] = {level: build_state(spec, level, eta, hbar) for level in levels}
        all_data[g_name] = eta_data

    min_abs_den = min(
        abs(state.denominator)
        for g_name in graphs
        for eta in eta_grid
        for state in all_data[g_name][eta].values()
    )
    denominator_ok = min_abs_den > 1.2

    cauchy_ok = True
    cauchy_monotone = True
    worst_cauchy_gap = 0.0
    graph_tail_profiles: dict[str, list[tuple[int, float]]] = {}
    for g_name, spec in graphs.items():
        size_factor = 1.0 + spec.num_vertices + spec.num_edges
        for eta in eta_grid:
            by_level = all_data[g_name][eta]
            rho_map = {level: by_level[level].rho for level in levels}
            num_map = {level: by_level[level].numerator for level in levels}
            den_map = {level: by_level[level].denominator for level in levels}
            rat_map = {level: by_level[level].ratio for level in levels}

            c_num = pairwise_rate_constant(num_map, rho_map)
            c_den = pairwise_rate_constant(den_map, rho_map)
            m_num = max(abs(value) for value in num_map.values())
            z_star = min(abs(value) for value in den_map.values())
            c_ratio = c_num / z_star + m_num * c_den / (z_star**2)

            # Combinatorial envelope surrogate.
            comb_bound = 0.080 * size_factor
            worst_cauchy_gap = max(worst_cauchy_gap, c_ratio - comb_bound)
            if c_ratio > comb_bound + 1.0e-12:
                cauchy_ok = False

            if eta == 0.0:
                tails = tail_cauchy(rat_map)
                graph_tail_profiles[g_name] = tails
                tail_vals = [value for _, value in tails]
                if any(
                    tail_vals[idx + 1] > tail_vals[idx] + 1.0e-12
                    for idx in range(len(tail_vals) - 1)
                ):
                    cauchy_monotone = False

    # Projective consistency defects under graph-shift correction.
    c_proj_star = 0.06
    proj_ok = True
    proj_gap_worst = 0.0
    finest_proj_defects: dict[str, float] = {}
    finest = max(levels)
    for parent_name, child_name in projective_pairs:
        parent_spec = graphs[parent_name]
        child_spec = graphs[child_name]
        missing_vertices = parent_spec.num_vertices - child_spec.num_vertices
        label = f"{parent_name}->{child_name}"
        max_defect = 0.0
        for eta in eta_grid:
            for level in levels:
                rho = all_data[parent_name][eta][level].rho
                parent_state = all_data[parent_name][eta][level]
                child_state = all_data[child_name][eta][level]

                # Restriction map proxy: shift-correct parent ratio onto child coordinates.
                projected_parent = parent_state.ratio + (child_state.graph_shift - parent_state.graph_shift)
                defect = abs(projected_parent - child_state.ratio)
                bound = c_proj_star * missing_vertices * rho
                proj_gap_worst = max(proj_gap_worst, defect - bound)
                max_defect = max(max_defect, defect)
                if defect > bound + 1.0e-12:
                    proj_ok = False
        finest_defect = 0.0
        for eta in eta_grid:
            parent_state = all_data[parent_name][eta][finest]
            child_state = all_data[child_name][eta][finest]
            projected_parent = parent_state.ratio + (child_state.graph_shift - parent_state.graph_shift)
            finest_defect = max(finest_defect, abs(projected_parent - child_state.ratio))
        finest_proj_defects[label] = finest_defect

    # De-regularization drift at finest scale.
    dereg_ok = True
    dereg_report: dict[str, dict[float, float]] = {}
    for g_name in graphs:
        omega_eta0 = all_data[g_name][0.0][finest].ratio
        drifts = {
            eta: abs(all_data[g_name][eta][finest].ratio - omega_eta0) for eta in eta_grid if eta > 0.0
        }
        eta_sorted = sorted(drifts)
        monotone = all(
            drifts[eta_sorted[idx + 1]] >= drifts[eta_sorted[idx]] - 1.0e-12
            for idx in range(len(eta_sorted) - 1)
        )
        small = drifts[min(drifts)] < 3.5e-3
        if not (monotone and small):
            dereg_ok = False
        dereg_report[g_name] = drifts

    print("AN-30 multiblock projective-consistency diagnostic")
    print(f"seed={seed}")
    print(f"hbar={hbar:.6f}")
    print(f"eta_grid={eta_grid}")
    print(f"levels={levels}")
    print(
        "graph_specs="
        + str({name: (spec.num_vertices, spec.num_edges) for name, spec in graphs.items()})
    )
    print(f"min_abs_denominator={min_abs_den:.10f}")
    print(f"worst_combinatorial_cauchy_gap={worst_cauchy_gap:.3e}")
    print(f"worst_projective_bound_gap={proj_gap_worst:.3e}")

    print("tail_cauchy_eta0_by_graph:")
    for g_name, profile in graph_tail_profiles.items():
        body = ", ".join(f"L>={lev}: {val:.6e}" for lev, val in profile)
        print(f"  {g_name}: {body}")

    print("finest_scale_projective_defects:")
    for label, value in finest_proj_defects.items():
        print(f"  {label}: defect={value:.8e}")

    print("finest_scale_de_regularization_drift:")
    for g_name in graphs:
        drifts = dereg_report[g_name]
        for eta in sorted(drifts.keys(), reverse=True):
            print(f"  {g_name} eta={eta:.2f}: drift={drifts[eta]:.8e}")

    print(f"check_denominator_lower_bound={denominator_ok}")
    print(f"check_combinatorial_cauchy_bound={cauchy_ok}")
    print(f"check_tail_cauchy_monotone={cauchy_monotone}")
    print(f"check_projective_bound={proj_ok}")
    print(f"check_dereg_stability={dereg_ok}")
    print(
        "all_checks_pass="
        f"{denominator_ok and cauchy_ok and cauchy_monotone and proj_ok and dereg_ok}"
    )


if __name__ == "__main__":
    main()
