#!/usr/bin/env python3.12
"""Dimension/model split table for Claim 8 rotating-class closure (Phase Y).

Run:
  python3.12 research/workspace/simulations/claim8_rotating_parameter_map_table.py
"""

from __future__ import annotations


def main() -> None:
    rows = [
        {
            "sector": "Static Tangherlini",
            "dimension": "D>=5",
            "result": "no stable circular timelike orbit",
            "status": "closed (local theorem note)",
            "source": "workspace theorem",
        },
        {
            "sector": "Rotating Myers-Perry",
            "dimension": "D=5",
            "result": "no radially bound timelike/null geodesics",
            "status": "closed (external theorem import)",
            "source": "Novo PRD 111 (2025), 064060",
        },
        {
            "sector": "Rotating Myers-Perry (singly spinning)",
            "dimension": "D=6",
            "result": "stable bound massive/null orbits exist above critical spin",
            "status": "closed (external theorem import)",
            "source": "Igata PRD 92 (2015), 024002",
        },
    ]

    print("Claim 8 rotating-class parameter map")
    print()
    print("| Sector | Dimension | Main result | Status | Source |")
    print("|---|---|---|---|---|")
    for row in rows:
        print(
            "| {sector} | {dimension} | {result} | {status} | {source} |".format(
                **row
            )
        )

    print()
    print("Interpretation:")
    print("  no-stable/no-bound is robust in key classes, but not universal for rotating D>=6.")


if __name__ == "__main__":
    main()
