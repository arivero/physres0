#!/usr/bin/env python3.12
"""Check scaling modes for point-supported distributions delta^(m).

For test function phi(x)=exp(x), one has phi^(m)(0)=1 for all m.
Hence:
  <delta^(m)(lambda x), phi> = (-1)^m * lambda^(-m-1)
while
  <delta^(m)(x), phi>        = (-1)^m.

Run:
  python3.12 research/workspace/simulations/claim1_point_supported_scaling_modes.py
"""

from __future__ import annotations

import math


def action_delta_m(m: int, lam: float) -> float:
    # For phi(x)=exp(x), phi^(m)(0)=1. Sign from distribution derivative pairing.
    return ((-1.0) ** m) * (lam ** (-(m + 1)))


def main() -> None:
    lams = [0.5, 0.8, 1.2, 2.0]
    for m in range(5):
        print(f"m={m}")
        base = action_delta_m(m, 1.0)
        for lam in lams:
            val = action_delta_m(m, lam)
            ratio = val / base
            pred = lam ** (-(m + 1))
            err = abs(ratio - pred)
            print(
                f"  lambda={lam:>4.1f}  ratio={ratio:+.12f}  "
                f"pred={pred:+.12f}  abs_err={err:.3e}"
            )
        print()


if __name__ == "__main__":
    main()
