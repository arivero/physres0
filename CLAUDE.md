# Cloud Instance Benchmark

**CPU:** Intel Sapphire/Emerald Rapids Xeon (4th/5th Gen Scalable)
  - Model: Family 6, Model 207, Stepping 2
  - Cores: 16 (1 thread/core, 2.1 GHz base)
  - Features: AVX512F, AVX512_FP16, AMX (BF16/TILE/INT8)
  - Cache: 8 MB L3
**RAM:** 21 GB total
**Disk Write:** 1.3 GB/s
**Memory BW:** ~8.8 TB/s (likely memory subsystem optimization)
**Lean Build:** 15,798/15,798 files compiled successfully ✓

# Lean CI Policy

Lean compilation is handled automatically by GitHub Actions (`.github/workflows/lean.yml`).
The workflow triggers **only** when Lean-related files change (`.lean`, `lakefile.toml`,
`lean-toolchain`, or `lake-manifest.json` under `research/workspace/proofs/`).

**Do not run `lake build` locally to verify Lean proofs as a CI step.** GitHub Actions will
build and type-check all Lean code on push and pull request. If you add or modify `.lean`
files, the CI pipeline will run automatically — no manual intervention is needed.

Manual runs can be triggered via `workflow_dispatch` from the GitHub Actions UI.
