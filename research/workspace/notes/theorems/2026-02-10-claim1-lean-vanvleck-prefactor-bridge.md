# Claim 1 Support (Newton-Limit Paradox): Lean Van Vleck Prefactor Bridge

Date: 2026-02-10 (US)  
Lean module: `research/workspace/proofs/Claim1lean/VanVleckPrefactorBridge.lean`

## Goal

Convert Schur-complement determinant identities into explicit determinant-prefactor
product laws in the algebraic `|det|^{-1/2}` channel.

## Machine-Checked Statements (Lean)

1. `detPrefactor`
   - defines matrix prefactor proxy `(|det M|)^{-1/2}` over `ℝ`.
2. `inv_sqrt_abs_mul`
   - scalar bridge:
     `sqrt(|xy|)^{-1} = sqrt(|x|)^{-1} * sqrt(|y|)^{-1}`.
3. `detPrefactor_fromBlocks₁₁`
   - with invertible 11-block pivot:
     prefactor of `fromBlocks` factorizes into prefactor of `A` times prefactor of Schur complement `D - C A^{-1} B`.
4. `detPrefactor_fromBlocks₂₂`
   - symmetric 22-pivot factorization.

## Validation Contract

1. Assumptions
   - finite square block matrices over `ℝ`;
   - invertibility of chosen pivot block (`A` or `D`) for Schur formulas.
2. Units and dimensions check
   - determinant prefactor carries inverse square-root determinant units; multiplicative factorization preserves unit balance under elimination.
3. Symmetry / conservation checks
   - both pivot channels (11 and 22) are formalized, checking pivot-choice consistency.
4. Independent cross-check path
   - independent from integration arguments: proof uses block determinant identities
     from `Claim1lean/SchurComplementDeterminant.lean` plus scalar sqrt/abs algebra.
5. Confidence statement
   - `verified` for finite-dimensional algebraic prefactor factorization.
6. Reproducibility metadata
   - toolchain: `research/workspace/proofs/lean-toolchain` (Lean 4.27.0);
   - command:
     - `cd research/workspace/proofs && /Users/arivero/.elan/bin/lake build Claim1lean.VanVleckPrefactorBridge`;
   - result on 2026-02-10: build passes.
