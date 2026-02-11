# Claim 1 Support (Newton-Limit Paradox): Lean Gaussian Scaling Rigidity

Date: 2026-02-10 (US)  
Lean module: `research/workspace/proofs/Claim1lean/GaussianSemigroupScalingRigidity.lean`

## Goal

Promote the 1D Gaussian prefactor witness to a dimension-indexed rigidity statement:
for `d : ℕ`, additive-semigroup multiplicativity plus a fixed `d=1` seed uniquely fixes
the full prefactor family.

## Machine-Checked Statements (Lean)

1. `nat_multiplicative_rigidity`
   - if `f : ℕ → ℝ` satisfies `f 0 = 1` and `f (d₁+d₂)=f d₁ * f d₂`,
     then `f d = (f 1)^d`.
2. `gaussianDimPrefactor_unique`
   - any dimension-indexed family with the same semigroup law and Gaussian `d=1` seed
     equals the Gaussian `d`-power prefactor.
3. `gaussianDimPrefactor_formula` / `gaussianDimPrefactor_formula'`
   - explicit `d`-power diagonal formulas, including sqrt-form `v^{-d/2}` structure.
4. `nat_multiplicative_not_unique_without_seed`
   - counterexample lane: without fixing the seed at `d=1`, multiplicative families are not unique.

## Validation Contract

1. Assumptions
   - dimension index `d` is discrete (`ℕ`);
   - factorized/product diagonal prefactor model;
   - Gaussian seed fixed by `gaussianPDFReal (0,v)(0)`.
2. Units and dimensions check
   - if variance `v` has units `L^2`, then `(sqrt v)^{-d}` has units `L^{-d}`, consistent with `d`-dimensional density scaling.
3. Symmetry / conservation checks
   - dimension lift is permutation-symmetric across coordinate factors (depends only on `d` and common `v`).
4. Independent cross-check path
   - algebraic recurrence `f (d+1) = f d * f 1` in Lean induction, independent of Gaussian measure convolution proofs.
5. Confidence statement
   - `verified` for the discrete dimension-indexed prefactor lane.
6. Reproducibility metadata
   - toolchain: `research/workspace/proofs/lean-toolchain` (Lean 4.27.0);
   - command:
     - `cd research/workspace/proofs && /Users/arivero/.elan/bin/lake build Claim1lean.GaussianSemigroupScalingRigidity`;
   - result on 2026-02-10: build passes.
