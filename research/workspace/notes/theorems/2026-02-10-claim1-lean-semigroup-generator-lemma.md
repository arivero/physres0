# Claim 1 Support (Newton-Limit Paradox): Lean Semigroup → Generator Lemma

Date: 2026-02-10 (US)  
Lean module: `research/workspace/proofs/Claim1lean/SemigroupGenerator.lean`

## Goal

Formalize a minimal, reusable statement of the principle:

> a local composition law (semigroup of coarse-graining maps) plus a right-derivative
> at zero defines an infinitesimal generator (beta function), and orbits satisfy a
> right-derivative ODE.

This is one of the concrete theorem targets listed in:

- `research/workspace/notes/2026-02-10-newton-limit-paradox-quantum-necessity.md`

## Machine-Checked Statement (Lean)

The Lean theorem

- `Claim1lean.orbit_hasDerivWithinAt_Ici`

proves the following (in a normed `ℝ`-vector space `E`):

Given

1. a family of maps `R : ℝ → E → E`,
2. a "right-action" semigroup law on `t ≥ 0`:
   \[
   R(s+t)(x)=R(t)(R(s)(x)),\qquad s,t\ge 0,
   \]
3. identity at zero: `R 0 x = x`,
4. a right-derivative at `0` for every trajectory `t ↦ R t x`:
   \[
   \frac{d}{dt}\Big|_{t=0^+} R(t)(x)=\beta(x),
   \]

then for each orbit `g(t) := R(t)(x0)` and each `t ≥ 0`, `g` has a right derivative at `t`
and satisfies the ODE in right-derivative form:
\[
g'(t^+)=\beta(g(t)).
\]

Lean formulation: `HasDerivWithinAt g (β (g t)) (Set.Ici t) t`.

## Why This Matters Here

This lemma is a clean "consistency axiom ⇒ generator" bridge:

1. it isolates the *semigroup/composition* structure as the primary assumption,
2. it avoids requiring differentiability of `R t` in the state variable,
3. it produces the beta-function/infinitesimal-generator object in a form that can
   be cited when connecting RG/coarse-graining structure to the Newton-limit paradox framing.

## Next Tightening Targets

1. Connect this semigroup-generator lemma to a concrete normalization/semigroup constraint
   in a Gaussian model (the `t^{-d/2}` prefactor lane). Partial Lean anchor:
   `research/workspace/notes/theorems/2026-02-10-claim1-lean-gaussian-semigroup-normalization.md`.
2. Upgrade to a setting closer to the field-side objects (e.g. maps acting on a space of
   couplings or states), with explicit regularity hypotheses clearly separated from the
   semigroup axiom.
