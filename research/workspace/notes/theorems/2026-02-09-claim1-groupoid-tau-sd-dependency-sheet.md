# Claim 1 Phase AJ: Tangent-Groupoid / \(\tau_\mu\) / Schwinger-Dyson Dependency Sheet

Date: 2026-02-09  
Depends on:

- `research/workspace/notes/theorems/2026-02-08-claim1-groupoid-halfdensity-theorem-pack.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-scale-flow-covariance.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-fd-schwinger-dyson-identity.md`

## Goal

Provide one compact theorem-style dependency sheet connecting:

1. tangent-groupoid scaling intuition,
2. \(\tau_\mu\)-covariance of dressed states,
3. Eq.(11)-type Schwinger-Dyson closures.

## Structural Map

For dressed finite-dimensional kernels
\[
\omega_{\kappa,\eta,h}(F)
=
\frac{\int e^{-(\eta-i/h)\kappa S(x)}F(x)\,dx}
{\int e^{-(\eta-i/h)\kappa S(x)}\,dx},
\]
set
\[
c:=(\eta-i/h)\kappa.
\]
Define
\[
\tau_\mu:(\kappa,\eta,h)\mapsto(\mu\kappa,\eta/\mu,\mu h),\qquad \mu>0.
\]

Then
\[
(\eta/\mu-i/(\mu h))(\mu\kappa)=c,
\]
so \(\tau_\mu\) preserves the dressed kernel exactly.

## Theorem 1 (\(\tau_\mu\)-Invariant Kernel Parameter)

For every \(\mu>0\),
\[
\omega_{\kappa,\eta,h}(F)=\omega_{\tau_\mu(\kappa,\eta,h)}(F).
\]
Hence observables depend on \((\kappa,\eta,h)\) only through \(c\).

### Consequence

The renormalized/dressed flow is a reparameterization of the same oscillatory state rather than a change of physics inside this scoped family.

## Theorem 2 (Schwinger-Dyson Compatibility with \(\tau_\mu\))

For smooth compactly supported \(\psi\), finite-dimensional identity:
\[
\left\langle \partial_i\psi\right\rangle_c
=
c\left\langle \psi\,\partial_i S\right\rangle_c.
\]
Because \(c\) is \(\tau_\mu\)-invariant, the same Schwinger-Dyson identity holds identically after \(\tau_\mu\).

So Eq.(11)-type closures are fixed-point relations along the \(\tau_\mu\)-orbit.

## Groupoid Interpretation (Dependency Statement)

Tangent-groupoid near-diagonal scaling encodes composition with scale change.  
In the scoped dressed family:

1. geometric \(1/2\)-density/groupoid composition gives multiplicative kernel structure,
2. \(\tau_\mu\) keeps the dressed kernel parameter \(c\) fixed,
3. Schwinger-Dyson identities are integration-by-parts invariants of that fixed \(c\)-kernel.

Thus groupoid scaling intuition and Eq.(11)-type identities are linked by the same preserved kernel parameter.

## Corollary (Foundational Dependency Diagram)

```text
groupoid geometric \(1/2\)-density composition
  -> scale-change map (near-diagonal refinement)
     -> tau_mu reparameterization preserving c=(eta-i/h)kappa
        -> invariant dressed kernel
           -> invariant Schwinger-Dyson identities (Eq.11 type)
```

This is the compact formal sheet requested by the foundational queue.

## Reproducibility

Run:

```bash
python3.12 research/workspace/simulations/claim1_groupoid_tau_sd_dependency_check.py
```

The script verifies numerically:

1. \(c\)-invariance under \(\tau_\mu\),
2. Schwinger-Dyson residuals before/after \(\tau_\mu\) on a test action.
