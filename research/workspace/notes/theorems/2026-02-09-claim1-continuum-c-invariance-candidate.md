# Claim 1 Phase AL: Continuum-Limit Candidate via \(c\)-Invariance Backbone

Date: 2026-02-09  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim1-groupoid-tau-sd-dependency-sheet.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-largeN-coupled-gaussian-tail.md`
- `research/workspace/notes/theorems/2026-02-09-claim1-fd-schwinger-dyson-identity.md`

## Goal

Provide a first explicit continuum-limit theorem candidate (beyond finite-dimensional truncations) that uses the \(c\)-invariance backbone.

## Terminology

In this note, `c-invariant` means:
any quantity unchanged when \((\kappa,\eta,h)\) are changed with
\[
c=(\eta-i/h)\kappa
\]
held fixed (equivalently unchanged along a \(\tau_\mu\)-orbit).

## Candidate Framework

Let
\[
\omega_{c,N}(F_m)
=
\frac{\int_{\R^N} e^{-cS_N(x)}F_m(x_1,\dots,x_m)\,dx}
{\int_{\R^N} e^{-cS_N(x)}\,dx},
\qquad
c\in\C,\ \Re c>0.
\]
Assume:

1. **Uniform Cauchy in \(N\)** on cylinders over compact \(c\)-sets:
   \[
   |\omega_{c,N'}(F_m)-\omega_{c,N}(F_m)|
   \le C_{F_m,K}\,\tau_N,\quad c\in K,\ \tau_N\to0.
   \]
2. **Uniform denominator non-vanishing** on \(K\) for large \(N\).
3. **Finite-\(N\) SD identity** for admissible \(\psi\):
   \[
   \omega_{c,N}(\partial_i\psi)=c\,\omega_{c,N}(\psi\,\partial_i S_N).
   \]
4. **\(\tau_\mu\)-orbit invariance of \(c\)**:
   parameter triples \((\kappa,\eta,h)\) with equal
   \[
   c=(\eta-i/h)\kappa
   \]
   represent the same kernel class.

## Theorem Candidate (Cylinder Continuum State + SD Pass-Through)

Under 1--4:

1. For each cylinder \(F_m\), \(\omega_{c,N}(F_m)\to\omega_c(F_m)\) as \(N\to\infty\), uniformly on compact \(c\)-sets.
2. \(\omega_c\) is a \(c\)-parametrized continuum cylinder state.
3. Along each \(\tau_\mu\)-orbit, \(\omega_c\) is unchanged (depends only on \(c\)).
4. If \(\partial_i S_N\to G_i\) in the cylinder pairing sense and the SD pairings are uniformly integrable, then
   \[
   \omega_c(\partial_i\psi)=c\,\omega_c(\psi\,G_i),
   \]
   i.e. Schwinger-Dyson passes to the continuum candidate.

## Proof Sketch

1. Item 1 from uniform Cauchy + denominator control.
2. Item 2 by projective consistency of cylinders.
3. Item 3 from \(c\)-invariance (same kernel parameter under \(\tau_\mu\)).
4. Item 4 by taking \(N\to\infty\) in finite-\(N\) SD identity under uniform bounds.

## Why This Matters

This is the first explicit candidate step that couples:

1. large-\(N\) continuum emergence,
2. \(\tau_\mu\)-parameter redundancy,
3. SD equation stability,

in one theorem-shaped statement beyond finite-dimensional closure.

## Reproducibility

Run:

```bash
python3.12 research/workspace/simulations/claim1_continuum_c_invariant_sd_candidate_check.py
```

The script instantiates a Gaussian-coupled model with analytic tail integration, showing:

1. large-\(N\) stabilization of \(\omega_{c,N}(F)\),
2. SD residuals near zero across \(N\),
3. equality for \(\tau_\mu\)-related parameter triples with identical \(c\).
