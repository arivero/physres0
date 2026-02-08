# Claim 1 Phase Q: Finite-Dimensional Schwinger-Dyson Identity (Rigorous Eq.(11)-Type Closure)

Date: 2026-02-09  
Triggered by source revisit: `conv_patched.md:801`, `conv_patched.md:804`, `conv_patched.md:805`, `conv_patched.md:807`, `conv_patched.md:2356`

## Goal

Turn the formal Eq.(11)-style manipulation into a clean theorem:
integration-by-parts identities for regularized oscillatory states, i.e. finite-dimensional Schwinger-Dyson equations.

## Setup

Let \(S\in C^2(\mathbb R^d;\mathbb R)\), \(\eta>0\), \(\varepsilon>0\), and \(c:=\eta-i/\varepsilon\).
Assume coercive growth ensuring absolute convergence and vanishing boundary terms:

1. \(e^{-\eta S}\in L^1(\mathbb R^d)\),
2. for test class \(\mathcal T\subset C^1\), \(e^{-\eta S}(|F|+|\nabla F|)\in L^1\),
3. same for vector fields \(V\in C^1\) with \(e^{-\eta S}(|V||F|+|\nabla\!\cdot(VF)|)\in L^1\).

Define unnormalized and normalized functionals:
\[
\mathcal I_c(F):=\int_{\mathbb R^d}e^{-cS(x)}F(x)\,dx,\qquad
\omega_c(F):=\frac{\mathcal I_c(F)}{\mathcal I_c(1)},
\]
whenever \(\mathcal I_c(1)\neq0\).

## Theorem 1 (Unnormalized Schwinger-Dyson Identity)

For each admissible \(F\) and \(V\),
\[
\mathcal I_c\!\big(V\cdot\nabla S\,F\big)
=
\frac{1}{c}\,
\mathcal I_c\!\big(\nabla\!\cdot(VF)\big).
\]

### Proof

Use divergence theorem on \(\nabla\!\cdot(e^{-cS}VF)\):
\[
0=\int_{\mathbb R^d}\nabla\!\cdot\!\big(e^{-cS}VF\big)\,dx
=
\int e^{-cS}\big(\nabla\!\cdot(VF)-c\,V\cdot\nabla S\,F\big)\,dx.
\]
Rearrange. \(\square\)

## Corollary 1 (Normalized Schwinger-Dyson Identity)

If \(\mathcal I_c(1)\neq0\), then
\[
\omega_c\!\big(V\cdot\nabla S\,F\big)
=
\frac{1}{c}\,
\omega_c\!\big(\nabla\!\cdot(VF)\big).
\]

In particular, for constant \(V=e_i\) and \(F\equiv1\):
\[
\omega_c(\partial_i S)=0.
\]

This is the rigorous finite-dimensional version of the formal “mean-value equation” motif around Eq.(11).

## Corollary 2 (De-Regularized Form)

If \(\omega_{\eta-i/\varepsilon}(G)\to\omega_{-i/\varepsilon}(G)\) for the observables involved as \(\eta\to0^+\), then
\[
\omega_{-i/\varepsilon}\!\big(V\cdot\nabla S\,F\big)
=
i\varepsilon\,\omega_{-i/\varepsilon}\!\big(\nabla\!\cdot(VF)\big).
\]

So the dressed/de-regularized branch preserves the same Schwinger-Dyson structure.

## Corollary 3 (Action-Insertion Identity)

Choosing \(V=\nabla S\), one obtains
\[
\omega_c\!\big(\|\nabla S\|^2 F\big)
=
\frac{1}{c}\,\omega_c\!\big(\nabla\!\cdot(F\nabla S)\big),
\]
which ties quadratic gradient insertions to divergence insertions.

## Scope Note

This theorem is finite-dimensional but model-independent under coercive integrability conditions; it is the correct rigorous replacement for the raw formal line \(\int e^{(i/h)L}\,dL\).

## Reproducibility

Run:

```bash
python3.12 research/workspace/simulations/claim1_fd_schwinger_dyson_check.py
```

The script checks the identity numerically in a quartic model for both constant and non-constant vector fields.
