# Claim 1 Phase R: Scale-Flow Covariance for the Dressed Family (\(\tau_\mu\)-Type Map)

Date: 2026-02-09  
Triggered by source revisit: `conv_patched.md:795`, `conv_patched.md:799`, `conv_patched.md:801`

## Goal

Formalize a rigorous finite-dimensional version of the dressed-series scale covariance idea
\[
\tau_\mu\langle \delta_h|=\langle \delta_{\mu h}|,
\]
in a parameterized oscillatory family.

## Setup

Let \(S:\mathbb R^d\to\mathbb R\) be measurable with integrable regularized weights.
For parameters \(\kappa>0,\ \eta>0,\ h>0\), define
\[
\omega_{\kappa,\eta,h}(F)
:=
\frac{\int_{\mathbb R^d}\exp\!\left(-(\eta-i/h)\kappa S(x)\right)\,F(x)\,dx}
{\int_{\mathbb R^d}\exp\!\left(-(\eta-i/h)\kappa S(x)\right)\,dx}.
\]

Define the scale-flow transform \(\tau_\mu\) (\(\mu>0\)) on parameters by
\[
\tau_\mu:\ (\kappa,\eta,h)\mapsto(\kappa',\eta',h')
:=
(\mu\kappa,\eta/\mu,\mu h).
\]

## Theorem (Exact Covariance/Invariance)

For every \(\mu>0\) and admissible observable \(F\),
\[
\omega_{\kappa,\eta,h}(F)=\omega_{\kappa',\eta',h'}(F),
\quad (\kappa',\eta',h')=\tau_\mu(\kappa,\eta,h).
\]

### Proof

Compute the kernel coefficient:
\[
(\eta'-i/h')\kappa'
=
\left(\frac{\eta}{\mu}-\frac{i}{\mu h}\right)\mu\kappa
=
(\eta-i/h)\kappa.
\]
So numerator and denominator integrands are identical before and after \(\tau_\mu\), hence the normalized ratio is identical. \(\square\)

## Corollary 1 (De-Regularized Branch)

At \(\eta=0\), this reduces to
\[
\omega_{\kappa,0,h}(F)=\omega_{\mu\kappa,0,\mu h}(F).
\]
So \(h\)-flow covariance is exact when accompanied by coupling scaling \(\kappa\mapsto\mu\kappa\).

## Corollary 2 (Invariant Product Parameter)

The family depends on \((\kappa,\eta,h)\) through the combination
\[
\Lambda:=(\eta-i/h)\kappa.
\]
Hence any flow preserving \(\Lambda\) leaves \(\omega\) invariant.

This provides a clean finite-dimensional model of “dressed-series invariance under scale transformation”.

## Scope

This is an exact parameter-covariance theorem, not yet a full RG fixed-point theorem.
It provides the algebraic kernel for scale-covariant comparison across discretization/control scales in Claim 1 constructions.

## Reproducibility

Run:

```bash
python3.12 research/workspace/simulations/claim1_scale_flow_covariance_check.py
```

The script verifies \(\omega_{\kappa,\eta,h}(F)=\omega_{\mu\kappa,\eta/\mu,\mu h}(F)\) numerically for a quartic model.
