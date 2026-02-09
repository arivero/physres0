# Claim 1 Phase A: Point-Supported Scaling Channels and Fixed-Mode Structure

Date: 2026-02-08  
Primary source anchors: `conv_patched.md:934`, `conv_patched.md:967`  
Supplementary scaling/fixed-point extraction: `research/workspace/notes/audits/2026-02-08-point-supported-distribution-scaling-subclaims.md`

## Goal

Make explicit that Claim 1 is not a single scaling channel story: point-supported distributions carry multiple dilation modes, and RG/fixed-point structure can be multi-channel.

## Proposition 1 (Point-Supported Basis in 1D)

Any distribution \(T\in\mathcal D'(\mathbb R)\) supported at \(\{0\}\) has finite expansion
\[
T=\sum_{m=0}^{M} c_m\,\delta^{(m)}.
\]
Thus point-supported sectors are finite-dimensional at fixed derivative order cutoff and naturally decompose by derivative mode \(m\).

## Proposition 2 (Dilation Weights)

Define dilation action on distributions by pullback:
\[
(U_\lambda T)(\varphi):=T(\varphi(\lambda\,\cdot)),\qquad \lambda>0.
\]
Then
\[
U_\lambda \delta^{(m)}=\lambda^{-m-1}\delta^{(m)}.
\]

Hence each \(\delta^{(m)}\) is a scaling eigenmode with exponent \(m+1\), and a generic point-supported distribution is a mixture of eigenmodes.

## Corollary (Multi-Channel Fixed-Mode Reading)

The Claim 1 bridge should be read as:

1. \(\delta(f')\) identifies a geometric critical-set selector.
2. The local distributional sector near concentrated support can still decompose into multiple scaling channels (\(\delta,\delta',\delta'',\dots\)).
3. RG evolution/regularization may preserve, mix, or suppress channels depending on symmetry and scheme.

So there can be multiple fixed structures/modes, not only one universal fixed point.

## Integration into Claim 1 Roadmap

The continuum bridge tasks must now track channel behavior explicitly:

1. identify which channel(s) a given regularization excites;
2. state whether channel mixing occurs under scale flow;
3. characterize fixed points/lines/manifolds in channel coordinates.

This aligns the Claim 1 program with the extracted fixed-point topology notes in
`arXiv-hep-th9411081v1/9411081.tex` (via the supplementary audit note), where point-supported degrees of freedom
appear as a nontrivial fixed-point landscape even in 1D QM.

## Toy Model: Wilson--Kogut RG for 1D Contact Interactions (hep-th/9411081)

This local preprint (`arXiv-hep-th9411081v1/9411081.tex`) is a concrete demonstration that
``point-supported sectors = multiple fixed points + relevant/irrelevant directions`` is not a metaphor.

### RG Action and Fixed Points (S-Matrix Form)

The preprint defines a Wilson--Kogut-style RG on the space of *dimensionless* cutoff interactions
represented by scattering matrices `\tilde S_{\tilde k}`. The RG action is simply an argument rescaling:

\[
\tilde S^t_{\tilde k} = T^t[\tilde S]_{\tilde k} = \tilde S_{e^{-t}\tilde k}.
\]

Hence fixed points are exactly the constant (in `\tilde k`) matrices in the allowed interaction space
(a subset of `U(2)` defined by physical conjugation/reciprocity constraints).

With time-reversal symmetry imposed, the fixed points reduce to a continuous circle plus two isolated points
(denoted `\pm Q` in the paper). The circle is interpreted there as Kurasov's scale-invariant `\delta'` family.

### Linearization: Scaling Exponents as Relevant/Irrelevant Directions

Perturbing around a fixed point using the Lie algebra of `U(2)`, the preprint obtains an eigenmode equation whose
solutions have explicit scaling form

\[
{\vec a}(k) = k^{-n}\,{\vec a}_0,
\]

with relevance/irrelevance controlled directly by the exponent `n` (in the usual RG sense: modes that grow toward the
IR are "relevant", those that die are "irrelevant", and those that stay flat are "marginal").

This is exactly the same structural statement as Proposition 2 above:
point-supported modes come with definite scaling weights, and RG evolution classifies them by those weights.

### Why This Matters for Claim 1

Claim 1 is trying to export a *delta-of-variation localization* story across refinement limits. The toy RG model says:

1. Even when the underlying bulk dynamics is free, the *point-supported* sector can have a rich fixed-point topology.
2. Scale invariance can live on a manifold of fixed points (a "fixed circle"), not only on isolated points.
3. Regularization choice matters: different regulators may land you in different attraction basins.

So a Claim 1 continuum statement must specify:

1. which local channel(s) are being targeted;
2. what the intended fixed structure is (point, line, manifold);
3. what counterterms/transport maps are used to keep the trajectory on (or near) the intended stable manifold.

## Bridge: Classical Limit vs Renormalization as Two Faces of Scaling

This note is focused on point-supported channels, but the same scaling logic underlies the two "big limits"
in the foundational program:

1. **Classical limit (`\hbar \to 0`)**: stationary phase concentrates amplitudes on extrema, and local prefactors encode
   Hessian/Van-Vleck determinants. This is a scaling limit of a deformation parameter.
2. **Continuum/QFT limit (cutoff `a\to 0`, lattice spacing, UV regulator removal)**: refinement can diverge, so one
   follows an RG trajectory; the existence of a continuum theory is controlled by fixed points and stable manifolds.

The contact-interaction fixed points show these are not separate ideas: both are about how a theory behaves under
rescaling and refinement, and both become sharp when expressed in terms of fixed points and scaling exponents.
Our internal `\tau_\mu` flow is the operational bridge: it is the repository's explicit "compare across scales"
mechanism, designed to be the analog of an RG reparameterization at the level of the dressed kernels.

## Reproducibility Check

Run:

```bash
python3.12 research/workspace/simulations/claim1_point_supported_scaling_modes.py
```

The script verifies the scaling law \(\delta^{(m)}(\lambda x)=\lambda^{-m-1}\delta^{(m)}(x)\) on analytic test functions.
