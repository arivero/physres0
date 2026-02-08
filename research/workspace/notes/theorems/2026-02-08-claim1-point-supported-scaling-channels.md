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
`arXiv-hep-th9411081v1/9411081.tex` (via the supplementary audit note).

## Reproducibility Check

Run:

```bash
python3.12 research/workspace/simulations/claim1_point_supported_scaling_modes.py
```

The script verifies the scaling law \(\delta^{(m)}(\lambda x)=\lambda^{-m-1}\delta^{(m)}(x)\) on analytic test functions.
