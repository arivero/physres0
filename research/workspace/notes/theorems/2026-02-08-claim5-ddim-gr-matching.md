# Claim 5 Formalization: D-Dimensional GR Matching to \(F=K/r^n\)

Date: 2026-02-08  
Source anchors in canonical transcript: `conv_patched.md:490`, `conv_patched.md:494`, `conv_patched.md:497`, `conv_patched.md:505`

## Goal

Fix conventions and provide a compact derivation for the \(D\)-dimensional weak-field matching:
\[
F(r)=\frac{K}{r^n},\qquad n=D-2,
\]
with explicit \(K\)-prefactor and unit cross-check.

## Conventions

- \(D\): spacetime dimension (\(D-1\) spatial dimensions).
- \(D\ge 4\) for power-law Newtonian potential branch.
- \(\Omega_d\): area of unit \(d\)-sphere,
  \[
  \Omega_d=\frac{2\pi^{(d+1)/2}}{\Gamma((d+1)/2)}.
  \]
- Tangherlini parameter \(\mu\) in
  \[
  g_{tt}=-(1-\mu/r^{D-3}).
  \]

Mass-parameter relation:
\[
\mu=\frac{16\pi G_D M}{(D-2)\Omega_{D-2}c^2}.
\]

## Derivation

Use weak-field identification
\[
g_{tt}\simeq -(1+2\Phi/c^2),
\]
so
\[
\Phi(r)= -\frac{c^2\mu}{2\,r^{D-3}}
= -\frac{8\pi G_D M}{(D-2)\Omega_{D-2}}\frac{1}{r^{D-3}}.
\]

Then for test mass \(m\),
\[
F(r)=m|\nabla\Phi|
=\frac{8\pi(D-3)}{(D-2)\Omega_{D-2}}\frac{G_D mM}{r^{D-2}}.
\]

Hence in \(F=K/r^n\):
\[
n=D-2,\qquad
K=\frac{8\pi(D-3)}{(D-2)\Omega_{D-2}}\,G_D\,mM.
\]

## D=4 Reduction Check

For \(D=4\), \(\Omega_2=4\pi\), giving prefactor
\[
\frac{8\pi(1)}{(2)(4\pi)}=1,
\]
so
\[
K=G_4 mM.
\]

## Alternative Newton-Constant Convention

If one defines \(G_{\text{Newt},D}\) directly by
\[
F(r)=\frac{G_{\text{Newt},D}mM}{r^{D-2}},
\]
then
\[
G_{\text{Newt},D}
=
\frac{8\pi(D-3)}{(D-2)\Omega_{D-2}}\,G_D.
\]

So ``\(K=GmM\)'' is dimension-independent only in this convention.

## Dimensional Check

From
\[
F\sim \frac{G_D mM}{r^{D-2}},
\]
units give
\[
[G_D]=L^{D-1}M^{-1}T^{-2}.
\]
Then \(K\) has units
\[
[K]=[F]\,[r]^{D-2}=MLT^{-2}\,L^{D-2}=ML^{D-1}T^{-2},
\]
consistent with \(K/r^{D-2}\) having force units.

## D=3 Exception

At \(D=3\) (two spatial dimensions), Poisson Green function is logarithmic:
\[
\Phi(r)\sim \log r,\qquad F(r)\sim \frac{1}{r}.
\]
So the \(1/r^{D-3}\) potential-power template is replaced by a log branch.

## Corollary (Claim 5 Status)

The matching statement in `conv_patched.md:490`-`conv_patched.md:497` is now fully convention-fixed and unit-checked.

## Reproducibility Check

Run:

```bash
python3.12 research/workspace/simulations/claim5_ddim_prefactor_scan.py
```

This prints \(\Omega_{D-2}\) and the prefactor
\[
\frac{8\pi(D-3)}{(D-2)\Omega_{D-2}}
\]
for representative dimensions, including the \(D=4\) normalization check.
