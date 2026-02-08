# Claim 8 Phase D Extension: Beyond Tangherlini via Asymptotic Stability Sign

Date: 2026-02-08  
Source anchor in canonical transcript: `conv_patched.md:539`

## Goal

Extend Claim 8 beyond the exact Tangherlini metric where possible, without over-claiming rotating/global classes.

## Asymptotic Model

In \(D\)-dimensional asymptotically-flat gravity, weak-field central attraction scales as
\[
U_{\text{grav}}(r)\sim -\frac{k}{r^{D-3}},\qquad k>0.
\]
The leading radial effective potential for timelike orbital motion is
\[
U_{\text{eff}}(r)=\frac{\ell^2}{2r^2}-\frac{k}{r^{D-3}}.
\]

## Proposition (Far-Zone Circular Stability Sign)

Circular condition:
\[
U_{\text{eff}}'(r)=0
\;\Longrightarrow\;
\ell^2 = k(D-3)\,r^{5-D}.
\]
Second derivative at circular radius:
\[
U_{\text{eff}}''(r)
=
\frac{3\ell^2}{r^4}
-k(D-3)(D-2)r^{-(D-1)}
=
k(D-3)(5-D)\,r^{1-D}.
\]

Hence:

1. \(D<5\): far-zone circular orbits are stable.
2. \(D=5\): marginal at leading order.
3. \(D>5\): far-zone circular orbits are unstable.

## Corollary (Scoped Extension)

Even beyond exact Tangherlini, the asymptotic sector already forbids large-radius stable circular timelike orbits for \(D>5\).  
Therefore any stable circular or bound family in high-\(D\) rotating/non-spherical backgrounds must come from genuinely strong-field effects, not Newtonian-tail asymptotics.

This extends Claim 8 where possible while keeping rotating/global claims explicitly open.

## Reproducibility Check

Run:

```bash
python3.12 research/workspace/simulations/claim8_asymptotic_stability_sign.py
```

It prints the sign factor \((5-D)\) controlling far-zone stability.
