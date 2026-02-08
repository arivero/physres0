# Claim 3 Formalization: Relativistic Coulomb Phase Classification

Date: 2026-02-08  
Source anchors in canonical transcript: `conv_patched.md:395`, `conv_patched.md:402`, `conv_patched.md:407`, `conv_patched.md:415`, `conv_patched.md:417`, `conv_patched.md:421`

## Goal

Formalize the \(n=2\) (Coulomb/Kepler) orbit regimes by the sign of
\[
\alpha^2:=1-\frac{K^2}{L^2c^2},
\]
and by the energy domain \(E\) relative to \(mc^2\).

## Model Equations

For \(V(r)=-K/r\), \(u=1/r\), \(K>0\), the orbit equation is
\[
u''+\alpha^2 u = B,\qquad B:=\frac{KE}{c^2L^2}.
\]

From radial momentum,
\[
p_r^2 = \frac{(E+Ku)^2-m^2c^4}{c^2}-L^2u^2,\qquad
p_r=-L u',
\]
so
\[
u'^2 = A + 2Bu - \alpha^2 u^2,\qquad
A:=\frac{E^2-m^2c^4}{L^2c^2}.
\]

## Proposition 1 (\(\alpha^2>0 \iff L>K/c\): Oscillatory \(u(\varphi)\))

Let \(\alpha=\sqrt{\alpha^2}>0\). Then
\[
u(\varphi)=u_c + e\cos\!\big(\alpha(\varphi-\varphi_0)\big),
\qquad
u_c=\frac{B}{\alpha^2},
\]
with
\[
e^2=\frac{B^2+\alpha^2 A}{\alpha^4}.
\]

Hence radial motion is periodic in \(\varphi\) with period \(2\pi/\alpha\), and the rotation number is
\[
\Theta=\alpha=\sqrt{1-\frac{K^2}{L^2c^2}}.
\]

## Proposition 2 (Energy Split for \(\alpha^2>0\), Physical \(E>0\))

In this branch:

1. \(0<E<mc^2\) (\(A<0\)): bound rosettes (\(u_{\min}>0\), so \(r\) stays finite).
2. \(E=mc^2\) (\(A=0\)): threshold/parabolic-type case (\(u_{\min}=0\)).
3. \(E>mc^2\) (\(A>0\)): scattering (\(u\) reaches \(0\), so \(r\to\infty\)).

Sketch: \(u_{\min}=u_c-e\). For \(E>0\), \(u_c>0\), and
\[
u_c>e \iff A<0,\qquad
u_c=e \iff A=0,\qquad
u_c<e \iff A>0.
\]

## Proposition 3 (\(\alpha^2=0 \iff L=K/c\): Critical/Marginal)

Then
\[
u''=B=\frac{E}{K},
\]
so
\[
u(\varphi)=\frac{E}{2K}(\varphi-\varphi_0)^2 + a_1(\varphi-\varphi_0)+a_0.
\]
No periodic orbits occur. For \(E>0\), quadratic growth in \(|\varphi|\) gives marginal plunge behavior.

## Proposition 4 (\(\alpha^2<0 \iff L<K/c\): Hyperbolic/Spiral Regime)

Let \(\lambda=\sqrt{-\alpha^2}>0\). Then
\[
u''-\lambda^2 u = B,
\]
with solution
\[
u(\varphi)=u_p + C_+e^{\lambda\varphi}+C_-e^{-\lambda\varphi},
\qquad
u_p=-\frac{B}{\lambda^2}.
\]
Generically one exponential dominates, so \(u\) is non-periodic and grows in one angular direction (spiral/plunge branch). The opposite direction can correspond to escape depending on constants.

## Corollary (Claim 3 Upgrade)

Within the SR Coulomb model, `conv_patched.md:395`-`conv_patched.md:417` admits an explicit regime classification:

- \(L>K/c\): oscillatory \(u\), with bound/threshold/scattering split by \(E\) vs \(mc^2\).
- \(L=K/c\): critical polynomial branch.
- \(L<K/c\): non-periodic hyperbolic branch (spiral/plunge behavior).

## Reproducibility Check

Run:

```bash
python3.12 research/workspace/simulations/claim3_coulomb_classification_scan.py
```

The script reports invariant quantities \((\alpha^2,A,B,e,u_{\min},u_{\max})\) and representative regime labels for benchmark cases.
