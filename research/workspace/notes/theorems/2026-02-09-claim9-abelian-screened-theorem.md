# Claim 9 Phase Z: Theorem-Grade Closure in the Abelian Screened Class

Date: 2026-02-09  
Source anchors in canonical transcript: `conv_patched.md:619`, `conv_patched.md:633`, `conv_patched.md:647`, `conv_patched.md:651`

## Goal

Upgrade one Claim 9 sector from proposition-level to theorem-level closure:
the static screened potential in a massive Abelian class, uniformly across spatial dimension.

## Framework

Let \(n=D-1\ge 1\) be spatial dimension and \(m>0\).  
In the static linearized screened class, the Green kernel \(G_{n,m}\) is defined by
\[
(-\Delta + m^2)G_{n,m}=\delta_0
\]
in \(\mathbb R^n\), with \(G_{n,m}(r)\to 0\) as \(r\to\infty\), \(r=|x|\).

For static sources \(q_1,q_2\), the interaction potential is
\[
V(r)=q_1q_2\,G_{n,m}(r).
\]

## Theorem (Explicit Kernel + Asymptotic Saturation)

For every \(n\ge 1\), \(m>0\), and \(r>0\),
\[
G_{n,m}(r)
=
\frac{1}{(2\pi)^{n/2}}
\left(\frac{m}{r}\right)^{\nu}
K_{\nu}(mr),
\qquad
\nu:=\frac n2-1,
\]
where \(K_\nu\) is the modified Bessel function of the second kind.

Moreover, as \(r\to\infty\),
\[
G_{n,m}(r)
=
\frac{1}{2(2\pi)^{(n-1)/2}}
m^{(n-3)/2}
r^{-(n-1)/2}
e^{-mr}
\left(1+O\!\left(\frac1r\right)\right).
\]

Hence:

1. \(V(r)\) is exponentially screened in every \(D\), with polynomial prefactor \(r^{-(D-2)/2}\).
2. \(V(r)\to 0\) as \(r\to\infty\), so the separated-pair energy saturates to a constant self-energy baseline.

## Proof

1. Fourier representation:
\[
G_{n,m}(x)=\frac{1}{(2\pi)^n}\int_{\mathbb R^n}\frac{e^{ik\cdot x}}{|k|^2+m^2}\,dk.
\]
Radial reduction plus the Hankel-transform identity yields the closed Bessel form above.
2. Use the standard large-argument asymptotic
\[
K_\nu(z)=\sqrt{\frac{\pi}{2z}}\,e^{-z}\left(1+O(z^{-1})\right),\qquad z\to+\infty.
\]
Insert \(z=mr\) into the exact kernel formula and collect powers of \(m\), \(r\), and constants.
This gives the stated large-\(r\) expansion.
3. The exponential factor \(e^{-mr}\) forces \(G_{n,m}(r)\to0\), hence \(V(r)\to0\).
Energy saturation follows by writing total energy as
`(self-energy terms independent of r) + V(r)`.

## Corollary (Claim 9 Upgrade, Scoped)

Within the screened Abelian class, the long-range statement is theorem-closed:
the asymptotic tail is Yukawa in every dimension, not Coulombic.

This removes one major model-dependence branch from Claim 9; remaining open branches are confining non-Abelian rigor and full dynamical-matter crossover theorems.

## Reproducibility Check

Run:

```bash
python3.12 research/workspace/simulations/claim9_abelian_screened_asymptotic_check.py
```

The script evaluates exact-vs-asymptotic kernel ratios for multiple dimensions and confirms convergence to 1 at large radius.
