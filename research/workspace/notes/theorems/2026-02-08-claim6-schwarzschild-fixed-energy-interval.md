# Claim 6 Formalization: Schwarzschild Fixed-Energy Angular-Momentum Interval

Date: 2026-02-08  
Source anchors in canonical transcript: `conv_patched.md:521`, `conv_patched.md:527`, `conv_patched.md:529`, `conv_patched.md:535`, `conv_patched.md:597`

## Goal

Derive the fixed-energy interval
\[
\ell_{\min}(E) < \ell \le \ell_{\max}(E)
\]
for timelike Schwarzschild geodesics in the conservative sector, and make the separatrix/double-root conditions explicit.

## Setup (Geometric Units)

Use \(G=c=M=1\), equatorial plane, and specific angular momentum \(\ell=L/m\). The radial equation is
\[
\dot r^2 = E^2 - V_{\text{eff}}(r;\ell),
\qquad
V_{\text{eff}}(r;\ell)=\left(1-\frac{2}{r}\right)\left(1+\frac{\ell^2}{r^2}\right),
\]
with \(E\) the specific energy.

Turning points satisfy
\[
R(r):=E^2-V_{\text{eff}}(r;\ell)=0.
\]
Boundary curves between orbit classes occur at double roots:
\[
R(r_\star)=0,\qquad R'(r_\star)=0.
\]

## Proposition 1 (Circular-Branch Formulas)

The circular-orbit conditions are equivalent to
\[
\ell^2(r)=\frac{r^2}{r-3},
\qquad
E^2(r)=\frac{(r-2)^2}{r(r-3)},
\]
valid for \(r>3\).

Stable circular branch: \(r>6\).  
Unstable circular branch: \(3<r<6\).  
ISCO: \(r=6,\;\ell=\sqrt{12},\;E=\sqrt{8/9}\).

## Proposition 2 (Fixed-\(E\) Circular Radii via Discriminant)

Set \(u:=1/r\). Then circular-energy relation becomes
\[
E^2=\frac{(1-2u)^2}{1-3u}
\;\Longleftrightarrow\;
4u^2+(3E^2-4)u+(1-E^2)=0.
\]

Discriminant:
\[
\Delta_u = E^2(9E^2-8).
\]

Hence circular roots exist iff \(E^2\ge 8/9\). In the bound sector \(E^2<1\), this gives
\[
\sqrt{8/9}\le E < 1.
\]

For \(E\in[\sqrt{8/9},1)\), the two roots are
\[
u_{\text{st}}(E)=\frac{4-3E^2-E\sqrt{9E^2-8}}{8},
\qquad
u_{\text{un}}(E)=\frac{4-3E^2+E\sqrt{9E^2-8}}{8},
\]
with \(u_{\text{st}}<u_{\text{un}}\), so
\[
r_{\text{st}}=\frac1{u_{\text{st}}}\ge 6,
\qquad
3<r_{\text{un}}=\frac1{u_{\text{un}}}\le 6.
\]

## Proposition 3 (Explicit \(\ell_{\min}(E),\ell_{\max}(E)\))

Using
\[
\ell^2=\frac{1}{u(1-3u)},
\]
define
\[
\ell_{\max}(E):=\frac{1}{\sqrt{u_{\text{st}}(E)(1-3u_{\text{st}}(E))}},
\]
\[
\ell_{\min}(E):=\frac{1}{\sqrt{u_{\text{un}}(E)(1-3u_{\text{un}}(E))}}.
\]

Then for \(E\in(\sqrt{8/9},1)\):
\[
\ell_{\min}(E)<\ell_{\max}(E),
\]
and the bound-motion shell exists only for
\[
\ell_{\min}(E)<\ell\le \ell_{\max}(E).
\]

Interpretation:

1. \(\ell=\ell_{\max}(E)\): outer stable circular orbit (zero-eccentricity boundary).
2. \(\ell=\ell_{\min}(E)\): unstable circular separatrix (bound/plunge boundary).
3. \(\ell<\ell_{\min}(E)\): no inner turning-point barrier; plunge sector.

Limits:
\[
E\to \sqrt{8/9}^{+}\!:\ \ell_{\min},\ell_{\max}\to\sqrt{12},
\]
\[
E\to 1^{-}\!:\ \ell_{\max}\to\infty,\quad \ell_{\min}\to 4.
\]

## SI Restoration

In SI units, multiply specific angular momentum by \(GM/c\):
\[
\ell_{\text{SI}} = \frac{GM}{c}\,\ell.
\]
Thus the ISCO threshold is
\[
\ell_{\text{ISCO}}=\sqrt{12}\,\frac{GM}{c},
\qquad
L_{\text{ISCO}}=m\,\ell_{\text{ISCO}}=\sqrt{12}\,\frac{GMm}{c}.
\]

## Corollary (Claim 6 Upgrade)

The interval statement in `conv_patched.md:529`-`conv_patched.md:535` is explicitly derived from the double-root/circular discriminant structure of the Schwarzschild radial equation.

## Reproducibility Check

Run:

```bash
python3.12 research/workspace/simulations/claim6_schwarzschild_interval_scan.py
```

The script verifies \(\ell_{\min}(E)\), \(\ell_{\max}(E)\), and the circular equalities \(E^2=V_{\text{eff}}(r_{\text{st/un}};\ell_{\max/\min})\) on representative energies.
