# Foundational Synthesis (Phase AH): Action-Reduction Unification Across SR/GR/Gauge

Date: 2026-02-09  
Source anchors in canonical transcript:

- `conv_patched.md:549`
- `conv_patched.md:555`
- `conv_patched.md:595`
- `conv_patched.md:601`
- `conv_patched.md:611`

## Goal

State a single mechanism underlying the force/orbit results used in this workspace:
action symmetry reduction to a one-dimensional turning-point problem.

## Abstract Reduction Statement

Let \(S=\int L(q,\dot q)\,d\lambda\) be invariant under:

1. time translations \(\Rightarrow\) conserved energy \(E\),
2. planar rotations \(\Rightarrow\) conserved angular momentum \(L\).

After eliminating cyclic coordinates, radial motion is equivalent to
\[
p_r^2=\mathcal R(r;E,L,\text{parameters}),
\]
or equivalently
\[
\dot r^2 + V_{\mathrm{eff}}(r;L)=E_{\mathrm{eff}}.
\]

### Turning-Point Principle

1. Allowed radial region: \(\mathcal R(r)\ge0\).
2. Bounded non-circular branch: two turning points \(r_{\min}<r_{\max}\).
3. Boundary of branch (separatrix/circular limit): double root
   \[
   \mathcal R(r_\star)=0,\qquad \mathcal R'(r_\star)=0.
   \]

This is the common discriminant mechanism behind the SR/GR statements.

## Instantiation A: SR Coulomb/Kepler Class

From Claim 3 notes, with \(u=1/r\),
\[
u'^2=A+2Bu-\alpha^2u^2,\qquad
\alpha^2=1-\frac{K^2}{L^2c^2}.
\]
Turning points are roots of a quadratic in \(u\); circular boundary is discriminant-zero:
\[
B^2+\alpha^2A=0.
\]
Sign regimes of \(\alpha^2\) split oscillatory/critical/hyperbolic sectors.

## Instantiation B: Schwarzschild Geodesic Class

From Claim 6 notes (\(G=c=M=1\)),
\[
\dot r^2=E^2-\left(1-\frac2r\right)\left(1+\frac{\ell^2}{r^2}\right)
=:R(r).
\]
The fixed-\(E\) interval
\[
\ell_{\min}(E)<\ell\le\ell_{\max}(E)
\]
is exactly the double-root structure of \(R\):

- outer stable circular branch,
- inner unstable circular separatrix,
- merger at ISCO.

## Instantiation C: Gauge-Theory Static Sector

For static sources, potential is defined by Wilson loop:
\[
\langle W(r,T)\rangle\sim e^{-V(r)T}.
\]
In a probe worldline action
\[
S_{\text{probe}}=\int \left(\text{kinetic} - qV(r)\right)dt,
\]
the same reduction gives radial \(\mathcal R(r)\), so turning-point/double-root logic applies once \(V(r)\) is fixed.
What changes across phases is the asymptotic form of \(V\):

1. Coulomb,
2. confining linear,
3. screened Yukawa/saturation.

So the geometry-of-force branch is encoded by the phase of the gauge theory, but the reduction mechanism is unchanged.

## Corollary (Narrative Lock)

The foundational narrative is mathematically coherent:

1. Newtonian area-law conservation gives the finite-step geometric conservation seed.
2. Action reduction translates symmetry to constants of motion.
3. Orbit/geodesic class boundaries are discriminant/double-root conditions.
4. The same action logic extends to gauge-defined static potentials.
5. This supplies the geometry side of the Claim 1 program (distribution/half-density/path-integral side).

## Reproducibility

Run:

```bash
python3.12 research/workspace/simulations/foundation_action_reduction_unification_check.py
```

The script prints representative SR and Schwarzschild double-root diagnostics and the gauge-phase asymptotic map in one table.
