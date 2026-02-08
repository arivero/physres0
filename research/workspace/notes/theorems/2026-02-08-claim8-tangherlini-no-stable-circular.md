# Claim 8 Formalization (Scoped): No Stable Circular Timelike Orbits in Tangherlini for \(D\ge 5\)

Date: 2026-02-08  
Source anchors in canonical transcript: `conv_patched.md:539`

## Scope

This note proves the claim for the static, spherically symmetric single-hole class (Schwarzschild--Tangherlini).  
It does **not** yet cover the full rotating Myers--Perry family.

## Setup

Let
\[
f(r)=1-\frac{\mu}{r^q},\qquad q:=D-3,\qquad D\ge 4,
\]
and for equatorial timelike geodesics use
\[
V_{\text{eff}}(r;\ell)=f(r)\left(1+\frac{\ell^2}{r^2}\right).
\]

Circular orbit condition \(V_{\text{eff}}'(r)=0\) gives
\[
\ell^2(r)=\frac{q\mu r^2}{2r^q-(q+2)\mu},
\]
so existence requires
\[
2r^q>(q+2)\mu.
\]

## Proposition (Stability Sign)

At a circular orbit radius, the second derivative simplifies to
\[
V_{\text{eff}}''(r)
=
\mu q\,r^{-q-4}
\Big((2-q)r^2-(q+2)\ell^2\Big).
\]

Therefore:

1. If \(q\ge 2\) (\(D\ge 5\)), then \((2-q)r^2\le 0\) while \((q+2)\ell^2>0\), so
   \[
   V_{\text{eff}}''(r)<0
   \]
   at every circular orbit. Hence no stable circular timelike orbit exists.
2. If \(q=1\) (\(D=4\)), both signs are possible; stability reduces to
   \[
   r^2>3\ell^2,
   \]
   reproducing the Schwarzschild stable branch (\(r>6M\), after \(\mu=2M\)).

## Corollary (Claim 8 Status Upgrade)

For standard static single-hole backgrounds (Tangherlini), the ``no stable circular orbits in higher dimensions'' statement is theorem-level for \(D\ge 5\).  
The broader multi-background claim in `conv_patched.md:539` remains partially open until rotating/more general classes are pinned with equal precision.

For asymptotic extension beyond exact Tangherlini, see:

`research/workspace/notes/theorems/2026-02-08-claim8-beyond-tangherlini-asymptotic.md`

## Reproducibility Check

Run:

```bash
python3.12 research/workspace/simulations/claim8_tangherlini_stability_scan.py
```

The script evaluates circular-orbit existence and stability indicators across dimensions.
