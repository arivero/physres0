# Claim 3 Phase X: Collision/Escape Asymptotic-Time Estimates for SR Coulomb

Date: 2026-02-09  
Depends on: `research/workspace/notes/theorems/2026-02-08-claim3-coulomb-phase-classification.md`, `research/workspace/notes/theorems/2026-02-08-claim3-coulomb-global-time-classification.md`

## Goal

Close the Claim 3 open item by adding explicit asymptotic coordinate-time estimates for:

1. escape to \(r\to\infty\),
2. collision \(r\to0\) in center-access branches.

## Setup

For \(V(r)=-K/r\), \(K>0\), conserved \(E,L\), the radial momentum satisfies
\[
p_r^2
=
\frac{(E+K/r)^2-m^2c^4}{c^2}-\frac{L^2}{r^2}
=
\frac{K^2/c^2-L^2}{r^2}+\frac{2EK}{c^2r}+\frac{E^2-m^2c^4}{c^2}.
\]
Since \(p_r=\gamma m\dot r\) and \(\gamma m=(E+K/r)/c^2\),
\[
\dot r=\frac{c^2\,p_r}{E+K/r},
\qquad
\frac{dt}{dr}
=
\frac{E+K/r}{c^2\,|p_r|}.
\]

## Theorem 1 (Escape Asymptotic for \(E>mc^2\), Scattering Branch)

Assume \(E>mc^2\) and consider an outgoing branch with \(r\to\infty\). Then
\[
p_r(r)=p_\infty+O(r^{-1}),
\qquad
p_\infty:=\frac{\sqrt{E^2-m^2c^4}}{c}>0.
\]
Hence
\[
\frac{dt}{dr}
=
\frac{E}{c^2p_\infty}+O(r^{-1}),
\qquad
\dot r
=
v_\infty+O(r^{-1}),
\]
with
\[
v_\infty
=
\frac{c\sqrt{E^2-m^2c^4}}{E}
=
c\sqrt{1-\frac{m^2c^4}{E^2}}.
\]
Therefore
\[
t(r)=\frac{E}{c^2p_\infty}\,r+O(\log r)\to\infty.
\]

### Proof

Expand \(p_r^2\) at large \(r\):
\[
p_r^2
=
p_\infty^2+\frac{2EK}{c^2r}+O(r^{-2}).
\]
Taking square root yields \(p_r=p_\infty+O(r^{-1})\). Insert in \(dt/dr\), then integrate.
\(\square\)

## Theorem 2 (Finite-Time Collision for \(L<K/c\))

Assume \(L<K/c\) and a branch with \(r\to0\). Set
\[
C_0:=\sqrt{K^2/c^2-L^2}>0.
\]
Then
\[
p_r(r)=\frac{C_0}{r}+O(1),
\qquad
\frac{dt}{dr}
=
\frac{K}{c^2C_0}+O(r).
\]
Hence there is a finite collision time \(t_*\) with
\[
t_*-t(r)=\frac{K}{c^2C_0}\,r+O(r^2),
\qquad r\to0.
\]

### Proof

Near \(r=0\), the \(r^{-2}\) term dominates in \(p_r^2\), giving
\[
p_r=\frac{C_0}{r}\sqrt{1+O(r)}=\frac{C_0}{r}+O(1).
\]
Also \(E+K/r=K/r+O(1)\). Substitute in \(dt/dr\):
\[
\frac{dt}{dr}
=
\frac{K/r+O(1)}{c^2(C_0/r+O(1))}
=
\frac{K}{c^2C_0}+O(r).
\]
Integrate from \(0\) to \(r\). \(\square\)

## Theorem 3 (Critical \(L=K/c\), \(E>0\): Finite-Time Square-Root Law)

Assume \(L=K/c\), \(E>0\), and a center-access branch \(r\to0\). Then
\[
p_r^2=\frac{2EK}{c^2r}+O(1),
\qquad
p_r=\sqrt{\frac{2EK}{c^2}}\,r^{-1/2}+O(r^{1/2}),
\]
and
\[
\frac{dt}{dr}
=
\frac{\sqrt{K}}{c\sqrt{2E}}\,r^{-1/2}+O(r^{1/2}).
\]
Therefore collision time is finite and
\[
t_*-t(r)=\frac{\sqrt{2K/E}}{c}\,\sqrt r+O(r^{3/2}).
\]

### Proof

At \(L=K/c\), the \(r^{-2}\) term cancels in \(p_r^2\), leaving the \(r^{-1}\) term dominant. Insert asymptotics into \(dt/dr\) and integrate.
\(\square\)

## Corollary (Claim 3 Upgrade)

Claim 3 now includes explicit asymptotic-time laws:

1. scattering branches (\(E>mc^2\), outgoing) have \(t\sim r/v_\infty\) and infinite escape time,
2. plunge branches (\(L<K/c\)) reach center in finite coordinate time with linear near-center law,
3. critical \(L=K/c\), \(E>0\) also reaches center in finite time with \(\sqrt r\)-law.

This closes the previously queued asymptotic-time gap for the SR Coulomb scoped model.

## Reproducibility

Run:

```bash
python3.12 research/workspace/simulations/claim3_asymptotic_time_estimates_check.py
```

The script confirms the three asymptotic constants numerically.
