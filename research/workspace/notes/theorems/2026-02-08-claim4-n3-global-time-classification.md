# Claim 4 Phase D: Global Time-Domain Classification for \(n=3\) SR Dynamics

Date: 2026-02-08  
Source anchors in canonical transcript: `conv_patched.md:426`, `conv_patched.md:434`, `conv_patched.md:436`

## Goal

Complete the \(n=3\) picture in coordinate time by explicit turning-point analysis in \(r\), not only \(\varphi\)-phase portrait.

## Setup

For \(V(r)=-K/(2r^2)\), define \(u=1/r\). Radial momentum equation:
\[
p_r^2=
\frac{(E+Ku^2/2)^2-m^2c^4}{c^2}
-L^2u^2.
\]
So
\[
p_r^2=
\frac{K^2}{4c^2}u^4
\left(\frac{EK}{c^2}-L^2\right)u^2
\frac{E^2-m^2c^4}{c^2}.
\]
Let \(y:=u^2\ge0\):
\[
p_r^2 = a_2 y^2 + a_1 y + a_0,
\]
with
\[
a_2=\frac{K^2}{4c^2}>0,\quad
a_1=\frac{EK}{c^2}-L^2,\quad
a_0=\frac{E^2-m^2c^4}{c^2}.
\]

## Proposition 1 (Allowed-Set Topology in \(y\))

Since \(a_2>0\), the polynomial is upward in \(y\).  
Hence allowed set \(\{y\ge0:p_r^2(y)\ge0\}\) can be:

1. all \(y\ge0\),
2. one semi-infinite interval \([y_*,\infty)\),
3. two disjoint semi-infinite pieces \([0,y_-]\cup[y_+,\infty)\) (if two positive roots).

There is no finite closed interval \([y_1,y_2]\subset(0,\infty)\) as the only allowed set, so no generic periodic bounded shell in \(r(t)\).

## Proposition 2 (Global Branch Types)

Map \(y=u^2=1/r^2\):

1. large \(y\) branch \(\Rightarrow r\to0\): plunge/collision channel,
2. small \(y\) branch near \(0\) \(\Rightarrow r\to\infty\): escape/scattering channel.

If two positive roots exist, the two channels are separated by forbidden gap; circular motion appears only at double-root tuning (measure-zero and unstable per Duffing analysis).

## Corollary (Claim 4 Upgrade)

Within the SR \(n=3\) model, global coordinate-time topology confirms:

1. no robust bounded non-circular family,
2. generic branch splitting into plunge/escape sectors,
3. circular finite-radius motion is nongeneric and unstable.

This closes the main global-time gap left in the earlier phase-portrait note.

## Reproducibility Check

Run:

```bash
python3.12 research/workspace/simulations/claim4_global_time_shell_scan.py
```
