# Claim 3 Phase D: Global Time-Domain Classification for SR Coulomb Dynamics

Date: 2026-02-08  
Source anchors in canonical transcript: `conv_patched.md:395`, `conv_patched.md:407`, `conv_patched.md:415`, `conv_patched.md:417`

## Goal

Close the remaining gap between \(\varphi\)-equation classification and global coordinate-time branch structure.

## Setup

For \(V(r)=-K/r\), \(u=1/r\), \(K>0\), conserved \((E,L)\), define
\[
\alpha^2:=1-\frac{K^2}{L^2c^2},\qquad
A:=\frac{E^2-m^2c^4}{L^2c^2},\qquad
B:=\frac{KE}{L^2c^2}.
\]
Then
\[
u'^2 = A+2Bu-\alpha^2u^2.
\]

From Hamiltonian flow:
\[
\dot r=\frac{\partial H}{\partial p_r}
\propto p_r,\qquad
p_r^2=L^2\big(A+2Bu-\alpha^2u^2\big).
\]
Hence global time branches are determined by positive-\(u\) roots of
\[
Q(u):=A+2Bu-\alpha^2u^2.
\]

## Proposition 1 (\(L>K/c\), \(\alpha^2>0\))

\(Q\) is a downward parabola.

For physical \(E>0\):

1. \(E<mc^2\) (\(A<0\)): two positive roots \(u_-<u_+\), allowed interval \(u\in[u_-,u_+]\) (bounded radial shell), oscillatory \(r(t)\).
2. \(E=mc^2\) (\(A=0\)): roots \(u=0\) and \(u=2B/\alpha^2>0\), threshold branch.
3. \(E>mc^2\) (\(A>0\)): one positive and one negative root, allowed \(u\in[0,u_+]\), scattering branch.

## Proposition 2 (\(L=K/c\), \(\alpha^2=0\))

\[
Q(u)=A+2Bu.
\]
No periodic branch exists. Motion is monotone between at most one turning point (if \(A<0\)); for \(E>0\) and \(A\ge0\), center-access branch is kinematically open.

## Proposition 3 (\(L<K/c\), \(\alpha^2<0\))

Write \(\lambda^2=-\alpha^2>0\), then
\[
Q(u)=A+2Bu+\lambda^2u^2,
\]
an upward parabola with positive large-\(u\) growth.  
For \(E>0\), large \(u\) is always allowed, so center-access/plunge branch exists; no periodic bounded shell arises.

## Corollary

Combining with the \(\varphi\)-classification from
`research/workspace/notes/theorems/2026-02-08-claim3-coulomb-phase-classification.md`,
the SR Coulomb dynamics is globally classified in coordinate time by turning-point count/sign in \(Q(u)\).

## Reproducibility Check

Run:

```bash
python3.12 research/workspace/simulations/claim3_global_time_classification_scan.py
```
