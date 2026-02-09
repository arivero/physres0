# Claim 9 Formalization: Gauge-Theory Long-Range Potential by Phase and Dimension

Date: 2026-02-08  
Source anchors in canonical transcript: `conv_patched.md:619`, `conv_patched.md:633`, `conv_patched.md:647`, `conv_patched.md:651`

## Goal

Replace a single broad long-range claim by explicit phase-split propositions with clear assumptions.

## Setup

Let \(G\) be gauge group, \(D\) spacetime dimension, and \(n=D-1\) spatial dimension.  
Define static inter-source potential from a large rectangular Wilson loop:
\[
\langle W(r,T)\rangle \sim e^{-V(r)T},\qquad T\to\infty.
\]

Dependency declaration:
\[
\mathrm{Goal9}=\mathrm{Goal9}(G,D;\text{phase},\text{matter}).
\]
Every statement below is tagged by both \(G\) and \(D\).

## Proposition 1 (Coulomb Phase, Massless Gauge Mode; \(G=U(1)\), \(D\))

Assume \(G=U(1)\), Coulomb phase, massless gauge propagation, and no IR mass gap.  
Then static kernel is the Laplacian Green function:
\[
\nabla^2\Phi_n(\mathbf x)=-\delta^{(n)}(\mathbf x),
\]
with asymptotics
\[
\Phi_n(r)\sim
\begin{cases}
r, & n=1,\\
\log r, & n=2,\\
r^{2-n}, & n>2.
\end{cases}
\]
Hence
\[
V_{\text{Coul}}(r)\propto g^2 C\,\Phi_n(r),
\]
so equivalently in \(D\):
\[
V_{\text{Coul}}(r)\sim
\begin{cases}
r, & D=2,\\
\log r, & D=3,\\
r^{3-D}, & D\ge 4.
\end{cases}
\]

## Proposition 2 (Screened/Higgs Phase; \(G=U(1)\), \(D\))

Assume \(G=U(1)\) with effective gauge mass scale \(m_{\mathrm{scr}}>0\).  
Then static kernel is Yukawa-type:
\[
(\nabla^2-m_{\mathrm{scr}}^2)G=-\delta,
\]
and for large \(r\):
\[
G(r)\sim r^{-(n-1)/2}e^{-m_{\mathrm{scr}}r}.
\]
Therefore the long-range potential is exponentially suppressed and approaches a constant at large separation (up to convention-dependent additive constants).

## Proposition 3 (Confining Phase, Area Law Sector; \(G=SU(N)\), \(D\))

Assume \(G=SU(N)\), \(N\ge2\), and an area law for large Wilson loops:
\[
\langle W(r,T)\rangle \sim e^{-\sigma rT},
\]
with string tension \(\sigma>0\). Then
\[
V_{\text{conf}}(r)\sim \sigma r
\]
at intermediate/large \(r\) in the pure-gauge sector.

With dynamical fundamental matter (\(N_f>0\)), string breaking can occur and
the asymptotic \(r\to\infty\) potential crosses over to saturation rather than
strict linear growth.

## Corollary (Claim 9 Upgrade)

The long-range term is phase-dependent, not a single universal power law:

1. \((G=U(1),D)\) Coulomb phase: Green-function power/log/linear by \(D\).
2. \((G=U(1),D)\) screened/Higgs phase: exponential suppression and saturation.
3. \((G=SU(N),D)\) confining area-law sector: linear regime (with possible
   string breaking for \(N_f>0\)).

## Scope Notes

- This classification is asymptotic and phase-conditional.
- It does not claim a universal phase diagram across all \((G,D)\) choices.

## Reproducibility Check

Run:

```bash
python3.12 research/workspace/simulations/claim9_phase_longrange_table.py
```

The script prints the asymptotic form table by \((G,D,\text{phase})\).

## Companion Model-Class Note

See:

`research/workspace/notes/theorems/2026-02-08-claim9-model-class-propositions.md`

for explicit assumption-by-assumption propositions (massless Abelian, Abelian Higgs, pure YM, YM + dynamical fundamental matter).
