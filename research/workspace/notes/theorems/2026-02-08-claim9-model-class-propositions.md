# Claim 9 Phase E: Model-Class Propositions for Gauge-Theory Long-Range Terms

Date: 2026-02-08  
Source anchors in canonical transcript: `conv_patched.md:619`, `conv_patched.md:633`, `conv_patched.md:647`, `conv_patched.md:651`

## Goal

Replace broad ``generic gauge theory'' language by explicit model-class propositions with assumptions and outcomes.

## Common Definition

For static sources at separation \(r\), define
\[
\langle W(r,T)\rangle \sim e^{-V(r)T},\qquad T\to\infty.
\]
Long-range classification is about the asymptotic behavior of \(V(r)\).

Dependency declaration:
\[
\mathrm{Goal9}=\mathrm{Goal9}(G,D;\text{phase},\text{matter}).
\]
All propositions below are explicit in both \(G\) and \(D\).

## Dependency Matrix (Model Class vs Dimension)

1. \((G=U(1),\text{massless},D)\): Coulomb kernel branch.
2. \((G=U(1),m_V>0,D)\): screened/Yukawa branch.
3. \((G=SU(N),N\ge2,N_f=0,D)\): pure YM confining branch.
4. \((G=SU(N),N\ge2,N_f>0,D)\): string-breaking crossover branch.

## Proposition A (Massless Abelian / Coulomb-Class Sector)

Assumptions:

1. gauge group is \(G=U(1)\) in a massless unscreened sector,
2. static kernel is Laplacian Green function in \(n=D-1\) space dimensions.

Conclusion:
\[
V(r)\sim g^2 C\,
\begin{cases}
r, & D=2,\\
\log r, & D=3,\\
r^{3-D}, & D\ge4.
\end{cases}
\]

## Proposition B (Abelian Higgs / Screened Sector)

Assumptions:

1. gauge group is \(G=U(1)\) with gauge boson mass \(m_V>0\) (Higgs mechanism),
2. static kernel is Yukawa-type Green function.

Conclusion:
\[
V(r)\sim r^{-(D-2)/2}e^{-m_V r}
\]
up to constants, hence saturation at very large \(r\).

## Proposition C (Pure Yang-Mills Confining Sector)

Assumptions:

1. gauge group is \(G=SU(N)\), \(N\ge2\), pure-gauge confining regime with Wilson-loop area law
   \(\langle W\rangle\sim e^{-\sigma rT}\),
2. no dynamical fundamental matter capable of string breaking.

Conclusion:
\[
V(r)\sim \sigma r
\]
at large separation.

## Proposition D (YM with Dynamical Fundamental Matter)

Assumptions:

1. gauge group is \(G=SU(N)\), \(N\ge2\), with \(N_f>0\) dynamical fundamentals,
2. confining-like flux tube forms at intermediate scales,
3. pair creation/string breaking is dynamically allowed.

Conclusion:

1. intermediate \(r\): approximately linear \(V(r)\sim \sigma r\),
2. sufficiently large \(r\): crossover to saturation (flattening of \(V\)).

## Corollary (Claim 9 Status)

Claim 9 is now split into assumption-explicit model classes.  
Remaining non-theorem gap is not conceptual but model-specific rigor:
for each \((G,D)\)-class, one still needs precise hypotheses and theorem-level
existence statements in chosen regularization framework.

## Reproducibility Check

Run:

```bash
python3.12 research/workspace/simulations/claim9_model_class_table.py
```

This prints the model-class assumption/outcome table by \((G,D)\).

## Companion Theorem (Scoped Closure)

For theorem-grade closure of Proposition B (screened Abelian class), see:

`research/workspace/notes/theorems/2026-02-09-claim9-abelian-screened-theorem.md`
