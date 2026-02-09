# Claim 9 Phase AB: Non-Abelian Area-Law to Linear-Potential Scoped Theorem (\(G,D\)-Explicit)

Date: 2026-02-09 (US)  
Depends on:

- `research/workspace/notes/theorems/2026-02-08-claim9-model-class-propositions.md`
- `research/workspace/notes/theorems/2026-02-09-claim9-abelian-screened-theorem.md`
- `research/workspace/reports/2026-02-09-claim9-gauge-phase-long-range-paper.tex`

## Goal

Upgrade the next Claim 9 non-Abelian lane from program-only wording to an
assumption-explicit scoped theorem: if a \((G,D)=(SU(N),D)\) branch obeys an
area-law plus perimeter remainder window, then the extracted static potential is
linear with explicit finite-\(T\) error bounds.

## Dependency Declaration

We track this lane as:
\[
\mathrm{C9\text{-}NA}(G,D)=\mathrm{C9\text{-}NA}(SU(N),D),\qquad N\ge2.
\]
No result is promoted unless both \(G\) and \(D\) are explicit in assumptions
and conclusions.

## Model Skeleton

1. gauge group: \(G=SU(N)\), \(N\ge2\),
2. spacetime dimension: \(D\ge3\), spatial \(n=D-1\),
3. finite lattice proxy Wilson rectangles \(W_{a,L}^{(G,D)}(r,T)\),
4. extracted potential:
   \[
   V_{a,L}^{(G,D)}(r;T):=-\frac1T\log\langle W_{a,L}^{(G,D)}(r,T)\rangle.
   \]

## Assumption Package (AB)

Fix a \((G,D)=(SU(N),D)\) branch and a finite distance window
\(r\in[r_{\min},r_{\max}]\), \(0<r_{\min}<r_{\max}\). Assume:

1. **(ALP)** area-law + perimeter + bounded remainder:
   \[
   \log\langle W(r,T)\rangle
   =-
   \sigma_D rT
   +p_D(r+T)
   +c_D
   +\varepsilon_D(r,T),
   \]
   with \(\sigma_D>0\), \(T\ge T_0\), and
   \[|\varepsilon_D(r,T)|\le C_D.\]
2. **(POS)** positivity window:
   \[
   0<\langle W(r,T)\rangle<1
   \quad (r\in[r_{\min},r_{\max}],\ T\ge T_0).
   \]
3. **(EXT)** large-\(T\) extraction is performed only inside this explicit
   \((G,D)\)-tagged window.

## Theorem 1 (Finite-\(T\) Linear Extraction Bound)

Under (ALP)+(POS)+(EXT),
\[
V(r;T)=\sigma_D r-p_D-\frac{p_Dr+c_D+\varepsilon_D(r,T)}{T}.
\]
Hence for every \(r\in[r_{\min},r_{\max}]\), \(T\ge T_0\),
\[
\left|V(r;T)-\bigl(\sigma_Dr-p_D\bigr)\right|
\le
\frac{|p_D|r+|c_D|+C_D}{T}.
\]
So the finite-\(T\) extracted potential converges to a linear law in \(r\) with
explicit \(O(T^{-1})\) rate.

### Proof sketch

Insert (ALP) into the definition
\(V(r;T)=-(1/T)\log\langle W(r,T)\rangle\), isolate the linear term,
and bound the remainder with \(|\varepsilon_D|\le C_D\). \(\square\)

## Theorem 2 (Two-Point Slope Recovery of \(\sigma_D\))

For any \(r_1<r_2\) in the same window,
\[
S_T(r_1,r_2):=\frac{V(r_2;T)-V(r_1;T)}{r_2-r_1}
\]
obeys
\[
\left|S_T(r_1,r_2)-\sigma_D\right|
\le
\frac{|p_D|}{T}+
\frac{2C_D}{T(r_2-r_1)}.
\]
So \(S_T\to\sigma_D\) with explicit \(O(T^{-1})\) control.

## Corollary (Scoped Claim 9 Upgrade)

In this assumption-explicit \((SU(N),D)\) lane, the confining branch is now
closed at scoped theorem level for finite-window extraction:

1. linear asymptotics follow with explicit finite-\(T\) remainder bounds,
2. string tension recovery from slope estimators is quantitatively controlled,
3. \((G,D)\)-dependency is explicit in both assumptions and output.

Open gap remains: deriving (ALP)+(POS) from a full continuum non-Abelian model,
and proving dynamical-matter string-breaking crossover at theorem level.
Phase AC now derives (ALP)+(POS) in an explicit strong-coupling lattice window
(`research/workspace/notes/theorems/2026-02-09-claim9-nonabelian-strong-coupling-window-derivation.md`).
The remaining gap is extending that derivation beyond the strong-coupling window
and closing dynamical-matter crossover rigor.

## Validation Contract

### Assumptions

1. all statements are conditioned on explicit \((G,D)=(SU(N),D)\),
2. finite-\(T\) extraction window \([r_{\min},r_{\max}]\) and \(T\ge T_0\) is explicit,
3. area-law and perimeter parameters are tracked separately.

### Units and dimensions check

1. \(\sigma_D\) has energy/length units in fixed \((G,D)\) conventions,
2. \(rT\) and \(r+T\) channels are separated in (ALP).

### Symmetry/conservation checks

1. gauge invariance is encoded via Wilson loops,
2. extraction uses only gauge-invariant observables.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim9_nonabelian_arealaw_linear_check.py
```

The script checks:

1. Wilson-loop positivity window in synthetic \((G,D)\)-tagged data,
2. theorem bound for \(|V-(\sigma r-p)|\),
3. theorem bound for two-point slope \(|S_T-\sigma|\),
4. \(T\to\infty\) string-tension recovery by \(1/T\) extrapolation.

### Confidence statement

This closes a scoped non-Abelian extraction theorem lane under explicit
assumptions. With Phase AC, those assumptions are now derived in a scoped
strong-coupling lattice window. Full continuum confinement/string-breaking rigor
outside that window remains open.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic seed printed by script,
3. date anchor: 2026-02-09 (US).
