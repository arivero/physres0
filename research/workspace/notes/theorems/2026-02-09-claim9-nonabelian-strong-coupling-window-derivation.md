# Claim 9 Phase AC: Deriving Non-Abelian ALP Hypotheses in a Strong-Coupling Lattice Window

Date: 2026-02-09 (US)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim9-nonabelian-arealaw-linear-program.md`
- `research/workspace/reports/2026-02-09-claim9-gauge-phase-long-range-paper.tex`

## Goal

Close the next Claim 9 dependency by deriving the AB assumption package
(area-law + perimeter + bounded remainder) from an explicit model class:
lattice \(SU(N)\) Yang-Mills in a strong-coupling window.

## Dependency Declaration

\[
\mathrm{C9\text{-}NA}(G,D)=\mathrm{C9\text{-}NA}(SU(N),D),\qquad N\ge2,\ D\ge3.
\]
No upgrade is accepted unless both \(G\) and \(D\) are explicit.

## Explicit Model Class

Work on hypercubic Euclidean lattice spacing \(a\), Wilson action
\[
S_W(U)=-\frac{\beta}{N}\sum_p \Re\operatorname{Tr}(U_p),\qquad 0<\beta\le\beta_{\mathrm{sc}}.
\]
For rectangular loop \(C(r,T)\) with \(r,T\in a\mathbb N\), define
\[
A(C)=\frac{rT}{a^2},\qquad P(C)=\frac{2(r+T)}{a}.
\]

## Strong-Coupling Input Package (AC)

Assume in this fixed \((G,D)\) class:

1. **(SC-EXP)** rectangle expansion form in a window \(0<\beta\le\beta_{\mathrm{sc}}\):
   \[
   \log\langle W(C)\rangle
   =
   -\sigma_{\mathrm{sc}}(\beta)\,A(C)
   +\pi_{\mathrm{sc}}(\beta)\,P(C)
   +\delta_{\mathrm{sc}}(C;\beta),
   \]
   with \(\sigma_{\mathrm{sc}}(\beta)>0\).
2. **(SC-REM)** bounded residual:
   \[
   |\delta_{\mathrm{sc}}(C;\beta)|\le C_{\mathrm{sc}}(\beta),
   \]
   uniformly for rectangles in the extraction window.
3. **(SC-POS)** positivity window:
   \[
   0<\langle W(C)\rangle<1.
   \]

## Theorem 1 (Strong-Coupling \(\Rightarrow\) AB Assumption Package)

Under (SC-EXP)+(SC-REM)+(SC-POS), define
\[
\sigma_D(\beta):=\frac{\sigma_{\mathrm{sc}}(\beta)}{a^2},\qquad
p_D(\beta):=\frac{2\pi_{\mathrm{sc}}(\beta)}{a},\qquad
c_D(\beta):=0,\qquad
\varepsilon_D(r,T;\beta):=\delta_{\mathrm{sc}}(C(r,T);\beta).
\]
Then the AB hypothesis form holds:
\[
\log\langle W(r,T)\rangle
=
-\sigma_D(\beta)\,rT
+p_D(\beta)\,(r+T)
+c_D(\beta)
+\varepsilon_D(r,T;\beta),
\]
with
\[
|\varepsilon_D(r,T;\beta)|\le C_{\mathrm{sc}}(\beta),
\]
and \(0<\langle W(r,T)\rangle<1\).

Hence the AC model class explicitly discharges the AB assumption package in that
strong-coupling window.

### Proof sketch

Substitute \(A(C)=rT/a^2\), \(P(C)=2(r+T)/a\) into (SC-EXP), then collect terms
by channels \(rT\), \(r+T\), and bounded residual. (SC-POS) is inherited
verbatim. \(\square\)

## Corollary (AC + AB)

Combining Theorem 1 with AB Theorem 1/2 yields a scoped linear-extraction result
in this explicit model class:

1. finite-\(T\) potential extraction is linear in \(r\) up to explicit \(O(T^{-1})\) errors,
2. two-point slope estimators recover \(\sigma_D(\beta)\) with explicit bounds,
3. all statements are indexed by explicit \((SU(N),D)\) and \(\beta\)-window data.

## Validation Contract

### Assumptions

1. fixed model class: Wilson lattice \(SU(N)\), explicit \(D\), explicit \(\beta\)-window,
2. rectangular loop extraction window is explicit.

### Units and dimensions check

1. \(A(C)=rT/a^2\) and \(P(C)=2(r+T)/a\) are dimensionless lattice counts,
2. \(\sigma_D\) has energy/length units and \(p_D\) has energy units.

### Symmetry/conservation checks

1. Wilson loops are gauge invariant by construction,
2. extraction uses only gauge-invariant loop observables.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim9_nonabelian_strong_coupling_window_check.py
```

The script checks:

1. \(\beta\)-window and positivity constraints,
2. explicit channel decomposition \((rT)\) + \((r+T)\) + bounded residual,
3. residual cap independent of \(r,T\) in the tested window,
4. compatibility of derived \((\sigma_D,p_D)\) with AB extraction checks.

### Confidence statement

AC provides a scoped derivation of AB assumptions in an explicit strong-coupling
model window. Phase AD now extends this with an explicit \(\beta\)-transfer
assumption lane (`research/workspace/notes/theorems/2026-02-09-claim9-nonabelian-beyond-window-transfer-assumptions.md`).
Remaining open gap: first-principles control of transfer assumptions and full
continuum non-Abelian confinement/string-breaking rigor.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic seed printed by script,
3. date anchor: 2026-02-09 (US).
