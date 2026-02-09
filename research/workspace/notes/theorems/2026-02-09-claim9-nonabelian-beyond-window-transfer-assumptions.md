# Claim 9 Phase AD: Beyond Strong-Coupling Window via \(\beta\)-Transfer Assumptions

Date: 2026-02-09 (US)  
Depends on:

- `research/workspace/notes/theorems/2026-02-09-claim9-nonabelian-strong-coupling-window-derivation.md`
- `research/workspace/notes/theorems/2026-02-09-claim9-nonabelian-arealaw-linear-program.md`

## Goal

Advance Claim 9 beyond the AC strong-coupling window by an explicit transfer
lane: propagate AB assumption-package control from an anchor
\(\beta_0\le\beta_{\mathrm{sc}}\) to a larger interval
\([\beta_0,\beta_1]\) under \(\beta\)-regularity assumptions on Wilson-loop
logarithms.

## Dependency Declaration

\[
\mathrm{C9\text{-}NA}(G,D)=\mathrm{C9\text{-}NA}(SU(N),D),\qquad N\ge2,\ D\ge3.
\]
All statements remain explicit in \((G,D)\), \(\beta\)-window, and extraction
window \((r,T)\).

## Transfer Assumption Package (AD)

Fix an anchor \(\beta_0\in(0,\beta_{\mathrm{sc}}]\) where AC provides
\[
\log\langle W(r,T)\rangle_{\beta_0}
=
-\sigma_0\,rT+p_0\,(r+T)+\varepsilon_0(r,T),
\qquad
|\varepsilon_0(r,T)|\le C_0.
\]
Assume for \(\beta\in[\beta_0,\beta_1]\):

1. **(TB-DIFF)** channelized \(\beta\)-derivative decomposition
   \[
   \partial_\beta\log\langle W(r,T)\rangle_\beta
   =
   -a_\beta\,rT+b_\beta\,(r+T)+R_\beta(r,T).
   \]
2. **(TB-BOUNDS)** uniform bounds
   \[
   |a_\beta|\le A_*,\qquad |b_\beta|\le B_*,\qquad |R_\beta(r,T)|\le R_*.
   \]
3. **(TB-POS)** positivity in the transfer window:
   \[
   0<\langle W(r,T)\rangle_\beta<1.
   \]

## Theorem 1 (AD Transfer to AB Form on \([\beta_0,\beta_1]\))

Under (TB-DIFF)+(TB-BOUNDS)+(TB-POS), define
\[
\sigma(\beta):=\sigma_0+\int_{\beta_0}^{\beta}a_s\,ds,\qquad
p(\beta):=p_0+\int_{\beta_0}^{\beta}b_s\,ds,
\]
\[
\varepsilon_\beta(r,T):=
\varepsilon_0(r,T)+\int_{\beta_0}^{\beta}R_s(r,T)\,ds.
\]
Then for every \(\beta\in[\beta_0,\beta_1]\):
\[
\log\langle W(r,T)\rangle_\beta
=
-\sigma(\beta)\,rT+p(\beta)\,(r+T)+\varepsilon_\beta(r,T),
\]
with explicit bounds
\[
|\sigma(\beta)-\sigma_0|\le A_*|\beta-\beta_0|,\qquad
|p(\beta)-p_0|\le B_*|\beta-\beta_0|,
\]
\[
|\varepsilon_\beta(r,T)|\le C_0+R_*|\beta-\beta_0|.
\]
Hence AB assumptions extend from \(\beta_0\) to the full transfer window.

### Proof sketch

Integrate (TB-DIFF) in \(\beta\) and collect channels \(rT\), \(r+T\), and
residual. Apply (TB-BOUNDS) to obtain explicit estimates. \(\square\)

## Corollary (AD + AB Extraction Control)

Combining Theorem 1 with AB finite-\(T\) extraction theorems gives, uniformly for
\(\beta\in[\beta_0,\beta_1]\),

1. linear extraction form \(V_\beta(r;T)\approx \sigma(\beta)r-p(\beta)\),
2. explicit \(O(T^{-1})\) extraction bounds with \(C_\beta=C_0+R_*|\beta-\beta_0|\),
3. explicit \(\beta\)-window continuity control of inferred string tension
   \(\sigma(\beta)\).

## Validation Contract

### Assumptions

1. anchor AC lane at \(\beta_0\) is explicit,
2. transfer assumptions are explicit (\(a_\beta,b_\beta,R_\beta\) bounds),
3. extraction window in \((r,T)\) is explicit.

### Units and dimensions check

1. \(\sigma(\beta)\) keeps energy/length units,
2. \(p(\beta)\) keeps energy units,
3. \(R_\beta\) contributes to dimensionless \(\log\langle W\rangle\) channel.

### Symmetry/conservation checks

1. Wilson-loop gauge invariance is unchanged,
2. transfer is performed on gauge-invariant loop expectations only.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim9_nonabelian_beyond_window_transfer_check.py
```

The script checks:

1. anchor AB form at \(\beta_0\),
2. transfer identity across \(\beta\)-grid in \([\beta_0,\beta_1]\),
3. residual-cap bound \(C_0+R_*|\beta-\beta_0|\),
4. compatibility of transferred parameters with AB extraction bounds.

### Confidence statement

AD is a scoped theorem lane under explicit transfer assumptions. It does not
prove those assumptions from first principles outside strong coupling; it
provides the explicit bridge object needed for that next step.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic seed printed by script,
3. date anchor: 2026-02-09 (US).
