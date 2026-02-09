# Claim 9 Phase AA: Non-Abelian Area-Law to Linear-Potential Program (\(G,D\)-Explicit)

Date: 2026-02-09 (US)  
Depends on:

- `research/workspace/notes/theorems/2026-02-08-claim9-model-class-propositions.md`
- `research/workspace/reports/2026-02-09-claim9-gauge-phase-long-range-paper.tex`

## Goal

Start the next Claim 9 closure lane after the screened-Abelian theorem:
derive a theorem-grade non-Abelian area-law to linear-potential statement with
explicit dependencies on gauge group \(G\) and dimension \(D\).

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
3. finite lattice proxy with Wilson rectangles \(W_{a,L}^{(G,D)}(r,T)\),
4. static potential extraction:
   \[
   V_{a,L}^{(G,D)}(r;T):=-\frac1T\log\langle W_{a,L}^{(G,D)}(r,T)\rangle.
   \]

## Target Theorem Template (Program Form)

Assume in a fixed \((G,D)=(SU(N),D)\) class:

1. area law window:
   \[
   \left|\log\langle W(r,T)\rangle+\sigma_D\,rT\right|
   \le
   c_{1,D}(r+T)+c_{0,D},
   \]
2. denominator positivity and finite-volume extraction controls,
3. \(T\)-uniform control of boundary/perimeter corrections in a fixed \(r\)-window.

Then:
\[
V(r)=\lim_{T\to\infty}V(r;T)=\sigma_D\,r+\beta_D(r),
\]
with explicit \((G,D)\)-tagged remainder control in the chosen window.

This is the next theorem-grade target for Claim 9.

## Immediate Deliverable (This Pass)

Provide an executable extraction sanity check demonstrating that when
\((G,D)\)-tagged area-law+perimeter structure is present, the fitted
large-\(T\) potential slope in \(r\) recovers \(\sigma_D\).

## Validation Contract

### Assumptions

1. synthetic or model-proxy Wilson data generated under explicit \((G,D)\) tags,
2. area-law + perimeter correction form is stated before fitting.

### Units and dimensions check

1. \(\sigma_D\) has energy/length units in fixed \((G,D)\) conventions,
2. \(rT\) area term and \(r+T\) perimeter term are separated explicitly.

### Symmetry/conservation checks

1. gauge invariance is encoded through Wilson-loop observables,
2. extraction uses only gauge-invariant loop expectations.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/claim9_nonabelian_arealaw_linear_check.py
```

The script checks:

1. large-\(T\) stabilization of \(V(r;T)\),
2. regression recovery of \(\sigma_D\),
3. robustness under small synthetic noise.

### Confidence statement

This note starts the non-Abelian \((G,D)\)-explicit lane; it is a program
template plus executable extraction check, not yet full theorem closure.

### Reproducibility metadata

1. Python: `python3.12`,
2. deterministic seed printed by script,
3. date anchor: 2026-02-09 (US).
