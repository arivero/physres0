# Top 10 Claim Audit (Next Pass)

Date: 2026-02-08  
Primary source: `conv_patched.md`  
Canonical rendered companion: `conv_patched.pdf`

## Label Criteria

- `proved`: derivation is explicit and closed within the stated model, or a standard external result is cited with no unresolved model jump.
- `heuristic`: claim is plausible and technically motivated but still depends on asymptotics, omitted steps, scope caveats, or unproven global assumptions.
- `speculative`: claim is interpretive/bridging/conceptual and currently lacks a strict theorem-level derivation.

## Top 10 Results

| Rank | Claim | Location | Label | Why this label | Upgrade path |
|---|---|---|---|---|---|
| 1 | Halved expression as a half-density/tangent-groupoid bridge to path integrals | `conv_patched.md:814`, `conv_patched.md:934`, `conv_patched.md:967` | `speculative` | Scoped in `research/workspace/notes/theorems/2026-02-08-claim1-scoped-bridge-statement.md`: static modulus-square limit is theorem-grade; QM/QFT are now organized as a variational-delta ladder \(\delta(\delta S)\) selecting extrema, but full infinite-dimensional equivalence is still open. | Prove finite-dimensional manifold half-density convolution limit, then construct a controlled cylinder-limit extension to path spaces. |
| 2 | SR center-access trichotomy from small-\(r\) scaling (\(n<2\), \(n=2\), \(n>2\)) | `conv_patched.md:371`, `conv_patched.md:388` | `proved` | Upgraded to theorem-level asymptotic classification in `research/workspace/notes/theorems/2026-02-08-claim2-center-access-trichotomy.md`, including explicit \(n=2,\;L=K/c\) energy-sign split. | Extend from local \(r\to0\) kinematics to a global phase-space statement (turning points, capture basins). |
| 3 | Relativistic Coulomb phase portrait via \(\alpha^2=1-K^2/(L^2c^2)\), including rotation number \(\Theta\) | `conv_patched.md:395`, `conv_patched.md:410`, `conv_patched.md:421` | `heuristic` | Partially upgraded in `research/workspace/notes/theorems/2026-02-08-claim3-coulomb-phase-classification.md`: explicit \(\alpha^2\)-regime split, energy-domain split for \(L>K/c\), and critical/hyperbolic branches are formalized. | Close the remaining gap from \(\varphi\)-domain classification to full time-parametrized global trajectory taxonomy with collision/escape asymptotics. |
| 4 | \(n=3\) Duffing-type reduction and non-generic bounded non-circular dynamics | `conv_patched.md:426`, `conv_patched.md:436` | `heuristic` | Partially upgraded in `research/workspace/notes/theorems/2026-02-08-claim4-n3-duffing-phase-portrait.md`: conserved Duffing Hamiltonian, unstable circular tuning, and escape/plunge branch structure are explicit in \(u=1/r>0\). | Close remaining gap between \(\varphi\)-phase portrait and full time-parametrized orbital classification (global measure statements). |
| 5 | D-dimensional GR matching in \(F=K/r^n\): \(n=D-2\), \(K\propto G_D mM\) with \(\Omega_{D-2}\) factor | `conv_patched.md:490`, `conv_patched.md:495` | `proved` | Weak-field matching is explicitly written from Tangherlini parameterization and recovers \(D=4\) correctly. | Add a compact derivation note with conventions fixed and unit checks. |
| 6 | Fixed-energy Schwarzschild bound-orbit interval \(\ell_{\min}(E)<\ell\le\ell_{\max}(E)\) via separatrix | `conv_patched.md:521`, `conv_patched.md:535` | `heuristic` | Standard picture is correct, but interval structure is not fully derived in-file from potential discriminants. | Compute turning-point polynomial/discriminant explicitly and derive interval endpoints. |
| 7 | GR ISCO threshold statement for stable bounded orbits (including \(L=\sqrt{12}\,GMm/c\) form) | `conv_patched.md:519`, `conv_patched.md:597` | `proved` | Canonical Schwarzschild result, correctly framed as geometry-driven threshold and source-backed. | Add unit-convention crosswalk (\(G=c=1\) vs SI) to avoid ambiguity. |
| 8 | Higher-D GR claim: no stable circular orbits for standard single-hole backgrounds in high dimensions | `conv_patched.md:539` | `heuristic` | Broad claim is likely right but depends on background class and assumptions; scope caveat is present but not formalized. | Pin to explicit theorem statements per geometry class (Tangherlini/Myers-Perry, test-particle sector). |
| 9 | Gauge-theory long-range taxonomy across dimensions/phases (Coulomb/log/linear/screened) | `conv_patched.md:619`, `conv_patched.md:633`, `conv_patched.md:647` | `heuristic` | Strong synthesis, but phase- and matter-content dependence prevents theorem-level single statement. | Split into separate propositions by phase and matter content; include Wilson-loop definitions with assumptions. |
| 10 | SR circular-orbit benchmark inequalities: \(n=2\Rightarrow L>K/c\), \(n=3\Rightarrow L^2\ge Km\) | `conv_patched.md:143`, `conv_patched.md:230` | `proved` | Formalized as model-internal benchmark derivations in `research/workspace/notes/theorems/2026-02-08-claim10-circular-threshold-benchmarks.md`. | Encode these identities as regression checks in symbolic/numeric pipelines. |

## Priority for Novelty Work (Post-Audit)

1. Claim 1 (speculative): highest novelty, highest risk.
2. Claim 6 (heuristic): medium novelty, medium risk, clear discriminant-based upgrade path.
3. Claim 4 (heuristic): medium-high novelty, medium risk, with remaining global-time classification gap.

## Immediate Work Plan

1. [done] Claim 2 theorem/proof note with explicit assumptions and critical-case split.
2. [done] Claim 10 formal benchmark sheet for \(n=2\) and \(n=3\) circular thresholds.
3. [done] Scoped Claim 1 into theorem-grade static core vs conjectural full bridge.
4. [done] Claim 4 formalized at phase-portrait/Hamiltonian level with numerical sanity check.
5. [done] Claim 3 Coulomb phase portrait formalized at \(\alpha^2\)- and energy-domain level with numeric diagnostics.
6. [next] Formalize Claim 6 Schwarzschild fixed-energy interval via turning-point/discriminant derivation.
