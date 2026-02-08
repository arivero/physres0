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
| 1 | Halved expression as a half-density/tangent-groupoid bridge to path integrals | `conv_patched.md:814`, `conv_patched.md:934`, `conv_patched.md:967` | `speculative` | Scoped and deepened in `research/workspace/notes/theorems/2026-02-08-claim1-scoped-bridge-statement.md`, `research/workspace/notes/theorems/2026-02-08-claim1-discrete-variational-delta-lemmas.md`, `research/workspace/notes/theorems/2026-02-08-claim1-manifold-halfdensity-convolution.md`, `research/workspace/notes/theorems/2026-02-08-claim1-point-supported-scaling-channels.md`, `research/workspace/notes/theorems/2026-02-08-claim1-cylinder-limit-program.md`, and `research/workspace/notes/theorems/2026-02-08-claim1-groupoid-halfdensity-theorem-pack.md`: static, finite-\(N\), manifold, multi-channel scaling, cylinder-limit, and explicit groupoid composition laws are in place; full continuum equivalence remains open. | Construct a renormalized continuum limit theorem with channel mixing control and observable-class convergence. |
| 2 | SR center-access trichotomy from small-\(r\) scaling (\(n<2\), \(n=2\), \(n>2\)) | `conv_patched.md:371`, `conv_patched.md:388` | `proved` | Upgraded to theorem-level asymptotic classification in `research/workspace/notes/theorems/2026-02-08-claim2-center-access-trichotomy.md`, including explicit \(n=2,\;L=K/c\) energy-sign split. | Extend from local \(r\to0\) kinematics to a global phase-space statement (turning points, capture basins). |
| 3 | Relativistic Coulomb phase portrait via \(\alpha^2=1-K^2/(L^2c^2)\), including rotation number \(\Theta\) | `conv_patched.md:395`, `conv_patched.md:410`, `conv_patched.md:421` | `heuristic` | Upgraded with explicit \(\varphi\)-regime and global-\(t\) turning-set notes in `research/workspace/notes/theorems/2026-02-08-claim3-coulomb-phase-classification.md` and `research/workspace/notes/theorems/2026-02-08-claim3-coulomb-global-time-classification.md`; still not a full asymptotic/collision-time theorem package. | Add explicit collision/escape asymptotic-time estimates and complete global uniqueness statements. |
| 4 | \(n=3\) Duffing-type reduction and non-generic bounded non-circular dynamics | `conv_patched.md:426`, `conv_patched.md:436` | `proved` | Combined notes `research/workspace/notes/theorems/2026-02-08-claim4-n3-duffing-phase-portrait.md` and `research/workspace/notes/theorems/2026-02-08-claim4-n3-global-time-classification.md` now provide conserved-quantity structure, instability of circular tuning, and global turning-set topology (no generic bounded shell). | Optional: add explicit time-to-plunge/escape asymptotics for selected parameter regimes. |
| 5 | D-dimensional GR matching in \(F=K/r^n\): \(n=D-2\), \(K\propto G_D mM\) with \(\Omega_{D-2}\) factor | `conv_patched.md:490`, `conv_patched.md:495` | `proved` | Formalized with conventions and unit cross-check in `research/workspace/notes/theorems/2026-02-08-claim5-ddim-gr-matching.md`. | Extend to explicit \(D=3\) log-potential branch in the same convention sheet. |
| 6 | Fixed-energy Schwarzschild bound-orbit interval \(\ell_{\min}(E)<\ell\le\ell_{\max}(E)\) via separatrix | `conv_patched.md:521`, `conv_patched.md:535` | `proved` | Formalized in `research/workspace/notes/theorems/2026-02-08-claim6-schwarzschild-fixed-energy-interval.md` with explicit circular-branch discriminant, closed-form \(u_{\mathrm{st/un}}(E)\), and \(\ell_{\min/\max}(E)\). | Extend to null geodesic analogue and Kerr deformation of the interval picture. |
| 7 | GR ISCO threshold statement for stable bounded orbits (including \(L=\sqrt{12}\,GMm/c\) form) | `conv_patched.md:519`, `conv_patched.md:597` | `proved` | Canonical Schwarzschild result, correctly framed as geometry-driven threshold and source-backed. | Add unit-convention crosswalk (\(G=c=1\) vs SI) to avoid ambiguity. |
| 8 | Higher-D GR claim: no stable circular orbits for standard single-hole backgrounds in high dimensions | `conv_patched.md:539` | `heuristic` | Scoped theorem exists for static Tangherlini in `research/workspace/notes/theorems/2026-02-08-claim8-tangherlini-no-stable-circular.md`, plus asymptotic extension in `research/workspace/notes/theorems/2026-02-08-claim8-beyond-tangherlini-asymptotic.md` showing far-zone instability for \(D>5\); rotating/global classes remain open. | Extend the same rigor to Myers-Perry and other non-static classes with precise parameter assumptions. |
| 9 | Gauge-theory long-range taxonomy across dimensions/phases (Coulomb/log/linear/screened) | `conv_patched.md:619`, `conv_patched.md:633`, `conv_patched.md:647` | `heuristic` | Upgraded to explicit phase and model-class propositions in `research/workspace/notes/theorems/2026-02-08-claim9-gauge-long-range-phase-split.md` and `research/workspace/notes/theorems/2026-02-08-claim9-model-class-propositions.md`; still assumption-sensitive and class-dependent. | Convert each model-class proposition into theorem-grade statements under specific rigorous frameworks (lattice/continuum assumptions). |
| 10 | SR circular-orbit benchmark inequalities: \(n=2\Rightarrow L>K/c\), \(n=3\Rightarrow L^2\ge Km\) | `conv_patched.md:143`, `conv_patched.md:230` | `proved` | Formalized as model-internal benchmark derivations in `research/workspace/notes/theorems/2026-02-08-claim10-circular-threshold-benchmarks.md`. | Encode these identities as regression checks in symbolic/numeric pipelines. |

## Priority for Novelty Work (Post-Audit)

1. Claim 1 (speculative): highest novelty, highest risk.
2. Claim 8 (heuristic): medium novelty, medium risk, rotating/global class closure pending.
3. Claim 3 (heuristic): medium novelty, medium risk, collision/escape asymptotic closure pending.

## Immediate Work Plan

1. [done] Claim 2 theorem/proof note with explicit assumptions and critical-case split.
2. [done] Claim 10 formal benchmark sheet for \(n=2\) and \(n=3\) circular thresholds.
3. [done] Scoped Claim 1 into theorem-grade static core vs conjectural full bridge.
4. [done] Claim 4 formalized at phase-portrait/Hamiltonian level with numerical sanity check.
5. [done] Claim 3 Coulomb phase portrait formalized at \(\alpha^2\)- and energy-domain level with numeric diagnostics.
6. [done] Claim 6 Schwarzschild fixed-energy interval formalized with explicit discriminant formulas and checks.
7. [done] Added compact derivation note for Claim 5 (D-dimensional GR matching conventions and unit cross-check).
8. [done] Added scoped theorem note for Claim 8 (Tangherlini \(D\ge 5\) no stable circular timelike orbits).
9. [done] Formalized Claim 9 into phase-split propositions with explicit assumptions (Coulomb/confining/screened).
10. [done] Deepened Claim 1 with finite-dimensional discrete-action \(\delta(\nabla S_N)\) lemmas for QM/lattice-QFT truncations.
11. [done] Built a finite-dimensional manifold half-density convolution statement (pre-infinite-dimensional bridge).
12. [done] Integrated multi-fixed-point point-supported distribution scaling channels into the Claim 1 bridge roadmap.
13. [done] Built a controlled cylinder-limit program (QM then lattice-QFT toy) with explicit convergence assumptions and failure modes.
14. [done] Tightened pair/tangent-groupoid half-density statements into theorem/proof format with explicit hypotheses and composition laws.
15. [done] Closed Claim 3/4 global time-domain classifications and extended Claim 8 beyond static Tangherlini via asymptotic theorem.
16. [done] Specialized Claim 9 into model-class propositions (pure YM, YM+fundamental matter, Abelian Higgs) with explicit assumptions.
17. [done] Produced synthesis note with dependency graph and long-horizon conjecture list (Phase F).
18. [done] Added Claim 1 continuum skeleton with explicit spaces/topologies/counterterm flow and convergence template.
19. [done] Proved Gaussian-model closure of Claim 1 continuum hypotheses H1-H6 with explicit counterterm-repair construction.
20. [next] Extend Claim 1 closure from Gaussian core to polynomial perturbations with explicit small-coupling bounds.
