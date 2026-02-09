# AGENTS.md

Last updated: 2026-02-09 (US date)

## Mission

This repository is configured for AI assisted research in:
- quantum theory (QM, QI, many body and open systems),
- quantum gravity (canonical, holographic, and string motivated formal work),
- elementary particle theory and phenomenology (SM, EFT, collider facing workflows).

The goal is not just fluent text generation. The goal is verifiable reasoning:
- formal proof when possible,
- symbolic checks when formal proof is not yet feasible,
- numerical checks with reproducible scripts and seeds.

## Operating Style

This setup is intentionally free wheeling in exploration style, but strict in validation:
- use broad hypothesis generation and fast iteration,
- keep conceptual and executable artifacts clearly separated,
- require dimensional, numerical, and known result checks before accepting claims,
- prioritize centaur workflows (human + tool assisted agent loops).

## External Reality Check (Recent, Date Anchored)

The stack is tuned to the 2025 to early 2026 landscape:

1. AlphaProof was published in Nature on 2025-11-12, showing RL based olympiad level formal proving in Lean.
2. Google DeepMind reported IMO 2025 gold level performance (35/42) on 2025-07-21 with an advanced Gemini Deep Think setup.
3. The AI for Math Initiative was announced on 2025-10-29 with institutional partners (Imperial, IAS, IHES, Simons Institute, TIFR).
4. AlphaEvolve (2025-05-14) reported verifiable algorithmic improvements, including 48 scalar multiplications for 4x4 complex matrix multiplication and gains on open math problems.
5. AxiomMath published full Putnam 2025 Lean solutions (12/12) with verification workflow.
6. Numina-Lean-Agent (arXiv:2601.14027, 2026) reports 12/12 Putnam 2025 and a paper level Brascamp-Lieb formalization.
7. Goedel-Prover-V2 reports up to 90.4 percent MiniF2F in self correction mode.
8. DeepSeek-Prover-V2 reports 88.9 percent MiniF2F and 49 PutnamBench solves.
9. PhysProver (arXiv:2601.15737, 2026-01-22) targets formal physics proving with RLVR and reports cross domain gains.
10. CERN colloquium "Centaur Science: Adventures in AI+Physics" took place on 2026-02-04, reinforcing the human + AI collaboration framing in particle physics.

Source links are tracked in `research/recent-developments-2026-02-08.md`.

## Agent Roles

Use a multi agent decomposition with explicit handoffs:

1. `scout`: paper and benchmark retrieval, source quality filtering, timeline extraction.
2. `formalizer`: Lean/PhysLean theorem formalization and proof search.
3. `symbolic`: CAS derivations (SymPy and Cadabra style workflows).
4. `numeric`: simulation and limiting case tests (SciPy/JAX/QuTiP).
5. `critic`: independent verification, unit checks, symmetries, and counterexample search.
6. `scribe`: concise result package with assumptions, confidence, and reproducibility data.

## Mandatory Validation Contract

Every technical output must include:

1. assumptions section (model, regime, approximations),
2. units and dimensions check,
3. symmetry and conservation law checks (when relevant),
4. at least one independent cross check path:
   - formal proof, or
   - symbolic re derivation, or
   - numerical sanity and limiting case tests,
5. uncertainty or confidence statement,
6. full reproducibility metadata (tool versions, seed, command log).

If any check fails, the claim is marked "unverified" and not promoted as a result.

## Domain Checklists

### Quantum Theory

- operator domains and hermiticity/self adjointness assumptions are explicit,
- commutator algebra and unitary evolution checks are explicit,
- perturbative results include control parameter and truncation error discussion.

### Quantum Gravity

- distinguish kinematical from dynamical statements,
- constraint closure and gauge fixing assumptions are explicit,
- semiclassical limits recover known GR/QFT results where expected.

### Elementary Particles

- representation and symmetry content stated upfront,
- renormalization scheme and scale documented,
- amplitude/cross section results cross checked in soft, collinear, or threshold limits.

## Environment

Primary setup and folders are in `research/README.md`.
Package baseline is in `research/requirements.txt`.
Reading program and project ideas are in `research/books-and-ideas.md`.

## Mandatory Hidden Notes Preload

These notes are easy to miss and must be loaded before nontrivial work.

At session start (or after a context reset), read in this order:

1. `research/workspace/notes/2026-02-09-core-goal-compass.md`
2. `research/workspace/notes/2026-02-09-foundational-glossary.md`
3. `research/workspace/notes/audits/2026-02-08-top10-claim-audit.md`
4. `research/workspace/notes/README.md`

Minimum extraction requirement:

1. current `next` item in the audit plan,
2. current Claim 1 status/score and open gap,
3. glossary definitions for `c-invariant`, `tau_mu`, and `de-regularization`.

If any of these files are not read, mark output as incomplete and do not start new theorem work.
