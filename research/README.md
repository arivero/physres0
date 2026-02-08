# Research Environment

Last updated: 2026-02-08

## What This Environment Is For

This setup is designed for verifiable AI assisted work in:
- quantum theory,
- quantum gravity,
- elementary particle theory/phenomenology.

It combines:
- formal proving (Lean/PhysLean),
- symbolic math (SymPy + optional Cadabra workflows),
- numerical checks (SciPy/JAX/QuTiP),
- HEP data interfaces (optional Scikit-HEP stack).

## Directory Layout

```
research/
  books-and-ideas.md
  recent-developments-2026-02-08.md
  requirements.txt
  workspace/
    notes/
    proofs/
    symbolic/
    simulations/
    reports/
```

## 1) Python Base Setup

```bash
python3 -m venv .venv
source .venv/bin/activate
python -m pip install --upgrade pip
pip install -r research/requirements.txt
```

## 2) Lean 4 + Mathlib + PhysLean Setup

Install elan (Lean toolchain manager):

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
source "$HOME/.elan/env"
```

Create a local Lean project (example):

```bash
mkdir -p research/workspace/proofs/lean-playground
cd research/workspace/proofs/lean-playground
lake init lean_playground
lake update
```

Clone PhysLean (optional but recommended):

```bash
cd research/workspace/proofs
git clone https://github.com/HEPLean/PhysLean.git
```

## 3) Working Rules

For each task:

1. Write assumptions and target statement in `research/workspace/notes/`.
2. Produce one executable artifact:
   - Lean file in `research/workspace/proofs/`, or
   - symbolic notebook/script in `research/workspace/symbolic/`, or
   - simulation script in `research/workspace/simulations/`.
3. Record validation and failure analysis in `research/workspace/reports/`.

## 4) Optional Extensions

Use these only when needed:
- Cadabra2 for tensor and field theory symbolic work.
- Scikit-HEP stack (`uproot`, `awkward`, `vector`, `pyhf`) for collider workflows.
- JAX for differentiable and accelerated numerical experiments.

## 5) Suggested Session Template

Before solving a problem, capture:

```text
Question:
Regime:
Assumptions:
Expected invariants/symmetries:
Primary method (formal/symbolic/numeric):
Independent cross-check:
Acceptance criteria:
```
