# Subclaims from `arXiv-hep-th9411081v1/9411081.tex` for Claim 1

Date: 2026-02-08  
Source file: `arXiv-hep-th9411081v1/9411081.tex`

## Why this note

Extract scaling/fixed-point statements relevant to clarifying the role of \(\delta(f')\), \(\delta'\), and multiple fixed points in the Claim 1 program.

## Extracted Subclaims (line-anchored)

1. RG action is explicit momentum rescaling:
   \[
   T^t[\tilde S_{\tilde k}] = \tilde S_{e^{-t}\tilde k}.
   \]
   Anchor: `arXiv-hep-th9411081v1/9411081.tex:255`.

2. Fixed points are \(k\)-independent \(S\)-matrices; under stated symmetry constraints they form a nontrivial set (continuous family plus isolated points), not a single point.
   Anchors: `arXiv-hep-th9411081v1/9411081.tex:258`, `arXiv-hep-th9411081v1/9411081.tex:263`, `arXiv-hep-th9411081v1/9411081.tex:269`, `arXiv-hep-th9411081v1/9411081.tex:271`.

3. Linearized scaling directions satisfy
   \[
   \vec a(k)=k^{-n}\vec a_0,\qquad \lambda-1=n\,\delta t,
   \]
   giving relevant/marginal/irrelevant channels by exponent.
   Anchors: `arXiv-hep-th9411081v1/9411081.tex:675`, `arXiv-hep-th9411081v1/9411081.tex:680`, `arXiv-hep-th9411081v1/9411081.tex:688`, `arXiv-hep-th9411081v1/9411081.tex:715`.

4. Around one reference fixed point, multiple independent directions coexist (including marginal channels associated in-text with \(\delta'\)-type families and a relevant channel associated with \(\delta\)-type flow).
   Anchors: `arXiv-hep-th9411081v1/9411081.tex:712`, `arXiv-hep-th9411081v1/9411081.tex:719`, `arXiv-hep-th9411081v1/9411081.tex:720`, `arXiv-hep-th9411081v1/9411081.tex:726`.

5. The text explicitly frames renormalized trajectories as endpointed by fixed points and highlights topology of multiple flows.
   Anchors: `arXiv-hep-th9411081v1/9411081.tex:348`, `arXiv-hep-th9411081v1/9411081.tex:1123`, `arXiv-hep-th9411081v1/9411081.tex:1132`.

## Implications for Claim 1 Wording

1. Keep \(\delta(f')\) and distribution derivative \(\delta'\) distinct at notation level, but do not present them as unrelated objects.
2. Explicitly acknowledge a multi-channel point-supported distribution structure (e.g. \(\delta,\delta',\delta'',\dots\)) under scaling.
3. Treat the ``halved expression'' as potentially selecting a channel/fixed-mode sector depending on regularization and scaling prescription.
4. In the static -> QM -> QFT ladder, preserve the possibility of multiple fixed structures rather than a single universal one.

## Immediate Integration Done

These clarifications were integrated into:

- `research/workspace/notes/theorems/2026-02-08-claim1-scoped-bridge-statement.md`
- `research/workspace/reports/2026-02-08-claim1-variational-delta-note.tex`
