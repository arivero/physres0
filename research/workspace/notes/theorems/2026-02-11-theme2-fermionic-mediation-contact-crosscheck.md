# Theme 2 Deliverable: Fermionic Field Mediation — Contact Interaction Cross-Check

Date: 2026-02-11 (US)
Depends on:
- `research/workspace/notes/2026-02-10-theme-fermionic-mediation-central-potential.md`

## Goal

Fix the model class, prove the selection rule preventing single-fermion-exchange
static potentials between bosonic sources, and verify that analytic low-momentum
amplitudes produce contact (point-supported) interactions in position space.

## I. Model Class and Regime

Consider a Yukawa-coupled theory in 3+1 dimensions:

\[
\mathcal{L} = \bar\psi(i\slashed\partial - m_f)\psi
+ \frac{1}{2}(\partial\phi)^2 - \frac{1}{2}m_b^2\phi^2
+ g\,\phi\,\bar\psi\psi,
\]

where `\phi` is a real scalar (bosonic source proxy) and `\psi` is a Dirac
fermion of mass `m_f`. Static sources are represented by external `\phi`
insertions.

## II. Selection Rule: No Single-Fermion Exchange Between Bosonic Sources

### Proposition

In the static limit, the leading exchange between two bosonic (`\phi`)
sources mediated by `\psi` starts at second order in the fermion propagator
(two-fermion exchange, i.e., a fermion loop).

### Proof

The vertex `g \phi \bar\psi \psi` is bilinear in fermion fields. A single
fermion propagator connects a `\bar\psi` at one vertex to a `\psi` at
another. For this to contribute to `\phi`-`\phi` scattering, we need an
even number of fermion lines forming a closed loop (by Grassmann number
conservation / fermion number conservation). The minimal diagram is a
one-loop box/triangle/bubble with two external `\phi` lines, which
corresponds to integrating out the fermion pair.

At tree level, there is no `\phi\phi` scattering vertex. Single-fermion
exchange would require an external fermion line, which is absent in
`\phi`-`\phi` scattering. Therefore the leading contribution is the
one-loop vacuum polarization (bubble) diagram.

## III. Low-Momentum Expansion and Contact Terms

The one-loop `\phi\phi` amplitude from a fermion bubble is:

\[
\mathcal{M}(\mathbf{q})
= -g^2 \int\frac{d^4k}{(2\pi)^4}
  \frac{\mathrm{tr}[(\slashed{k}+m_f)(\slashed{k}+\slashed{q}+m_f)]}
       {(k^2-m_f^2)((k+q)^2-m_f^2)}.
\]

In the static limit (`q_0 = 0`, `\mathbf{q} \to 0`), the amplitude is
analytic in `\mathbf{q}^2`:

\[
\mathcal{M}(\mathbf{q}) = c_0 + c_2 \mathbf{q}^2 + c_4 \mathbf{q}^4 + \cdots,
\]

with `c_0 = g^2 \Pi(0)` where `\Pi` is the vacuum polarization scalar function.

### Fourier Transform to Position Space

\[
V(\mathbf{r}) \propto \int \frac{d^3q}{(2\pi)^3} e^{i\mathbf{q}\cdot\mathbf{r}}
\mathcal{M}(\mathbf{q}).
\]

Term by term:

- `c_0` → `c_0 \delta^{(3)}(\mathbf{r})` (contact),
- `c_2 \mathbf{q}^2` → `-c_2 \nabla^2 \delta^{(3)}(\mathbf{r})` (derivative contact),
- etc.

All terms are point-supported (contact interactions).

## IV. First Non-Analytic Threshold

The branch cut in `\Pi(q^2)` starts at `q^2 = 4m_f^2` (fermion pair threshold).
This produces the leading long-range tail:

\[
V(r) \sim \frac{g^2}{r^5} e^{-2m_f r}
\quad (r \to \infty),
\]

in 3+1 dimensions (the `1/r^5` prefactor comes from the threshold behavior
of the spectral function for two massive fermions).

## Validation Contract

### Assumptions

1. Perturbative Yukawa coupling (`g^2 \ll 16\pi^2`),
2. static limit (no recoil),
3. one-loop approximation.

### Units and dimensions check

1. `\mathcal{M}` is dimensionless (in natural units),
2. `c_0` has dimensions matching `\delta^{(3)}` integration: `[energy][length]^3`,
3. `V(r)` has units of energy.

### Symmetry/conservation checks

1. fermion number conservation enforces even fermion lines → loop diagram,
2. rotational invariance preserved → central potential,
3. parity invariance of `\phi\bar\psi\psi` vertex preserved.

### Independent cross-check path

Run:

```bash
python3.12 research/workspace/simulations/theme2_fermionic_contact_crosscheck.py
```

The script verifies:
1. analytic `q^2`-expansion coefficients produce delta/derivative-delta terms,
2. the `2m_f` threshold gives the correct asymptotic tail exponent.

### Confidence statement

High confidence on the selection rule and contact-term structure. The `1/r^5`
prefactor of the asymptotic tail is model-dependent; the `e^{-2m_f r}` exponent
is robust.

### Reproducibility metadata

1. Python: `python3.12`,
2. analytic coefficient verification,
3. date anchor: 2026-02-11 (US).
