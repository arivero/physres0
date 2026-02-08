# Claim 1 Phase O: Non-Vanishing Lower Bounds for Oscillatory Partition Factors

Date: 2026-02-09  
Depends on: `research/workspace/notes/theorems/2026-02-09-claim1-largeN-coupled-gaussian-tail.md`

## Goal

Provide explicit sufficient conditions ensuring non-vanishing of finite-dimensional normalized oscillatory partition factors used in continuity constants.

## Setup

Let \(S:\mathbb R^d\to\mathbb R\) be measurable with
\[
A_\eta:=\int_{\mathbb R^d} e^{-\eta S(x)}\,dx\in(0,\infty),\qquad \eta>0.
\]
Define probability measure
\[
\mu_\eta(dx):=\frac{e^{-\eta S(x)}}{A_\eta}\,dx.
\]
Oscillatory partition factor:
\[
Z_{\varepsilon,\eta}
:=
\int_{\mathbb R^d}e^{-(\eta-i/\varepsilon)S(x)}\,dx
=
A_\eta\,\mathbb E_{\mu_\eta}\!\left[e^{iS/\varepsilon}\right].
\]

## Theorem 1 (First-Moment Non-Vanishing Criterion)

Define \(M_1:=\mathbb E_{\mu_\eta}|S|\). Then
\[
|Z_{\varepsilon,\eta}|
\ge
A_\eta\left(1-\frac{M_1}{\varepsilon}\right).
\]
In particular, if \(\varepsilon>M_1\), then \(Z_{\varepsilon,\eta}\neq0\) and
\[
|Z_{\varepsilon,\eta}|
\ge
A_\eta\left(1-\frac{M_1}{\varepsilon}\right)>0.
\]

### Proof

Let \(X:=S/\varepsilon\) under \(\mu_\eta\). Then
\[
\left|\mathbb E[e^{iX}]\right|
=
\left|1+\mathbb E[e^{iX}-1]\right|
\ge
1-\mathbb E|e^{iX}-1|.
\]
Use \(|e^{it}-1|\le |t|\):
\[
\mathbb E|e^{iX}-1|
\le
\mathbb E|X|
=
\frac{M_1}{\varepsilon}.
\]
Multiply by \(A_\eta\). \(\square\)

## Theorem 2 (Second-Moment Real-Part Criterion)

Define \(M_2:=\mathbb E_{\mu_\eta}[S^2]\). Then
\[
\Re\!\left(\frac{Z_{\varepsilon,\eta}}{A_\eta}\right)
=
\mathbb E_{\mu_\eta}\!\left[\cos\!\left(\frac{S}{\varepsilon}\right)\right]
\ge
1-\frac{M_2}{2\varepsilon^2}.
\]
Hence if \(\varepsilon^2 > M_2/2\), then \(Z_{\varepsilon,\eta}\neq0\) and
\[
|Z_{\varepsilon,\eta}|
\ge
\Re Z_{\varepsilon,\eta}
\ge
A_\eta\left(1-\frac{M_2}{2\varepsilon^2}\right)>0.
\]

### Proof

Use \(\cos t\ge 1-t^2/2\), take expectation, and multiply by \(A_\eta\). \(\square\)

## Corollary (Uniform Lower Bound on a Compact Model Class)

If a model family satisfies uniform bounds
\[
\sup_{\theta\in\Theta} M_1(\theta)\le \overline M_1<\infty
\quad\text{or}\quad
\sup_{\theta\in\Theta} M_2(\theta)\le \overline M_2<\infty,
\]
then for
\[
\varepsilon>\overline M_1
\quad\text{or}\quad
\varepsilon>\sqrt{\overline M_2/2},
\]
one gets a uniform positive lower bound on \(|Z_{\varepsilon,\eta}|\) across \(\Theta\).

This directly supports continuity constants of the form
\[
C=\frac{\int e^{-\eta S}}{|Z_{\varepsilon,\eta}|}.
\]

## Scope Note

These are sufficient conditions (not necessary).  
They close the non-vanishing requirement in the regime where \(\varepsilon\) dominates phase moments under \(\mu_\eta\).

## Reproducibility

Run:

```bash
python3.12 research/workspace/simulations/claim1_partition_nonvanishing_bound_check.py
```

The script evaluates \(|Z_{\varepsilon,\eta}|\) and both lower bounds on a quartic block and confirms the inequalities.
