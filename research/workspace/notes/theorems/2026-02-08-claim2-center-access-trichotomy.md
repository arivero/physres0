# Claim 2 Formalization: SR Center-Access Trichotomy

Date: 2026-02-08  
Source anchors in canonical transcript: `conv_patched.md:371`, `conv_patched.md:384`, `conv_patched.md:388`, `conv_patched.md:415`

## Goal

Upgrade the Claim 2 scaling argument into a theorem-style statement with explicit assumptions and proof skeleton.

## Model and Assumptions

We work in the special-relativistic central-force model with:

- rest mass \(m>0\),
- speed of light \(c>0\),
- attractive power-law force magnitude \(F(r)=K/r^n\) with \(K>0\),
- exponent \(n>1\) and \(n\neq 1\),
- scalar potential
  \[
  V(r)=-\frac{K}{n-1}r^{1-n},
  \]
- fixed conserved energy \(E\in\mathbb{R}\) (finite),
- fixed conserved angular momentum \(L\in\mathbb{R}\) (finite).

Define radial momentum square:
\[
p_r^2(r)
=
\frac{(E-V(r))^2-m^2c^4}{c^2}
-\frac{L^2}{r^2}.
\]

Allowed radii satisfy \(p_r^2(r)\ge 0\).

## Definitions

1. `Center-excluded` for given \((E,L)\): there exists \(r_0>0\) such that
   \(p_r^2(r)<0\) for all \(0<r<r_0\).
2. `Center-allowed` for given \((E,L)\): there exists \(r_0>0\) such that
   \(p_r^2(r)\ge 0\) for all \(0<r<r_0\).

## Lemma 1 (Potential Asymptotic)

Let
\[
a:=\frac{K}{n-1}>0,\qquad V(r)=-a\,r^{1-n}.
\]
As \(r\to 0^+\),
\[
\frac{(E-V)^2-m^2c^4}{c^2}

=
\frac{a^2}{c^2}r^{2-2n}
+\frac{2aE}{c^2}r^{1-n}
+O(1).
\]

### Proof sketch

Expand \((E+a r^{1-n})^2\), collect terms, and divide by \(c^2\).

## Lemma 2 (Dominant Exponent Comparison)

In \(p_r^2\), the two singular candidates are:

- \(+\frac{a^2}{c^2}r^{2-2n}\),
- \(-\frac{L^2}{r^2}\).

Their exponents are \(2-2n\) and \(-2\), respectively.

- If \(n<2\): \(2-2n>-2\), so \(-L^2/r^2\) is more singular.
- If \(n=2\): same exponent \(-2\), coefficients compete.
- If \(n>2\): \(2-2n<-2\), so \(+a^2 r^{2-2n}/c^2\) is more singular.

## Theorem (Center-Access Trichotomy)

Under the assumptions above:

1. If \(1<n<2\):
   - for \(L\neq 0\), trajectories are center-excluded;
   - for \(L=0\), center is kinematically allowed.

2. If \(n=2\):
   - the leading sign near \(r=0\) is controlled by
     \[
     \frac{K^2}{c^2}-L^2.
     \]
   - hence \(L>K/c\) implies center-excluded;
   - \(L<K/c\) implies center-allowed;
   - \(L=K/c\) is a critical/marginal case requiring next-order terms.

3. If \(n>2\):
   - for any finite \(L\), center is kinematically allowed
     (\(p_r^2(r)\to +\infty\) as \(r\to 0^+\)).

### Proof sketch

Use Lemma 1 and Lemma 2:

- \(1<n<2\): \(-L^2/r^2\) dominates when \(L\neq 0\), forcing negativity.
  If \(L=0\), leading term is \(+(a^2/c^2)r^{2-2n}>0\).
- \(n=2\): combine equal-order coefficients:
  \[
  p_r^2(r)=\left(\frac{K^2}{c^2}-L^2\right)\frac1{r^2}+O(r^{-1}).
  \]
- \(n>2\): positive \(r^{2-2n}\) term dominates all others.

## Proposition (Explicit Critical Branch for \(n=2,\;L=K/c\))

Assume \(n=2\), \(K>0\), and \(L=K/c\). Then
\[
V(r)=-\frac{K}{r},
\]
and
\[
p_r^2(r)=\frac{(E+K/r)^2-m^2c^4}{c^2}-\frac{L^2}{r^2}
=\frac{2EK}{c^2}\frac1r+\frac{E^2-m^2c^4}{c^2}.
\]

Therefore, as \(r\to 0^+\):

1. If \(E>0\), then \(p_r^2(r)\to +\infty\), so the center is kinematically allowed.
2. If \(E<0\), then \(p_r^2(r)\to -\infty\), so the center is excluded.
3. If \(E=0\), then
   \[
   p_r^2(r)\equiv -m^2c^2<0,
   \]
   so no radius is allowed in this branch.

### Proof sketch

At \(L=K/c\), the \(r^{-2}\) coefficient is exactly zero:
\[
\frac{K^2}{c^2}-L^2=0.
\]
The next singular term is \((2EK/c^2)r^{-1}\), whose sign is the sign of \(E\). If \(E=0\), only the constant term remains and is strictly negative.

## Corollary (Claim 2 Status Upgrade)

The qualitative statement in `conv_patched.md:388` is mathematically justified as a theorem-level asymptotic classification (with explicit critical handling at \(n=2\)).

## Reproducibility Check (Numerical Sanity, Optional)

Run:

```bash
python3.12 research/workspace/simulations/claim2_trichotomy_scan.py
```

This script does not prove the theorem, but numerically checks sign trends for representative parameter sets, including the \(n=2,\;L=K/c\) critical branch split by energy sign.
