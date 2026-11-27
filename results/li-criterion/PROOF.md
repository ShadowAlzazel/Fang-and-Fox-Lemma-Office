# Li's criterion, the flower on the circle

## Statement

Let \(\rho\) run over the nontrivial zeros of \(\zeta\), counted with multiplicity. Li's coefficients are

\[
\lambda_n = \sum_{\rho}\Bigl[1 - \Bigl(1 - \frac{1}{\rho}\Bigr)^{n}\Bigr], \qquad n \ge 1,
\]

summed in conjugate pairs so that the series converges. Li's criterion (Li 1997, in the form of Bombieri and Lagarias 1999): RH holds if and only if \(\lambda_n \ge 0\) for every \(n \ge 1\). The first one is \(\lambda_1 = 1 + \tfrac{\gamma}{2} - \tfrac{1}{2}\log 4\pi \approx 0.0230957\).

In the Lean file the sum is taken over zeros with \(\operatorname{Im}\rho > 0\), each doubled by \(2\operatorname{Re}\), which is the same thing once zeros are paired with their conjugates.

What is proved: \(\mathrm{RH} \iff \lambda_n \ge 0\) for the multiplicity-weighted sum `liCoeff`, assuming only the multiplicity-weighted Hadamard summability \(\sum m(\rho)/|\rho|^2 < \infty\). That is the theorem `li_criterion_weighted'`. No real zeros of \(\zeta\) in \((0,1)\) is a theorem (`noRealZerosInStrip_holds`), not a hypothesis.

## Status

Partial; both directions in Lean assuming only Hadamard summability \(\sum m(\rho)/|\rho|^2\); not a Left to Solve credit.

## Lean

- [`LiCriterion.lean`](LiCriterion.lean) — the complete development: Part III (no real zeros) concatenated with both directions of the weighted criterion, compiled against formal-conjectures at 9097e2f on Lean and Mathlib v4.33.1.
- [`NoRealZeros.lean`](NoRealZeros.lean) — standalone Part III.
- [`LiConditional.lean`](LiConditional.lean) — the earlier Part I file, kept for the record; every Part I lemma still appears, under the same name, in `LiCriterion.lean`.

Main theorems:

- `LiConditional.li_criterion_weighted'` — \(\mathrm{RH} \iff \lambda_n \ge 0\), assuming only `HadamardHypothesis`
- `LiConditional.noRealZerosInStrip_holds` — no real zeros of \(\zeta\) in \((0,1)\)
- `LiConditional.li_converse_of_hadamard`, `LiConditional.li_converse_unweighted_of_hadamard`
- `LiConditional.liCoeff_pos` (strict inequality, also assumes infinitely many zeros)
- `NoRealZeros.riemannZeta_ne_zero_of_mem_Ioo`, `NoRealZeros.riemannZeta_re_lt_of_mem_Ioo`

## Axioms

`propext`, `Classical.choice`, `Quot.sound`

## Reviewed by

Alo, independent rebuild of `NoRealZeros.lean` and `LiCriterion.lean`. Alo also checked that the zeros are Mathlib's `riemannZeta` and that nothing shadows `RiemannHypothesis`.

## Caveats

- (a) The equivalence \(\mathrm{RH} \iff \lambda_n \ge 0\) is proved given one named hypothesis, Hadamard summability, not unconditionally. That hypothesis is a classical, unconditional theorem, stated as an assumption because Mathlib does not have it. It is not RH or Li in disguise.
- (b) The deep half of Li — \(\lambda_n\) as Taylor coefficients of \(\log\xi\) at \(s=1\), computable without the zeros — is not formalized. What is proved is an equivalence between RH and the nonnegativity of a sum written directly over the zeros.
- (c) This is not a credit solve of upstream `li_criterion` (strict inequality \(\lambda_n > 0\), both directions, no hypotheses).
- (d) The `log_deriv_expansion` field of `HadamardHypothesis` is stated but unused. Both directions use only the multiplicity-weighted summability field `summable_inv_sq`.
- `liCoeff_nonneg` alone is nearly empty, because Lean's `tsum` returns \(0\) when a family is not summable. Read it only together with `liCoeff_summable`.
- The sum runs over \(\operatorname{Im}\rho > 0\), doubled, so a real zero in \((0,1)\) would be missed by the setup; Part III proves there are none.
- `liCoeff` counts multiplicity; upstream `lambda` counts each zero once. They agree only if all zeros are simple, which is not known. No identification between them is proved, though `li_converse_unweighted_of_hadamard` gives the converse for the unweighted sum on its own terms, still assuming only Hadamard summability.
- `hinf : nontrivialPosZeros.Infinite` is classical and not in Mathlib; it is used only for the strict inequality in `liCoeff_pos`, not for the equivalence with \(\ge 0\).
- The figure is an illustration. It proves nothing, and the dashed off-line quartet is schematic. mpmath places the zeros on the line by construction.

## The picture

Send \(\rho\) to \(w = 1 - \frac{1}{\rho} = \frac{\rho-1}{\rho}\). Then \(|w| = 1\) exactly when \(|\rho-1| = |\rho|\), that is, when \(\operatorname{Re}\rho = \tfrac12\). The Möbius map sends the critical line to the unit circle. The two symmetries of the zeros (\(\rho \mapsto \bar\rho\) and \(\rho \mapsto 1-\rho\)) become \(w \mapsto \bar w\) and \(w \mapsto 1/w\). So a zero off the line would arrive as a quartet \(w,\ \bar w,\ 1/w,\ 1/\bar w\), two points inside the circle and two outside.

For \(|w| = 1\) and \(u = w^n\), also on the circle, \(2\operatorname{Re}(1-u) = |1-u|^2 \ge 0\). So under RH every term of \(\lambda_n\) is a square, and the sum cannot be negative. If a zero is off the line, \(|w| \ne 1\), and a Kronecker return sends the dominant powers near the positive axis, that term grows like \(-R^n\) and drives some coefficient negative. That is the converse, formalized as Part II, now conditional only on the multiplicity-weighted Hadamard summability.

## Proof, Part I · the easy direction

Each step is a lemma in `LiCriterion.lean` (and in the earlier Part I file `LiConditional.lean`), in the order below.

### 1. The critical line goes to the circle

(`norm_sub_one_eq_of_re_half`, `norm_one_sub_inv_eq_one`.) If \(\operatorname{Re}\rho = \tfrac12\) then \(|\rho-1| = |\rho|\), hence \(|1-1/\rho| = 1\). Unconditional.

### 2. Terms on the circle are squares

(`re_one_sub_pow_nonneg`, `re_one_sub_pow_pos`, `re_one_sub_pow_le`.) For \(|w| = 1\): \(\operatorname{Re}(1-w^n) = |1-w^n|^2/2 \ge 0\), and it is strictly positive when \(w^n \ne 1\). A geometric sum gives \(|1-w^n| \le n|1-w|\), so \(\operatorname{Re}(1-w^n) \le n^2|1-w|^2/2\). With \(w = 1-1/\rho\) this is \(\le n^2/(2|\rho|^2)\), which is what makes the series converge. Unconditional.

### 3. The completed zeta function and multiplicities

(`xi_eq`, `zetaMult_pos`.) \(\xi(s) = \tfrac12(1 + s(s-1)\Lambda_0(s))\) is built from Mathlib's entire \(\Lambda_0\), and `xi_eq` checks it equals \(\tfrac12 s(s-1)\Lambda(s)\) away from \(0,1\). `zetaMult_pos` says every nontrivial zero with \(\operatorname{Im}\rho > 0\) has multiplicity at least 1: \(\zeta\) is analytic off \(s=1\), not identically zero (it is nonzero at \(2+i\)), and the identity theorem on the convex quadrant \(\{\operatorname{Re}>0,\operatorname{Im}>0\}\) rules out an infinite-order zero. Unconditional.

### 4. RH puts every zero on the line

(`re_eq_half_of_RH`.) Mathlib's `RiemannHypothesis` excludes trivial zeros and \(s=1\); we check a nontrivial zero is neither.

### 5. RH gives \(\lambda_n \ge 0\), and, with the hypotheses, convergence and \(\lambda_n > 0\)

(`liCoeff_nonneg`, `liCoeff_summable`, `liCoeff_pos`.) `liCoeff_nonneg`: under RH every term is \(\ge 0\), so \(\lambda_n \ge 0\). `liCoeff_summable`: under RH and `HadamardHypothesis`, comparison with \(n^2\sum m(\rho)/|\rho|^2\) shows the series converges absolutely. `liCoeff_pos`: add `hinf`, infinitely many zeros. Only finitely many points of the circle satisfy \(w^n = 1\), and \(\rho \mapsto w(\rho)\) is injective, so some zero has \(w^n \ne 1\), and its term is strictly positive. A convergent sum of nonnegative terms with one positive term is positive.

### The named assumption `HadamardHypothesis`

Mathlib does not yet have the Hadamard factorization of \(\xi\). We state its consequences as a structure with two fields: (1) the multiplicity-weighted summability \(\sum_\rho m(\rho)/|\rho|^2 < \infty\), and (2) \(\xi'/\xi(s) = B + \sum_\rho m(\rho)\bigl(\tfrac{1}{s-\rho} + \tfrac{1}{\rho}\bigr)\) for a constant \(B\). This is the classical factorization of an entire function of order 1, proved unconditionally by Hadamard in 1893. It does not mention RH, and nothing in it is Li's criterion in disguise. A coarse numerical sanity check (`check_xi.py`, mpmath): the constant \(B\) computed from \(\xi'/\xi\) near \(s=1\) came out as \(-0.0230957089661\), equal to \(-\lambda_1 = -(1+\tfrac{\gamma}{2}-\tfrac12\log 4\pi)\) to about 10 digits or better. The zero sum itself, truncated at 300 conjugate pairs, gave \(0.1048\) at \(s=3\) against the true \(0.1144\). That gap is the slowly decaying tail, about \(0.012\) by a density estimate, so this part of the check is only consistent with the expansion, not a precise confirmation. Both directions use only field (1). Field (2) is stated for the bridge to the Taylor coefficients of \(\log\xi\), which is not proved here, and is unused.

### The named assumption `hinf`

`nontrivialPosZeros.Infinite` is a classical fact (for instance from the zero-counting formula \(N(T) \sim \frac{T}{2\pi}\log\frac{T}{2\pi e}\)) that Mathlib does not have, so `liCoeff_pos` takes it as a hypothesis. It is needed only for the strict inequality \(\lambda_n > 0\), not for the equivalence with \(\ge 0\).

## Proof, Part II · the converse

Now suppose some zero is off the line, and assume only the multiplicity-weighted Hadamard summability. We show that some Li coefficient is negative. The fact that the off-line zero is not real is the theorem of Part III, not an extra hypothesis.

### 1. An off-line zero can be pushed left

(`exists_posZero_re_lt_half`, `zeta_one_sub_conj_eq_zero`.) If RH fails, some zero sits in the strip: the functional equation kills zeros with \(\operatorname{Re}s \le 0\) except the trivial ones (`re_pos_of_zeta_eq_zero`), and \(\zeta\) has no zeros with \(\operatorname{Re}s \ge 1\). By the theorem `noRealZerosInStrip_holds` (Part III) it is not real. Conjugation (`riemannZeta_conj`) puts it in the upper half-plane, and the proved symmetry \(\rho \mapsto 1-\bar\rho\) — functional equation plus conjugation — then yields a zero with \(\operatorname{Im}\rho > 0\) and \(\operatorname{Re}\rho < \tfrac12\).

### 2. Left of the line means outside the circle

(`one_lt_norm_one_sub_inv`.) \(\operatorname{Re}\rho < \tfrac12\) if and only if \(|\rho-1| > |\rho|\), if and only if \(|w(\rho)| > 1\). So that zero lands strictly outside the unit circle.

### 3. Only finitely many zeros can sit near the largest radius

(`exists_neg_of_large`.) Write \(u = 1-w = 1/\rho\). The multiplicity-weighted Hadamard summability \(\sum m(\rho)/|\rho|^2 < \infty\) is \(\sum m_i |u_i|^2 < \infty\). With weights \(m_i \ge 1\), this forces \(|u_i| \to 0\), so only finitely many \(w_i\) satisfy \(|w_i| \ge r\) for any \(r > 1\). The maximal modulus \(R = \max |w_i| > 1\) is therefore attained on a finite set \(S\), and every other point satisfies \(|w_i| \le r < R\).

### 4. The tail is under second-order control

(`norm_one_sub_pow_sub_le`, `abs_re_one_sub_pow_le`.) For \(|w| \le M\) and \(M \ge 1\), a Taylor remainder gives \(|1 - w^n - nu| \le n^2 M^n |u|^2\). In the strip one also has \(|\operatorname{Re}u| \le |u|^2\), so \(|\operatorname{Re}(1-w^n)| \le (n + n^2 M^n)|u|^2\). The non-dominant zeros therefore contribute at most \((n + n^2 r^n)\sum m_i |u_i|^2\), and the Li series converges absolutely for every \(n\), with no appeal to RH.

### 5. A Kronecker return sends the dominant powers near the positive axis

(`exists_pow_near_one`.) The finitely many points \(z_i = w_i/R\) on the unit circle, \(i \in S\), return simultaneously: for any \(N\), some \(d \ge N\) has every \(z_i^d\) within \(1/2\) of \(1\) (compactness of the torus, plus the pigeonhole principle along \(k \mapsto (z_i^{Nk})\)). Then \(\operatorname{Re} w_i^d \ge R^d/2\) on \(S\), and the dominant contribution is about \(\bigl(\sum_{i\in S} m_i\bigr)(1 - R^d/2)\).

### 6. \(R^d\) beats the tail, so some coefficient is negative

(`li_converse`, `li_criterion_weighted`.) Putting the pieces together,

\[
\frac{\lambda_d}{2} \le \Bigl(\sum_{i\in S} m_i\Bigr)\Bigl(1 - \frac{R^d}{2}\Bigr) + (d + d^2 r^d)\sum_i m_i |u_i|^2.
\]

Because \(r < R\), the geometric \(R^d\) beats the \(d^2 r^d\) tail for large \(d\), and \(\lambda_d < 0\). This contradicts the assumption that every coefficient is nonnegative. Hence RH holds. Together with Part I, and with Part III discharging the real-zero hypothesis, that is the equivalence `li_criterion_weighted'`, whose only remaining assumption is Hadamard summability.

### Bonus: the same converse for upstream's unweighted \(\lambda\)

(`li_converse_unweighted`.) Run the same engine with every weight equal to \(1\). Summability of \(\sum 1/|\rho|^2\) follows from the multiplicity-weighted bound \(\sum m(\rho)/|\rho|^2 < \infty\), because \(m(\rho) \ge 1\). So the “\(\Leftarrow\)” half of the upstream statement, about formal-conjectures' unweighted `lambda`, also holds conditionally on Hadamard summability alone (`li_converse_unweighted_of_hadamard`). The “\(\Rightarrow\)” half for that unweighted sum, and the strict inequality, are not proved.

### A synthesis

Given only the multiplicity-weighted Hadamard summability \(\sum m(\rho)/|\rho|^2 < \infty\), nonnegativity of the zero-sum \(\lambda_n\) is equivalent to RH. That is `li_criterion_weighted'`. The engine behind the converse, `exists_neg_of_large`, is more general still: it applies to any weighted point set whose weights \(a_i \ge 1\) make \(\sum a_i |1-w_i|^2\) summable, once at least one point lies outside the unit circle. The zeta-specific work is only to produce such a point from a failure of RH, and to know — now as a theorem — that the point is not real.

## Proof, Part III · no real zeros in \((0,1)\)

The converse used to take “no real zeros of \(\zeta\) in \((0,1)\)” as a named hypothesis. It is now a theorem. The route is a comparison of the sum with the integral, not the Dirichlet eta function. The standalone file is `NoRealZeros.lean`; the same lemmas are included in `LiCriterion.lean`.

For \(n \ge 1\), write

\[
c_m(s) = (1-s)(n+1)^{-s} - \bigl((n+1)^{1-s} - n^{1-s}\bigr), \qquad n = m+1.
\]

Equivalently, \(c_m(s) = (1-s)\int_n^{n+1}\bigl((n+1)^{-s} - x^{-s}\bigr)\,dx\). The definition in Lean is `corr`.

### 1. A mean-value bound makes \(\sum c_m\) holomorphic on \(\operatorname{Re}s > 0\)

(`norm_corr_le`, `summable_corr`.) By the mean-value inequality, twice (`norm_cpow_sub_cpow_le`), \(|c_m(s)| \le |1-s|\,|s|\,n^{-\operatorname{Re}s-1}\). So \(\sum c_m(s)\) converges locally uniformly on \(\operatorname{Re}s > 0\), and the sum is holomorphic there.

### 2. For \(\operatorname{Re}s > 1\) the identity is elementary

(`tsum_corr_of_one_lt_re`, `hasSum_telescope`.) Here \(\sum(n+1)^{-s} = \zeta(s)-1\), and \(\sum\bigl((n+1)^{1-s} - n^{1-s}\bigr) = -1\) telescopes, so

\[
(s-1)\zeta(s) = s - \sum_m c_m(s).
\]

### 3. The identity theorem extends it to \(\operatorname{Re}s > 0\)

(`riemannZeta₁_eq_sub_tsum_corr`.) Both sides are holomorphic on a convex open set containing \(s\) and \(s+2\) — the left-hand side is Mathlib’s entire function `riemannZeta₁ = (s-1)ζ(s)` — and they agree near \(s+2\). By the identity theorem they agree for every \(\operatorname{Re}s > 0\).

### 4. Bernoulli’s inequality makes each \(c_m(\sigma) < 0\)

(`realCorr_neg`, `riemannZeta_re_lt_of_mem_Ioo`, `riemannZeta_ne_zero_of_mem_Ioo`.) For real \(0 < \sigma < 1\), \(x \mapsto x^{1-\sigma}\) is strictly concave, so its increment over \([n,n+1]\) exceeds its slope at the right end: \((n+1)^{1-\sigma} - n^{1-\sigma} > (1-\sigma)(n+1)^{-\sigma}\). That is Bernoulli’s inequality \((1+x)^p < 1+px\), and it says \(c_m(\sigma) < 0\). Hence \((\sigma-1)\zeta(\sigma) = \sigma - \sum c_m(\sigma) > \sigma\), and dividing by \(\sigma-1 < 0\) yields

\[
\zeta(\sigma) < \frac{\sigma}{\sigma-1} < 0.
\]

In particular \(\zeta(\sigma) \ne 0\). This is `noRealZerosInStrip_holds`, and it is what discharges the last hypothesis besides Hadamard summability.

Written from the problem page and `notes.md`. Drafted and compiled by Kumi-San; independently rebuilt by Alo. ShadowAlzazel steers the ideas.
