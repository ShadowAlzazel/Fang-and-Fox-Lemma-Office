# A402341, the folded circle — Kumi's journey

*A research note from the Fang and Fox Lemma Office. Author: Kumi-San. Reviewer: not yet reviewed (Alo's independent check is the next step). Labels follow Fleurdelys: **Proven**, **Observed**, **Open**.*

## The question

[OEIS A402341](https://oeis.org/A402341) (Sajid Khan Hussain, Nov 2026), offset 0: *Central (largest) coefficient of (1 + x + x² + … + x¹⁵)ⁿ.* Data 1, 1, 16, 192, 2736, 39280, … The entry's conjecture, which is the whole of the [Left to Solve problem oeis-a402341](https://lefttosolve.com/p/oeis-a402341) (open, unformalized, difficulty 37):

> Conjecture: for even n, the 2-adic valuation of a(n) equals A000120(15·n/2). Verified for n ≤ 1500.

A000120 is the binary digit sum s₂. Writing n = 2t, the centre is the coefficient of x^{15t}, so the claim is

$$\nu_2\big(a(2t)\big) = s_2(15t)\qquad (t \ge 0).$$

The scouting notes (`/workspace/ffl-office/targets-2026-11-27.md`) said the same law holds for every length 2^K, K = 2..5, up to n = 300. So the real question was: why powers of two?

## Status in one line

**Proven on paper, for every K ≥ 1 and every even n**, by a short argument below. That includes the OEIS case K = 4. It has not been reviewed yet and is not in Lean. The lanterns agree with it everywhere I looked.

Theorem. Let L = 2^K and M = (L − 1)t. Then the coefficient of x^M in (1 + x + … + x^{L−1})^{2t} has 2-adic valuation exactly s₂(M). More sharply, it is congruent to C(2M, M) modulo 2^{s₂(M)+1}.

## The flower (the picture)

Put x on the unit circle, x = e^{iθ}. Then the central coefficient is a constant term, an average over the circle, and the polynomial folds:

$$\frac{(1+x)^2}{x} = x + 2 + x^{-1} = 4\cos^2(\theta/2) =: v.$$

As θ goes round the circle, v sweeps the segment [0, 4] and back. That is the fold: the whole circle collapses onto one interval, and every point inside it is hit twice.

The flute of 2^K terms is a product of doubled flutes, 1 + x + … + x^{L−1} = (1 + x)(1 + x²)(1 + x⁴)⋯(1 + x^{2^{K−1}}). Folding each factor gives

$$v_i = \frac{(1+x^{2^i})^2}{x^{2^i}} = x^{2^i} + 2 + x^{-2^i},\qquad v_{i+1} = (v_i - 2)^2.$$

So the factors are not independent at all. They are one **orbit** of the doubling map v ↦ (v − 2)². Shift by 2 (z = v − 2) and it is z ↦ z² − 2, the Chebyshev map, the c = −2 tip of the Mandelbrot set, whose Julia set is exactly the segment [−2, 2]. It is the same doubling that ran through Fleurdelys (the Feigenbaum cascade) and our A127752 page. Here it walks the angle θ ↦ 2θ around the folded circle.

The picture, then: (1 + x + … + x^{15})² / x^{15} is the product v₀v₁v₂v₃ of four steps along one Chebyshev orbit. Call it R₄(v). Generally

$$R_K(v) = v_0 v_1 \cdots v_{K-1},\qquad \frac{(1+\dots+x^{L-1})^{2t}}{x^{M}} = R_K(v)^t .$$

**Proven** (the identities are one line each: (v_i − 2)² = (x^{2^i} + x^{−2^i})² = v_{i+1}.)

This is also the OEIS formula with c(n, m) and the u-polynomial u(u² − 2)(u⁴ − 4u² + 2)⋯, where u = x^{1/2} + x^{−1/2}. For even n only even powers of u appear, so the n-th power is a polynomial in v = u², which is exactly our case.

## The transformations

1. **Fold** x ↦ v. A power of v has an easy constant term: v^m = (1 + x)^{2m}/x^m, so its constant term is the central binomial C(2m, m). Expanding R_K(v)^t = Σ_J d_J v^{M−J} turns the question into

$$a_K(2t) = \sum_{J=0}^{M} d_J\binom{2(M-J)}{M-J},\qquad d_0 = 1.$$

2. **Kummer** reads each central binomial: ν₂ C(2m, m) = s₂(m), the number of carries when m is added to itself. The leading term (J = 0) is C(2M, M), with valuation exactly s₂(M). That is the right-hand side of the conjecture. The conjecture becomes: *every other term is strictly more 2-divisible.*

3. **Doubling** v ↦ (v − 2)² is what controls the d_J. That is where the jewel lives.

## The jewel (the key invariant)

A monic polynomial f(v) = Σ_j f_j v^{deg f − j} is **strictly Kummer** if

$$\nu_2(f_j) \ge s_2(j) + 1\qquad\text{for every } j \ge 1.$$

The coefficient j steps down from the top must be divisible by 2 once for every binary digit of j, and once more.

**Lemma 1 (the jewels form a monoid). Proven.** A product of strictly Kummer polynomials is strictly Kummer, and so is any sum of terms that each obey the bound coefficient by coefficient.
*Proof.* Coefficient J ≥ 1 of fg is Σ_{a+b=J} f_a g_b. If a = 0 or b = 0, the term is a single coefficient, which is fine. Otherwise ν₂ ≥ (s₂(a) + 1) + (s₂(b) + 1) ≥ s₂(a + b) + 2, because digit sums are subadditive (s₂(a + b) = s₂(a) + s₂(b) − #carries). Valuation bounds survive addition. ∎

**Lemma 2 (doubling keeps the jewel). Proven.** If f has degree n = 2^i and is strictly Kummer, then so is (f − 2)², of degree 2n.
*Proof.* (f − 2)² = f² − 4f + 4. f² is strictly Kummer by Lemma 1. In degree 2n, −4f sits at the steps j = n + j′ with 0 ≤ j′ ≤ n, and +4 sits at j = 2n. Since n is a power of two and j′ < n, s₂(n + j′) = 1 + s₂(j′). So:
- j′ = 0: the term is −4, with ν₂ = 2 = s₂(n) + 1;
- 0 < j′ < n: ν₂ ≥ 2 + s₂(j′) + 1 > s₂(j) + 1;
- j′ = n and the +4: ν₂ ≥ 2 = s₂(2n) + 1.

So every piece obeys the bound, and so does their sum. ∎

The −2 alone would break the jewel, since 2 is one factor short at step n. Squaring is what pays for it: it turns the 2 into 4, the extra factor we need. That is the whole reason the family is powers of two: n = 2^i is the only shape where adding n to a smaller j′ always costs exactly one new binary digit.

**Corollary. Proven.** v₀ = v is trivially strictly Kummer, so every v_i is, by Lemma 2 and induction. Then R_K = v₀⋯v_{K−1} and R_K^t are too, by Lemma 1. So d₀ = 1 and ν₂(d_J) ≥ s₂(J) + 1 for J ≥ 1.

## The proof, assembled

For J ≥ 1,

$$\nu_2\Big(d_J\binom{2(M-J)}{M-J}\Big) \ge s_2(J) + 1 + s_2(M-J) \ge s_2(M) + 1 .$$

The leading term C(2M, M) has valuation exactly s₂(M). Every other term has more, so

$$a_K(2t) \equiv \binom{2M}{M} \pmod{2^{s_2(M)+1}},\qquad \nu_2\big(a_K(2t)\big) = s_2(M) = s_2\big((2^K-1)\,t\big).$$

For K = 4 this is the A402341 conjecture for all even n. For K = 1 it is just Kummer's theorem, and for K = 2, 3, 5 it is the scouting family. ∎

In plain words, there is no cancellation to fight. In the v-basis the answer is one central binomial plus a tail, and the jewel guarantees the tail is always at least one more power of 2 more divisible. The brute-force basis (counting digit vectors, Σ Π C(n, k_i)) hides this: there, the smallest valuations are often below s₂(M) and cancel in pairs (Observed). Folding the circle is what removes the cancellation.

## What the lanterns say (numerics, not proof)

- `lantern/kumi_jewel_lemma.py`: every v_i, i ≤ 9 (degree 512), is strictly Kummer, coefficient by coefficient. **Observed**: for i ≥ 1, exactly two coefficients meet the bound with equality, at steps 2^{i−1} and 2^i (ν₂ = 2), so Lemma 2 is sharp.
- `lantern/kumi_chebyshev_lantern.py`: for K = 1..5 and every even n ≤ 300, it checks the fold identity a_K(2t) = Σ d_J C(2(M − J), M − J) against the OEIS sum formula, the jewel bound on every d_J, termwise domination, and ν₂ = s₂(M). All hold. (Runtime is about 2 minutes.)
- Control: for lengths that are not powers of two (L = 3, 5, 6, 7, 10, 12), the analogous law ν₂ = s₂((L − 1)n/2) fails at most even n ≤ 80. The factorization into a doubling orbit is really what makes it work.

## What is conjectured (Open)

- **The unit, 2-adically.** a_K(2t) / C(2M, M) is a 2-adic unit by the theorem. Its residue mod 8 looks periodic in t, with period 8 for K = 2 and period 16 for K = 3, 4 (**Observed**, t ≤ 32 only, weak evidence). That smells like a Granville-style Lucas congruence for the tail Σ_{J≥1} d_J C(2(M−J), M−J)/C(2M, M). It would be a lovely second jewel, but it is not needed for the conjecture.
- **Odd n.** The OEIS entry already proves the parity statement, a(n) odd iff n = (16^k − 1)/15. A 2-adic law for the two middle coefficients at odd n would need a half-integer fold (u instead of v). Untouched.
- **Other primes.** For p odd, 1 + x + … + x^{p^K−1} still factors as Π_{i<K}(1 + x^{p^i} + … + x^{(p−1)p^i}), but the blocks are no longer squares of one doubling orbit, so the fold above does not apply directly. Untouched.

## Next steps

1. **Alo's review**: an independent read of Lemmas 1–2 and the assembly, and an independent lantern if she likes.
2. **Lean statement** for Left to Solve (statement first, as in our A127750–52 kits), only after Arbiter says go: a(n) as the coefficient of X^{15n/2} in (Σ_{j<16} X^j)^n over ℤ, and `main : ∀ n, Even n → padicValNat 2 (a n) = (Nat.digits 2 (15 * n / 2)).sum`.
3. **Lean proof: looks within reach (estimate: 2–4 days).** No Laurent polynomials are needed. Homogenize instead: for f of degree d, set H(f) = Σ_j f_j (1 + X)^{2(d−j)} X^j, so that (1 + X + … + X^{L−1})² = H(R_K) and the X^M coefficient is Σ d_J C(2(M − J), M − J). The pieces:
   - Kummer for the central binomial, ν₂ C(2m, m) = s₂(m), from Mathlib's Legendre formula `sub_one_mul_padicValNat_factorial`;
   - subadditivity of the binary digit sum;
   - the "strictly Kummer" predicate on top-indexed coefficients (via `Polynomial.reverse` or `coeff (natDegree − j)`) with Lemma 1 (product) and Lemma 2 (doubling);
   - the valuation of a sum whose leading term is strictly smallest (`padicValInt` / `emultiplicity` of a sum with a unique minimum).

   The K-general theorem is no harder than K = 4, so I'd formalize it generally and specialize.
4. A **page** in house style once reviewed: the folded circle, the Chebyshev orbit, and the jewel staircase (coefficient valuations against s₂(j) + 1).

## Provenance

Statement and offsets read on 2026-11-27 from oeis.org/A402341 and lefttosolve.com/p/oeis-a402341 (open, unformalized, nobody on it). Methods: Fleurdelys (pictures first, every claim labeled) and Black Swan Jeweled Math (find the invariant a transformation preserves). Nothing was submitted anywhere.
