# A127752, the triangle that doubles

## Statement

[OEIS A127752](https://oeis.org/A127752) (Paul Barry, 2007), offset 0, is: “Row sums of inverse of number triangle \(A(n,k) = 1/(3n+1)\) if \(k \le n \le 2k\), 0 otherwise.” Its data begin \(1, 4, 3, 7, 3, 6, 3, 10, 3, 6, 3, 9, 3, 6, 3, 13, \ldots\), and the entry carries the comments

> a(n) mod 2 is first Feigenbaum symbolic sequence A035263 (conjecture).

> The conjecture is true at least up to 2048 first terms. (But please note the different indexing, here 0-based.) — Antti Karttunen, Sep 29 2018

[A035263](https://oeis.org/A035263) (offset 1) is “Trajectory of 1 under the morphism 0 -> 11, 1 -> 10; parity of 2-adic valuation of 2n: a(n) = A000035(A001511(n)).”

The precise claim proved here is: for all \(n \ge 0\), \(a(n)\) is an integer and

\[
\mathrm{A127752}(n) \equiv \mathrm{A035263}(n+1) = \nu_2\bigl(2(n+1)\bigr) \pmod{2}.
\]

The same statement covers the sibling conjecture [oeis-a127751](https://lefttosolve.com/p/oeis-a127751) about the triangle [A127751](https://oeis.org/A127751) itself.

## Status

Proven for all \(n\), Lean-verified; Left to Solve lists [oeis-a127752](https://lefttosolve.com/p/oeis-a127752) as unformalized, so no credit match yet.

## Lean

- File: [`A127752.lean`](A127752.lean) (Lean 4 + Mathlib v4.33.1, `import Mathlib` only)
- Headline theorem: `A127752.a127752_mod_two`
- Supporting theorems: `a127752_eq_r`, `r_mod_two`
- Steps, in order: `tri_mulVec_r`, `blockSum_r`; the recursion `r` with `r_zero`, `r_odd`, `r_even`; `tri_lower`, `tri_det_isUnit`, `rowSum_inv_tri`, `a127752_eq_r`; `r_mod_two`, `a127752_mod_two`

## Axioms

`propext`, `Classical.choice`, `Quot.sound`

## Reviewed by

Alo, independent rebuild. Alo also checked the definitions against OEIS and checked the doubling step by hand.

## Outside review

An independent referee, who did not take part in the Lean work, recomputed the inverse triangle exactly up to \(N = 200\), checked the written argument and the Lean statement, and found the proof correct and the formalization faithful to the OEIS definition. Their suggestions on presentation (the window table, explicit uniqueness, the induction for parity) are what this version implements.

## Caveats

- (a) A035263 is defined via \(\nu_2\) from its OEIS name (“parity of 2-adic valuation of 2n”), not via the morphism \(0 \to 11\), \(1 \to 10\). The equivalence of the two descriptions is classical but not formalized here; the 34-term guard only checks they agree at the start.
- (b) \(a(n)\) is defined with the \((n+1)\times(n+1)\) truncation of the infinite triangle, using Mathlib's matrix inverse. The lemma `rowSum_inv_tri` shows every larger truncation gives the same row sum, so the choice does not matter. The determinant is proved a unit, so Mathlib's convention that a singular matrix has inverse \(0\) never applies.
- (c) Index shift: A127752 is 0-based and A035263 is 1-based, so the theorem pairs \(\mathrm{A127752}(n)\) with \(\mathrm{A035263}(n+1)\). The OEIS data confirm this is the intended shift.
- (d) Not an upstream credit match: google-deepmind/formal-conjectures (at 9097e2f) has no statement for it yet; this is our own formalization plus a proof. Upstream may choose different conventions (for example a function \(\mathbb{N} \to \mathbb{Z}\)).
- (e) The theorem also covers `oeis-a127751`, whose conjecture is the same statement about the row sums of A127751.
- Evaluation guards (`#guard`, used by no proof): `r` matches all 106 terms of the OEIS data section; `A035263 (n+1)` matches the first 34 OEIS terms of A035263; a computable exact inverse of the \(40\times 40\) triangle satisfies \(A\cdot B = I\) with row sums equal to the OEIS terms. Changing one OEIS digit makes three guards fail.
- Numerics (`check.py`, exact fractions): an inverse for \(N = 250\) has integer row sums equal to `r`; all 2,049 b-file terms match; the conjecture, the form \(1 - (\nu_2(n+1) \bmod 2)\), and the closed form below hold for all \(n < 10^6\).
- The figures are illustrations computed from the recursion. The proof does not depend on them.
- Rechecked against Left to Solve on 2026-11-26: `oeis-a127752` and `oeis-a127751` were still listed as unformalized, unclaimed and unsolved.

## The picture

Invert a sparse triangle of fractions, add up each row, and read the answers mod 2. Out comes the Feigenbaum kneading sequence, the symbolic itinerary of the logistic map at the end of the period-doubling cascade. The whole proof is: stop inverting, and look at what the row sums have to satisfy.

## Proof

Write \(A\) for the lower-triangular matrix with \(A(n,k) = \frac{1}{3n+1}\) when \(k \le n \le 2k\) (equivalently \(\lceil n/2\rceil \le k \le n\)) and \(0\) otherwise, \(B = A^{-1}\), and \(a = B\mathbf{1}\) for the row sums of \(B\). The proof never inverts anything: it only uses the row equations of \(A a = \mathbf{1}\).

### 1. Every window sums to \(3n+1\)

Since \(AB = I\), we get \(Aa = AB\mathbf{1} = \mathbf{1}\). Row \(n\) of \(A\) is the constant \(\frac{1}{3n+1}\) on the window \(\lceil n/2\rceil \le k \le n\) and zero elsewhere, so row \(n\) of \(Aa = \mathbf{1}\) says

\[
S(n) := \sum_{\lceil n/2\rceil \le k \le n} a(k) = 3n+1 \qquad (n \ge 0).
\]

This is `tri_mulVec_r` and `blockSum_r`. The window depends on the parity of \(n\):

| \(n\) | \(\lceil n/2\rceil\) | window | \(S(n)\) |
| --- | --- | --- | --- |
| \(2m\) | \(m\) | \([m,\,2m]\) | \(6m+1\) |
| \(2m+1\) | \(m+1\) | \([m+1,\,2m+1]\) | \(6m+4\) |
| \(2m+2\) | \(m+1\) | \([m+1,\,2m+2]\) | \(6m+7\) |

### 2. Compare neighbouring windows: a doubling recursion

First, \(S(0) = a(0) = 1\), since the window of row 0 is \([0,0]\). Now compare windows from the table, for every \(m \ge 0\) (the case \(m = 0\) compares \([1,1]\) with \([0,0]\), and \([1,2]\) with \([1,1]\)):

- \([m+1,2m+1]\) is \([m,2m]\) with \(a(m)\) removed and \(a(2m+1)\) added, so
  \(S(2m+1) - S(2m) = a(2m+1) - a(m) = (6m+4) - (6m+1) = 3\).
- \([m+1,2m+2]\) is \([m+1,2m+1]\) with \(a(2m+2)\) added and nothing removed, so
  \(S(2m+2) - S(2m+1) = a(2m+2) = (6m+7) - (6m+4) = 3\).

Hence

\[
a(0) = 1, \qquad a(2m+1) = a(m) + 3, \qquad a(2m+2) = 3 \qquad (m \ge 0).
\]

Every index \(n \ge 1\) is exactly one of \(2m+1\) or \(2m+2\), so these equations define \(a\) completely, by recursion on \(n\). That is the Lean function `r`, with `r_zero`, `r_odd`, `r_even`; `blockSum_r` proves that `r` satisfies every window equation.

### 3. Uniqueness: the recursion is the row sum of the inverse

Each truncation of \(A\) is lower triangular with nonzero diagonal \(A(n,n) = \frac{1}{3n+1}\), so its determinant is nonzero (a unit in \(\mathbb{Q}\)) and \(A\,x = \mathbf{1}\) has exactly one solution. The function \(r\) of step 2 solves it, and so does \(a = B\mathbf{1}\). Hence \(a = r\), for every truncation size that contains row \(n\). In particular every \(a(n)\) is a positive integer, which is not obvious from a matrix of fractions.

This is `tri_lower`, `tri_det_isUnit`, `rowSum_inv_tri`, `a127752_eq_r`. The determinant being a unit is also what guarantees Mathlib's convention (a singular matrix has inverse \(0\)) never applies.

### 4. Parity, by strong induction

Claim: \(a(n) \equiv 1 + \nu_2(n+1) \pmod 2\) for all \(n \ge 0\). Assume it for all smaller indices.

- \(n = 0\): \(a(0) = 1\) and \(\nu_2(1) = 0\), so both sides are \(1\). (Here \(a(0) = 1\), not \(3\) as in the even case below, but \(1 \equiv 3\) mod 2, so the parity pattern is the same.)
- \(n = 2m+2\), even and positive: \(a(n) = 3 \equiv 1\), and \(n+1\) is odd, so \(\nu_2(n+1) = 0\).
- \(n = 2m+1\), odd: \(n+1 = 2(m+1)\) has exactly one more factor of 2 than \(m+1\), so \(1 + \nu_2(n+1) = 2 + \nu_2(m+1)\). On the other side, \(a(n) = a(m) + 3 \equiv a(m) + 1 \equiv (1 + \nu_2(m+1)) + 1\) by the induction hypothesis, since \(m < n\). The two sides agree.

So

\[
a(n) \equiv 1 + \nu_2(n+1) \equiv \nu_2\bigl(2(n+1)\bigr) \pmod{2}.
\]

Each step \(n+1 \mapsto 2(n+1)\) adds a factor of 2 and one odd 3, so it flips the bit; an odd \(n+1\) resets it to 1. This is Cloitre's rule for the period-doubling sequence, "concatenate, then change the last term", read backwards. It is `r_mod_two`, and the headline `a127752_mod_two`.

### Remark: the rows of \(B\) (not in Lean)

The same window comparison, done on whole rows instead of row sums, gives \(B\) explicitly. Row \(n\) of \(AB = I\) says \(\sum_{\lceil n/2\rceil \le k \le n} B_k = (3n+1)\,e_n\), where \(B_k\) is row \(k\) of \(B\) and \(e_n\) the \(n\)-th unit vector. Comparing neighbouring windows as in step 2 gives

\[
B_{2m+2} = (6m+7)\,e_{2m+2} - (6m+4)\,e_{2m+1}, \qquad
B_{2m+1} = B_m + (6m+4)\,e_{2m+1} - (6m+1)\,e_{2m}.
\]

For example \(B_2 = (0,-4,7)\) and \(B_3 = (0,4,-7,10)\), matching the triangle in [A127751](https://oeis.org/A127751). Summing entries recovers \(a(2m+2) = 3\) and \(a(2m+1) = a(m)+3\). These two formulas were verified with exact rational arithmetic for every row below \(N = 200\) (computed independently of `check.py` and not part of the repository); they are not stated in Lean.

## Closed form, not in Lean

Unwinding \(a(2m+1) = a(m)+3\) down to an even index or to 0 gives

\[
a(n) =
\begin{cases}
3k+1 & n = 2^k-1, \\
3\,\nu_2(n+1)+3 & \text{otherwise.}
\end{cases}
\]

This is numerics plus paper, not Lean: unwinding the recursion by hand gives the formula, and `check.py` confirms it for all \(n < 10^6\) (an exact inverse for \(N = 200\) also agrees). It is not stated or proved in Lean, since the parity theorem does not need it.

## The Black Swan link

ShadowAlzazel's Black Swan notes checked that the kneading sequence at the Feigenbaum accumulation point, \(\mathrm{RLRRRLRL}\ldots\), is the ruler function \(\nu_2(j) \bmod 2\), with R meaning “\(\nu_2(j)\) even”. The proof above shows why a matrix built from \(1/(3n+1)\) lands on the same word: the window \([\lceil n/2\rceil, n]\) is a halving, so its sliding produces the recursion \(a(2m+1) = a(m) + \mathrm{const}\). That is a renormalization step, one period doubling per factor of 2. The value \(3n+1\) only fixes the constant 3; any odd constant would give the same parity pattern. With \(2n+1\) in place of \(3n+1\) the constant is 2, and the parity is 1 exactly at \(n = 2^k-1\): the Fredholm–Rueppel sequence, which is the conjecture on [oeis-a127750](https://lefttosolve.com/p/oeis-a127750). That sibling is checked numerically here (80 terms) but not yet in Lean.

Written from the problem page and `notes.md`. Proof, Lean, `check.py`, figures and page by Kumi-San; independently reviewed and rebuilt by Alo. For ShadowAlzazel.
