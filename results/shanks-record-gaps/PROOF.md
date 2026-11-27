# Records never stop

## Statement

Write \(p_n\) for the \(n\)-th prime, with \(p_0 = 2\), and \(g_n = p_{n+1} - p_n\) for the gap after it. Index \(n\) is a *record* when \(g_m < g_n\) for every \(m < n\). There are infinitely many record indices.

## Status

Proven; no credit, already solved upstream.

## Lean

- File: [`Proof.lean`](Proof.lean)
- Main theorem: `ShanksWarmup.infinite_maximalPrimeGapIndex`
- Steps, in order: `gap_unbounded`, `first_exceeder_is_record`, `infinite_maximalPrimeGapIndex`
- The final theorem has exactly the type of `MaximalPrimeGap.infinite_maximalPrimeGapIndex` in [formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/Wikipedia/MaximalPrimeGap.lean#L86).

## Axioms

`propext`, `Classical.choice`, `Quot.sound`

## Reviewed by

Alo, independent rebuild (`lake env lean` against formal-conjectures, Lean/Mathlib v4.33.1).

## Caveats

- Already solved on [Left to Solve](https://lefttosolve.com/p/MaximalPrimeGap.infinite_maximalPrimeGapIndex); this was our pipeline dry run, not a credited submission.
- Proven, elementary. No use of RH or any heuristic.
- `gap_unbounded` states \(k \le g_n\) (the story's \(k+1\) bound is used via \(H+1\)), equivalent for our purpose.
- A real submission would wrap the theorem as `OMA.solution : type_of% @MaximalPrimeGap.infinite_maximalPrimeGapIndex`.
- The open Shanks question this warmup does not touch is the growth rate \(g_n \sim (\log p_n)^2\).

## The picture

Walk along the primes and keep a high-water mark of the widest gap seen so far. Each time the water rises, that index is a *record*. The question is whether the water ever stops rising. It cannot: there are deserts of composites as wide as we like, and the first gap that beats the old mark is, by its very firstness, a new record.

## Proof

### 1. Deserts as wide as we like (`gap_unbounded`)

For every \(k \ge 1\) there is \(n\) with \(g_n \ge k+1\).

Let \(N = (k+1)!\). For \(2 \le j \le k+1\), \(j\) divides both \(N\) and \(j\), so \(j\) divides \(N+j\) with \(N+j > j\); hence \(N+2, \dots, N+k+1\) are all composite. Let \(p_n\) be the largest prime \(\le N+1\) (it exists since \(2 \le N+1\)). The next prime lies beyond the desert, so \(p_{n+1} \ge N+k+2\) and \(g_n \ge k+1\).

### 2. The first to beat the mark is a record (`first_exceeder_is_record`)

Fix \(M\) and let \(H = \max_{m \le M} g_m\). If \(n\) is the *least* index with \(g_n > H\), then \(n > M\) and \(n\) is a record.

Indeed \(n > M\) because every \(g_m\) with \(m \le M\) is \(\le H\). Take \(m < n\). If \(m \le M\) then \(g_m \le H < g_n\). If \(M < m < n\) then \(g_m \le H\) by minimality of \(n\), so again \(g_m < g_n\).

### 3. So there are infinitely many (`infinite_maximalPrimeGapIndex`)

Given any \(M\), step 1 with \(k = H\) gives some \(g_n > H\); the least such \(n\) is a record beyond \(M\) by step 2. A set of naturals with an element past every bound is infinite.

## Why it is on the record

Nothing here is deep; that is the point. The shape of the argument (an unbounded quantity forces infinitely many records, via the least exceeder) isolates exactly what the open Shanks record-index problem asks beyond this: not *whether* records recur, but *how fast*, \(g_n \sim (\log p_n)^2\).

Written from `story.tex` and the problem page. Lean drafted by Kumi-San; independently rebuilt by Alo. For ShadowAlzazel.
