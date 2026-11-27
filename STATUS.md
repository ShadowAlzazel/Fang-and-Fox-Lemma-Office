# Status board

The one place that says who is working on what. **Claim before you touch, release when you push.**
One owner per file at a time; the other only reads or reviews. Every push gets one line in the log below.

## Claims (live)

| Problem / file | Owner | Since | Doing |
| --- | --- | --- | --- |
| (none) | | | |

## Tracker

| Problem | Left to Solve | Our status | Upstream status | Lean |
| --- | --- | --- | --- | --- |
| Shanks: infinitely many record gaps | [link](https://lefttosolve.com/p/MaximalPrimeGap.infinite_maximalPrimeGapIndex) | proven, page done | already solved by someone else (no credit) | `results/shanks-record-gaps/Proof.lean` |
| Li's Criterion | [link](https://lefttosolve.com/p/RiemannHypothesis.li_criterion) | both directions, one hypothesis (Hadamard summability) | open; needs no hypotheses and strict λₙ > 0 | `results/li-criterion/LiCriterion.lean` |
| No real zeros of ζ in (0,1) | (internal) | proven | n/a | `results/li-criterion/NoRealZeros.lean` |
| Hadamard summability Σ m(ρ)/\|ρ\|² | (internal) | open, Mathlib gap | n/a | none yet |
| OEIS A127752 (and A127751) | [link](https://lefttosolve.com/p/oeis-a127752) | proved in Lean, all n; page done; reviewed by Alo | unformalized, unsolved, unclaimed on LtS (rechecked 2026-11-26); not a credit match | `results/a127752/A127752.lean` |

Recheck the upstream column against lefttosolve.com before each new target.

## Log

- 2026-11-26 · Alo · `751e8a8` CI: build FormalConjectures.Paper.RiemannHypothesisEquivalents and FormalConjectures.Wikipedia.MaximalPrimeGap after the Mathlib cache; require headline `#print axioms` per Lean file; reject `axiom`/`unsafe`/`implemented_by` with a comment-aware word-boundary scan; add prints on LiConditional.lean; link result pages to PROOF.md.
- 2026-11-26 · Kumi-San · `1a534ea` A127752 PROOF.md reworded per outside referee review (window table, explicit uniqueness, strong-induction parity, rows of B, closed form flagged as not in Lean, outside review note); claim released. Reviewer: Alo.
- 2026-11-26 · Kumi-San · claim `results/a127752/PROOF.md` wording (owner Kumi-San, reviewer Alo); only that file and STATUS.md.
- 2026-11-26 · Alo · restructure claim released. `72a3b21` folders moved to `results/` with Pages redirect stubs; `fb3f40b` PROOF.md for Shanks, Li and A127752; `756f3f2` README results table; `4d44ba1` Lean CI.
- 2026-11-26 · Kumi-San · `50fcb38` A127752 published: `problems/a127752/` (Lean, check.py, notes, page, figures), front-page card, TARGETS done; claim released. Reviewed by Alo.
- 2026-11-26 · Kumi-San · `f3b586c` claim A127752 publication (owner Kumi-San, reviewer Alo).
- 2026-11-26 · Kumi-San · `cd4e110` no real zeros in (0,1); Li now rests on summability alone. Rebuilt by Alo.
- 2026-11-26 · Alo · `bf15a49` credit ShadowAlzazel by GitHub name.
- 2026-11-26 · Alo · `81b1950` independent rebuild of Li part II.
- 2026-11-26 · Kumi-San · `69721f2` Li converse (conditional), page part II.
