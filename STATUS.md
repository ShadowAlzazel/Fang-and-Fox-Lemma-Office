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

- 2026-11-27 · Alo · `7fa0074` README links [CLAIMING.md](CLAIMING.md) from the "Where to look" table. Referee copy-paste drafts for A127752 are in [results/a127752/claim/REFEREE-BLOCKS.md](results/a127752/claim/REFEREE-BLOCKS.md) (reviewer comment for #4276, proof PR body, two X replies). Nothing submitted.
- 2026-11-27 · Kumi-San · `d2ee0a6` [CLAIMING.md](CLAIMING.md): playbook for Left to Solve claims (fast path used for A127752 PR 1, #4276). Pointer added in `results/a127752/claim/HOW-TO-CLAIM.md`. README left for Alo to link. Claim released.
- 2026-11-26 · Kumi-San · `0fd31d7` A127752 Left to Solve claim kit in `results/a127752/claim/`: statement and proof drafts for oeis-a127752 and oeis-a127751 (stored as `.lean.txt` so our CI skips them), OEIS comment draft, HOW-TO-CLAIM. Upstream `tools/lint.py` ok and `tools/check.sh` accepted at formal-conjectures 9097e2f (proof axioms propext, Classical.choice, Quot.sound). Nothing submitted. Claim released. Reviewed by Alo (see next line).
- 2026-11-26 · Alo · claim kit review: all four files independently rebuilt with upstream check.sh at open-math-agents@4d8b8ac and formal-conjectures 9097e2f; statements accepted, proofs kernel-accepted (propext, Classical.choice, Quot.sound). Ready for Arbiter.
- 2026-11-26 · Kumi-San · claim `results/a127752/claim/` (Left to Solve claim prep, owner Kumi-San, reviewer Alo); only that folder and STATUS.md.
- 2026-11-26 · Kumi-San · first commit as Kumiho-San: A127752 notes.md gets the outside-review line.
- 2026-11-26 · Alo · `02d87bc` CI: parse `#print axioms` names that end in a prime (`li_criterion_weighted'`), after `33cfe3d` missed that print format.
- 2026-11-26 · Alo · `33cfe3d` CI: build FormalConjectures.Paper.RiemannHypothesisEquivalents and FormalConjectures.Wikipedia.MaximalPrimeGap after the Mathlib cache; require headline `#print axioms` per Lean file; reject `axiom`/`unsafe`/`implemented_by` with a comment-aware word-boundary scan; add prints on LiConditional.lean; link result pages to PROOF.md.
- 2026-11-26 · Kumi-San · `3a63289` A127752 PROOF.md reworded per outside referee review (window table, explicit uniqueness, strong-induction parity, rows of B, closed form flagged as not in Lean, outside review note); claim released. Reviewer: Alo.
- 2026-11-26 · Kumi-San · claim `results/a127752/PROOF.md` wording (owner Kumi-San, reviewer Alo); only that file and STATUS.md.
- 2026-11-26 · Alo · restructure claim released. `0624720` folders moved to `results/` with Pages redirect stubs; `92a4517` PROOF.md for Shanks, Li and A127752; `e9f058a` README results table; `e0ca5a5` Lean CI.
- 2026-11-26 · Kumi-San · `9a1d0e0` A127752 published: `problems/a127752/` (Lean, check.py, notes, page, figures), front-page card, TARGETS done; claim released. Reviewed by Alo.
- 2026-11-26 · Kumi-San · `5038405` claim A127752 publication (owner Kumi-San, reviewer Alo).
- 2026-11-26 · Kumi-San · `790efd5` no real zeros in (0,1); Li now rests on summability alone. Rebuilt by Alo.
- 2026-11-26 · Alo · `69180dc` credit ShadowAlzazel by GitHub name.
- 2026-11-26 · Alo · `3fdbb9f` independent rebuild of Li part II.
- 2026-11-26 · Kumi-San · `faa6cbd` Li converse (conditional), page part II.
