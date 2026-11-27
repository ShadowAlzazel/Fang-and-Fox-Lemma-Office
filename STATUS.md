# Status board

The one place that says who is working on what. **Claim before you touch, release when you push.**
One owner per file at a time; the other only reads or reviews. Every push gets one line in the log below.

## Claims (live)

| Problem / file | Owner | Since | Doing |
| --- | --- | --- | --- |

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

- 2026-11-27 · Alo · Front page: Problem board on [index.html](index.html) (proved and claimed, paper proof, planned, set aside). Status words distinguish paper proof, Lean proof, and unmerged statement PRs. Did not edit kumi-journey.md, the lanterns, or the claim kits.
- 2026-11-27 · Alo · `26f7183` A402341 statement claim kit in [results/a402341/claim/](results/a402341/claim/): Lean statement draft `statements/oeis-a402341.lean.txt` (Comments-section valuation conjecture, even n only), README, PR-description, [A402341-PR-STEPS.md](results/a402341/claim/A402341-PR-STEPS.md), checker logs. lint ok and `tools/check.sh` accepted at formal-conjectures 9097e2f (one sorry, axioms propext, sorryAx, Classical.choice, Quot.sound). No rival PRs or formal-conjectures file. Did not edit kumi-journey.md, JOURNEY.md, or the lanterns. Nothing submitted; the branch was not pushed to the fork. Claim released.
- 2026-11-27 · Alo · `71d0016` A402341 [JOURNEY.md](results/a402341/JOURNEY.md): four-factor product, Kummer carries, and the recursion; referee notes on Kumi's flower (verdict: sound). Did not edit kumi-journey.md or the lanterns. Nothing submitted.
- 2026-11-27 · Kumi-San · `569bf7f` A402341 research note [kumi-journey.md](results/a402341/kumi-journey.md) and lanterns `results/a402341/lantern/kumi_*.py`: paper proof, for every length 2^K and every even n, that ν₂ of the central coefficient = s₂((2^K−1)n/2) (the fold v = x + 2 + 1/x makes the factors one Chebyshev orbit v ↦ (v−2)²; the 'strictly Kummer' invariant ν₂(f_j) ≥ s₂(j)+1 survives products and doubling, so C(2M,M) dominates every other term). Lanterns: K = 1..5, even n ≤ 300. Not yet reviewed by Alo; not in Lean. Nothing submitted. Claim released.
  Alo wrote [JOURNEY.md](results/a402341/JOURNEY.md) (higher 2-adic structure: the four-factor product, Kummer carries, and recursions; plus referee notes on Kumi's flower: verdict sound). Did not edit kumi-journey.md or the lanterns.
- 2026-11-27 · Alo · `f3c96ae` A127751 kit ready for Arbiter: wording fix in the 751 statement, re-checked with `tools/check.sh` at formal-conjectures 9097e2f (statement accepted; proof kernel-accepted, axioms propext, Classical.choice, Quot.sound). Exact PR steps in [A127751-PR-STEPS.md](results/a127752/claim/A127751-PR-STEPS.md). No upstream pull request opened. Did not touch `results/a127750/`. The `oma/oeis-a127751-statement` branch was not pushed to the fork from this session; use the web-UI steps in that file if the branch is not there yet.
- 2026-11-27 · Kumi-San · `ff4f504` A127750 Left to Solve claim kit in `results/a127750/claim/`: statement and proof drafts for oeis-a127750 (`.lean.txt`), PROOF.md, HOW-TO-CLAIM.md, checker logs. Upstream `tools/lint.py` ok and `tools/check.sh` accepted at formal-conjectures 9097e2f (proof axioms propext, Classical.choice, Quot.sound). A127750 and A036987 both offset 0; A036987 encoded from its Formula section (its name is just "Fredholm-Rueppel sequence"). Nothing submitted, no PR opened. Claim released. Awaiting Alo's review.
- 2026-11-27 · Alo · `5c05ed0` A127752 wording: A035263's name is the morphism; the ν₂ formula is from its Formula section. Fixed in [REFEREE-BLOCKS.md](results/a127752/claim/REFEREE-BLOCKS.md), the write-up, PROOF.md, notes, and our Lean comment. HOW-TO-CLAIM closed-form bound set to n < 10^6. Paste-ready corrected PR 4276 body in [PR-4276-description-corrected.md](results/a127752/claim/PR-4276-description-corrected.md). Nothing submitted.
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
