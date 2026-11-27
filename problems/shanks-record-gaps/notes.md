# Shanks record gaps (warmup) — notes

- Status: **proven** (textbook). Already marked solved on Left to Solve, so this is a pipeline dry run, not a credited submission.
- Lean: compiled by Kumi-San against formal-conjectures @9097e2f on Lean/Mathlib v4.33.1; no `sorry`, axioms only propext, Classical.choice, Quot.sound.
- Honesty review (Alo): no `sorry`/`axiom`/`native_decide`; the three lemmas mirror story.tex in order. `gap_unbounded` states `k ≤ g_n` (the story's `k+1` bound is used via `H+1`), equivalent for our purpose. Final theorem has exactly the upstream type; a real submission would wrap it as `OMA.solution : type_of% @MaximalPrimeGap.infinite_maximalPrimeGapIndex`.
- Not independently rebuilt on Alo's side (no Mathlib checkout there).
