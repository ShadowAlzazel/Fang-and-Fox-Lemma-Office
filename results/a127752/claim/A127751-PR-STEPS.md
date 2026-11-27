# A127751 statement PR: exact steps for Arbiter

Nothing in this file has been submitted. Do not let an agent open the pull request; open it yourself as ShadowAlzazel.

## What this is

A first Lean statement of the OEIS A127751 conjecture, as its own Left to Solve problem (`oeis-a127751`, still open and unformalized as of 2026-11-27, no rival PRs). The file is `statements/oeis-a127751.lean`, prepared from `results/a127752/claim/statements/oeis-a127751.lean.txt`.

It was re-checked after the A035263 wording fix with `tools/check.sh` against formal-conjectures `9097e2f`: the statement compiles (one `sorry`, the body of `main`; axioms `propext`, `sorryAx`, `Classical.choice`, `Quot.sound`). The follow-up proof file is also kernel-accepted with only `propext`, `Classical.choice` and `Quot.sound`. Open the proof PR only after this statement has merged.

## Honest note for the reviewer (please keep this in the description)

A127751 is the inverse triangle; A127752 is its row sums. The only conjecture on the A127751 entry is: “Row sums A127752 mod 2 are conjectured to be first Feigenbaum symbolic sequence A035263.” That is the same claim as on A127752, which adds the 0-based vs 1-based offset warning. This formalization follows that comment and uses the shift `A035263(n+1)`. A reviewer may treat this as a companion of [PR #4276](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4276), or as a duplicate. Either reading is fair; the description below says so.

## If the branch `oma/oeis-a127751-statement` is already on the fork

1. Sign in to GitHub as **ShadowAlzazel**.
2. Open this compare URL (base = `GuillaumeBAUD-coder/open-math-agents` `main`, head = the branch on your fork):

   https://github.com/GuillaumeBAUD-coder/open-math-agents/compare/main...ShadowAlzazel:open-math-agents:oma/oeis-a127751-statement

3. Confirm the diff is **exactly one new file**, `statements/oeis-a127751.lean`, and nothing else.
4. Click **Create pull request**.
5. Title:

   ```
   oeis-a127751: Lean statement
   ```

6. Paste the description in the next section, replacing anything GitHub pre-fills. Do not add a `Lease:` line (we did not take a desk lease).
7. Create the pull request. Do not merge it; a maintainer has to review the translation, as with #4276.

Branch on the fork (after a successful push): https://github.com/ShadowAlzazel/open-math-agents/tree/oma/oeis-a127751-statement

## If the branch is not on the fork yet (web UI)

AlephTwooo may not have had push access at the time this was written. You already sent a collaborator invitation; you can also add the file yourself:

1. Sign in as **ShadowAlzazel**. First sync your fork with upstream `main` (the fork’s “Sync fork” button on https://github.com/ShadowAlzazel/open-math-agents), so the new branch is not cut from a stale fork `main`.
2. From the synced default branch, use **Add file → Create new file**.
3. Name the file exactly `statements/oeis-a127751.lean`.
4. Paste the contents of `results/a127752/claim/statements/oeis-a127751.lean.txt` from this repo, unchanged (it already has the A035263 Formula-section wording).
5. Commit to a **new branch** named `oma/oeis-a127751-statement`, not to `main`. Commit message: `oeis-a127751: Lean statement`.
6. Then follow the compare URL and title/body steps above. Do not open the pull request against your fork’s `main`; the base must be `GuillaumeBAUD-coder/open-math-agents` `main`.

You can also add **AlephTwooo** as a collaborator on the fork if you want Alo to push the next branch (the proof branch) herself.

## PR description to paste

```
Agent: Fang and Fox Lemma Office (Kumi-San, Alo)

Problem: https://lefttosolve.com/p/oeis-a127751
First Lean statement of the OEIS A127751 conjecture: row sums A127752 mod 2 = A035263(n+1)
(A127751 and its row sums A127752 are 0-based, A035263 is 1-based; the A127752 entry notes the shift).
A035263 is encoded as the parity of the 2-adic valuation of 2n, i.e. A000035(A001511(n)), from the Formula section of OEIS A035263 (its name gives the equivalent morphism 0 → 11, 1 → 10).
Companion to https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4276 (oeis-a127752). The conjecture text is the same claim, recorded on the inverse triangle's entry rather than on the row-sums entry; a reviewer may treat this as a duplicate, which is fair.
The triangle is truncated to any size N; main quantifies over every N and every row n < N, and also
asserts that the row sum is an integer, since a(n) mod 2 presupposes that.
Checked locally with tools/lint.py and tools/check.sh at formal-conjectures 9097e2f: compiles,
with one sorry, the body of main.
```

## After this statement merges: the proof PR

Wait until the statement is on upstream `main`. Then, from a fresh branch `oma/oeis-a127751` cut from the updated upstream `main`, add exactly one file, `proofs/oeis-a127751.lean`, copied from `results/a127752/claim/proofs/oeis-a127751.lean.txt`. Suggested title: `oeis-a127751: Lean proof`. Body:

```
Agent: Fang and Fox Lemma Office (Kumi-San, Alo)

Problem: https://lefttosolve.com/p/oeis-a127751
Proof of the OEIS A127751 conjecture: the row sums of the inverse 1/(3n+1) triangle satisfy a(n) mod 2 = A035263(n+1). The argument is a window-sum identity, a doubling recursion, uniqueness from triangularity, and a parity induction.
Checked locally with tools/check.sh at formal-conjectures 9097e2f: accepted, axioms propext, Classical.choice, Quot.sound.
Write-up: https://shadowalzazel.github.io/Fang-and-Fox-Lemma-Office/results/a127752/

Follows the oeis-a127751 statement PR, companion to #4276. The closed form a(n) = 3ν₂(n+1)+3, except a(2^k−1) = 3k+1, is not claimed in this file; it was only checked numerically for n < 10^6 and is not in Lean.
```

Open that pull request the same way (compare against `GuillaumeBAUD-coder/open-math-agents` `main`, as ShadowAlzazel). An accepted proof of an open problem also gets human review and is not auto-merged.
