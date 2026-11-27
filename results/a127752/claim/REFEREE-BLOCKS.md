# Referee blocks for A127752

Copy-paste drafts for Arbiter to post himself. Nothing here has been submitted.

The Lean statement and the proof file cover the window-sum / parity claim only:
`a(n)` is an integer and `a(n) mod 2 = A035263(n+1)`. The closed form
`a(n) = 3ν₂(n+1)+3`, except `a(2^k-1) = 3k+1`, is not in Lean. It was
checked numerically for every `n < 10^6` in `check.py`.

---

## A. Comment for the human reviewer of PR 4276

Paste this as a comment on https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4276 (do not treat it as already posted).

```
Thanks for reviewing this statement, and for the wording correction: A035263's name is the morphism 0 → 11, 1 → 10, and the ν₂ formula is from its Formula section. The Lean docstring already said that; the description below now matches.

What is stated. `main` says: for every truncation size N and every row n < N, the n-th row sum of the inverse of the triangle A(n,k) = 1/(3n+1) when k ≤ n ≤ 2k (and 0 otherwise) is an integer m with m mod 2 = A035263(n+1). A035263 is encoded as the parity of the 2-adic valuation of 2n, i.e. A000035(A001511(n)), from the Formula section of OEIS A035263 (its name gives the equivalent morphism 0 → 11, 1 → 10). The body of `main` is the single allowed sorry.

Why this matches the OEIS comment. The A127752 entry conjectures that "a(n) mod 2 is first Feigenbaum symbolic sequence A035263", and it warns that A127752 is 0-based while A035263 is 1-based. The statement uses that shift, and it includes integrality because "a(n) mod 2" presupposes an integer. The triangle is taken from the OEIS name. The claim is quantified over every truncation that contains row n, so it does not depend on a choice of N. We did not formalize the equivalent morphism description of A035263 (0 → 11, 1 → 10); only the valuation formula.

CI. The `check` job on this pull request completed successfully (https://github.com/GuillaumeBAUD-coder/open-math-agents/actions/runs/45962360956). The bot reported that the statement compiles and applied the needs-human-review label.

Proof, ready but not submitted. A follow-up proof of this exact `main` has been kernel-checked locally with tools/check.sh against formal-conjectures 9097e2f. Its axioms are only propext, Classical.choice and Quot.sound. We will open that proof PR after this statement is merged. A write-up of the argument is at https://shadowalzazel.github.io/Fang-and-Fox-Lemma-Office/results/a127752/. The closed form a(n) = 3ν₂(n+1)+3, except a(2^k−1) = 3k+1, is not part of this statement; it is only a numerical check (n < 10^6) and is not in Lean.
```

---

## B. Draft body for the follow-up proof PR

Open this only after PR 4276 has merged, from a branch that adds exactly one file, `proofs/oeis-a127752.lean`, copied from `results/a127752/claim/proofs/oeis-a127752.lean.txt`. Suggested title: `oeis-a127752: Lean proof`. There is no `Lease:` line, because we did not take a desk lease.

```
Agent: Fang and Fox Lemma Office (Kumi-San, Alo)

Problem: https://lefttosolve.com/p/oeis-a127752
Proof of the OEIS A127752 conjecture: the row sums of the inverse 1/(3n+1) triangle satisfy a(n) mod 2 = A035263(n+1). The argument is a window-sum identity, a doubling recursion, uniqueness from triangularity, and a parity induction.
Checked locally with tools/check.sh at formal-conjectures 9097e2f: accepted, axioms propext, Classical.choice, Quot.sound.
Write-up: https://shadowalzazel.github.io/Fang-and-Fox-Lemma-Office/results/a127752/

Follows statement PR #4276. The closed form a(n) = 3ν₂(n+1)+3, except a(2^k−1) = 3k+1, is not claimed in this file; it was only checked numerically for n < 10^6 and is not in Lean.
```

---

## C. X reply drafts for the Left to Solve thread

Each block is under 280 characters, counting each URL as 23 characters the way X does. Post only if you want to; neither has been posted.

### Reply 1

```
CI is green on our Lean statement for OEIS A127752; it is waiting on a human reviewer.
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4276

The window-sum/parity claim is proved in Lean. The closed form is only a numerical check.
https://shadowalzazel.github.io/Fang-and-Fox-Lemma-Office/results/a127752/
```

### Reply 2

```
Statement PR for A127752 (a(n) mod 2 = A035263(n+1)) is up for review: https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4276

Write-up, with the Lean parity proof and a note that the closed form is numerical only: https://shadowalzazel.github.io/Fang-and-Fox-Lemma-Office/results/a127752/
```
