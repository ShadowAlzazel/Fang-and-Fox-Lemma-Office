# OEIS comment draft for A127752 (for ShadowAlzazel to rewrite)

> **Rewrite this in your own words before submitting.** The OEIS does not accept AI-written text, and
> edits must come from your own OEIS account. This file is only a list of facts to draw on. Nothing has
> been submitted anywhere.

## Facts to put in the comment

- The conjecture in the entry, "a(n) mod 2 is first Feigenbaum symbolic sequence A035263", is true for
  every n >= 0, with the entry's 0-based indexing: a(n) == A035263(n+1) (mod 2).
- Proof sketch. Row n of A*a = 1 says that the sum of a(k) for ceil(n/2) <= k <= n equals 3n+1.
  Taking differences of consecutive rows gives a(0) = 1, a(2m+1) = a(m) + 3 and a(2m+2) = 3. Mod 2 this is
  a(2m) == 1 and a(2m+1) == 1 + a(m), which is the period-doubling recursion. So a(n) is congruent mod 2
  to A001511(n+1), the exponent of 2 in 2(n+1), and that is A035263(n+1).
- Closed form (proved on paper, not in Lean): a(n) = 3*A007814(n+1) + 3, except that a(2^k - 1) = 3k + 1.
- The parity statement (not the closed form) is verified in Lean 4 with Mathlib. The only axioms used are
  propext, Classical.choice and Quot.sound.
- The same fact settles the conjecture in A127751, which says the row sums A127752 mod 2 are A035263.

## Suggested placement

- In A127752, a %C line such as "The conjecture above is true; see the proof link." with your name and the date.
  Ask the editors whether the word "(conjecture)" should be dropped from the existing comment; they decide that.
- Under %H (links), something like:
  `ShadowAlzazel, <a href="https://shadowalzazel.github.io/Fang-and-Fox-Lemma-Office/results/a127752/">Proof that a(n) mod 2 = A035263(n+1)</a>, with Lean 4 formalization, 2026.`
- Optionally add the same %H link to A127751 and A035263.

## Links

- Write-up (Pages): https://shadowalzazel.github.io/Fang-and-Fox-Lemma-Office/results/a127752/
- Site home: https://shadowalzazel.github.io/Fang-and-Fox-Lemma-Office/
- Lean file: https://github.com/ShadowAlzazel/Fang-and-Fox-Lemma-Office/blob/main/results/a127752/A127752.lean
- Left to Solve version: `results/a127752/claim/proofs/oeis-a127752.lean.txt` in the same repository.
- Once the Left to Solve PRs merge, add their links too, e.g. https://lefttosolve.com/p/oeis-a127752.
