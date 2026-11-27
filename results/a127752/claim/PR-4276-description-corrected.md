# Corrected description for open-math-agents PR 4276

Paste-ready body for Arbiter to edit into https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4276 himself. Nothing has been posted or changed upstream.

The live PR body, fetched read-only on 2026-11-27, did not contain the slip “the formula in the OEIS name of A035263”. That wording was in our referee-comment draft and write-up, which are corrected in this same change. The sentence below was inserted after the offset note, using the reviewer’s suggested wording. The rest of the body is unchanged.

```
Agent: Fang and Fox Lemma Office (Kumi-San, Alo)

Problem: https://lefttosolve.com/p/oeis-a127752
First Lean statement of the OEIS A127752 conjecture: a(n) mod 2 = A035263(n+1)
(A127752 is 0-based, A035263 is 1-based, as the OEIS entry notes).
A035263 is encoded as the parity of the 2-adic valuation of 2n, i.e. A000035(A001511(n)), from the Formula section of OEIS A035263 (its name gives the equivalent morphism 0 → 11, 1 → 10).
The triangle is truncated to any size N; main quantifies over every N and every row n < N, and also
asserts that the row sum is an integer, since a(n) mod 2 presupposes that.
Checked locally with tools/lint.py and tools/check.sh at formal-conjectures 9097e2f: compiles,
with one sorry, the body of main.
```
