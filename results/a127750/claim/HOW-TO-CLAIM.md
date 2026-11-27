# How to claim A127750 on Left to Solve (for ShadowAlzazel)

The general playbook is [CLAIMING.md](../../../CLAIMING.md). This file is the A127750-specific part.
Everything here is a **draft**; Arbiter opens every pull request himself, signed in as ShadowAlzazel (that account gets the credit).

Problem page: https://lefttosolve.com/p/oeis-a127750 (unformalized, so two pull requests)
OEIS: https://oeis.org/A127750 (offset 0) and https://oeis.org/A036987 (Fredholm-Rueppel sequence, offset 0)

## Step 1: PR 1 (statement)

Kumi pushes a one-file branch to the fork. Arbiter opens the pull request from the compare link:

    https://github.com/GuillaumeBAUD-coder/open-math-agents/compare/main...ShadowAlzazel:open-math-agents:oma/oeis-a127750-statement

Title: `oeis-a127750`

Body:

    Agent: Fang and Fox Lemma Office (Kumi-San, Alo)

    Problem: https://lefttosolve.com/p/oeis-a127750
    First Lean statement of the OEIS A127750 conjecture: a(n) mod 2 gives the Fredholm-Rueppel sequence A036987
    (the OEIS comment on A127750). Both A127750 and A036987 are indexed from 0, so there is no index shift.
    A036987 is encoded as a(n) = 1 iff n = 2^k - 1 for some k, 0 otherwise, from the Formula section of
    OEIS A036987 (its name is just "Fredholm-Rueppel sequence"; its data 1, 1, 0, 1, 0, 0, 0, 1, ... agree).
    The triangle is truncated to any size N; main quantifies over every N and every row n < N, and also
    asserts that the row sum is an integer, since a(n) mod 2 presupposes that.
    Checked locally with tools/lint.py and tools/check.sh at formal-conjectures 9097e2f: compiles,
    with one sorry, the body of main.

The pull request must add exactly one file and nothing else.

## Step 2: PR 2 (proof), only after PR 1 merges

Kumi cuts `oma/oeis-a127750` from the new upstream `main` with only `proofs/oeis-a127750.lean`. Title `oeis-a127750`. Body:

    Agent: Fang and Fox Lemma Office (Kumi-San, Alo)

    Problem: https://lefttosolve.com/p/oeis-a127750
    Proof of the conjecture: the window identity sum_(ceil(n/2)<=k<=n) a(k) = 2n+1 gives the doubling recursion
    a(0)=1, a(2m+1)=a(m)+2, a(2m+2)=2, and by strong induction a(n) is odd iff n = 2^k - 1, i.e. a(n) mod 2 = A036987(n).
    Checked locally with tools/check.sh: accepted, axioms propext, Classical.choice, Quot.sound.
    Write-up: https://shadowalzazel.github.io/Fang-and-Fox-Lemma-Office/results/oeis-a127750/

(Drop the Write-up line unless a page exists. The lease line is left out, as for A127752.)

## OEIS

Arbiter's own account and words; see CLAIMING.md. Facts: the recursion above, offsets 0/0, rows 0..63 checked with exact fractions, Lean proof for all n.

## What we checked locally

- `tools/lint.py` and `tools/check.sh` against open-math-agents@0babb05 and formal-conjectures 9097e2f: see `checker-logs/`.
- Statement axioms `[propext, sorryAx, Classical.choice, Quot.sound]` (sorryAx is the one allowed sorry); proof axioms `[propext, Classical.choice, Quot.sound]`.
- Not yet independently rebuilt by Alo.
