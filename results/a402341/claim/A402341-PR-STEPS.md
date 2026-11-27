# A402341 statement PR: exact steps for Arbiter or Kumi

Nothing in this file has been submitted. Do not let an agent open the pull request; open it yourself as ShadowAlzazel. Do not push the branch from an Alo session unless Arbiter has asked you to; this kit does not push to the fork.

## What this is

A first Lean statement of the OEIS A402341 conjecture, as the Left to Solve problem [`oeis-a402341`](https://lefttosolve.com/p/oeis-a402341). The problem is still open and unformalized (rechecked 2026-11-27, 0 agents, no rival pull requests or issues on GuillaumeBAUD-coder/open-math-agents, and no formal-conjectures file at pin `9097e2f`). The file to add is exactly one path, `statements/oeis-a402341.lean`, copied from `results/a402341/claim/statements/oeis-a402341.lean.txt` in this repo.

Local check with `tools/lint.py` and `tools/check.sh` against formal-conjectures `9097e2f90e66d2f6244209cb1c07f7120d17ec53` (`OMA_FC=/tmp/fc-oma`): lint ok; the statement compiles (one `sorry`, the body of `main`; axioms `propext`, `sorryAx`, `Classical.choice`, `Quot.sound`).

SHA-256 of the statement file (must match after the copy):

```
876362681b19a98e0bef180bedbe658f2cc1e2dd6b7fa2d18312b5938842d346
```

## The base commit

Cut the branch from **current upstream `main`**, not from the fork's `main`. This repo moves every few minutes, and the fork lags.

The upstream `main` SHA at the time this kit was written (2026-11-27, 3:05 PM Pacific) was

```
dfe2c6daf967e72fc4cf82f03edad4ddbfc344d8
```

(`dfe2c6d`, message `proof: oeis-a362560 (#10100)`). Re-fetch at branch time and use whatever `main` is then. If GitHub later says the branch is 1 ahead and N behind, that is still fine if the compare view shows **exactly one new file**, `statements/oeis-a402341.lean`. Do not rebase with a force-push unless Arbiter explicitly says to.

## If the branch `oma/oeis-a402341-statement` is already on the fork

(It is not, as of this writing.)

1. Sign in to GitHub as **ShadowAlzazel**.
2. Open this compare URL (base = `GuillaumeBAUD-coder/open-math-agents` `main`, head = the branch on your fork):

   https://github.com/GuillaumeBAUD-coder/open-math-agents/compare/main...ShadowAlzazel:open-math-agents:oma/oeis-a402341-statement

3. Confirm the diff is **exactly one new file**, `statements/oeis-a402341.lean`, and nothing else.
4. Click **Create pull request**.
5. Title:

   ```
   oeis-a402341: Lean statement
   ```

6. Paste the description from [`PR-description.md`](PR-description.md) (also copied below), replacing anything GitHub pre-fills. Do not add a `Lease:` line.
7. Create the pull request. Do not merge it; a maintainer has to review the translation.

## If the branch is not on the fork yet (git, easy path)

Kumi (as Kumiho-San) or Arbiter (as ShadowAlzazel) can do this. Alo is not pushing the branch in this kit.

From a throwaway clone, cut from **upstream** `main`:

```bash
workdir=/tmp/open-math-agents-a402341-branch
git init "$workdir" && cd "$workdir"
git remote add origin https://github.com/ShadowAlzazel/open-math-agents.git
git remote add upstream https://github.com/GuillaumeBAUD-coder/open-math-agents.git
git fetch --depth 1 --no-tags upstream main
git checkout -b oma/oeis-a402341-statement FETCH_HEAD

# office is the Fang-and-Fox-Lemma-Office checkout:
cp /path/to/Fang-and-Fox-Lemma-Office/results/a402341/claim/statements/oeis-a402341.lean.txt statements/oeis-a402341.lean
cmp /path/to/Fang-and-Fox-Lemma-Office/results/a402341/claim/statements/oeis-a402341.lean.txt statements/oeis-a402341.lean
sha256sum statements/oeis-a402341.lean
# must be 876362681b19a98e0bef180bedbe658f2cc1e2dd6b7fa2d18312b5938842d346

git add statements/oeis-a402341.lean
git commit -m 'oeis-a402341: Lean statement'
git push origin oma/oeis-a402341-statement
```

Then follow the compare URL and title/body steps above. The pull request base must be `GuillaumeBAUD-coder/open-math-agents` `main`, not the fork's `main`.

## If the branch is not on the fork yet (web UI)

1. Sign in as **ShadowAlzazel**. First sync your fork with upstream `main` (the fork's "Sync fork" button on https://github.com/ShadowAlzazel/open-math-agents), so the new branch is not cut from a stale fork `main`.
2. From the synced default branch, use **Add file → Create new file**.
3. Name the file exactly `statements/oeis-a402341.lean`.
4. Paste the contents of `results/a402341/claim/statements/oeis-a402341.lean.txt` from this repo, unchanged.
5. Commit to a **new branch** named `oma/oeis-a402341-statement`, not to `main`. Commit message: `oeis-a402341: Lean statement`.
6. Then follow the compare URL and title/body steps above.

## PR description to paste

Title: `oeis-a402341: Lean statement`

```
Agent: Fang and Fox Lemma Office (Kumi-San, Alo)

Problem: https://lefttosolve.com/p/oeis-a402341
First Lean statement of the OEIS A402341 conjecture: for even n, the 2-adic valuation of the central coefficient of (1 + x + ⋯ + x^15)^n equals A000120(15n/2).
The definition of a(n) is the OEIS name of A402341 (offset 0). The valuation conjecture is from the Comments section of that entry, not from the name and not from the Formula section.
A000120 is encoded as the sum of binary digits (the 1's-counting sequence / binary weight). The statement is only for even n, including n = 0; it does not claim a law at odd n.
Checked locally with tools/lint.py and tools/check.sh at formal-conjectures 9097e2f: compiles, with one sorry, the body of main.
```

## After this statement merges

A Lean proof is a later, separate pull request (`proofs/oeis-a402341.lean`), cut from the updated upstream `main`. This kit does not include that proof file.

Compare URL (once the branch exists on the fork):

https://github.com/GuillaumeBAUD-coder/open-math-agents/compare/main...ShadowAlzazel:open-math-agents:oma/oeis-a402341-statement
