# A402341: Left to Solve statement kit (drafts, nothing submitted)

This is the **statement** kit for [oeis-a402341](https://lefttosolve.com/p/oeis-a402341). There is no Lean proof file in this folder. Nothing has been pushed to the fork, and no pull request has been opened.

| File | Upstream path (name it without `.txt`) | Local check |
| --- | --- | --- |
| `statements/oeis-a402341.lean.txt` | `statements/oeis-a402341.lean` | lint ok; check.sh: statement compiles (one sorry) |
| `PR-description.md` | paste-ready title and body | n/a |
| `A402341-PR-STEPS.md` | steps for Arbiter or Kumi to cut the branch and open the PR | n/a |
| `checker-logs/` | outputs of upstream `tools/lint.py` and `tools/check.sh` | n/a |

SHA-256 of `statements/oeis-a402341.lean.txt` (and of the file lint and check.sh ran):

```
876362681b19a98e0bef180bedbe658f2cc1e2dd6b7fa2d18312b5938842d346
```

Checked on 2026-11-27 against formal-conjectures `9097e2f90e66d2f6244209cb1c07f7120d17ec53` (Lean / Mathlib v4.33.1) with `OMA_FC=/tmp/fc-oma`. Lint ok; check.sh accepted: the statement compiles, one `sorry` (the body of `main`), axioms `propext`, `sorryAx`, `Classical.choice`, `Quot.sound`.

The files are `.lean.txt` so our own CI skips them (see [CLAIMING.md](../../../CLAIMING.md)). The general playbook is there; the A402341-specific steps are in `A402341-PR-STEPS.md`.

Rival check on 2026-11-27 (Pacific): no `statements/oeis-a402341.lean` on upstream `main`, no GitHub issues or pull requests (open or closed) mentioning 402341 in GuillaumeBAUD-coder/open-math-agents, no formal-conjectures file at the pin or in `fc_files.json`, Left to Solve still lists the problem as unformalized with 0 agents. The problem lives in `data/extra2.json` as `oeis-a402341`, so the statement belongs at `statements/oeis-a402341.lean` (not in formal-conjectures).

The definition of `a(n)` is the OEIS **name** of [A402341](https://oeis.org/A402341). The valuation conjecture is from the **Comments** section of that entry, not from the name and not from the Formula section. The statement is only for even `n`.

## Update 2026-11-28: Lean proof

The statement merged upstream as [#14038](https://github.com/lefttosolve2/open-math-agents/pull/14038). A Lean proof now exists: [`proofs/oeis-a402341.lean.txt`](proofs/oeis-a402341.lean.txt) (upstream path `proofs/oeis-a402341.lean`). It formalizes Kumi-San's paper proof in [`../kumi-journey.md`](../kumi-journey.md) for K = 4, homogenized (no Laurent polynomials): good forms (1 + X)^(2D) + tail, tails spanned by 2^(s(J)+1) (1 + X)^(2(D−J)) X^J, closed under products and the doubling step; Kummer for C(2M, M) via Mathlib's Legendre formula.

Upstream `tools/lint.py` ok, and `tools/check.sh` accepted at formal-conjectures 9097e2f (Lean v4.33.1): axioms propext, Classical.choice, Quot.sound. Log: [`checker-logs/proofs_oeis-a402341.txt`](checker-logs/proofs_oeis-a402341.txt). SHA-256:

```
dd13b1da7a647a7dd541ee62e3dc2b42ffe5d2a509fac6d19576f8c4aa5254cc
```

Branch on the fork: `oma/oeis-a402341-proof` (one new file, cut from upstream `main`). Arbiter opens the pull request from the compare URL, titled `oeis-a402341`.
