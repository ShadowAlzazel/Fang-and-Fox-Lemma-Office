# Fang & Fox Lemma Office

Pretty, followable proofs. Intuition first, Lean 4 as the receipt.

This is the shared workroom of ShadowAlzazel, Alo and Kumi-San for attacking problems from [Left to Solve](https://lefttosolve.com), where a Lean 4 proof checker, not a person, decides what counts. It grows out of two earlier playgrounds:

- [Fleurdelys](https://shadowalzazel.github.io/fleurdelys-math/): zeta flowers, Newton dynamics, prime spectra, Collatz cycles.
- [Black Swan Jeweled Math](https://shadowalzazel.github.io/black-swan-jeweled-math/): SAT landscapes, golden rotations, quasicrystals, aperiodic tilings.

Like those two, this repository records failures and controls alongside wins, and tags every claim as **proven** (checked by Lean or in the literature), **open**, or **observed** (seen in our code, not proven).

## Results

| Problem | Lean | Left to Solve | Notes |
| --- | --- | --- | --- |
| [Shanks: infinitely many record prime gaps](results/shanks-record-gaps/) | ✅ fully verified | [MaximalPrimeGap.infinite_maximalPrimeGapIndex](https://lefttosolve.com/p/MaximalPrimeGap.infinite_maximalPrimeGapIndex) | Pipeline warmup. Already solved upstream; no credit. |
| [Li's criterion](results/li-criterion/) | 🟡 partial / conditional | [RiemannHypothesis.li_criterion](https://lefttosolve.com/p/RiemannHypothesis.li_criterion) | Both directions in Lean, assuming only Hadamard summability \(\sum m(\rho)/\|\rho\|^2 < \infty\). No real zeros of \(\zeta\) in \((0,1)\) is a theorem. Not a Left to Solve credit. |
| [OEIS A127752](results/a127752/) | ✅ fully verified | [oeis-a127752](https://lefttosolve.com/p/oeis-a127752) | Proven for all \(n\). Upstream still lists the entry as unformalized, so no credit match yet. Also covers [oeis-a127751](https://lefttosolve.com/p/oeis-a127751). |

Each result folder holds a mathematician-readable [PROOF.md](results/shanks-record-gaps/PROOF.md) beside its Lean file. The public site is [shadowalzazel.github.io/Fang-and-Fox-Lemma-Office](https://shadowalzazel.github.io/Fang-and-Fox-Lemma-Office/). Older public page URLs still work: a tiny stub at the former path redirects to `results/<slug>/`.

## How this repo works

`main` is the permanent record. It was rewritten exactly once, on November 26, 2026, to move our commits onto our own GitHub accounts; the files did not change and old commit hashes are remapped in STATUS.md. Work happens on short-lived branches like `kumi/<topic>` or `alo/<topic>`. A result reaches `main` only after the other agent independently rebuilds it. Claims live in [STATUS.md](STATUS.md).

A GitHub Action on every push and pull request to `main` rebuilds every `results/**/*.lean` against [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at 9097e2f (Lean/Mathlib v4.33.1), rejects `sorry`, `admit` and `native_decide`, and checks that `#print axioms` uses only `propext`, `Classical.choice` and `Quot.sound`.

## The rule of two halves

Every target ships as a pair:

1. **The story**: a written proof a working mathematician can follow step by step, led by the picture that made us believe it (`PROOF.md`, and a page or `story.tex` when we have one).
2. **The receipt**: a Lean 4 file whose named lemmas mirror the story's steps one for one.

A proof that checks but cannot be followed is only half done. A story that reads well but does not check is not done at all. See [METHOD.md](METHOD.md).

## Where to look

| File | What it holds |
| --- | --- |
| [TARGETS.md](TARGETS.md) | The problems we picked, ranked, with difficulty, status and why each fits |
| [STATUS.md](STATUS.md) | Who is working on what right now, the tracker against Left to Solve, and the push log |
| [IDEAS.md](IDEAS.md) | The bridges between our pictures and the problems: the synthesis we hope to add |
| [METHOD.md](METHOD.md) | Workflow, roles, the honesty checklist and how submission works |
| [CLAIMING.md](CLAIMING.md) | How we prepare a Left to Solve claim. Arbiter opens every upstream pull request himself. |
| `results/<id>/` | One folder per result: `PROOF.md`, Lean, `notes.md`, `figures/`, and the page |

## Who does what

- **ShadowAlzazel**: picks the problem, supplies the intuition and the pictures, has the last word on the story.
- **Kumi-San**: numerics, experiments and Mathlib lemma hunting.
- **Alo** ([@AlephTwooo](https://github.com/AlephTwooo)): Lean drafting alongside Kumi-San, the honesty checks, and keeping the story and the receipt in step.
- **Claude** (a Claude Code cloud session that ShadowAlzazel runs in the MasterCloud environment, which has Lean ready): writes the Lean receipt from a finished paper proof when Kumi-San or Alo has not started it, runs the upstream checker, and pushes the claim branch. See [METHOD.md](METHOD.md#the-claude-lean-lane).

Project-wide license: not yet selected.
