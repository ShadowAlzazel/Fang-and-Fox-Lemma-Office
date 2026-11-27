# Fang & Fox Lemma Office

Pretty, followable proofs. Intuition first, Lean 4 as the receipt.

This is the shared workroom of ShadowAlzazel, Alo and Kumi-San for attacking problems from [Left to Solve](https://lefttosolve.com), where a Lean 4 proof checker, not a person, decides what counts. It grows out of two earlier playgrounds:

- [Fleurdelys](https://shadowalzazel.github.io/fleurdelys-math/): zeta flowers, Newton dynamics, prime spectra, Collatz cycles.
- [Black Swan Jeweled Math](https://shadowalzazel.github.io/black-swan-jeweled-math/): SAT landscapes, golden rotations, quasicrystals, aperiodic tilings.

Like those two, this repository records failures and controls alongside wins, and tags every claim as **proven** (checked by Lean or in the literature), **open**, or **observed** (seen in our code, not proven).

## The rule of two halves

Every target ships as a pair:

1. **The story**: a LaTeX write-up a working mathematician can follow step by step, led by the picture that made us believe it.
2. **The receipt**: a single Lean 4 file whose named lemmas mirror the story's steps one for one.

A proof that checks but cannot be followed is only half done. A story that reads well but does not check is not done at all. See [METHOD.md](METHOD.md).

## Where to look

| File | What it holds |
| --- | --- |
| [TARGETS.md (and live claims in [STATUS.md](STATUS.md))](TARGETS.md) | The problems we picked, ranked, with difficulty, status and why each fits |
| [IDEAS.md](IDEAS.md) | The bridges between our pictures and the problems: the synthesis we hope to add |
| [METHOD.md](METHOD.md) | Workflow, roles, the honesty checklist and how submission works |
| `problems/<id>/` | One folder per target: `story.tex`, `Proof.lean`, `notes.md`, `figures/` |

## Who does what

- **ShadowAlzazel**: picks the problem, supplies the intuition and the pictures, has the last word on the story.
- **Kumi-San**: numerics, experiments and Mathlib lemma hunting.
- **Alo**: Lean drafting alongside Kumi-San, the honesty checks, and keeping the story and the receipt in step.

## Status

Nothing submitted yet. First target: the Shanks warmup to test the pipeline, then Li's Criterion.

Project-wide license: not yet selected.
