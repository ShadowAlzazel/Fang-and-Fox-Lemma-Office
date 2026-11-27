# Method

`main` is the permanent, never-rewritten record. Work happens on short-lived branches like `kumi/<topic>` or `alo/<topic>`. A result reaches `main` only after the other of us independently rebuilds the Lean. Claims live in [STATUS.md](STATUS.md).

## Workflow for one target

0. **Claim.** Before touching a problem or file, add a row to [STATUS.md](STATUS.md); remove it and log the commit when you push. One owner per file at a time.
1. **Pick.** ShadowAlzazel chooses from [TARGETS.md](TARGETS.md).
2. **Branch.** Open a short-lived `kumi/<topic>` or `alo/<topic>` branch; do not draft on `main`.
3. **Picture.** Reproduce or draw the figure that makes the statement believable. Save it in `results/<id>/figures/`.
4. **Story.** Write `results/<id>/PROOF.md` (and `story.tex` or the page when we have one): statement, picture, proof sketch broken into numbered steps, references, and the honesty caveats.
5. **Lemma map.** For each step, name the Lean lemma that will prove it and find the Mathlib results it leans on (Kumi-San).
6. **Receipt.** Write the Lean file in `results/<id>/`, one named lemma per story step. Compile locally against formal-conjectures at 9097e2f (Lean/Mathlib v4.33.1).
7. **Honesty check.** Run the checklist below (Alo). The other of us independently rebuilds the Lean before it is merged to `main`.
8. **Submit.** Through the Left to Solve desk from ShadowAlzazel's own machine and GitHub account (see below).
9. **Record.** Log the verdict and what we learned in `results/<id>/notes.md`, including failures.

## Honesty checklist

- Is every claim tagged **proven**, **open** or **observed**?
- Does each story step have a matching Lean lemma, and does each lemma's statement say what the step says?
- Did we prove what the site states (for example Li's *equivalence*, not RH)?
- Does the look-alike test pass? Try the claim on L(s, χ₄) and Davenport–Heilbronn; a property that also holds for Davenport–Heilbronn cannot be what forces RH.
- Before calling an idea new, did we search the literature for it?
- No `sorry`, and no axioms beyond `propext`, `Classical.choice`, `Quot.sound`.

## Submission (Left to Solve)

- Join instructions: <https://lefttosolve.com/join>. Accepted proofs are merged into the site's public repository and credited by GitHub handle.
- Needs Lean with Mathlib (about 10 GB), `elan`, `git` and `gh` signed in as ShadowAlzazel. Turn on GitHub's "Keep my email addresses private" before the first pull request.
- Only the Lean file is public through the site. Stories stay here until ShadowAlzazel decides to publish them.
