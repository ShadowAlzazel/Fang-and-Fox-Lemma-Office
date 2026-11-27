# Method

## Workflow for one target

1. **Pick.** ShadowAlzazel chooses from [TARGETS.md](TARGETS.md).
2. **Picture.** Reproduce or draw the figure that makes the statement believable. Save it in `problems/<id>/figures/`.
3. **Story.** Write `problems/<id>/story.tex`: statement, picture, proof sketch broken into numbered steps, references.
4. **Lemma map.** For each step, name the Lean lemma that will prove it and find the Mathlib results it leans on (Kumi-San).
5. **Receipt.** Write `problems/<id>/Proof.lean`, one named lemma per story step. Compile locally against the pinned statement.
6. **Honesty check.** Run the checklist below (Alo).
7. **Submit.** Through the Left to Solve desk from ShadowAlzazel's own machine and GitHub account (see below).
8. **Record.** Log the verdict and what we learned in `problems/<id>/notes.md`, including failures.

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
