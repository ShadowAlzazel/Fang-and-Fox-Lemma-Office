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

## The Claude Lean lane

Added 2026-11-28, at ShadowAlzazel's request, after the A402341 proof was formalized this way in one session. The goal is speed (lesson 1 in [CLAIMING.md](CLAIMING.md#lessons-from-a127750--a127752-2026-11-28): the first accepted proof wins) and spreading model usage across agents.

**When.** A paper proof is done (story step 4, ideally reviewed by Alo), and nobody has claimed the Lean receipt in [STATUS.md](STATUS.md) within a few hours, or ShadowAlzazel asks for it directly. Kumi-San and Alo keep first call; if one of them has claimed the receipt, Claude does not start a second one.

**Where.** A Claude Code cloud session in ShadowAlzazel's **MasterCloud** environment. Its setup script ([tools/lean-setup.sh](tools/lean-setup.sh), the same text) installs Lean v4.33.1 at `/opt/lean` and formal-conjectures at the pin `9097e2f` in `/opt/lean/fc` with the Mathlib cache, so the checker runs without setup. The environment allows lefttosolve.com and the Lean and Mathlib download hosts.

**How.**

1. Claim the receipt in STATUS.md (owner: Claude).
2. Read the paper proof (`results/<id>/…journey.md` or `PROOF.md`) and the merged upstream statement. Formalize it step by step, one named lemma per step where it helps, and prefer a homogenized or elementary form over new machinery (A402341 avoided Laurent polynomials by working with (1 + X)^(2D) and X^J).
3. Check it with the site's own tools from a fresh clone of upstream, exactly as their CI does:

   ```bash
   export PATH="$HOME/.elan/bin:$PATH"
   git clone --depth 1 https://github.com/lefttosolve2/open-math-agents oma && cd oma
   cp /path/to/proof.lean proofs/<id>.lean
   python3 -I tools/lint.py proofs/<id>.lean data/catalog.json
   OMA_FC=/opt/lean/fc tools/check.sh proofs/<id>.lean
   # want: accepted, kernel accepted; axioms within propext, Classical.choice, Quot.sound
   ```

4. Save the file as `results/<id>/claim/proofs/<id>.lean.txt` with the checker log in `results/<id>/claim/checker-logs/`, and log it in STATUS.md.
5. Push a one-file branch `oma/<id>-proof`, cut from upstream `main`, to the fork, and give ShadowAlzazel the compare URL, title and body. ShadowAlzazel opens the pull request; credit follows the account that opens it.
6. Release the claim.

**Review.** For a proof file, the upstream checker is the referee: if the kernel accepts it against the merged statement, it proves that statement. So the pull request does not wait for a rebuild. Alo (or Kumi-San) still rebuilds it independently afterwards for our record, as for any receipt, and notes the result in STATUS.md. A **statement** is different: a machine cannot check a translation, so Alo's honesty check on a statement stays before submission.
