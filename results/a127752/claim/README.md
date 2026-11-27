# A127752: Left to Solve claim kit (drafts, nothing submitted)

| File | Upstream path (name it without `.txt`) | Local check |
| --- | --- | --- |
| `statements/oeis-a127752.lean.txt` | `statements/oeis-a127752.lean` | lint ok; check.sh: statement compiles (one sorry) |
| `proofs/oeis-a127752.lean.txt` | `proofs/oeis-a127752.lean` | lint ok; check.sh: accepted, axioms propext, Classical.choice, Quot.sound |
| `statements/oeis-a127751.lean.txt` | `statements/oeis-a127751.lean` | lint ok; check.sh: statement compiles (one sorry) |
| `proofs/oeis-a127751.lean.txt` | `proofs/oeis-a127751.lean` | lint ok; check.sh: accepted, axioms propext, Classical.choice, Quot.sound |
| `OEIS-comment-draft.md` | facts for ShadowAlzazel to rewrite in his own words | n/a |
| `HOW-TO-CLAIM.md` | the step-by-step guide (PRs from his own account, then OEIS, then an optional DOI) | n/a |
| `checker-logs/` | outputs of upstream `tools/lint.py` and `tools/check.sh` | n/a |

The checks ran with the upstream checker from GuillaumeBAUD-coder/open-math-agents@33bf6f4, against
formal-conjectures 9097e2f (Lean v4.33.1).
The files are `.lean.txt` so our own CI doesn't try to build them: statements must contain a `sorry`, and the
proofs import `OMAStatements.*`, which exists only inside the Left to Solve checker.
The proof is adapted from `results/a127752/A127752.lean`, using the same argument against the upstream statement's definitions.
Review by Alo is pending.
