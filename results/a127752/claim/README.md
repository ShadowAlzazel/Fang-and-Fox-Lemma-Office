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
Alo reviewed and independently rebuilt all four on 2026-11-26 with a fresh checkout of open-math-agents@4d8b8ac (newer than the 33bf6f4 used above) and her own formal-conjectures copy at 9097e2f: both statements accepted (compile, one sorry) and both proofs kernel-accepted with axioms propext, Classical.choice, Quot.sound. Statements read faithfully against the OEIS entries, including the 0-based/1-based offset. The closed form in the OEIS draft matches the recursion for n < 5000 (paper fact, not Lean).
