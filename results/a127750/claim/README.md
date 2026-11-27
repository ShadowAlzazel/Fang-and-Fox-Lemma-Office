# A127750: Left to Solve claim kit (drafts, nothing submitted)

| File | Upstream path (name it without `.txt`) | Local check |
| --- | --- | --- |
| `statements/oeis-a127750.lean.txt` | `statements/oeis-a127750.lean` | lint ok; check.sh: statement compiles (one sorry) |
| `proofs/oeis-a127750.lean.txt` | `proofs/oeis-a127750.lean` | lint ok; check.sh: accepted, axioms propext, Classical.choice, Quot.sound |
| `PROOF.md` | proof sketch | n/a |
| `HOW-TO-CLAIM.md` | steps for Arbiter | n/a |
| `checker-logs/` | outputs of upstream `tools/lint.py` and `tools/check.sh` | n/a |

Checked against GuillaumeBAUD-coder/open-math-agents@0babb05 and formal-conjectures 9097e2f (Lean v4.33.1) on 2026-11-27.
The files are `.lean.txt` so our own CI skips them (see [CLAIMING.md](../../../CLAIMING.md)). Not yet independently rebuilt by Alo.
