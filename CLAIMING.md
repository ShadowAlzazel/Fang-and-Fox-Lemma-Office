# Claiming a Left to Solve problem

A short playbook for turning a Lemma Office proof into a Left to Solve credit. The worked example is OEIS A127752: statement drafts in [`results/a127752/claim/`](results/a127752/claim/), and PR 1 opened by ShadowAlzazel as [GuillaumeBAUD-coder/open-math-agents#4276](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4276).

Upstream repo: [GuillaumeBAUD-coder/open-math-agents](https://github.com/GuillaumeBAUD-coder/open-math-agents).  
Our fork (already exists): [ShadowAlzazel/open-math-agents](https://github.com/ShadowAlzazel/open-math-agents), with Kumiho-San as a collaborator.  
Site: [lefttosolve.com](https://lefttosolve.com). Join notes: [lefttosolve.com/join](https://lefttosolve.com/join).

Nothing in this file is a submission. We prepare branches and drafts; **Arbiter opens every upstream pull request** from his own GitHub account.

## Checklist

1. Claim the draft files in [STATUS.md](STATUS.md). One owner per file; Alo reviews.
2. Write the Lean as `*.lean.txt` under `results/<id>/claim/` (see [.lean.txt](#the-leantxt-trick)).
3. Lint and compile locally with their `tools/lint.py` and `tools/check.sh` against formal-conjectures `9097e2f` at `/tmp/fcpin`.
4. Alo independently rebuilds and signs off. Do not send Arbiter a compare link until she has.
5. Kumi cuts a branch from **upstream** `main` on the fork, adds exactly one file, and pushes that branch only (no force, no pull request).
6. Arbiter opens the pull request from the compare URL, signed in as ShadowAlzazel. He does not need to review the Lean.
7. If the problem was unformalized: wait for PR 1 to merge, then repeat steps 5–6 for the proof (PR 2). If a statement already exists, this is the only pull request.
8. Optional: take a lease; add an OEIS comment in Arbiter's own words; mint a Zenodo DOI.

## Who gets credit

Left to Solve credits the **GitHub account that authored the merged pull request** (upstream README, "Credit policy": that account is the solver of record). The `Agent:` and `Model:` lines in the pull request body are metadata only.

So the pull request must be opened by **ShadowAlzazel**. Commits on the branch may be by Kumiho-San; that does not move the credit. Never open the upstream pull request from a Kumiho-San or Alo account.

## Two pull requests, or one

Look up the problem on lefttosolve.com and in the upstream catalogue (`data/catalog.json`, plus `data/extra.json` / `extra2.json` for the long tail).

- **Unformalized** (no Lean statement yet, as with `oeis-a127752`): two pull requests.
  1. **PR 1, the statement.** Exactly one new file, `statements/<id>.lean`. CI checks that it compiles. A person then reviews the translation (`needs-human-review`) before merging.
  2. **PR 2, the proof.** Only after PR 1 is merged. Exactly one new file, `proofs/<id>.lean`. CI lints it, compiles it against formal-conjectures `9097e2f` (Lean v4.33.1), and audits axioms. An accepted proof of an open problem also gets `needs-human-review` and is **not auto-merged**.
- **Statement already exists** (in formal-conjectures, or already merged under `statements/`): a **single proof pull request**, `proofs/<id>.lean`. Skip PR 1.

Each pull request must add exactly one file and change nothing else. You can open PR 2 before PR 1 merges, but their CI will reject it until the statement is on upstream `main`.

## File names, namespaces, first-line import

`<id>` is the Left to Solve problem id (letters, digits, `_ . ' -` only). A sanitized copy `S_<id>` replaces every non-alphanumeric character with `_` (so `oeis-a127752` becomes `S_oeis_a127752`).

**Statement** (`statements/<id>.lean`):

- First line: `import Mathlib` (or `import Mathlib.Foo.Bar`); only Mathlib imports after that.
- Opens `namespace OMA.S_<id>` and closes with `end OMA.S_<id>`.
- Exactly one `theorem main : <the actual statement> := by sorry`. That is the only `sorry`, and the only theorem or lemma.
- Definitions must be complete. `main` may not be a placeholder (`sorry`, `True`, `False`).

**Proof** (`proofs/<id>.lean`), for a statement we contributed:

- First line must be exactly `import OMAStatements.S_<id>`. Only Mathlib imports may follow.
- Exactly one `theorem OMA.solution : type_of% @OMA.S_<id>.main := ...` (or `OMA.disproof : ¬ (type_of% @OMA.S_<id>.main) := ...`), and no other mention of those names.
- Do not mention the upstream declaration except inside that `type_of% @...` form.
- No `sorry`.

If the problem already had a formal-conjectures statement, the first line is `import <catalogue module>` instead, and `OMA.solution` is `type_of% @<upstream decl>`.

## Lint bans

Their `tools/lint.py` is a static gate, run on the file after comments are stripped. It is stricter than our own CI. In particular it rejects:

- `sorry` (except the single `sorry` in a statement's `theorem main`), `admit`, `axiom`, `axioms`, `native_decide`, `unsafe`, `partial`, `opaque`, `implemented_by`, `extern`
- every `#` command (`#print`, `#eval`, `#check`, `#reduce`, …) — so **do not** leave a `#print axioms` in a submitted file
- `macro` / `syntax` / `elab` / `notation` / `infix` / `prefix` / `postfix`, `initialize`, `run_cmd`, `run_tac`, `run_elab`, `by_elab`, `attribute`, `declare_*`, `meta`, `IO`, `import Lean`
- `Lean.Elab`, `Lean.Meta`, `Lean.Compiler`, and related trusted APIs; `decide := true`
- any double-quote character (no string literals)
- attributes other than `@[simp]` and `@[local simp]`
- `set_option`, except a numeric `maxHeartbeats` / `maxRecDepth` / `synthInstance.maxHeartbeats` / `synthInstance.maxSize` scoped with `in`
- files larger than 512 KiB, or not UTF-8

Our checker still wants axioms limited to `propext`, `Classical.choice` and `Quot.sound`. A statement is allowed the extra `sorryAx` from its one `sorry`.

## The `.lean.txt` trick

Store drafts in this repo as `results/<id>/claim/statements/<id>.lean.txt` and `results/<id>/claim/proofs/<id>.lean.txt`. When the file goes upstream, drop the `.txt`.

Our Action (`.github/workflows/lean.yml`) compiles every `results/**/*.lean` and rejects `sorry`. A statement file must contain exactly one `sorry`, so it cannot live here as `.lean`. A proof file starts with `import OMAStatements.S_<id>`, which exists only inside the Left to Solve checker, so it would also fail our CI. The `.txt` suffix keeps both out of that glob. Copy the bytes unchanged; do not re-type them.

## Local lint and check

The pin is formal-conjectures commit `9097e2f90e66d2f6244209cb1c07f7120d17ec53` (Lean / Mathlib v4.33.1), checked out at `/tmp/fcpin` on this machine. Their `tools/check.sh` will refuse to run if `OMA_FC` is at any other commit.

Run everything from a checkout of `open-math-agents` (the fork or a throwaway clone of upstream), after placing the draft at the upstream path **without** `.txt`. `check.sh` already runs `lint.py`, but running lint alone first is faster when it fails.

```bash
export PATH="$HOME/.elan/bin:$PATH"
export OMA_FC=/tmp/fcpin
git -C /tmp/fcpin rev-parse HEAD
# must print 9097e2f90e66d2f6244209cb1c07f7120d17ec53

cd /path/to/open-math-agents

# statement
cp /path/to/Fang-and-Fox-Lemma-Office/results/<id>/claim/statements/<id>.lean.txt statements/<id>.lean
python3 -I tools/lint.py statements/<id>.lean data/catalog.json
tools/check.sh statements/<id>.lean
# want: "accepted" / "the statement compiles; it now needs a human review of the translation"
# axioms may be [propext, sorryAx, Classical.choice, Quot.sound]

# proof (the statement file must already be at statements/<id>.lean, or lint will reject the proof)
cp /path/to/Fang-and-Fox-Lemma-Office/results/<id>/claim/proofs/<id>.lean.txt proofs/<id>.lean
python3 -I tools/lint.py proofs/<id>.lean data/catalog.json
tools/check.sh proofs/<id>.lean
# want: "accepted" / "kernel accepted; axioms within propext, Classical.choice, Quot.sound"
```

Do not commit those copies on the fork's `main`. They belong on a fresh topic branch, one file per branch.

## Alo's review gate

Alo rebuilds each file with the same `tools/check.sh` and `/tmp/fcpin` pin, on her own checkout, and reads the statement against the source (OEIS, paper, Left to Solve page). A compare link goes to Arbiter only after she signs off. For A127752 she independently accepted all four drafts on 2026-11-26.

## Fast path (this is what worked)

The fork [ShadowAlzazel/open-math-agents](https://github.com/ShadowAlzazel/open-math-agents) already exists, and Kumiho-San is a collaborator. Arbiter does not need to fork again.

Kumi prepares the branch. Cut it from **upstream** `main`, not from the fork's `main`: this repo moves every few minutes, and the fork lags. Add exactly one file, push only that branch, and do not force-push.

```bash
workdir=/tmp/open-math-agents-fork
git init "$workdir" && cd "$workdir"
git remote add origin https://github.com/ShadowAlzazel/open-math-agents.git
git remote add upstream https://github.com/GuillaumeBAUD-coder/open-math-agents.git
git fetch --depth 1 --no-tags upstream main
git checkout -b oma/<id>-statement FETCH_HEAD

cp /path/to/Fang-and-Fox-Lemma-Office/results/<id>/claim/statements/<id>.lean.txt statements/<id>.lean
cmp /path/to/Fang-and-Fox-Lemma-Office/results/<id>/claim/statements/<id>.lean.txt statements/<id>.lean
sha256sum statements/<id>.lean   # must match the draft

git add statements/<id>.lean
git -c user.name='Kumiho-San' -c user.email='361845516+Kumiho-San@users.noreply.github.com' \
  commit -m '<id>: Lean statement'

# authenticate as Kumiho-San via http.extraheader basic auth (token from the environment,
# never printed, never committed, never forced)
git push origin oma/<id>-statement
```

Use `oma/<id>` for the proof branch. Confirm the compare view shows **exactly one file changed**. If upstream moved in the meantime, GitHub may say the branches have diverged (1 ahead, N behind); that is still fine if the only file in the diff is ours. Do not rebase with a force-push unless Arbiter explicitly says to.

Then send Arbiter the compare URL. He opens the pull request himself, signed in as ShadowAlzazel. He does not need to review the Lean.

```
https://github.com/GuillaumeBAUD-coder/open-math-agents/compare/main...ShadowAlzazel:open-math-agents:<branch>
```

Title the pull request `<id>` (for example `oeis-a127752`). Paste the body from the templates below. For A127752, this is how PR 1 became [#4276](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4276).

## Do not write with the GitHub connector

The `user-GitHub-xai` connector can *read* as ShadowAlzazel (`get_me` returns that login, and it has a `create_pull_request` tool), but writes fail with `403 Resource not accessible by integration`. It also has no sync-fork / merge-upstream tool. Do not use it to create branches, commit, or open pull requests. Prepare with git as Kumiho-San; let Arbiter open the pull request from the compare URL.

## Pull request body templates

Statement (PR 1):

```
Lease: <lease, or delete this line>
Agent: Fang and Fox Lemma Office (Kumi-San, Alo)
Model: <optional>

Problem: https://lefttosolve.com/p/<id>
First Lean statement of <one-line description of the claim>.
Checked locally with tools/lint.py and tools/check.sh at formal-conjectures 9097e2f: compiles,
with one sorry, the body of main.
```

Proof (PR 2, or the only pull request when a statement already exists):

```
Lease: <lease, or delete this line>
Agent: Fang and Fox Lemma Office (Kumi-San, Alo)
Model: <optional>

Problem: https://lefttosolve.com/p/<id>
Proof of <one-line description of the argument>.
Checked locally with tools/check.sh: accepted, axioms propext, Classical.choice, Quot.sound.
Write-up: https://shadowalzazel.github.io/Fang-and-Fox-Lemma-Office/results/<id>/
```

## PR 2 only after PR 1 merges

For an unformalized problem, do not cut the proof branch until PR 1 is on upstream `main`. Then fetch upstream `main` again (so the merged statement is in the tree their CI will see), add only `proofs/<id>.lean`, and hand Arbiter a fresh compare URL. Their bot should comment that the checker accepted the proof and that it needs human review. A maintainer merges it; that merge is the credit, in ShadowAlzazel's name.

## Optional lease

`join.txt` asks contributors to open pull requests only for a problem they hold. CI does not enforce this, but it is polite. A lease is a plain HTTP call with Arbiter's GitHub login as the handle:

```bash
curl -s 'https://lefttosolve.com/api/desk/next?handle=ShadowAlzazel&agent=fang-and-fox&problem=<id>'
```

Save the `lease` value for the pull request body. Send a beat every 5 minutes while work is in flight (`POST https://lefttosolve.com/api/desk/beat?lease=<lease>`), and release it when the pull request is opened (`POST .../api/desk/release?lease=<lease>&reason=submitted`). If you skip the lease, delete the `Lease:` line from the body. We did not take one for A127752.

## OEIS

This is Arbiter's, on his own account, in his own words. A new OEIS account needs an editor's approval and can take a while. Once he is in, he edits the sequence (for A127752, [oeis.org/A127752](https://oeis.org/A127752)), adds a comment and a link to the write-up, and submits it for the editors to review. Facts he can draw on live in the claim kit (for A127752, [`results/a127752/claim/OEIS-comment-draft.md`](results/a127752/claim/OEIS-comment-draft.md)); he should not paste that draft, because the OEIS rejects AI-written text.

## Optional Zenodo DOI

A GitHub release of this repo can be archived on [Zenodo](https://zenodo.org) for a permanent DOI: sign in with GitHub, enable Fang-and-Fox-Lemma-Office under GitHub → Repositories, then create a release such as `<id>-v1`. Add the DOI to the OEIS comment and the write-up page if we make one.
