# How to claim A127752 on Left to Solve (for ShadowAlzazel)

Everything in this folder is a **draft**. The Lean drafts are stored as `*.lean.txt`, because our own CI
(`.github/workflows/lean.yml`) compiles every `results/**/*.lean` and rejects `sorry`, and a statement file must
contain exactly one. When you create the file upstream, name it **without** the `.txt` (for example
`statements/oeis-a127752.lean`) and paste the contents unchanged. Nothing has been opened, posted or submitted. Every step below
happens from **your own** accounts, because Left to Solve credits the GitHub account that authored the
merged pull request (README, "Credit policy"), and the OEIS only accepts edits from a registered person.

Upstream repo: https://github.com/GuillaumeBAUD-coder/open-math-agents
Problem pages: https://lefttosolve.com/p/oeis-a127752 and https://lefttosolve.com/p/oeis-a127751

## Why two pull requests

`oeis-a127752` has no Lean statement upstream (catalogue kind "unformalized", from `data/extra2.json`). The rules
(README "Problems without a Lean statement", `statements/README.md`, `tools/lint.py`):

1. **PR 1, the statement:** exactly one new file, `statements/oeis-a127752.lean`. It imports Mathlib only, opens
   `namespace OMA.S_oeis_a127752`, and has exactly one `sorry`, which is the body of `theorem main`.
   CI checks that it compiles. Then **a person reviews it** (label `needs-human-review`) before merging.
2. **PR 2, the proof:** only after PR 1 is merged. Exactly one new file, `proofs/oeis-a127752.lean`. The first
   line must be `import OMAStatements.S_oeis_a127752` and the file holds exactly one
   `theorem OMA.solution : type_of% @OMA.S_oeis_a127752.main := ...`. CI lints the file, compiles it against
   formal-conjectures `9097e2f` (Lean v4.33.1) and audits the axioms. Because the problem is "open",
   an accepted proof also gets `needs-human-review` and is **not auto-merged**. A maintainer merges it.

You can open PR 2 before PR 1 merges, but CI will reject it until the statement is on `main`.

## Step 0: optional, take a lease

join.txt asks contributors to open PRs only "for a problem you hold". CI doesn't enforce this, but it's polite.
A lease is a plain HTTP call with your GitHub login as the handle:

    curl -s 'https://lefttosolve.com/api/desk/next?handle=ShadowAlzazel&agent=fang-and-fox&problem=oeis-a127752'

Save the `lease` value from the reply for the PR body. Send a beat every 5 minutes while you work
(`POST https://lefttosolve.com/api/desk/beat?lease=<lease>`), and release it when you're done
(`POST .../api/desk/release?lease=<lease>&reason=submitted`). If you skip leasing, leave the Lease line out.

## Step 1: PR 1 (statement), in the GitHub web UI

1. Open https://github.com/GuillaumeBAUD-coder/open-math-agents and click **Fork**, signed in as ShadowAlzazel.
2. In your fork, click **Add file → Create new file** and name it `statements/oeis-a127752.lean`.
3. Paste in the contents of `results/a127752/claim/statements/oeis-a127752.lean.txt` from our repo, unchanged.
4. Commit to a **new branch**, for example `oma/oeis-a127752-statement`, then click **Propose changes / Create pull request**
   against `GuillaumeBAUD-coder/open-math-agents:main`.
5. Title: `oeis-a127752`
6. Body:

        Lease: <lease, or delete this line>
        Agent: Fang and Fox Lemma Office (Kumi-San, Alo)
        Model: <optional>

        Problem: https://lefttosolve.com/p/oeis-a127752
        First Lean statement of the OEIS A127752 conjecture: a(n) mod 2 = A035263(n+1)
        (A127752 is 0-based, A035263 is 1-based, as the OEIS entry notes).
        The triangle is truncated to any size N; main quantifies over every N and every row n < N, and also
        asserts that the row sum is an integer, since a(n) mod 2 presupposes that.
        Checked locally with tools/lint.py and tools/check.sh at formal-conjectures 9097e2f: compiles,
        with one sorry, the body of main.

The PR must add **exactly one file and change nothing else**. Don't touch README, data or anything else.

## Step 2: PR 2 (proof), after PR 1 is merged

1. In your fork, sync `main` with upstream (**Sync fork**), so the merged statement is in your fork.
2. Create `proofs/oeis-a127752.lean` on a new branch, for example `oma/oeis-a127752`. Paste the contents of
   `results/a127752/claim/proofs/oeis-a127752.lean.txt` unchanged.
3. Open a PR to upstream `main`. Title: `oeis-a127752`. Body:

        Lease: <lease, or delete this line>
        Agent: Fang and Fox Lemma Office (Kumi-San, Alo)
        Model: <optional>

        Problem: https://lefttosolve.com/p/oeis-a127752
        Proof of the conjecture: the window identity sum_(ceil(n/2)<=k<=n) a(k) = 3n+1 gives the doubling recursion
        a(0)=1, a(2m+1)=a(m)+3, a(2m+2)=3, and by strong induction a(n) mod 2 = A035263(n+1).
        Checked locally with tools/check.sh: accepted, axioms propext, Classical.choice, Quot.sound.
        Write-up: https://shadowalzazel.github.io/Fang-and-Fox-Lemma-Office/results/a127752/

4. Wait for the bot's verdict comment. "ACCEPTED by the Lean checker … needs-human-review" is the expected result.
   A maintainer then merges it, and the credit goes to the PR author, ShadowAlzazel.

## Optional: A127751 (a separate catalogue entry)

`oeis-a127751` is its own problem on Left to Solve with its own id. The conjecture text is the same: "Row sums
A127752 mod 2 are conjectured to be … A035263". The same two-PR process works with the files
`statements/oeis-a127751.lean` and `proofs/oeis-a127751.lean`, titled `oeis-a127751`. Both drafts are ready.
Expect the reviewer to ask whether it duplicates A127752. They might merge it, close it as a duplicate, or ask
for a single statement. It's honest to say so in the PR body: "Same conjecture as oeis-a127752, recorded in
the triangle's entry."

## Step 3: OEIS

1. Sign in at https://oeis.org with your OEIS account. Registration is needed, and approval of a new
   account can take a while.
2. Open A127752 and click **edit**. Add a comment and a link in **your own words**. Use the facts in
   `OEIS-comment-draft.md`, but don't paste it, because the OEIS does not accept AI-written text.
3. Submit the edit for the editors' review, and optionally do the same for A127751.

## Step 4: optional, a permanent DOI

1. Sign in to https://zenodo.org with GitHub and enable the Fang-and-Fox-Lemma-Office repo under **GitHub → Repositories**.
2. Create a GitHub release of the repo, for example `a127752-v1`. Zenodo archives it and mints a DOI.
3. Add the DOI to the OEIS link and the write-up page.

## What we checked locally (so nothing surprises you)

- `tools/lint.py`: all four files pass.
- `tools/check.sh` with `OMA_FC` set to formal-conjectures at `9097e2f90e66` (Lean v4.33.1, the same Mathlib the CI uses):
  - The statements are "accepted - the statement compiles; it now needs a human review". Their axioms are
    `[propext, sorryAx, Classical.choice, Quot.sound]`, where sorryAx is the one allowed sorry.
  - The proofs are "accepted - kernel accepted". Their axioms are `[propext, Classical.choice, Quot.sound]`.
- Alo reviewed and independently rebuilt all four on 2026-11-26 with a fresh checkout of open-math-agents@4d8b8ac (newer than the 33bf6f4 used above) and her own formal-conjectures copy at 9097e2f: both statements accepted (compile, one sorry) and both proofs kernel-accepted with axioms propext, Classical.choice, Quot.sound. Statements read faithfully against the OEIS entries, including the 0-based/1-based offset. The closed form in the OEIS draft matches the recursion for n < 5000 (paper fact, not Lean).
