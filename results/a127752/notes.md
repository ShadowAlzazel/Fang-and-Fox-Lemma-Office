# OEIS A127752 (row sums mod 2 = period-doubling sequence): notes

- Status: **proven in Lean, all n** (`A127752.a127752_mod_two`). Upstream: Left to Solve [`oeis-a127752`](https://lefttosolve.com/p/oeis-a127752) is "unformalized" and unsolved, unclaimed as of 2026-11-26 (rechecked via the LtS API at 20:58 PST). The sibling [`oeis-a127751`](https://lefttosolve.com/p/oeis-a127751) states the same conjecture and is covered by the same theorem. This is **not** an upstream credit match: google-deepmind/formal-conjectures (at 9097e2f) has no statement for it yet.
- OEIS A127752 `%N`, verbatim: "Row sums of inverse of number triangle A(n,k) = 1/(3n+1) if k <= n <= 2k, 0 otherwise." Offset 0.
- Conjecture, verbatim: "a(n) mod 2 is first Feigenbaum symbolic sequence A035263 (conjecture)." and "The conjecture is true at least up to 2048 first terms. (But please note the different indexing, here 0-based.)" (Antti Karttunen, 2018).
- A035263 `%N`, verbatim: "Trajectory of 1 under the morphism 0 -> 11, 1 -> 10; parity of 2-adic valuation of 2n: a(n) = A000035(A001511(n))." Offset 1.
- Precise statement proved: for all n ≥ 0, a(n) is an integer and a(n) ≡ A035263(n+1) = ν₂(2(n+1)) (mod 2).
- Proof (lemma names in `A127752.lean`):
  1. A·a = 𝟙 for the row sums a = A⁻¹𝟙, i.e. Σ_{⌈n/2⌉ ≤ k ≤ n} a(k) = 3n+1 (`tri_mulVec_r`, `blockSum_r`).
  2. Sliding the window gives a(0) = 1, a(2m+2) = 3, a(2m+1) = a(m) + 3 (`r`).
  3. Each truncation is lower triangular with diagonal 1/(3n+1) ≠ 0, so the solution is unique and a = r for every truncation containing row n (`tri_lower`, `tri_det_isUnit`, `rowSum_inv_tri`, `a127752_eq_r`).
  4. Mod 2: a(2m) ≡ 1, a(2m+1) ≡ 1 + a(m), so a(n) ≡ 1 + ν₂(n+1) (`r_mod_two`, headline `a127752_mod_two`).
  - Closed form (numerics only, not in Lean): a(2ᵏ − 1) = 3k + 1, otherwise a(n) = 3ν₂(n+1) + 3.
- Who did what: **Kumi-San** wrote the proof, the Lean file, `check.py`, the figures and the page. **Alo** independently rebuilt the file, checked the definitions against OEIS and checked the doubling step by hand. Done for **ShadowAlzazel**.
- Compile: `export PATH=$HOME/.elan/bin:$PATH; cd /tmp/fc; lake env lean /absolute/path/to/A127752.lean` (Lean 4 + Mathlib v4.33.1; only `import Mathlib`). Zero errors, zero warnings, about 6 s. No `sorry`, `admit`, `native_decide` or new `axiom`.
- Axioms (`#print axioms`) of `a127752_mod_two`, `a127752_eq_r`, `r_mod_two`: propext, Classical.choice, Quot.sound only.
- Guards (`#guard`, evaluation only, used by no proof): `r` matches all 106 terms of the OEIS data section; `A035263 (n+1)` matches the first 34 OEIS terms of A035263; a computable exact inverse of the 40×40 triangle satisfies A·B = I with row sums equal to the OEIS terms. Changing one OEIS digit makes three guards fail.
- Numerics (`check.py`, exact fractions): inverse for N = 250 has integer row sums equal to `r`; all 2,049 b-file terms match; the conjecture, the Black Swan form 1 − (ν₂(n+1) mod 2), and the closed form hold for all n < 10⁶.
- Honesty caveats (also on the page):
  - (a) A035263 is defined via ν₂ from its OEIS name, not via the morphism 0 → 11, 1 → 10; their equivalence is not formalized.
  - (b) a(n) is defined with the (n+1)×(n+1) truncation; `rowSum_inv_tri` shows any larger truncation gives the same value. The determinant is proved a unit, so Mathlib's "singular inverse = 0" convention never applies.
  - (c) Index shift: A127752(n) ↔ A035263(n+1).
  - (d) Not an upstream credit match: no formal-conjectures statement exists yet; upstream may pick other conventions.
  - (e) Covers `oeis-a127751` too.
- Black Swan link: the Feigenbaum kneading word RLRRRLRL… is ν₂(j) mod 2 with R = "ν₂(j) even" (`CALLBACKS_AND_NEXT_STEPS.md` §4). The halving window makes the recursion a renormalization step: one flip per factor of 2.
- Next, observed only: with 2n+1 instead of 3n+1 the same argument gives constant 2 and parity 1 exactly at n = 2ᵏ − 1, i.e. Fredholm–Rueppel A036987, which is the conjecture on [`oeis-a127750`](https://lefttosolve.com/p/oeis-a127750). Checked for 80 terms; not in Lean.
- Figures: `figures/make_figure.py` (pure Python) writes `a_of_n.svg` and `parity.svg`, both inlined in the page. Illustrations only.
