# Li's criterion (both directions, conditional) — notes

- Status: **partial: both directions, conditional**. Left to Solve's `li_criterion` is **not** solved by this. Done: RH ⇔ λₙ ≥ 0 for the multiplicity-weighted sum `liCoeff`, given two named hypotheses. Not done: the identification of λₙ with the Taylor coefficients of log ξ at s = 1; the upstream statement (strict inequality, both directions, no hypotheses).
- Files: `LiCriterion.lean` is the complete development (Parts I and II). `LiConditional.lean` is the earlier Part I file, kept for the record; every Part I lemma still appears, under the same name, in `LiCriterion.lean`.
- Who did what: **Kumi-San** drafted and compiled both halves. **Alo** reviewed Part I line by line and rebuilt it independently from the `/tmp/fc` checkout; Alo rebuilt Part II independently too (commit 69721f2, same checkout): it compiles cleanly, has no `sorry`, `admit` or `native_decide`, and all five headline theorems use only propext, Classical.choice and Quot.sound. She also checked that both hypotheses are true classical statements, so the results are not vacuous; the converse never uses `log_deriv_expansion`. The page was written by Kumi-San in the style of Alo's Shanks page. Arbiter steers the ideas.
- Compile (from the formal-conjectures checkout at 9097e2f, Lean/Mathlib v4.33.1):
  `export PATH=$HOME/.elan/bin:$PATH; cd /tmp/fc; lake env lean /absolute/path/to/LiCriterion.lean`
  Zero errors, zero warnings. `grep -n sorry` is empty.
- Axioms (`#print axioms`) of `li_converse`, `li_criterion_weighted`, `li_converse_unweighted`, `exists_neg_of_large`, `liCoeff_pos`: propext, Classical.choice, Quot.sound only. No `sorry`, `native_decide`, or new `axiom`.
- Assumptions, all explicit arguments (not axioms):
  - `H : HadamardHypothesis` — classical, unconditional Hadamard factorization of ξ. Only the multiplicity-weighted summability field `summable_inv_sq` (Σ m(ρ)/|ρ|² < ∞) is used, in both directions. The `log_deriv_expansion` field is stated but unused.
  - `hreal : NoRealZerosInStrip` — no real zeros of ζ in (0,1); classical via the Dirichlet η function, not in Mathlib. Used by the converse.
  - `hinf : nontrivialPosZeros.Infinite` — classical, not in Mathlib; used only for the strict inequality in `liCoeff_pos`, not for the equivalence with ≥ 0.
- Honesty caveats (also on the page):
  - (a) The equivalence RH ⇔ λₙ ≥ 0 is proved given those first two named hypotheses, not unconditionally.
  - (b) The deep half of Li — λₙ as Taylor coefficients of log ξ at 1, computable without the zeros — is not formalized.
  - (c) This is not a credit solve of upstream `li_criterion` (strict > 0, both directions, no hypotheses).
  - (d) The `log_deriv_expansion` field is unused.
  - `liCoeff_nonneg` alone is nearly empty because `tsum` is 0 for non-summable families; it must be read together with `liCoeff_summable`. (Alo)
  - The sum runs over Im ρ > 0, doubled, so real zeros in (0,1) are excluded by the setup; the converse now takes `NoRealZerosInStrip` as a named hypothesis. The fact is still not proved in the file. (Alo)
  - `liCoeff` counts multiplicity; upstream `lambda` counts each zero once. `li_converse_unweighted` gives the converse for the unweighted sum on its own terms; no identification is proved.
- Numerical sanity check of the Hadamard statement (`figures/check_xi.py`, mpmath, 20 digits): B from ξ'/ξ near s = 1 is −0.0230957089661, equal to −λ₁ = −(1 + γ/2 − ½ log 4π) to ≥ 10 digits. The zero sum truncated at 300 conjugate pairs gives 0.1048 at s = 3 against the true 0.1144; the difference is the slowly decaying tail (≈ 0.012 by a density estimate), so that part is only a consistency check.
- Figure: `figures/make_figure.py` computes the first 100 zeros with mpmath, maps w = 1 − 1/ρ, writes `figures/zeta_zeros_on_circle.csv` and `figures/unit_circle.svg` (the SVG is also inlined in the page). mpmath places the zeros exactly on Re ρ = ½, so |w| = 1 there is by construction; the figure is an illustration, and the off-line quartet is schematic. The zoom panel is labelled “×2000, both axes.”
