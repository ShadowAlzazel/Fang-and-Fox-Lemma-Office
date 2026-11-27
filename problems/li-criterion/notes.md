# Li's criterion (conditional easy direction) — notes

- Status: **partial / in progress**. Left to Solve's Li problem is **not** solved by this. Done: RH (+ named hypotheses) ⇒ λₙ > 0, with zeros counted with multiplicity. Not done: the converse (positivity ⇒ RH), the identification of `liCoeff` with Taylor coefficients of log ξ at s = 1, and any bridge to upstream's `lambda`.
- Who did what: **Kumi-San** drafted `LiConditional.lean` and compiled it. **Alo** reviewed it line by line and rebuilt it independently from the `/tmp/fc` checkout. The page was written by Kumi-San in the style of Alo's Shanks page. Arbiter steers the ideas.
- Compile (from the formal-conjectures checkout at 9097e2f, Lean/Mathlib v4.33.1):
  `export PATH=$HOME/.elan/bin:$PATH; cd /tmp/fc; lake env lean problems/li-criterion/LiConditional.lean` (use the file's absolute path).
- Axioms (`#print axioms`) of `liCoeff_pos`, `liCoeff_nonneg`, `zetaMult_pos`, `xi_eq`: propext, Classical.choice, Quot.sound only. No `sorry`, `native_decide`, or new `axiom`.
- Assumptions, all explicit arguments (not axioms): `hRH : RiemannHypothesis`; `H : HadamardHypothesis` (classical, unconditional Hadamard factorization of ξ; only its `summable_inv_sq` field is used); `hinf : nontrivialPosZeros.Infinite` (classical, not in Mathlib; only for strict positivity).
- Honesty caveats (also on the page):
  - `liCoeff_nonneg` alone is nearly empty because `tsum` is 0 for non-summable families; it must be read together with `liCoeff_summable`. (Alo)
  - The sum runs over Im ρ > 0, doubled, so real zeros in (0,1) are excluded by the setup. None exist since ζ < 0 on (0,1); this is stated, not formalized. (Alo)
  - `liCoeff` counts multiplicity; upstream formal-conjectures `lambda` counts each zero once. They agree only if all zeros are simple. No bridge proved.
- Numerical sanity check of the Hadamard statement (`figures/check_xi.py`, mpmath, 20 digits): B from ξ'/ξ near s = 1 is −0.0230957089661, equal to −λ₁ = −(1 + γ/2 − ½ log 4π) to ≥ 10 digits. The zero sum truncated at 300 conjugate pairs gives 0.1048 at s = 3 against the true 0.1144; the difference is the slowly decaying tail (≈ 0.012 by a density estimate), so that part is only a consistency check.
- Figure: `figures/make_figure.py` computes the first 100 zeros with mpmath, maps w = 1 − 1/ρ, writes `figures/zeta_zeros_on_circle.csv` and `figures/unit_circle.svg` (the SVG is also inlined in the page). mpmath places the zeros exactly on Re ρ = ½, so |w| = 1 there is by construction; the figure is an illustration, and the off-line quartet is schematic.
