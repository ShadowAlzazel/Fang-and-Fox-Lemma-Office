import FormalConjectures.Paper.RiemannHypothesisEquivalents

/-!
# Li's criterion, multiplicity-weighted: both directions, conditional on Hadamard summability

**Human proof sketch.**  Put `w(ρ) = 1 - 1/ρ = (ρ - 1)/ρ`, the Möbius map used by Li.

* *(unconditional)* If `Re ρ = 1/2` then `|ρ - 1| = |ρ|`, so `|w(ρ)| = 1`: the critical line goes
  to the unit circle.  For `|w| = 1` and any `n`, `Re (1 - wⁿ) = |1 - wⁿ|²/2 ≥ 0`.
  Moreover `|1 - wⁿ| ≤ n |1 - w| = n/|ρ|`, so `Re (1 - wⁿ) ≤ n²/(2|ρ|²)`.
* Hence under RH every term of `liCoeff n = ∑_ρ m(ρ) · 2 Re (1 - w(ρ)ⁿ)` is `≥ 0` – so
  `0 ≤ liCoeff n` (a `tsum` of nonnegative terms).
* For strict positivity we need (i) summability, which follows from the bound above and the
  classical convergence of `∑ m(ρ)/|ρ|²` (part of `HadamardHypothesis`), and (ii) one zero with
  `w(ρ)ⁿ ≠ 1`.  Since `ρ ↦ w(ρ)` is injective and there are only `n` many `n`-th roots of unity,
  infinitely many zeros (`hinf`, a classical fact not in Mathlib) give such a zero.

**Part II – the converse (Bombieri–Lagarias style), `li_converse`.**
Assume `∑ m(ρ)/|ρ|² < ∞` (`HadamardHypothesis.summable_inv_sq`) and that `0 ≤ λₙ` for all `n ≥ 1`.

* *Zeros off the line can be pushed left* (`exists_posZero_re_lt_half`).  A zero violating RH lies
  in the strip (`re_pos_of_zeta_eq_zero`: the functional equation kills `Re s ≤ 0` except at the
  trivial zeros; `riemannZeta_ne_zero_of_one_le_re` kills `Re s ≥ 1`); it is not real
  (`NoRealZerosInStrip`, a classical fact stated as an explicit hypothesis); after conjugation
  (`riemannZeta_conj`) it has `Im > 0`; and after the reflection `ρ ↦ 1 - ρ̄`
  (`zeta_one_sub_conj_eq_zero`, from `Λ(1-s) = Λ(s)`) it has `Re ρ < 1/2`.
* *Left of the line means outside the circle* (`one_lt_norm_one_sub_inv`):
  `Re ρ < 1/2 ⇔ |ρ - 1| > |ρ| ⇔ |w(ρ)| > 1`.
* *A dominant ring of zeros* (`exists_neg_of_large`, abstract).  Write `uᵢ = 1 - wᵢ = 1/ρᵢ`.
  Summability of `∑ mᵢ |uᵢ|²` with `mᵢ ≥ 1` forces `|uᵢ| → 0`, so only finitely many `wᵢ` have
  `|wᵢ| ≥ r` for any `r > 1`.  Hence `R = max |wᵢ| > 1` is attained on a finite set `S`, and all
  other `wᵢ` satisfy `|wᵢ| ≤ r < R`.
* *Second-order Taylor control of the tail* (`norm_one_sub_pow_sub_le`, `abs_re_one_sub_pow_le`):
  `|1 - wⁿ - n u| ≤ n² Mⁿ |u|²` for `|w| ≤ M`, `M ≥ 1`, and `|Re u| ≤ |u|²` (as `0 < Re ρ < 1`),
  so `|Re (1 - wⁿ)| ≤ (n + n² Mⁿ) |u|²`.  The non-dominant zeros contribute at most
  `(n + n² rⁿ) · ∑ mᵢ|uᵢ|²`, and the Li series converges absolutely for every `n` (no RH needed).
* *Kronecker–Dirichlet return* (`exists_pow_near_one`): for finitely many unit complex numbers
  `zᵢ = wᵢ/R` (`i ∈ S`) and any `N`, some `d ≥ N` has every `zᵢ^d` within `1/2` of `1`
  (compactness of the torus + pigeonhole along `k ↦ (zᵢ^{Nk})`).  Then `Re wᵢ^d ≥ R^d/2` on `S`.
* *Conclusion*: `λ_d/2 ≤ (∑_S mᵢ)(1 - R^d/2) + (d + d² r^d) ∑ mᵢ|uᵢ|² < 0` for `d` large, because
  `R^d` beats `d² r^d` (`r < R`).  Contradiction with `0 ≤ λ_d`.

The same engine with all weights `1` gives `li_converse_unweighted` for the upstream
`RiemannHypothesis.lambda` (the "←" half of the upstream `li_criterion`, conditionally).

Only the *summability* field of `HadamardHypothesis` is used, in both directions; the `ξ'/ξ`
expansion would only be needed to identify `liCoeff n` with the Taylor coefficients of `log ξ`
at `s = 1` (the "bridge"), which is still **not** done here.

The main theorems take `NoRealZerosInStrip` (`ζ(σ) ≠ 0` for `0 < σ < 1`) as an explicit hypothesis.
That fact is classical — via `(1 - 2^{1-σ}) ζ(σ) = η(σ) > 0` — but Mathlib has no Dirichlet `η`,
so it is not proved in this file.

Nothing here assumes RH or Li's criterion except where a theorem's hypothesis says `RiemannHypothesis`.
-/

open Complex

namespace LiConditional

open RiemannHypothesis (nontrivialPosZeros)

/- ### Definitions -/

/-- All nontrivial zeros of `ζ` (both signs of the imaginary part): `0 < Re ρ < 1`, `ζ ρ = 0`. -/
def nontrivialZeros : Set ℂ := {z | 0 < z.re ∧ z.re < 1 ∧ riemannZeta z = 0}

lemma nontrivialPosZeros_subset : nontrivialPosZeros ⊆ nontrivialZeros :=
  fun _ h => ⟨h.1, h.2.1, h.2.2.2⟩

/-- The multiplicity of `ρ` as a zero of `ζ` (analytic order at `ρ`; `ζ` is analytic away from
`1`, and not identically zero, so for a zero this is the usual finite positive multiplicity). -/
noncomputable def zetaMult (ρ : ℂ) : ℕ := analyticOrderNatAt riemannZeta ρ

/-- **Multiplicity-weighted Li coefficient**
`λₙ = ∑_{ρ, Im ρ > 0} m(ρ) · 2 Re (1 - (1 - 1/ρ)ⁿ)`,
summing over nontrivial zeros with positive imaginary part, each counted with multiplicity. -/
noncomputable def liCoeff (n : ℕ) : ℝ :=
  ∑' ρ : nontrivialPosZeros, (zetaMult ρ.1 : ℝ) * (2 * (1 - (1 - 1 / ρ.1) ^ n).re)

/-- The completed zeta function `ξ(s) = ½ (1 + s(s-1) Λ₀(s))`, entire, equal to
`½ s (s-1) π^{-s/2} Γ(s/2) ζ(s)` for `s ≠ 0, 1`.  (Built from Mathlib's entire `Λ₀`, so no junk
values at `s = 0, 1`: `ξ 0 = ξ 1 = 1/2`.) -/
noncomputable def xi (s : ℂ) : ℂ := (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2

/-- Sanity check: `xi` is the usual `½ s (s-1) Λ(s)` away from `s = 0, 1`. -/
lemma xi_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xi s = s * (s - 1) * completedRiemannZeta s / 2 := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hs2 : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [xi, completedRiemannZeta_eq]
  field_simp
  ring

/-- **The analytic input, as an explicit assumption** (the Hadamard factorization of `ξ`,
a classical *theorem* since 1893 that Mathlib does not have; it is true unconditionally and does
*not* involve RH).  Two parts, both about all nontrivial zeros counted with multiplicity:

1. `summable_inv_sq`: `∑ m(ρ)/|ρ|² < ∞` (finite order ≤ 1 of `ξ`);
2. `log_deriv_expansion`: for some constant `B`, for every `s` with `ξ s ≠ 0`,
   `ξ'(s)/ξ(s) = B + ∑_ρ m(ρ) (1/(s-ρ) + 1/ρ)` (convergent sum).

The easy direction of Li uses only (1).  (2) is what the bridge to `log ξ` Taylor coefficients
would use. -/
structure HadamardHypothesis : Prop where
  summable_inv_sq :
    Summable fun ρ : nontrivialZeros => (zetaMult ρ.1 : ℝ) / ‖ρ.1‖ ^ 2
  log_deriv_expansion :
    ∃ B : ℂ, ∀ s : ℂ, xi s ≠ 0 →
      HasSum (fun ρ : nontrivialZeros => (zetaMult ρ.1 : ℂ) * (1 / (s - ρ.1) + 1 / ρ.1))
        (deriv xi s / xi s - B)

/- ### Unconditional facts about the Möbius map `ρ ↦ 1 - 1/ρ` -/

/-- On the critical line, `|ρ - 1| = |ρ|`. -/
lemma norm_sub_one_eq_of_re_half {ρ : ℂ} (h : ρ.re = 1 / 2) : ‖ρ - 1‖ = ‖ρ‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp [h]
  ring

/-- **Möbius fact**: for `Re ρ = 1/2` (so `ρ ≠ 0`), `|1 - 1/ρ| = 1`. -/
lemma norm_one_sub_inv_eq_one {ρ : ℂ} (h : ρ.re = 1 / 2) : ‖1 - 1 / ρ‖ = 1 := by
  have hρ : ρ ≠ 0 := by
    intro h0; rw [h0] at h; simp at h
  have : 1 - 1 / ρ = (ρ - 1) / ρ := by field_simp
  rw [this, norm_div, norm_sub_one_eq_of_re_half h, div_self (norm_ne_zero_iff.mpr hρ)]

/-- For `|u| = 1`, `Re (1 - u) = |1 - u|² / 2`. -/
lemma re_one_sub_eq_norm_sq {u : ℂ} (hu : ‖u‖ = 1) : (1 - u).re = ‖1 - u‖ ^ 2 / 2 := by
  have h1 : u.re * u.re + u.im * u.im = 1 := by
    have := Complex.sq_norm u
    rw [hu, Complex.normSq_apply] at this
    linarith
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  nlinarith

/-- For `|w| = 1`, every `n`: `0 ≤ Re (1 - wⁿ)`. -/
lemma re_one_sub_pow_nonneg {w : ℂ} (hw : ‖w‖ = 1) (n : ℕ) : 0 ≤ (1 - w ^ n).re := by
  rw [re_one_sub_eq_norm_sq (by simp [hw])]
  positivity

/-- For `|w| = 1`: `Re (1 - wⁿ) > 0` as soon as `wⁿ ≠ 1`. -/
lemma re_one_sub_pow_pos {w : ℂ} (hw : ‖w‖ = 1) {n : ℕ} (h : w ^ n ≠ 1) :
    0 < (1 - w ^ n).re := by
  rw [re_one_sub_eq_norm_sq (by simp [hw])]
  have : ‖1 - w ^ n‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm h))
  positivity

/-- `|1 - wⁿ| ≤ n |1 - w|` when `|w| = 1` (geometric sum). -/
lemma norm_one_sub_pow_le {w : ℂ} (hw : ‖w‖ = 1) (n : ℕ) : ‖1 - w ^ n‖ ≤ n * ‖1 - w‖ := by
  have h : 1 - w ^ n = (∑ i ∈ Finset.range n, w ^ i) * (1 - w) := by
    have := geom_sum_mul w n
    linear_combination this
  rw [h, norm_mul]
  gcongr
  calc ‖∑ i ∈ Finset.range n, w ^ i‖ ≤ ∑ i ∈ Finset.range n, ‖w ^ i‖ := norm_sum_le _ _
    _ = n := by simp [hw]

/-- The quantitative bound used for summability: `Re (1 - wⁿ) ≤ n² |1 - w|² / 2`. -/
lemma re_one_sub_pow_le {w : ℂ} (hw : ‖w‖ = 1) (n : ℕ) :
    (1 - w ^ n).re ≤ (n : ℝ) ^ 2 * ‖1 - w‖ ^ 2 / 2 := by
  rw [re_one_sub_eq_norm_sq (by simp [hw])]
  have := norm_one_sub_pow_le hw n
  have h0 := norm_nonneg (1 - w ^ n)
  have : ‖1 - w ^ n‖ ^ 2 ≤ ((n : ℝ) * ‖1 - w‖) ^ 2 := by gcongr
  nlinarith

/- ### Zeros: multiplicity and RH -/

/-- Under RH a nontrivial zero lies on the critical line. -/
lemma re_eq_half_of_RH (hRH : RiemannHypothesis) {ρ : ℂ} (h : ρ ∈ nontrivialZeros) :
    ρ.re = 1 / 2 := by
  refine hRH ρ h.2.2 ?_ ?_
  · rintro ⟨k, hk⟩
    have := h.1
    rw [hk] at this
    simp at this
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  · rintro rfl
    exact absurd h.2.1 (by simp)

/-- A nontrivial zero with positive imaginary part has multiplicity `≥ 1`.
(Needs `ζ` not identically zero near `ρ`: identity theorem on the convex set
`{Re > 0, Im > 0}`, which avoids the pole at `1` and contains `2 + i`, where `ζ ≠ 0`.) -/
lemma zetaMult_pos {ρ : ℂ} (h : ρ ∈ nontrivialPosZeros) : 0 < zetaMult ρ := by
  have hρ1 : ρ ≠ 1 := by rintro rfl; exact absurd h.2.1 (by simp)
  have hd : DifferentiableOn ℂ riemannZeta {(1 : ℂ)}ᶜ :=
    fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt
  have hall : AnalyticOnNhd ℂ riemannZeta {(1 : ℂ)}ᶜ := hd.analyticOnNhd isOpen_compl_singleton
  have hana : AnalyticAt ℂ riemannZeta ρ := hall ρ hρ1
  set U : Set ℂ := {s | 0 < s.re ∧ 0 < s.im} with hU
  have hUc : Convex ℝ U := (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)
  have hUana : AnalyticOnNhd ℂ riemannZeta U := by
    intro s hs
    exact hall s (by rintro rfl; exact absurd hs.2 (by simp))
  have hρU : ρ ∈ U := ⟨h.1, h.2.2.1⟩
  have hpt : (2 + Complex.I) ∈ U := by simp [hU]
  have hne : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have := hUana.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc.isPreconnected hρU htop hpt
    exact riemannZeta_ne_zero_of_one_le_re (s := 2 + Complex.I) (by simp) this
  have hpos : analyticOrderAt riemannZeta ρ ≠ 0 := by
    rw [Ne, analyticOrderAt_eq_zero]
    push Not
    exact ⟨hana, h.2.2.2⟩
  unfold zetaMult analyticOrderNatAt
  exact ENat.toNat_pos hpos hne

/- ### The easy direction -/

/-- Under RH each term of the Li sum is `≥ 0`. -/
lemma liTerm_nonneg (hRH : RiemannHypothesis) (n : ℕ) (ρ : nontrivialPosZeros) :
    0 ≤ (zetaMult ρ.1 : ℝ) * (2 * (1 - (1 - 1 / ρ.1) ^ n).re) := by
  have h := norm_one_sub_inv_eq_one (re_eq_half_of_RH hRH (nontrivialPosZeros_subset ρ.2))
  have := re_one_sub_pow_nonneg h n
  positivity

/-- **RH ⇒ `0 ≤ λₙ`** (needs no analytic hypothesis: a `tsum` of nonnegative terms). -/
theorem liCoeff_nonneg (hRH : RiemannHypothesis) (n : ℕ) : 0 ≤ liCoeff n :=
  tsum_nonneg (liTerm_nonneg hRH n)

/-- Under RH and `HadamardHypothesis` the Li series converges absolutely. -/
theorem liCoeff_summable (hRH : RiemannHypothesis) (H : HadamardHypothesis) (n : ℕ) :
    Summable fun ρ : nontrivialPosZeros =>
      (zetaMult ρ.1 : ℝ) * (2 * (1 - (1 - 1 / ρ.1) ^ n).re) := by
  have hsub : Summable fun ρ : nontrivialPosZeros => (zetaMult ρ.1 : ℝ) / ‖ρ.1‖ ^ 2 := by
    have := H.summable_inv_sq.comp_injective
      (Set.inclusion_injective nontrivialPosZeros_subset)
    exact this
  refine Summable.of_nonneg_of_le (liTerm_nonneg hRH n) (fun ρ => ?_) (hsub.mul_left ((n : ℝ) ^ 2))
  have hre := re_eq_half_of_RH hRH (nontrivialPosZeros_subset ρ.2)
  have hw := norm_one_sub_inv_eq_one hre
  have hρ : ρ.1 ≠ 0 := by intro h0; have := ρ.2.1; rw [h0] at this; simp at this
  have h1 : ‖1 - (1 - 1 / ρ.1)‖ = 1 / ‖ρ.1‖ := by simp
  have := re_one_sub_pow_le hw n
  rw [h1] at this
  have hm : (0 : ℝ) ≤ zetaMult ρ.1 := Nat.cast_nonneg _
  calc (zetaMult ρ.1 : ℝ) * (2 * (1 - (1 - 1 / ρ.1) ^ n).re)
      ≤ (zetaMult ρ.1 : ℝ) * (2 * ((n : ℝ) ^ 2 * (1 / ‖ρ.1‖) ^ 2 / 2)) := by gcongr
    _ = (n : ℝ) ^ 2 * ((zetaMult ρ.1 : ℝ) / ‖ρ.1‖ ^ 2) := by
        field_simp

/-- **RH ⇒ `0 < λₙ`** for `n ≥ 1`, from RH, the Hadamard-type summability hypothesis, and
infinitely many zeros in the upper half of the strip (`hinf`; classical, but not in Mathlib,
so stated as an explicit hypothesis). -/
theorem liCoeff_pos (hRH : RiemannHypothesis) (H : HadamardHypothesis)
    (hinf : nontrivialPosZeros.Infinite) {n : ℕ} (hn : 0 < n) : 0 < liCoeff n := by
  -- some zero has `w ^ n ≠ 1`
  have hex : ∃ ρ : nontrivialPosZeros, (1 - 1 / ρ.1) ^ n ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hfin : nontrivialPosZeros.Finite := by
      refine Set.Finite.of_injOn (f := fun ρ : ℂ => 1 - 1 / ρ)
        (t := ((Polynomial.nthRootsFinset n (1 : ℂ) : Finset ℂ) : Set ℂ)) ?_ ?_
        (Finset.finite_toSet _)
      · intro ρ hρ
        simpa [Polynomial.mem_nthRootsFinset hn] using hcon ⟨ρ, hρ⟩
      · intro ρ hρ ρ' hρ' heq
        have a : ρ ≠ 0 := by intro h0; have := hρ.1; rw [h0] at this; simp at this
        have b : ρ' ≠ 0 := by intro h0; have := hρ'.1; rw [h0] at this; simp at this
        have : 1 / ρ = 1 / ρ' := by simpa using heq
        simpa [a, b] using this
    exact hinf hfin
  obtain ⟨ρ₀, hρ₀⟩ := hex
  have hw := norm_one_sub_inv_eq_one (re_eq_half_of_RH hRH (nontrivialPosZeros_subset ρ₀.2))
  have hpos : 0 < (zetaMult ρ₀.1 : ℝ) * (2 * (1 - (1 - 1 / ρ₀.1) ^ n).re) := by
    have := re_one_sub_pow_pos hw hρ₀
    have hm : (0 : ℝ) < zetaMult ρ₀.1 := Nat.cast_pos.mpr (zetaMult_pos ρ₀.2)
    positivity
  exact (liCoeff_summable hRH H n).tsum_pos (liTerm_nonneg hRH n) ρ₀ hpos

/- ## Part II: the converse, Li ⇒ RH -/

/- ### The abstract analytic engine -/

/-- **Kronecker–Dirichlet return lemma** -/
lemma exists_pow_near_one {κ : Type*} [Fintype κ] (z : κ → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℕ, N ≤ d ∧ ∀ i, ‖z i ^ d - 1‖ < ε := by
  set v : ℕ → (κ → ℂ) := fun k i => z i ^ (N * k) with hvdef
  have hv : ∀ k, v k ∈ Metric.closedBall (0 : κ → ℂ) 1 := by
    intro k
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    simp [v, hz]
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : κ → ℂ) 1).tendsto_subseq hv
  obtain ⟨K, hK⟩ := Metric.cauchySeq_iff'.1 hlim.cauchySeq ε hε
  have hlt : φ K < φ (K + 1) := hφ (Nat.lt_succ_self K)
  refine ⟨N * (φ (K + 1) - φ K), ?_, fun i => ?_⟩
  · have : 1 ≤ φ (K + 1) - φ K := by omega
    calc N = N * 1 := by ring
      _ ≤ _ := Nat.mul_le_mul_left N this
  · have h := hK (K + 1) (by omega)
    have hi : ‖z i ^ (N * φ (K + 1)) - z i ^ (N * φ K)‖ < ε := by
      refine lt_of_le_of_lt ?_ h
      rw [← dist_eq_norm]
      exact dist_le_pi_dist (v (φ (K + 1))) (v (φ K)) i
    have hsplit : z i ^ (N * φ (K + 1)) = z i ^ (N * φ K) * z i ^ (N * (φ (K + 1) - φ K)) := by
      rw [← pow_add, ← Nat.mul_add, Nat.add_sub_cancel' hlt.le]
    rw [hsplit, ← mul_sub_one, norm_mul, norm_pow, hz, one_pow, one_mul] at hi
    exact hi

/-- `‖wⁱ - 1‖ ≤ n Mⁿ ‖1 - w‖` for `i ≤ n`, `‖w‖ ≤ M`, `1 ≤ M`. -/
lemma norm_pow_sub_one_le {w : ℂ} {M : ℝ} (hM : 1 ≤ M) (hw : ‖w‖ ≤ M) {i n : ℕ} (hi : i ≤ n) :
    ‖w ^ i - 1‖ ≤ n * M ^ n * ‖1 - w‖ := by
  have h : w ^ i - 1 = (∑ j ∈ Finset.range i, w ^ j) * (w - 1) := (geom_sum_mul w i).symm
  rw [h, norm_mul, norm_sub_rev w 1]
  gcongr
  calc ‖∑ j ∈ Finset.range i, w ^ j‖ ≤ ∑ j ∈ Finset.range i, ‖w ^ j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range i, M ^ n := by
        gcongr with j hj
        rw [norm_pow]
        calc ‖w‖ ^ j ≤ M ^ j := pow_le_pow_left₀ (norm_nonneg _) hw j
          _ ≤ M ^ n := pow_le_pow_right₀ hM (by simp at hj; omega)
    _ = i * M ^ n := by simp
    _ ≤ n * M ^ n := by gcongr

/-- Second-order Taylor bound: `‖1 - wⁿ - n(1-w)‖ ≤ n² Mⁿ ‖1-w‖²`. -/
lemma norm_one_sub_pow_sub_le {w : ℂ} {M : ℝ} (hM : 1 ≤ M) (hw : ‖w‖ ≤ M) (n : ℕ) :
    ‖1 - w ^ n - n * (1 - w)‖ ≤ (n : ℝ) ^ 2 * M ^ n * ‖1 - w‖ ^ 2 := by
  have h : 1 - w ^ n - n * (1 - w) = (1 - w) * ∑ i ∈ Finset.range n, (w ^ i - 1) := by
    have := geom_sum_mul w n
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    linear_combination this
  rw [h, norm_mul]
  have hs : ‖∑ i ∈ Finset.range n, (w ^ i - 1)‖ ≤ n * (n * M ^ n * ‖1 - w‖) := by
    calc _ ≤ ∑ i ∈ Finset.range n, ‖w ^ i - 1‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range n, (n * M ^ n * ‖1 - w‖) := by
          gcongr with i hi
          exact norm_pow_sub_one_le hM hw (by simp at hi; omega)
      _ = _ := by simp
  calc ‖1 - w‖ * ‖∑ i ∈ Finset.range n, (w ^ i - 1)‖ ≤ ‖1 - w‖ * (n * (n * M ^ n * ‖1 - w‖)) := by
        gcongr
    _ = _ := by ring

/-- Real-part bound used for the tail. -/
lemma abs_re_one_sub_pow_le {w : ℂ} {M : ℝ} (hM : 1 ≤ M) (hw : ‖w‖ ≤ M)
    (hre : |(1 - w).re| ≤ ‖1 - w‖ ^ 2) (n : ℕ) :
    |(1 - w ^ n).re| ≤ (n + (n : ℝ) ^ 2 * M ^ n) * ‖1 - w‖ ^ 2 := by
  have h1 := norm_one_sub_pow_sub_le hM hw n
  have h2 : |(1 - w ^ n - n * (1 - w)).re| ≤ ‖1 - w ^ n - n * (1 - w)‖ := abs_re_le_norm _
  have h3 : (1 - w ^ n).re = (1 - w ^ n - n * (1 - w)).re + n * (1 - w).re := by
    simp [Complex.sub_re, Complex.mul_re]
  rw [h3]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc _ ≤ |(1 - w ^ n - n * (1 - w)).re| + |(n : ℝ) * (1 - w).re| := abs_add_le _ _
    _ ≤ (n : ℝ) ^ 2 * M ^ n * ‖1 - w‖ ^ 2 + n * ‖1 - w‖ ^ 2 := by
        rw [abs_mul, abs_of_nonneg hn]
        gcongr
        linarith
    _ = _ := by ring

/-- **The abstract Bombieri–Lagarias lemma.** -/
theorem exists_neg_of_large {ι : Type*} (a : ι → ℝ) (w : ι → ℂ) (ha : ∀ i, 1 ≤ a i)
    (hsum : Summable fun i => a i * ‖1 - w i‖ ^ 2)
    (hre : ∀ i, |(1 - w i).re| ≤ ‖1 - w i‖ ^ 2)
    (hbig : ∃ i, 1 < ‖w i‖) :
    ∃ n : ℕ, 0 < n ∧ Summable (fun i => a i * (1 - w i ^ n).re) ∧
      ∑' i, a i * (1 - w i ^ n).re < 0 := by
  classical
  obtain ⟨i0, hi0⟩ := hbig
  have ha0 : ∀ i, 0 ≤ a i := fun i => by linarith [ha i]
  -- Step 1: only finitely many `w i` outside any disc of radius `r > 1`.
  have hfin : ∀ r : ℝ, 1 < r → {i | r ≤ ‖w i‖}.Finite := by
    intro r hr
    have hev : ∀ᶠ i in Filter.cofinite, a i * ‖1 - w i‖ ^ 2 < (r - 1) ^ 2 :=
      (tendsto_order.1 hsum.tendsto_cofinite_zero).2 _ (by nlinarith)
    refine (Filter.eventually_cofinite.1 hev).subset fun i hi => ?_
    simp only [Set.mem_ofPred_eq, not_lt] at hi ⊢
    have h1 : ‖w i‖ ≤ 1 + ‖1 - w i‖ := by
      calc ‖w i‖ = ‖1 - (1 - w i)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖(1 : ℂ)‖ + ‖1 - w i‖ := norm_sub_le _ _
        _ = _ := by simp
    have h3 : (r - 1) ^ 2 ≤ ‖1 - w i‖ ^ 2 := by gcongr; linarith
    nlinarith [ha i, sq_nonneg ‖1 - w i‖]
  -- Step 2: the maximal modulus `R > 1`, attained on a finite set `S`; the rest is `≤ r < R`.
  set r0 : ℝ := (1 + ‖w i0‖) / 2 with hr0
  have hr0gt : 1 < r0 := by linarith
  have hr0lt : r0 < ‖w i0‖ := by linarith
  set F := (hfin r0 hr0gt).toFinset with hF
  have hmemF : ∀ i, i ∈ F ↔ r0 ≤ ‖w i‖ := fun i => by simp [F]
  have hi0F : i0 ∈ F := (hmemF i0).2 hr0lt.le
  obtain ⟨i1, hi1F, hi1max⟩ := F.exists_max_image (fun i => ‖w i‖) ⟨i0, hi0F⟩
  set R := ‖w i1‖ with hRdef
  have hR1 : r0 < R := lt_of_lt_of_le hr0lt (hi1max i0 hi0F)
  have hR : ∀ i, ‖w i‖ ≤ R := by
    intro i
    by_cases hi : i ∈ F
    · exact hi1max i hi
    · rw [hmemF] at hi; linarith
  set S := F.filter (fun i => ‖w i‖ = R) with hS
  set G := F.filter (fun i => ‖w i‖ < R) with hG
  obtain ⟨r, hr0r, hrR, hrG⟩ : ∃ r, r0 ≤ r ∧ r < R ∧ ∀ i ∈ G, ‖w i‖ ≤ r := by
    rcases G.eq_empty_or_nonempty with hG0 | hG0
    · exact ⟨r0, le_rfl, hR1, by simp [hG0]⟩
    · obtain ⟨i2, hi2G, hi2⟩ := G.exists_max_image (fun i => ‖w i‖) hG0
      exact ⟨max r0 ‖w i2‖, le_max_left _ _, max_lt hR1 (Finset.mem_filter.1 hi2G).2,
        fun i hi => le_max_of_le_right (hi2 i hi)⟩
  have hnotS : ∀ i, i ∉ S → ‖w i‖ ≤ r := by
    intro i hi
    by_cases hiF : i ∈ F
    · have : ‖w i‖ ≠ R := fun h => hi (Finset.mem_filter.2 ⟨hiF, h⟩)
      exact hrG i (Finset.mem_filter.2 ⟨hiF, lt_of_le_of_ne (hR i) this⟩)
    · rw [hmemF] at hiF; linarith
  have hi1S : i1 ∈ S := Finset.mem_filter.2 ⟨hi1F, rfl⟩
  have hr1 : 1 ≤ r := by linarith
  have hRone : 1 ≤ R := by linarith
  have hRpos : 0 < R := by linarith
  -- Step 3: the dominant term `Rⁿ` beats `n² rⁿ` eventually.
  set T := ∑' i, a i * ‖1 - w i‖ ^ 2 with hTdef
  have hq1 : |1 / R| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one hRpos]; linarith
  have hq2 : |r / R| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one hRpos]; linarith
  have hlim : Filter.Tendsto (fun n : ℕ => (1 / R) ^ n + T * ((n : ℝ) ^ 1 * (1 / R) ^ n) +
      T * ((n : ℝ) ^ 2 * (r / R) ^ n)) Filter.atTop (nhds 0) := by
    have h1 := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq1
    have h2 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hq1
    have h3 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hq2
    simpa using (h1.add (h2.const_mul T)).add (h3.const_mul T)
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 hlim).2 (1 / 2) (by norm_num))
  -- Step 4: Kronecker–Dirichlet return: all `(w i / R)^d` near `1` for some `d ≥ N0 + 1`.
  have hzS : ∀ i : S, ‖w i.1 / (R : ℂ)‖ = 1 := by
    intro i
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hRpos.le,
      (Finset.mem_filter.1 i.2).2, div_self hRpos.ne']
  obtain ⟨d, hd, hdS⟩ := exists_pow_near_one (fun i : S => w i.1 / (R : ℂ)) hzS (N0 + 1)
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hdpos : 0 < d := by omega
  have hreS : ∀ i ∈ S, R ^ d / 2 ≤ (w i ^ d).re := by
    intro i hi
    have h := hdS ⟨i, hi⟩
    simp only at h
    set z := (w i / (R : ℂ)) ^ d
    have hz : 1 / 2 ≤ z.re := by
      have := abs_re_le_norm (z - 1)
      rw [Complex.sub_re, Complex.one_re] at this
      have := neg_abs_le (z.re - 1)
      linarith
    have hw : w i ^ d = ((R ^ d : ℝ) : ℂ) * z := by
      have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
      simp only [z, div_pow, Complex.ofReal_pow]
      field_simp
    rw [hw, Complex.re_ofReal_mul]
    have : 0 < R ^ d := by positivity
    nlinarith
  -- Step 5: summability and the final estimate.
  have hsumd : Summable (fun i => a i * (1 - w i ^ d).re) := by
    refine Summable.of_norm_bounded (hsum.mul_left ((d : ℝ) + (d : ℝ) ^ 2 * R ^ d)) fun i => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha0 i)]
    have := abs_re_one_sub_pow_le hRone (hR i) (hre i) d
    calc a i * |(1 - w i ^ d).re| ≤ a i * (((d : ℝ) + (d : ℝ) ^ 2 * R ^ d) * ‖1 - w i‖ ^ 2) := by
          gcongr; exact ha0 i
      _ = _ := by ring
  refine ⟨d, hdpos, hsumd, ?_⟩
  set e : ι → ℝ := fun i => if i ∈ S then a i * (1 - R ^ d / 2) else 0 with he_def
  set C : ℝ := (d : ℝ) + (d : ℝ) ^ 2 * r ^ d with hC
  have hC0 : 0 ≤ C := by positivity
  have hle : ∀ i, a i * (1 - w i ^ d).re ≤ e i + C * (a i * ‖1 - w i‖ ^ 2) := by
    intro i
    by_cases hiS : i ∈ S
    · have h := hreS i hiS
      simp only [e, if_pos hiS]
      have h' : (1 - w i ^ d).re = 1 - (w i ^ d).re := by simp
      rw [h']
      have : 0 ≤ C * (a i * ‖1 - w i‖ ^ 2) := by have := ha0 i; positivity
      nlinarith [ha0 i]
    · simp only [e, if_neg hiS, zero_add]
      have := abs_re_one_sub_pow_le hr1 (hnotS i hiS) (hre i) d
      calc a i * (1 - w i ^ d).re ≤ a i * |(1 - w i ^ d).re| := by
            gcongr; exacts [ha0 i, le_abs_self _]
        _ ≤ a i * (C * ‖1 - w i‖ ^ 2) := by gcongr; exact ha0 i
        _ = _ := by ring
  have he : Summable e := summable_of_ne_finset_zero (s := S) (fun i hi => by simp [e, hi])
  have htsum_e : ∑' i, e i = (∑ i ∈ S, a i) * (1 - R ^ d / 2) := by
    rw [tsum_eq_sum (s := S) (fun i hi => by simp [e, hi]), Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => by simp [e, hi]
  have hmain := hsumd.tsum_le_tsum hle (he.add (hsum.mul_left C))
  rw [he.tsum_add (hsum.mul_left C), tsum_mul_left, htsum_e] at hmain
  -- numerics
  have hA : 1 ≤ ∑ i ∈ S, a i :=
    le_trans (ha i1) (Finset.single_le_sum (fun i _ => ha0 i) hi1S)
  have hRd : 0 < R ^ d := by positivity
  have key : 1 + T * d + T * ((d : ℝ) ^ 2 * r ^ d) < R ^ d / 2 := by
    have h := mul_lt_mul_of_pos_right (hN0 d (by omega)) hRd
    have e1 : (1 / R) ^ d * R ^ d = 1 := by
      rw [div_pow, one_pow, div_mul_cancel₀ _ hRd.ne']
    have e2 : (r / R) ^ d * R ^ d = r ^ d := by
      rw [div_pow, div_mul_cancel₀ _ hRd.ne']
    have : ((1 / R) ^ d + T * ((d : ℝ) ^ 1 * (1 / R) ^ d) + T * ((d : ℝ) ^ 2 * (r / R) ^ d)) * R ^ d
        = (1 / R) ^ d * R ^ d + T * d * ((1 / R) ^ d * R ^ d) + T * d ^ 2 * ((r / R) ^ d * R ^ d) := by
      ring
    rw [this, e1, e2] at h
    linarith
  have hneg : (∑ i ∈ S, a i) * (1 - R ^ d / 2) ≤ 1 - R ^ d / 2 := by
    have hT0 : 0 ≤ T := tsum_nonneg fun i => mul_nonneg (ha0 i) (sq_nonneg _)
    have h1 : 0 ≤ T * d := by positivity
    have h2 : 0 ≤ T * ((d : ℝ) ^ 2 * r ^ d) := by have := hr1; positivity
    have : 1 - R ^ d / 2 ≤ 0 := by linarith
    nlinarith
  have : C * T = T * d + T * ((d : ℝ) ^ 2 * r ^ d) := by rw [hC]; ring
  linarith

/- ### Zeta-specific input: where the zeros can be -/

/-- No zeros of `ζ` in `Re s ≤ 0` apart from the trivial zeros (from the functional equation). -/
lemma re_pos_of_zeta_eq_zero {s : ℂ} (hz : riemannZeta s = 0)
    (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) : 0 < s.re := by
  by_contra hle
  push Not at hle
  have hs0 : s ≠ 0 := by
    rintro rfl; rw [riemannZeta_zero] at hz; norm_num at hz
  set t := 1 - s with ht
  have hst : s = 1 - t := by rw [ht]; ring
  have htre : 1 ≤ t.re := by simp [ht]; linarith
  have htn : ∀ n : ℕ, t ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have ht1 : t ≠ 1 := by intro h; apply hs0; rw [hst, h]; ring
  have hfe := riemannZeta_one_sub htn ht1
  rw [← hst, hz] at hfe
  have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  have hcpow : (2 * (Real.pi : ℂ)) ^ (-t) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero h2pi]; exact Complex.exp_ne_zero _
  have hG : Gamma t ≠ 0 := Complex.Gamma_ne_zero htn
  have hzt : riemannZeta t ≠ 0 := riemannZeta_ne_zero_of_one_le_re htre
  have hcos : cos ((Real.pi : ℂ) * t / 2) ≠ 0 := by
    intro hc
    obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.1 hc
    have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    have htk : t = 2 * k + 1 := by
      apply mul_left_cancel₀ hpi
      linear_combination 2 * hk
    have hsk : s = -2 * k := by rw [hst, htk]; ring
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · rcases m with _ | n
      · apply hs0; rw [hsk]; simp
      · exact htriv ⟨n, by rw [hsk]; push_cast; ring⟩
    · have := congrArg Complex.re hsk
      simp at this
      rcases m with _ | n
      · apply hs0; rw [hsk]; simp
      · have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        push_cast at *
        linarith
  have : (2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-t) * Gamma t * cos ((Real.pi : ℂ) * t / 2) * riemannZeta t ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hcpow) hG) hcos) hzt
  exact this hfe.symm

/-- In the critical strip, `ζ s = 0 ↔ Λ s = 0`. -/
lemma zeta_eq_zero_iff_completed {s : ℂ} (hs : 0 < s.re) :
    riemannZeta s = 0 ↔ completedRiemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff]
  have := Gammaℝ_ne_zero_of_re_pos hs
  tauto

/-- **Reflection symmetry of the zero set** `ρ ↦ 1 - ρ̄` (functional equation + conjugation). -/
lemma zeta_one_sub_conj_eq_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) : riemannZeta (1 - (starRingEnd ℂ) s) = 0 := by
  have hc : riemannZeta ((starRingEnd ℂ) s) = 0 := by rw [riemannZeta_conj, hz, map_zero]
  have hre1 : 0 < (1 - (starRingEnd ℂ) s).re := by simp; linarith
  have hre2 : 0 < ((starRingEnd ℂ) s).re := by simpa using h0
  rw [zeta_eq_zero_iff_completed hre1, completedRiemannZeta_one_sub,
    ← zeta_eq_zero_iff_completed hre2]
  exact hc

/-- **Classical fact, stated as an explicit hypothesis:** `ζ` has no real zeros in `(0, 1)`.
(Proof: `(1 - 2^{1-σ}) ζ(σ) = η(σ) = ∑ (-1)^{n-1} n^{-σ} > 0` by the alternating series test,
while `1 - 2^{1-σ} < 0`.)  This has nothing to do with RH: it is a statement about the real axis. -/
def NoRealZerosInStrip : Prop := ∀ σ : ℝ, 0 < σ → σ < 1 → riemannZeta σ ≠ 0

/-- If RH fails (and `ζ` has no real zeros in the strip) there is a zero with `Im ρ > 0` and
`Re ρ < 1/2`. -/
lemma exists_posZero_re_lt_half (hreal : NoRealZerosInStrip) (hRH : ¬ RiemannHypothesis) :
    ∃ ρ ∈ nontrivialPosZeros, ρ.re < 1 / 2 := by
  simp only [RiemannHypothesis, not_forall] at hRH
  obtain ⟨s, hz, htriv, -, hre⟩ := hRH
  have h0 := re_pos_of_zeta_eq_zero hz htriv
  have h1 : s.re < 1 := by
    by_contra h
    push Not at h
    exact riemannZeta_ne_zero_of_one_le_re h hz
  have him : s.im ≠ 0 := by
    intro him
    have hs : s = (s.re : ℂ) := Complex.ext (by simp) (by simp [him])
    exact hreal s.re h0 h1 (hs ▸ hz)
  obtain ⟨s', hz', h0', h1', him', hre'⟩ : ∃ s' : ℂ, riemannZeta s' = 0 ∧ 0 < s'.re ∧
      s'.re < 1 ∧ 0 < s'.im ∧ s'.re ≠ 1 / 2 := by
    rcases lt_or_gt_of_ne him with h | h
    · exact ⟨starRingEnd ℂ s, by rw [riemannZeta_conj, hz, map_zero], by simpa, by simpa,
        by simp; linarith, by simpa using hre⟩
    · exact ⟨s, hz, h0, h1, h, hre⟩
  rcases lt_or_gt_of_ne hre' with h | h
  · exact ⟨s', ⟨h0', h1', him', hz'⟩, h⟩
  · exact ⟨1 - starRingEnd ℂ s', ⟨by simp; linarith, by simp; linarith, by simpa using him',
      zeta_one_sub_conj_eq_zero h0' h1' hz'⟩, by simp; linarith⟩

/-- **Left of the line ⇔ outside the unit circle**: `Re ρ < 1/2 ⇒ |1 - 1/ρ| > 1`. -/
lemma one_lt_norm_one_sub_inv {ρ : ℂ} (h0 : 0 < ρ.re) (h : ρ.re < 1 / 2) :
    1 < ‖1 - 1 / ρ‖ := by
  have hρ : ρ ≠ 0 := by rintro rfl; simp at h0
  have e : 1 - 1 / ρ = (ρ - 1) / ρ := by field_simp
  rw [e, norm_div, one_lt_div (norm_pos_iff.2 hρ),
    ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp
  nlinarith

/-- In the strip, `|Re (1/ρ)| ≤ |1/ρ|²` (as `Re (1/ρ) = Re ρ / |ρ|²` and `0 < Re ρ < 1`). -/
lemma abs_re_inv_le {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : |(1 / ρ).re| ≤ ‖1 / ρ‖ ^ 2 := by
  have hn : 0 < Complex.normSq ρ := Complex.normSq_pos.2 (by rintro rfl; simp at h0)
  rw [one_div, Complex.inv_re, norm_inv, inv_pow, Complex.sq_norm, abs_div, abs_of_pos h0,
    abs_of_pos hn, div_le_iff₀ hn, inv_mul_cancel₀ hn.ne']
  linarith

/- ### The converse -/

/-- **Li ⇒ RH** (multiplicity-weighted, Bombieri–Lagarias argument), conditional only on the
Hadamard summability `∑ m(ρ)/|ρ|² < ∞` and the classical absence of real zeros in `(0,1)`. -/
theorem li_converse (H : HadamardHypothesis) (hreal : NoRealZerosInStrip)
    (hLi : ∀ n : ℕ, 0 < n → 0 ≤ liCoeff n) : RiemannHypothesis := by
  by_contra hRH
  obtain ⟨ρ0, hρ0, hlt⟩ := exists_posZero_re_lt_half hreal hRH
  have hsum : Summable fun ρ : nontrivialPosZeros =>
      (zetaMult ρ.1 : ℝ) * ‖1 - (1 - 1 / ρ.1)‖ ^ 2 := by
    have := H.summable_inv_sq.comp_injective (Set.inclusion_injective nontrivialPosZeros_subset)
    refine this.congr fun ρ => ?_
    simp [div_eq_mul_inv]
  obtain ⟨n, hn, -, hneg⟩ := exists_neg_of_large (fun ρ : nontrivialPosZeros => (zetaMult ρ.1 : ℝ))
    (fun ρ => 1 - 1 / ρ.1) (fun ρ => Nat.one_le_cast.2 (zetaMult_pos ρ.2)) hsum
    (fun ρ => by rw [sub_sub_cancel]; exact abs_re_inv_le ρ.2.1 ρ.2.2.1)
    ⟨⟨ρ0, hρ0⟩, one_lt_norm_one_sub_inv hρ0.1 hlt⟩
  have h := hLi n hn
  have heq : liCoeff n =
      2 * ∑' ρ : nontrivialPosZeros, (zetaMult ρ.1 : ℝ) * (1 - (1 - 1 / ρ.1) ^ n).re := by
    rw [liCoeff, ← tsum_mul_left]
    congr 1; ext ρ; ring
  rw [heq] at h
  linarith

/-- **Weighted Li criterion**, both directions, conditional on Hadamard summability and on the
absence of real zeros in `(0,1)`. -/
theorem li_criterion_weighted (H : HadamardHypothesis) (hreal : NoRealZerosInStrip) :
    RiemannHypothesis ↔ ∀ n : ℕ, 0 < n → 0 ≤ liCoeff n :=
  ⟨fun hRH n _ => liCoeff_nonneg hRH n, li_converse H hreal⟩

/-- **Bonus: the converse for the upstream (unweighted) `RiemannHypothesis.lambda`.**  The same
engine with all weights `= 1`; summability of `∑ 1/|ρ|²` follows from the weighted one since
`m(ρ) ≥ 1`.  Together with this, the "←" half of the upstream `li_criterion` holds conditionally. -/
theorem li_converse_unweighted (H : HadamardHypothesis) (hreal : NoRealZerosInStrip)
    (hLi : ∀ n : ℕ, 0 < n → 0 ≤ RiemannHypothesis.lambda n) : RiemannHypothesis := by
  by_contra hRH
  obtain ⟨ρ0, hρ0, hlt⟩ := exists_posZero_re_lt_half hreal hRH
  have hw : Summable fun ρ : nontrivialPosZeros =>
      (zetaMult ρ.1 : ℝ) * ‖1 - (1 - 1 / ρ.1)‖ ^ 2 := by
    have := H.summable_inv_sq.comp_injective (Set.inclusion_injective nontrivialPosZeros_subset)
    refine this.congr fun ρ => ?_
    simp [div_eq_mul_inv]
  have hsum : Summable fun ρ : nontrivialPosZeros => (1 : ℝ) * ‖1 - (1 - 1 / ρ.1)‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => ?_) hw
    have := Nat.one_le_cast (α := ℝ).2 (zetaMult_pos ρ.2)
    have := sq_nonneg ‖1 - (1 - 1 / ρ.1)‖
    nlinarith
  obtain ⟨n, hn, -, hneg⟩ := exists_neg_of_large (fun _ : nontrivialPosZeros => (1 : ℝ))
    (fun ρ => 1 - 1 / ρ.1) (fun _ => le_rfl) hsum
    (fun ρ => by rw [sub_sub_cancel]; exact abs_re_inv_le ρ.2.1 ρ.2.2.1)
    ⟨⟨ρ0, hρ0⟩, one_lt_norm_one_sub_inv hρ0.1 hlt⟩
  have h := hLi n hn
  have heq : RiemannHypothesis.lambda n =
      2 * ∑' ρ : nontrivialPosZeros, (1 : ℝ) * (1 - (1 - 1 / ρ.1) ^ n).re := by
    rw [RiemannHypothesis.lambda, ← tsum_mul_left]
    congr 1; ext ρ; ring
  rw [heq] at h
  linarith

end LiConditional

#print axioms LiConditional.li_converse
#print axioms LiConditional.li_criterion_weighted
#print axioms LiConditional.li_converse_unweighted
#print axioms LiConditional.exists_neg_of_large
#print axioms LiConditional.liCoeff_pos
