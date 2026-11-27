import FormalConjectures.Paper.RiemannHypothesisEquivalents

/-!
# Li's criterion, the conditional (multiplicity-weighted) half

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

**What is NOT done here.**  The converse (Li ⇒ RH) and the identification of `liCoeff n` with the
Taylor coefficients of `log ξ` at `s = 1` (the "bridge", which is where the Hadamard expansion
of `ξ'/ξ` in `HadamardHypothesis` would be used) are not proved.  The easy direction below only
uses the *summability* field of the hypothesis.

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

end LiConditional

#print axioms LiConditional.liCoeff_nonneg
#print axioms LiConditional.liCoeff_summable
#print axioms LiConditional.liCoeff_pos
