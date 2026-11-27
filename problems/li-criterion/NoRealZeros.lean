import Mathlib

/-!
# `ζ` has no zeros on the real segment `(0, 1)`

**Main results** (namespace `NoRealZeros`):
* `riemannZeta_ne_zero_of_mem_Ioo : 0 < σ → σ < 1 → riemannZeta σ ≠ 0`;
* the sharper `riemannZeta_re_lt_of_mem_Ioo : (riemannZeta σ).re < σ / (σ - 1)` (hence `< 0`,
  `riemannZeta_re_neg_of_mem_Ioo`) and `riemannZeta_im_eq_zero_of_mem_Ioo : (riemannZeta σ).im = 0`.

**Human proof sketch** (Euler–Maclaurin / "compare the sum with the integral", route B).

For `n ≥ 1` put
  `c_n(s) = (1 - s)(n+1)^{-s} - ((n+1)^{1-s} - n^{1-s}) = (1 - s) ∫ₙⁿ⁺¹ ((n+1)^{-s} - x^{-s}) dx`.
1. *Second-order cancellation* (`norm_corr_le`).  By the mean value inequality, twice,
   `|c_n(s)| ≤ |1 - s| |s| n^{-Re s - 1}`.  So `∑ c_n(s)` converges locally uniformly on
   `Re s > 0`, and its sum is holomorphic there (`differentiableOn_tsum_of_summable_norm`).
2. *The identity for `Re s > 1`* (`tsum_corr_of_one_lt_re`).  Here `∑ (n+1)^{-s} = ζ(s) - 1` and
   `∑ ((n+1)^{1-s} - n^{1-s}) = -1` telescopes, so `(s - 1) ζ(s) = s - ∑ c_n(s)`.
3. *Analytic continuation* (`riemannZeta₁_eq_sub_tsum_corr`).  Both sides are holomorphic on a
   convex open set containing `s` and `s + 2` (Mathlib's entire `riemannZeta₁ = (s - 1) ζ(s)` on the
   left), and agree near `s + 2`; by the identity theorem they agree for every `Re s > 0`.
4. *Sign on the real axis* (`realCorr_neg`).  For real `0 < σ < 1`, `x ↦ x^{1-σ}` is strictly
   concave, so its increment over `[n, n+1]` exceeds its slope at the right end:
   `(n+1)^{1-σ} - n^{1-σ} > (1-σ)(n+1)^{-σ}`, i.e. `c_n(σ) < 0` (Bernoulli's inequality
   `(1+x)^p < 1 + p x`).  Hence `(σ - 1) ζ(σ) = σ - ∑ c_n(σ) > σ`, and dividing by `σ - 1 < 0`:
   `ζ(σ) < σ / (σ - 1) < 0`.
-/

open Complex Filter Topology Set

namespace NoRealZeros

/-- Mean value bound for `t ↦ t ^ w` on the positive reals. -/
lemma norm_cpow_sub_cpow_le {a x y : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxy : x ≤ y) {w : ℂ}
    (hw : w.re ≤ 1) :
    ‖(y : ℂ) ^ w - (x : ℂ) ^ w‖ ≤ ‖w‖ * a ^ (w.re - 1) * (y - x) := by
  refine norm_image_sub_le_of_norm_deriv_le_segment' (f := fun t : ℝ => (t : ℂ) ^ w)
    (f' := fun t : ℝ => w * (t : ℂ) ^ (w - 1)) (fun t ht => ?_) (fun t ht => ?_) y ⟨hxy, le_rfl⟩
  · have ht0 : 0 < t := ha.trans_le (hax.trans ht.1)
    exact ((Complex.hasStrictDerivAt_cpow_const (c := w)
      (Complex.ofReal_mem_slitPlane.2 ht0)).hasDerivAt.comp_ofReal).hasDerivWithinAt
  · have ht0 : 0 < t := ha.trans_le (hax.trans ht.1)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, sub_re, one_re]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ha (hax.trans ht.1) (by linarith)) (norm_nonneg w)


/-- The `m`-th correction term (with `n = m + 1`):
`c_m(s) = (1 - s) (n+1)^{-s} - ((n+1)^{1-s} - n^{1-s}) = (1 - s) ∫ₙⁿ⁺¹ ((n+1)^{-s} - x^{-s}) dx`. -/
noncomputable def corr (s : ℂ) (m : ℕ) : ℂ :=
  (1 - s) * ((m : ℂ) + 2) ^ (-s) - (((m : ℂ) + 2) ^ (1 - s) - ((m : ℂ) + 1) ^ (1 - s))

/-- Second-order cancellation: `‖c_m(s)‖ ≤ ‖1 - s‖ ‖s‖ n^{-Re s - 1}`. -/
lemma norm_corr_le {s : ℂ} (hs : 0 < s.re) (m : ℕ) :
    ‖corr s m‖ ≤ ‖1 - s‖ * ‖s‖ * ((m : ℝ) + 1) ^ (-s.re - 1) := by
  set n : ℝ := (m : ℝ) + 1 with hn_def
  have hn : 1 ≤ n := by simp [hn_def]
  have hn0 : 0 < n := by linarith
  set h : ℝ → ℂ := fun t => (t : ℂ) ^ (1 - s) - (1 - s) * ((n + 1 : ℝ) : ℂ) ^ (-s) * t
  have key : ‖h (n + 1) - h n‖ ≤ ‖1 - s‖ * ‖s‖ * n ^ (-s.re - 1) * (n + 1 - n) := by
    refine norm_image_sub_le_of_norm_deriv_le_segment' (f := h)
      (f' := fun t => (1 - s) * (t : ℂ) ^ (-s) - (1 - s) * ((n + 1 : ℝ) : ℂ) ^ (-s))
      (fun t ht => ?_) (fun t ht => ?_) (n + 1) ⟨by linarith, le_rfl⟩
    · have ht0 : 0 < t := hn0.trans_le ht.1
      have h1 := (Complex.hasStrictDerivAt_cpow_const (c := 1 - s)
        (Complex.ofReal_mem_slitPlane.2 ht0)).hasDerivAt.comp_ofReal
      have h2 := ((hasDerivAt_id t).ofReal_comp).const_mul ((1 - s) * ((n + 1 : ℝ) : ℂ) ^ (-s))
      have e : (1 - s - 1 : ℂ) = -s := by ring
      rw [e] at h1
      convert (h1.sub h2).hasDerivWithinAt using 1
      · funext y; simp [h]
      · simp
    · have ht0 : 0 < t := hn0.trans_le ht.1
      have hb := norm_cpow_sub_cpow_le hn0 ht.1 ht.2.le (w := -s) (by simp; linarith)
      rw [← mul_sub, norm_mul, norm_sub_rev ((t : ℂ) ^ (-s))]
      simp only [neg_re, norm_neg] at hb
      have : ‖((n + 1 : ℝ) : ℂ) ^ (-s) - (t : ℂ) ^ (-s)‖ ≤ ‖s‖ * n ^ (-s.re - 1) := by
        refine hb.trans ?_
        have := ht.2
        have : 0 ≤ ‖s‖ * n ^ (-s.re - 1) := by positivity
        nlinarith [ht.1]
      calc ‖1 - s‖ * ‖((n + 1 : ℝ) : ℂ) ^ (-s) - (t : ℂ) ^ (-s)‖
          ≤ ‖1 - s‖ * (‖s‖ * n ^ (-s.re - 1)) := mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ = ‖1 - s‖ * ‖s‖ * n ^ (-s.re - 1) := by ring
  have e : corr s m = -(h (n + 1) - h n) := by
    simp only [corr, h, hn_def]; push_cast; ring_nf
  rw [e, norm_neg]
  simpa using key


lemma summable_rpow_bound {ε : ℝ} (hε : 0 < ε) :
    Summable fun m : ℕ => ((m : ℝ) + 1) ^ (-ε - 1) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -ε - 1 < -1))
  simpa using h

lemma summable_corr {s : ℂ} (hs : 0 < s.re) : Summable (corr s) :=
  Summable.of_norm_bounded ((summable_rpow_bound hs).mul_left (‖1 - s‖ * ‖s‖))
    (norm_corr_le hs)

lemma differentiable_corr (m : ℕ) : Differentiable ℂ fun s => corr s m := by
  have h1 : ((m : ℂ) + 2) ≠ 0 := by norm_cast
  have h2 : ((m : ℂ) + 1) ≠ 0 := by norm_cast
  unfold corr
  fun_prop (disch := simp [h1, h2])

/-- `∑_{m ≥ 0} (m+2)^{-s} = ζ(s) - 1` for `Re s > 1`. -/
lemma hasSum_cpow_add_two {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun m : ℕ => ((m : ℂ) + 2) ^ (-s)) (riemannZeta s - 1) := by
  have hsum : Summable fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s := by
    have := (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs)
    simpa using this
  have h := (hasSum_nat_add_iff' 1).mpr (zeta_eq_tsum_one_div_nat_add_one_cpow hs ▸ hsum.hasSum)
  have e1 : (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℂ) + 1) ^ s) = fun m : ℕ => ((m : ℂ) + 2) ^ (-s) := by
    funext m; rw [cpow_neg, one_div]; push_cast; ring_nf
  rw [e1, Finset.sum_range_one] at h
  simpa using h

/-- Telescoping: `∑_{m ≥ 0} ((m+2)^{1-s} - (m+1)^{1-s}) = -1` for `Re s > 1`. -/
lemma hasSum_telescope {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun m : ℕ => ((m : ℂ) + 2) ^ (1 - s) - ((m : ℂ) + 1) ^ (1 - s)) (-1) := by
  have hsum : Summable fun m : ℕ => ((m : ℂ) + 2) ^ (1 - s) - ((m : ℂ) + 1) ^ (1 - s) := by
    refine (((hasSum_cpow_add_two hs).summable.mul_left (1 - s)).sub
      (summable_corr (by linarith))).congr fun m => ?_
    simp [corr]
  have hpart : ∀ N : ℕ, ∑ m ∈ Finset.range N, (((m : ℂ) + 2) ^ (1 - s) - ((m : ℂ) + 1) ^ (1 - s))
      = ((N : ℂ) + 1) ^ (1 - s) - 1 := by
    intro N
    have := Finset.sum_range_sub (fun k : ℕ => ((k : ℂ) + 1) ^ (1 - s)) N
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, one_cpow] at this
    rw [← this]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring_nf
  have hlim : Tendsto (fun N : ℕ => ((N : ℂ) + 1) ^ (1 - s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have e : ∀ N : ℕ, ‖((N : ℂ) + 1) ^ (1 - s)‖ = ((N : ℝ) + 1) ^ (-(s.re - 1)) := by
      intro N
      have : ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
      simp
    simp only [e]
    exact (tendsto_rpow_neg_atTop (by linarith)).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have h1 := hsum.hasSum.tendsto_sum_nat
  simp only [hpart] at h1
  have h2 : Tendsto (fun N : ℕ => ((N : ℂ) + 1) ^ (1 - s) - 1) atTop (𝓝 (0 - 1)) :=
    hlim.sub tendsto_const_nhds
  rw [zero_sub] at h2
  rw [← tendsto_nhds_unique h1 h2]
  exact hsum.hasSum

/-- For `Re s > 1`: `∑ c_m(s) = (1 - s)(ζ(s) - 1) + 1`, i.e. `(s - 1) ζ(s) = s - ∑ c_m(s)`. -/
lemma tsum_corr_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    ∑' m, corr s m = (1 - s) * (riemannZeta s - 1) + 1 := by
  have h := ((hasSum_cpow_add_two hs).mul_left (1 - s)).sub (hasSum_telescope hs)
  rw [sub_neg_eq_add] at h
  exact h.tsum_eq


/-- **Analytic continuation.** For `Re s > 0`: `(s - 1) ζ(s) = s - ∑ₘ c_m(s)`
(stated with Mathlib's entire function `riemannZeta₁ s = (s - 1) ζ(s)`). -/
theorem riemannZeta₁_eq_sub_tsum_corr {s : ℂ} (hs : 0 < s.re) :
    riemannZeta₁ s = s - ∑' m, corr s m := by
  set ε := s.re / 2 with hε_def
  have hε : 0 < ε := by positivity
  set R := ‖s‖ + 3 with hR_def
  set V : Set ℂ := {z | ε < z.re} ∩ Metric.ball 0 R with hV_def
  have hVo : IsOpen V := (isOpen_lt continuous_const continuous_re).inter Metric.isOpen_ball
  have hVc : Convex ℝ V := (convex_halfSpace_re_gt ε).inter (convex_ball 0 R)
  have hsV : s ∈ V := ⟨by simp only [mem_ofPred_eq]; linarith, by simp [hR_def]⟩
  have hs2V : s + 2 ∈ V := by
    refine ⟨by simp only [mem_ofPred_eq, add_re]; norm_num; linarith, ?_⟩
    rw [mem_ball_zero_iff]
    calc ‖s + 2‖ ≤ ‖s‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
      _ < R := by simp [hR_def]; norm_num
  have hF : AnalyticOnNhd ℂ riemannZeta₁ V :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd hVo
  have hbound : ∀ (m : ℕ) (z : ℂ), z ∈ V →
      ‖corr z m‖ ≤ (R + 1) * R * ((m : ℝ) + 1) ^ (-ε - 1) := by
    intro m z hz
    have hzr : ε < z.re := hz.1
    have hzR : ‖z‖ < R := mem_ball_zero_iff.mp hz.2
    have h1z : ‖1 - z‖ ≤ R + 1 := by
      calc ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ R + 1 := by simp; linarith
    have hpow : ((m : ℝ) + 1) ^ (-z.re - 1) ≤ ((m : ℝ) + 1) ^ (-ε - 1) :=
      Real.rpow_le_rpow_of_exponent_le (by simp) (by linarith)
    refine (norm_corr_le (hε.trans hzr) m).trans ?_
    gcongr
  have hG : AnalyticOnNhd ℂ (fun z => z - ∑' m, corr z m) V := by
    refine DifferentiableOn.analyticOnNhd ?_ hVo
    exact differentiableOn_id.sub (differentiableOn_tsum_of_summable_norm
      ((summable_rpow_bound hε).mul_left _) (fun m => (differentiable_corr m).differentiableOn)
      hVo hbound)
  have hEq : riemannZeta₁ =ᶠ[𝓝 (s + 2)] fun z => z - ∑' m, corr z m := by
    have hre : 1 < (s + 2).re := by simp; linarith
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hre] with z hz
    have hz1 : z ≠ 1 := by rintro rfl; simp at hz
    have hzeta := riemannZeta_eq_inv_sub_mul hz1
    have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    rw [tsum_corr_of_one_lt_re hz, hzeta]
    field_simp
    ring
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG hVc.isPreconnected hs2V hEq hsV

/-- The correction term at a real point, as a real number. -/
noncomputable def realCorr (σ : ℝ) (m : ℕ) : ℝ :=
  (1 - σ) * ((m : ℝ) + 2) ^ (-σ) - (((m : ℝ) + 2) ^ (1 - σ) - ((m : ℝ) + 1) ^ (1 - σ))

lemma corr_ofReal (σ : ℝ) (m : ℕ) : corr σ m = realCorr σ m := by
  have h2 : (0 : ℝ) ≤ (m : ℝ) + 2 := by positivity
  have h1 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
  simp only [corr, realCorr]
  push_cast [Complex.ofReal_cpow h2, Complex.ofReal_cpow h1]
  rfl

/-- **Concavity.** For `0 < σ < 1` each correction term is negative:
`(n+1)^{1-σ} - n^{1-σ} > (1-σ)(n+1)^{-σ}` since `x ↦ x^{1-σ}` is strictly concave. -/
lemma realCorr_neg {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) (m : ℕ) : realCorr σ m < 0 := by
  set p := 1 - σ with hp
  set N : ℝ := (m : ℝ) + 2 with hN_def
  have hN : 2 ≤ N := by simp [hN_def]
  have hN0 : 0 < N := by linarith
  have hb := rpow_one_add_lt_one_add_mul_self (s := -1 / N)
    (by rw [neg_div, neg_le_neg_iff, div_le_one hN0]; linarith)
    (by simp; linarith) (p := p) (by linarith) (by linarith)
  have e1 : 1 + -1 / N = ((m : ℝ) + 1) / N := by field_simp; simp [hN_def]; ring
  rw [e1, Real.div_rpow (by positivity) hN0.le] at hb
  have hNp : 0 < N ^ p := by positivity
  rw [div_lt_iff₀ hNp] at hb
  have e2 : N ^ (-σ) = N ^ p / N := by
    rw [show -σ = p - 1 by rw [hp]; ring, Real.rpow_sub_one hN0.ne']
  have e3 : (1 + p * (-1 / N)) * N ^ p = N ^ p - p * (N ^ p / N) := by field_simp; ring
  simp only [realCorr]
  rw [← hN_def, ← hp, e2]
  linarith

/-- **Main estimate.** For `0 < σ < 1`, `ζ(σ)` is the real number `(σ - T)/(σ - 1)` with
`T = ∑ c_m(σ) < 0`; in particular `ζ(σ) < σ/(σ - 1) < 0`. -/
theorem riemannZeta_eq_ofReal_lt {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    ∃ x : ℝ, riemannZeta σ = x ∧ x < σ / (σ - 1) := by
  have hsum : Summable (realCorr σ) := by
    have : Summable fun m => (realCorr σ m : ℂ) :=
      (summable_corr (s := σ) (by simpa using h0)).congr fun m => corr_ofReal σ m
    exact Complex.summable_ofReal.mp this
  set T := ∑' m, realCorr σ m with hT
  have hTneg : T < 0 := by
    have := hasSum_lt (f := realCorr σ) (g := fun _ => 0) (i := 0)
      (fun m => (realCorr_neg h0 h1 m).le) (realCorr_neg h0 h1 0) hsum.hasSum hasSum_zero
    simpa [hT] using this
  have hs1 : (σ : ℂ) ≠ 1 := by exact_mod_cast h1.ne
  refine ⟨(σ - T) / (σ - 1), ?_, ?_⟩
  · rw [riemannZeta_eq_inv_sub_mul hs1, riemannZeta₁_eq_sub_tsum_corr (by simpa using h0)]
    simp only [corr_ofReal]
    rw [← Complex.ofReal_tsum, ← hT]
    push_cast
    ring
  · have hneg : σ - 1 < 0 := by linarith
    exact (div_lt_div_right_of_neg hneg).mpr (by linarith)

theorem riemannZeta_im_eq_zero_of_mem_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    (riemannZeta σ).im = 0 := by
  obtain ⟨x, hx, -⟩ := riemannZeta_eq_ofReal_lt h0 h1
  simp [hx]

theorem riemannZeta_re_lt_of_mem_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    (riemannZeta σ).re < σ / (σ - 1) := by
  obtain ⟨x, hx, hlt⟩ := riemannZeta_eq_ofReal_lt h0 h1
  simpa [hx] using hlt

theorem riemannZeta_re_neg_of_mem_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    (riemannZeta σ).re < 0 :=
  (riemannZeta_re_lt_of_mem_Ioo h0 h1).trans (div_neg_of_pos_of_neg h0 (by linarith))

/-- **No real zeros in the critical strip.** -/
theorem riemannZeta_ne_zero_of_mem_Ioo {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  intro h
  have := riemannZeta_re_neg_of_mem_Ioo h0 h1
  rw [h, zero_re] at this
  exact lt_irrefl 0 this

end NoRealZeros

#print axioms NoRealZeros.riemannZeta_ne_zero_of_mem_Ioo
#print axioms NoRealZeros.riemannZeta_re_lt_of_mem_Ioo
#print axioms NoRealZeros.riemannZeta_im_eq_zero_of_mem_Ioo
