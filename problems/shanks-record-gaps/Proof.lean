import FormalConjectures.Wikipedia.MaximalPrimeGap

/-!
# Shanks warm-up: infinitely many record prime gaps

Human proof sketch (lemma names match the Lean below):
1. `gap_unbounded`: with `N = (k+1)!`, the numbers `N+2, …, N+k+1` are composite (`j ∣ N + j`).
   Let `p` be the largest prime `≤ N+1`; the next prime is `≥ N+k+2`, so that gap is `≥ k+1`.
2. `first_exceeder_is_record`: let `H` be the largest gap among indices `≤ M`. By step 1 some gap
   exceeds `H`; the *first* index `n` doing so has `n > M` and beats all earlier gaps: a record.
3. `infinite_maximalPrimeGapIndex`: records exist beyond every `M`, so there are infinitely many.
-/

namespace ShanksWarmup

open MaximalPrimeGap

/-- Step 1: prime gaps are unbounded (factorial run of composites). -/
lemma gap_unbounded (k : ℕ) : ∃ n, k ≤ primeGap n := by
  set M : ℕ := (k + 1).factorial + 2 with hM
  have hfact : 0 < (k + 1).factorial := Nat.factorial_pos _
  have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  -- count of primes below M is positive since 2 < M
  have hcpos : 0 < Nat.count Nat.Prime M := by
    rw [Nat.lt_nth_iff_count_lt hinf, Nat.nth_prime_zero_eq_two]
    omega
  obtain ⟨n, hn⟩ : ∃ n, Nat.count Nat.Prime M = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hcpos).symm⟩
  -- the prime p_n lies below M, and p_{n+1} does not
  have hlow : Nat.nth Nat.Prime n < M := by
    rw [← Nat.lt_nth_iff_count_lt hinf]; omega
  have hhigh : M ≤ Nat.nth Nat.Prime (n + 1) := by
    by_contra h
    rw [not_le, ← Nat.lt_nth_iff_count_lt hinf] at h
    omega
  have hprime : (Nat.nth Nat.Prime (n + 1)).Prime := Nat.nth_mem_of_infinite hinf _
  -- p_{n+1} is not in the composite run, hence ≥ N + k + 2
  have hbig : (k + 1).factorial + k + 2 ≤ Nat.nth Nat.Prime (n + 1) := by
    by_contra h
    set q := Nat.nth Nat.Prime (n + 1) with hq
    have hj : q - (k + 1).factorial ∣ q := by
      obtain ⟨j, hjdef⟩ : ∃ j, j = q - (k + 1).factorial := ⟨_, rfl⟩
      have hq' : (k + 1).factorial + j = q := by omega
      have hd : j ∣ (k + 1).factorial := Nat.dvd_factorial (by omega) (by omega)
      rw [← hjdef, ← hq']
      exact Nat.dvd_add hd dvd_rfl
    rcases hprime.eq_one_or_self_of_dvd _ hj with h1 | h1 <;> omega
  refine ⟨n, ?_⟩
  unfold primeGap
  omega

/-- Step 2: the first index whose gap exceeds all gaps up to `M` is a record beyond `M`. -/
lemma first_exceeder_is_record (M : ℕ) :
    ∃ n, M < n ∧ IsMaximalPrimeGapIndex n := by
  classical
  set H : ℕ := (Finset.range (M + 1)).sup primeGap with hH
  have hex : ∃ n, H < primeGap n := by
    obtain ⟨n, hn⟩ := gap_unbounded (H + 1)
    exact ⟨n, by omega⟩
  refine ⟨Nat.find hex, ?_, ?_⟩
  · by_contra h
    have hle : primeGap (Nat.find hex) ≤ H :=
      Finset.le_sup (f := primeGap) (Finset.mem_range.mpr (by omega))
    have := Nat.find_spec hex
    omega
  · intro m hm
    have := Nat.find_min hex hm
    have h2 := Nat.find_spec hex
    omega

/-- Step 3: there are infinitely many maximal prime gap indices (copy of the original statement). -/
theorem infinite_maximalPrimeGapIndex :
    {n : ℕ | IsMaximalPrimeGapIndex n}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun M => ?_
  obtain ⟨n, hn, hrec⟩ := first_exceeder_is_record M
  exact ⟨n, hrec, hn⟩

end ShanksWarmup
