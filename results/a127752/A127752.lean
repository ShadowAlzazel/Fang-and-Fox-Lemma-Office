/-
# OEIS A127752: the row sums mod 2 are the period-doubling sequence

OEIS A127752 (Paul Barry, 2007):
  "Row sums of inverse of number triangle A(n,k) = 1/(3n+1) if k <= n <= 2k, 0 otherwise."
  Offset 0. Data: 1,4,3,7,3,6,3,10,3,6,3,9,3,6,3,13,...
Conjecture (OEIS comment, listed on Left to Solve as `oeis-a127752`):
  "a(n) mod 2 is first Feigenbaum symbolic sequence A035263 (conjecture)."
  "(But please note the different indexing, here 0-based.)"
A035263 has offset 1: A035263(n) = A000035(A001511(n)) = ν₂(2n) mod 2.
So the precise claim is: for every n ≥ 0, a(n) ≡ A035263(n+1) (mod 2).

## Proof story

Write A for the (infinite, lower-triangular) triangle and B = A⁻¹. Because A is lower
triangular with nonzero diagonal 1/(3n+1), every finite truncation `tri N` is invertible
and its inverse is the truncation of B, so a(n) does not depend on the truncation size
(`rowSum_inv_tri` holds for every N > n).

1. *Row sums of B solve a linear system.* Let a = B·𝟙. Then A·a = A·B·𝟙 = 𝟙.
   Row n of A·a = 𝟙 reads  (1/(3n+1)) · Σ_{⌈n/2⌉ ≤ k ≤ n} a(k) = 1, i.e.
       Σ_{⌈n/2⌉ ≤ k ≤ n} a(k) = 3n + 1.                         (`blockSum_r`)
   Since A is invertible this system has exactly one solution.
2. *Differencing gives a doubling recursion.* Subtracting row n-1 from row n
   (the window [⌈n/2⌉, n] slides right by one on top, and by one on the bottom only when
   n is odd):
       a(0) = 1,   a(2m+2) = 3,   a(2m+1) = a(m) + 3.            (`r`)
   So `r` is the unique solution, hence a = r                    (`a127752_eq_r`).
   Closed form: a(n) = 3·ν₂(n+1) + 3, except a(2^k - 1) = 3k + 1.
3. *Period doubling.* Mod 2 the recursion is  a(2m) ≡ 1,  a(2m+1) ≡ 1 + a(m).
   That is exactly Cloitre's "copy and flip the last bit" / Toeplitz construction
   of the period-doubling sequence; in 2-adic language a(n) ≡ 1 + ν₂(n+1) = ν₂(2(n+1))
   (mod 2): each factor of 2 in n+1 is one period doubling, and flips the parity.
                                                                 (`r_mod_two`)
   This is the Black Swan observation "kneading = ruler function ν₂ mod 2"
   (with R = 1 = "ν₂(j) even").
Main theorem: `a127752_mod_two`.
-/
import Mathlib

open Matrix Finset

namespace A127752

/-- The OEIS triangle truncated to indices `0..N-1`:
`A(n,k) = 1/(3n+1)` if `k ≤ n ≤ 2k`, and `0` otherwise. -/
def tri (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  fun n k => if (k : ℕ) ≤ n ∧ (n : ℕ) ≤ 2 * k then 1 / (3 * (n : ℚ) + 1) else 0

/-- `a(n)` = the `n`-th row sum of the inverse triangle, computed in the
`(n+1) × (n+1)` truncation (we prove below the answer is the same for every truncation
containing row `n`). `⁻¹` is Mathlib's matrix inverse. -/
noncomputable def a127752 (n : ℕ) : ℚ := ∑ k, (tri (n + 1))⁻¹ (Fin.last n) k

/-- A035263 (offset 1), as in its OEIS name: parity of the 2-adic valuation of `2n`. -/
def A035263 (n : ℕ) : ℕ := padicValNat 2 (2 * n) % 2

/-- The doubling recursion: `r 0 = 1`, `r (2m+1) = r m + 3`, `r (2m+2) = 3`. -/
def r : ℕ → ℕ
  | 0 => 1
  | n + 1 => if (n + 1) % 2 = 1 then r (n / 2) + 3 else 3

lemma r_zero : r 0 = 1 := by simp [r]

lemma r_odd (m : ℕ) : r (2 * m + 1) = r m + 3 := by
  rw [r, if_pos (by omega)]
  congr 2; omega

lemma r_even (m : ℕ) : r (2 * m + 2) = 3 := by
  rw [r, if_neg (by omega)]

/-! ### Guards against misformalization: OEIS data -/

/-- All 106 terms (n = 0..105) of the A127752 data section of the OEIS entry (`%S %T %U` lines). -/
def oeisData : List ℕ :=
  [1,4,3,7,3,6,3,10,3,6,3,9,3,6,3,13,3,6,3,9,3,6,3,12,3,6,3,9,3,6,3,16,
   3,6,3,9,3,6,3,12,3,6,3,9,3,6,3,15,3,6,3,9,3,6,3,12,3,6,3,9,3,6,3,19,
   3,6,3,9,3,6,3,12,3,6,3,9,3,6,3,15,3,6,3,9,3,6,3,12,3,6,3,9,3,6,3,18,3,6,3,9,3,6,3,12,3,6]

#guard (List.range oeisData.length).map r == oeisData
-- First 34 terms of A035263 (offset 1) from OEIS.
#guard (List.range 34).map (fun n => A035263 (n + 1)) ==
  [1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0]
-- the conjecture itself on the OEIS data
#guard (List.range oeisData.length).all (fun n => oeisData[n]! % 2 == A035263 (n + 1))

/-- A *computable* forward-substitution inverse of the truncated triangle, used only to
check (by evaluation) that row sums of the genuine inverse match OEIS. -/
def triQ (n k : ℕ) : ℚ := if k ≤ n ∧ n ≤ 2 * k then 1 / (3 * (n : ℚ) + 1) else 0
def invCol (N j : ℕ) : Array ℚ := Id.run do
  let mut b : Array ℚ := Array.replicate N 0
  for i in [j:N] do
    let s := (if i = j then (1 : ℚ) else 0) -
      ((List.range (i - j)).map (fun t => triQ i (j + t) * b.getD (j + t) 0)).sum
    b := b.set! i (s / triQ i i)
  return b
def invMat (N : ℕ) : Array (Array ℚ) := (Array.range N).map (invCol N)  -- columns
-- check  A * B = I  and the row sums of B against OEIS, for N = 40
#guard let N := 40; let B := invMat N
  (List.range N).all fun i => (List.range N).all fun j =>
    ((List.range N).map (fun k => triQ i k * (B.getD j #[]).getD k 0)).sum == (if i = j then 1 else 0)
#guard let N := 40; let B := invMat N
  (List.range N).map (fun i => ((List.range N).map (fun j => (B.getD j #[]).getD i 0)).sum)
    == (oeisData.take N).map (fun x => (x : ℚ))

/-! ### Step 1–2: the block-sum identity -/

/-- `Σ_{⌈n/2⌉ ≤ k ≤ n} r k = 3n + 1`. -/
lemma blockSum_r (n : ℕ) : ∑ k ∈ Ico ((n + 1) / 2) (n + 1), r k = 3 * n + 1 := by
  induction n with
  | zero => simp [r_zero]
  | succ n ih =>
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · -- n = 2m, new row 2m+1: window [m, 2m] becomes [m+1, 2m+1]
      have h1 : (2 * m + 1) / 2 = m := by omega
      have h2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      rw [h1] at ih; rw [h2]
      have e : ∑ k ∈ Ico m (2 * m + 1 + 1), r k
          = r m + ∑ k ∈ Ico (m + 1) (2 * m + 1 + 1), r k :=
        Finset.sum_eq_sum_Ico_succ_bot (by omega) _
      rw [Finset.sum_Ico_succ_top (by omega), ih, r_odd] at e
      omega
    · -- n = 2m+1, new row 2m+2: window [m+1, 2m+1] becomes [m+1, 2m+2]
      have h1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      have h2 : (2 * m + 1 + 1 + 1) / 2 = m + 1 := by omega
      rw [h1] at ih; rw [h2, Finset.sum_Ico_succ_top (by omega), ih,
        show 2 * m + 1 + 1 = 2 * m + 2 from rfl, r_even]
      omega

/-! ### Step 1: row sums of the inverse solve `A · a = 𝟙` -/

lemma tri_mulVec_r (N : ℕ) :
    tri N *ᵥ (fun k : Fin N => (r k : ℚ)) = fun _ => 1 := by
  funext i
  simp only [mulVec, dotProduct, tri, ite_mul, zero_mul]
  rw [Fin.sum_univ_eq_sum_range
    (fun x => if x ≤ (i : ℕ) ∧ (i : ℕ) ≤ 2 * x then 1 / (3 * (i : ℚ) + 1) * (r x : ℚ) else 0)]
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  have hf : (range N).filter (fun x => x ≤ (i : ℕ) ∧ (i : ℕ) ≤ 2 * x)
      = Ico (((i : ℕ) + 1) / 2) ((i : ℕ) + 1) := by
    ext x; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [hf, ← Nat.cast_sum, blockSum_r]
  push_cast
  field_simp

lemma tri_lower (N : ℕ) : (tri N).IsLowerTriangular := by
  intro i j hij
  have : (i : ℕ) < j := hij
  simp only [tri]; rw [if_neg (by omega)]

lemma tri_det_isUnit (N : ℕ) : IsUnit (tri N).det := by
  rw [det_of_isLowerTriangular _ (tri_lower N), isUnit_iff_ne_zero,
    Finset.prod_ne_zero_iff]
  intro i _
  simp only [tri, le_refl, true_and]
  rw [if_pos (by omega)]
  positivity

/-- Row sums of the inverse of *any* truncation are given by `r`
(so the definition of `a127752` does not depend on the truncation size). -/
theorem rowSum_inv_tri (N : ℕ) (n : Fin N) : ∑ k, (tri N)⁻¹ n k = r n := by
  have h : (tri N)⁻¹ *ᵥ (fun _ => (1 : ℚ)) = fun k : Fin N => (r k : ℚ) := by
    rw [← tri_mulVec_r, mulVec_mulVec, nonsing_inv_mul _ (tri_det_isUnit N), one_mulVec]
  have := congrFun h n
  simpa [mulVec, dotProduct] using this

theorem a127752_eq_r (n : ℕ) : a127752 n = r n := by
  rw [a127752, rowSum_inv_tri]; simp

/-! ### Step 3: period doubling / 2-adic parity -/

theorem r_mod_two (n : ℕ) : r n % 2 = A035263 (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    unfold A035263
    rcases n with _ | n
    · simp [r_zero]
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · -- n+1 = 2m+1 odd index, so (2m+1)+1 = 2(m+1)
      have ihm := ih m (by omega)
      unfold A035263 at ihm
      rw [r_odd, show 2 * (2 * m + 1 + 1) = 2 * (2 * (m + 1)) by ring,
        padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num)]
      omega
    · -- index 2m+2 even, so index+1 = 2m+3 is odd
      rw [show 2 * m + 1 + 1 = 2 * m + 2 from rfl, r_even,
        padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
        padicValNat.eq_zero_of_not_dvd (by omega)]

/-- **OEIS A127752 conjecture.** `a(n)` is an integer and `a(n) mod 2 = A035263(n+1)`
(A127752 is 0-based, A035263 is 1-based). -/
theorem a127752_mod_two (n : ℕ) :
    ∃ m : ℤ, a127752 n = m ∧ m % 2 = (A035263 (n + 1) : ℤ) := by
  refine ⟨r n, by rw [a127752_eq_r]; norm_cast, ?_⟩
  rw [← r_mod_two]; push_cast; rfl

end A127752

#print axioms A127752.a127752_mod_two
#print axioms A127752.a127752_eq_r
#print axioms A127752.r_mod_two
