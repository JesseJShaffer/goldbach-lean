import WR2Step247WR2SubHalfMURGlobalMinFacAndEndToEndStep209Closure

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step249WR2NativeFirstMissingPrimeExistenceAndUnconditionalMURShield.lean — Unconditional Existence & Uniqueness of the First Missing Odd Prime via the Factorial Lighthouse & Unconditional `Step209` Rescued-MUR Pincer (`WR2` Track 1)

Discharges the `IsFirstMissingOddPrime` and `h_fmp` hypotheses across `WR2Step223`–`WR2Step247`
using our native Factorial Lighthouse prime generator (`hasNextPrimeConnection_unconditional` /
`predictedNextPrime`):

1. **Section 1 — Unconditional Existence & Uniqueness of `IsFirstMissingOddPrime N q_E`
   (`oddPrimeNonDivisorsUpTo`, `exists_isFirstMissingOddPrime_native`, `isFirstMissingOddPrime_unique`):**
   - For every `N ≥ 1`, `hasNextPrimeConnection_unconditional (max N 2)` produces a prime
     `P > max N 2` (`3 ≤ P`, `P % 2 = 1`, `N % P = N ≥ 1`), proving that
     `oddPrimeNonDivisorsUpTo N P` is nonempty and its `Finset.min'` `q_E` satisfies
     `IsFirstMissingOddPrime N q_E ∧ 3 ≤ q_E ∧ q_E ≤ P`.
   - Proves that `q_E` is unique (`isFirstMissingOddPrime_unique`).
2. **Section 2 — Unconditional `Step209` Rescued-MUR Pincer (`unconditional_first_missing_prime_rescued_mur_pincer_wr2`):**
   - Instantiates `q_E` for `2 * M` (`1 ≤ M`), discharging `h_fmp` unconditionally for all
     `M ≥ 1` and `k : ℕ` without any external First-Missing-Prime hypothesis!
-/

/-!
## Section 1: Unconditional Existence & Uniqueness of the First Missing Odd Prime
-/

/-- Finite carrier of odd primes `q ≤ P` that do not divide `N` (`1 ≤ N % q`). -/
def oddPrimeNonDivisorsUpTo (N P : ℕ) : Finset ℕ :=
  (range (P + 1)).filter (fun q : ℕ =>
    IsPrimeNat q ∧ q % 2 = 1 ∧ 1 ≤ N % q)

/-- **Theorem 1.1 (`exists_isFirstMissingOddPrime_native`):**
    Unconditional Existence of the First Missing Odd Prime via the Native Factorial Lighthouse:
    For EVERY `N ≥ 1`, there exists an odd prime `q_E` paired with the Factorial Lighthouse
    upper prime `P` (`max N 2 < P`, `IsPrimeNat P`) such that:
    1. `IsFirstMissingOddPrime N q_E`,
    2. `3 ≤ q_E` and `q_E ≤ P`, and
    3. `predictedNextPrime (max N 2) = nextPrimeBoundedAux (max N 2 + 1) (factorialNat (max N 2) + 1)`. -/
theorem exists_isFirstMissingOddPrime_native {N : ℕ} (hN1 : 1 ≤ N) :
    ∃ q_E P : ℕ,
      max N 2 < P ∧
      IsPrimeNat P ∧
      3 ≤ q_E ∧
      q_E ≤ P ∧
      IsFirstMissingOddPrime N q_E ∧
      predictedNextPrime (max N 2) =
        nextPrimeBoundedAux (max N 2 + 1) (factorialNat (max N 2) + 1) := by
  obtain ⟨P, hP_gt, hP_isp⟩ := hasNextPrimeConnection_unconditional (max N 2)
  have hN_le_max : N ≤ max N 2 := Nat.le_max_left N 2
  have h2_le_max : 2 ≤ max N 2 := Nat.le_max_right N 2
  have hN_lt_P : N < P := Nat.lt_of_le_of_lt hN_le_max hP_gt
  have h2_lt_P : 2 < P := Nat.lt_of_le_of_lt h2_le_max hP_gt
  have hP_odd : P % 2 = 1 := by
    rcases isPrimeNat_eq_two_or_odd_wr2 hP_isp with hP2 | hPo
    · omega
    · exact hPo
  have hN_mod_P : N % P = N := Nat.mod_eq_of_lt hN_lt_P
  have hN_mod_P_pos : 1 ≤ N % P := by omega
  have hP_mem : P ∈ oddPrimeNonDivisorsUpTo N P := by
    rw [oddPrimeNonDivisorsUpTo, mem_filter, mem_range]
    exact ⟨Nat.lt_succ_self P, hP_isp, hP_odd, hN_mod_P_pos⟩
  have h_nonempty : (oddPrimeNonDivisorsUpTo N P).Nonempty := ⟨P, hP_mem⟩
  set q_E := (oddPrimeNonDivisorsUpTo N P).min' h_nonempty
  have hqE_mem : q_E ∈ oddPrimeNonDivisorsUpTo N P :=
    Finset.min'_mem (oddPrimeNonDivisorsUpTo N P) h_nonempty
  rw [oddPrimeNonDivisorsUpTo, mem_filter, mem_range] at hqE_mem
  obtain ⟨hqE_lt_succ, hqE_isp, hqE_odd, hqE_mod_pos⟩ := hqE_mem
  have hqE_two : 2 ≤ q_E := hqE_isp.1
  have hqE_ge3 : 3 ≤ q_E := by omega
  have hqE_le_P : q_E ≤ P := by omega
  have hqE_fmp : IsFirstMissingOddPrime N q_E := by
    refine ⟨hqE_isp, hqE_odd, by omega, ?_⟩
    intro r hr_isp hr_odd hr_lt
    if hr_mod0 : N % r = 0 then
      exact hr_mod0
    else
      have hr_mod_pos : 1 ≤ N % r := by omega
      have hr_lt_succ : r < P + 1 := Nat.lt_trans hr_lt hqE_lt_succ
      have hr_mem : r ∈ oddPrimeNonDivisorsUpTo N P := by
        rw [oddPrimeNonDivisorsUpTo, mem_filter, mem_range]
        exact ⟨hr_lt_succ, hr_isp, hr_odd, hr_mod_pos⟩
      have h_min_le : q_E ≤ r :=
        Finset.min'_le (oddPrimeNonDivisorsUpTo N P) r hr_mem
      omega
  exact ⟨q_E, P, hP_gt, hP_isp, hqE_ge3, hqE_le_P, hqE_fmp, rfl⟩

/-- **Theorem 1.2 (`isFirstMissingOddPrime_unique`):**
    The First Missing Odd Prime `q_E` of any `N` is uniquely determined. -/
theorem isFirstMissingOddPrime_unique
    {N q₁ q₂ : ℕ}
    (h1 : IsFirstMissingOddPrime N q₁) (h2 : IsFirstMissingOddPrime N q₂) :
    q₁ = q₂ := by
  match Nat.lt_or_ge q₁ q₂ with
  | Or.inl hlt =>
    have h_mod0 : N % q₁ = 0 := h2.2.2.2 q₁ h1.1 h1.2.1 hlt
    have h_pos1 : 1 ≤ N % q₁ := h1.2.2.1
    exact False.elim (false_of_one_le_of_eq_zero_wr2 h_pos1 h_mod0)
  | Or.inr hge =>
    match Nat.lt_or_ge q₂ q₁ with
    | Or.inl hlt2 =>
      have h_mod0 : N % q₂ = 0 := h1.2.2.2 q₂ h2.1 h2.2.1 hlt2
      have h_pos2 : 1 ≤ N % q₂ := h2.2.2.1
      exact False.elim (false_of_one_le_of_eq_zero_wr2 h_pos2 h_mod0)
    | Or.inr hge2 =>
      exact Nat.le_antisymm hge2 hge

/-!
## Section 2: Unconditional `Step209` Rescued-MUR Pincer (Discharging `h_fmp`)
-/

/-- **Theorem 2.1 (`unconditional_first_missing_prime_rescued_mur_pincer_wr2`):**
    Unconditional `Step209` + `Step198` Rescued-MUR Pincer on Track 1 (`WR2`):
    For EVERY `M ≥ 1` and EVERY block index `k : ℕ` (with ZERO external `h_fmp` hypothesis),
    there exists the unique First Missing Odd Prime `q_E` of `2 * M` (`3 ≤ q_E`,
    `IsFirstMissingOddPrime (2 * M) q_E`) such that:
    1. `(sqrtActiveOwnerPrimes M q_E).card + (aboveSqrtLowerMURPrimesCutoff M q_E).card ≤ (roughSurvivorSet (fullLowerMURUpper M) q_E).card`,
    2. `(pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) q_E k) q_E).card + (aboveSqrtLowerMURPrimesCutoff M q_E).card ≤ (roughSurvivorSet (fullLowerMURUpper M) q_E).card`,
    3. If `M ≤ 2 * q_E + 3`, then `(aboveSqrtLowerMURPrimesCutoff M q_E).card ≤ (primeSurvivorSet (fullLowerMURUpper M) q_E).card`, and
    4. If `q_E < M` and `2 * M < q_E * q_E`, then `q_E` itself is in `aboveSqrtLowerMURPrimesCutoff M q_E`,
       `(pn1RoughCompositeTail (fullLowerMURUpper M) q_E).card = 0`,
       `1 ≤ (primeSurvivorSet (fullLowerMURUpper M) q_E).card`, and `2 * M` is unconditionally
       a Binary Goldbach sum `2 * M = p + q'` paired with `p < p_next'`! -/
theorem unconditional_first_missing_prime_rescued_mur_pincer_wr2
    {M : ℕ} (hM1 : 1 ≤ M) (k : ℕ) :
    ∃ q_E : ℕ,
      3 ≤ q_E ∧
      IsFirstMissingOddPrime (2 * M) q_E ∧
      (sqrtActiveOwnerPrimes M q_E).card +
        (aboveSqrtLowerMURPrimesCutoff M q_E).card ≤
        (roughSurvivorSet (fullLowerMURUpper M) q_E).card ∧
      (pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) q_E k) q_E).card +
        (aboveSqrtLowerMURPrimesCutoff M q_E).card ≤
        (roughSurvivorSet (fullLowerMURUpper M) q_E).card ∧
      (M ≤ 2 * q_E + 3 →
        (aboveSqrtLowerMURPrimesCutoff M q_E).card ≤
          (primeSurvivorSet (fullLowerMURUpper M) q_E).card) ∧
      (q_E < M → 2 * M < q_E * q_E →
        (pn1RoughCompositeTail (fullLowerMURUpper M) q_E).card = 0 ∧
        1 ≤ (primeSurvivorSet (fullLowerMURUpper M) q_E).card ∧
        ∃ p q' p_next' : ℕ,
          Nat.Prime p ∧ Nat.Prime q' ∧ 2 * M = p + q' ∧
          p < p_next' ∧ Nat.Prime p_next' ∧ IsPrimeNat p_next') := by
  have h2M_ge1 : 1 ≤ 2 * M := by omega
  obtain ⟨q_E, _, _, _, hqE_ge3, _, hqE_fmp, _⟩ :=
    exists_isFirstMissingOddPrime_native h2M_ge1
  have h_max_eq : max q_E 3 = q_E := by omega
  have h_fmp :
      ∀ p0 : ℕ, IsPrimeNat p0 → p0 % 2 = 1 → p0 < max q_E 3 → (2 * M) % p0 = 0 := by
    rw [h_max_eq]
    exact hqE_fmp.2.2.2
  have h_resc :=
    unconditional_strict_sqrt_owner_lt_rescued_lower_mur_survivors_wr2 M q_E k h_fmp
  have h1 := h_resc.1
  have h2 := h_resc.2.1
  rw [h_max_eq] at h1 h2
  refine ⟨q_E, hqE_ge3, hqE_fmp, h1, h2, ?_, ?_⟩
  · intro hM_le
    have hM_le_max : M ≤ 2 * max q_E 3 + 3 := by
      rw [h_max_eq]
      exact hM_le
    have h_glob :=
      (step198_step209_global_rescued_survivor_to_binary_goldbach_wr2 hM_le_max h_fmp).2.1
    rw [h_max_eq] at h_glob
    exact h_glob
  · intro hqE_lt_M h_sq
    have h_sqrt_le : Nat.sqrt (2 * M) + 1 ≤ q_E :=
      sqrt_add_one_le_of_lt_sq_native h_sq
    have h_col := sqrt_succ_horizon_collapses_all_blocks_and_composite_tail h_sqrt_le
    have hqE_mem_above : q_E ∈ aboveSqrtLowerMURPrimesCutoff M q_E := by
      rw [aboveSqrtLowerMURPrimesCutoff, mem_filter, mem_range]
      exact ⟨hqE_lt_M, hqE_fmp.1, hqE_fmp.2.1, by omega, h_sq⟩
    have h_above_pos : 0 < (aboveSqrtLowerMURPrimesCutoff M q_E).card :=
      card_pos.mpr ⟨q_E, hqE_mem_above⟩
    have h_rough_pos : 0 < (roughSurvivorSet (fullLowerMURUpper M) q_E).card := by omega
    have h_prime_ge1 : 1 ≤ (primeSurvivorSet (fullLowerMURUpper M) q_E).card := by
      rw [← h_col.2.1]
      omega
    exact ⟨h_col.1, h_prime_ge1, h_col.2.2 h_rough_pos⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.exists_isFirstMissingOddPrime_native
#print axioms WuPaper.ESZerosBridge.isFirstMissingOddPrime_unique
#print axioms WuPaper.ESZerosBridge.unconditional_first_missing_prime_rescued_mur_pincer_wr2
