import WR2Step248LiLiuSubHalfMURGlobalMinFacAnd71ModuleCapstone

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step250LiLiuNativeFirstMissingPrimeAnd73ModuleMasterCapstone.lean — Unconditional Existence & Uniqueness of the First Missing Odd Prime via the Factorial Lighthouse, Unconditional `Step209` Rescued-MUR Pincer & Master 73-Module `D19 N` Capstone

Discharges `IsFirstMissingOddPrimeLiliu N q_E` and `h_fmp` unconditionally on Track 2 (`D19 N`)
and welds the complete 73-module suite into the `Goldbach.All` Master Capstone.
-/

def liliuOddPrimeNonDivisorsUpTo (N P : ℕ) : Finset ℕ :=
  (range (P + 1)).filter (fun q : ℕ =>
    IsPrimeNat q ∧ q % 2 = 1 ∧ 1 ≤ N % q)

/-- **Theorem 1.1 (`exists_isFirstMissingOddPrimeLiliu_native`):**
    Unconditional Existence of the First Missing Odd Prime on Track 2 (`D19 N`) via
    `hasNextPrimeConnection_unconditional (max N 2)`. -/
theorem exists_isFirstMissingOddPrimeLiliu_native {N : ℕ} (hN1 : 1 ≤ N) :
    ∃ q_E P : ℕ,
      max N 2 < P ∧
      IsPrimeNat P ∧
      3 ≤ q_E ∧
      q_E ≤ P ∧
      IsFirstMissingOddPrimeLiliu N q_E ∧
      predictedNextPrime (max N 2) =
        nextPrimeBoundedAux (max N 2 + 1) (factorialNat (max N 2) + 1) := by
  obtain ⟨P, hP_gt, hP_isp⟩ := hasNextPrimeConnection_unconditional (max N 2)
  have hN_le_max : N ≤ max N 2 := Nat.le_max_left N 2
  have h2_le_max : 2 ≤ max N 2 := Nat.le_max_right N 2
  have hN_lt_P : N < P := Nat.lt_of_le_of_lt hN_le_max hP_gt
  have h2_lt_P : 2 < P := Nat.lt_of_le_of_lt h2_le_max hP_gt
  have hP_odd : P % 2 = 1 := by
    rcases isPrimeNat_eq_two_or_odd_liliu hP_isp with hP2 | hPo
    · omega
    · exact hPo
  have hN_mod_P : N % P = N := Nat.mod_eq_of_lt hN_lt_P
  have hN_mod_P_pos : 1 ≤ N % P := by omega
  have hP_mem : P ∈ liliuOddPrimeNonDivisorsUpTo N P := by
    rw [liliuOddPrimeNonDivisorsUpTo, mem_filter, mem_range]
    exact ⟨Nat.lt_succ_self P, hP_isp, hP_odd, hN_mod_P_pos⟩
  have h_nonempty : (liliuOddPrimeNonDivisorsUpTo N P).Nonempty := ⟨P, hP_mem⟩
  set q_E := (liliuOddPrimeNonDivisorsUpTo N P).min' h_nonempty
  have hqE_mem : q_E ∈ liliuOddPrimeNonDivisorsUpTo N P :=
    Finset.min'_mem (liliuOddPrimeNonDivisorsUpTo N P) h_nonempty
  rw [liliuOddPrimeNonDivisorsUpTo, mem_filter, mem_range] at hqE_mem
  obtain ⟨hqE_lt_succ, hqE_isp, hqE_odd, hqE_mod_pos⟩ := hqE_mem
  have hqE_two : 2 ≤ q_E := hqE_isp.1
  have hqE_ge3 : 3 ≤ q_E := by omega
  have hqE_le_P : q_E ≤ P := by omega
  have hqE_fmp : IsFirstMissingOddPrimeLiliu N q_E := by
    refine ⟨hqE_isp, hqE_odd, by omega, ?_⟩
    intro r hr_isp hr_odd hr_lt
    if hr_mod0 : N % r = 0 then
      exact hr_mod0
    else
      have hr_mod_pos : 1 ≤ N % r := by omega
      have hr_lt_succ : r < P + 1 := Nat.lt_trans hr_lt hqE_lt_succ
      have hr_mem : r ∈ liliuOddPrimeNonDivisorsUpTo N P := by
        rw [liliuOddPrimeNonDivisorsUpTo, mem_filter, mem_range]
        exact ⟨hr_lt_succ, hr_isp, hr_odd, hr_mod_pos⟩
      have h_min_le : q_E ≤ r :=
        Finset.min'_le (liliuOddPrimeNonDivisorsUpTo N P) r hr_mem
      omega
  exact ⟨q_E, P, hP_gt, hP_isp, hqE_ge3, hqE_le_P, hqE_fmp, rfl⟩

/-- **Theorem 1.2 (`isFirstMissingOddPrimeLiliu_unique`):**
    The First Missing Odd Prime `q_E` of any `N` is unique. -/
theorem isFirstMissingOddPrimeLiliu_unique
    {N q₁ q₂ : ℕ}
    (h1 : IsFirstMissingOddPrimeLiliu N q₁) (h2 : IsFirstMissingOddPrimeLiliu N q₂) :
    q₁ = q₂ := by
  match Nat.lt_or_ge q₁ q₂ with
  | Or.inl hlt =>
    have h_mod0 : N % q₁ = 0 := h2.2.2.2 q₁ h1.1 h1.2.1 hlt
    have h_pos1 : 1 ≤ N % q₁ := h1.2.2.1
    exact False.elim (false_of_one_le_of_eq_zero_liliu h_pos1 h_mod0)
  | Or.inr hge =>
    match Nat.lt_or_ge q₂ q₁ with
    | Or.inl hlt2 =>
      have h_mod0 : N % q₂ = 0 := h1.2.2.2 q₂ h2.1 h2.2.1 hlt2
      have h_pos2 : 1 ≤ N % q₂ := h2.2.2.1
      exact False.elim (false_of_one_le_of_eq_zero_liliu h_pos2 h_mod0)
    | Or.inr hge2 =>
      exact Nat.le_antisymm hge2 hge

/-- **Theorem 2.1 (`unconditional_first_missing_prime_rescued_mur_pincer_liliu`):**
    Unconditional `Step209` + `Step198` Rescued-MUR Pincer on Track 2 (`D19 N`):
    For EVERY `M ≥ 1` and `k : ℕ`, constructs the unique First Missing Odd Prime `q_E` of `2 * M`
    and discharges `h_fmp` unconditionally! -/
theorem unconditional_first_missing_prime_rescued_mur_pincer_liliu
    {M : ℕ} (hM1 : 1 ≤ M) (k : ℕ) :
    ∃ q_E : ℕ,
      3 ≤ q_E ∧
      IsFirstMissingOddPrimeLiliu (2 * M) q_E ∧
      (liliuSqrtActiveOwnerPrimes M q_E).card +
        (liliuAboveSqrtLowerMURPrimesCutoff M q_E).card ≤
        (liliuRoughSurvivorSet (liliuFullLowerMURUpper M) q_E).card ∧
      (liliuPn1RoughCompositeTail
        (liliuSubTwoQBlock (liliuFullLowerMURUpper M) q_E k) q_E).card +
        (liliuAboveSqrtLowerMURPrimesCutoff M q_E).card ≤
        (liliuRoughSurvivorSet (liliuFullLowerMURUpper M) q_E).card ∧
      (M ≤ 2 * q_E + 3 →
        (liliuAboveSqrtLowerMURPrimesCutoff M q_E).card ≤
          (liliuPrimeSurvivorSet (liliuFullLowerMURUpper M) q_E).card) ∧
      (q_E < M → 2 * M < q_E * q_E →
        (liliuPn1RoughCompositeTail (liliuFullLowerMURUpper M) q_E).card = 0 ∧
        1 ≤ (liliuPrimeSurvivorSet (liliuFullLowerMURUpper M) q_E).card ∧
        ∃ p q' p_next' : ℕ,
          Nat.Prime p ∧ Nat.Prime q' ∧ 2 * M = p + q' ∧
          p < p_next' ∧ IsPrimeNat p_next') := by
  have h2M_ge1 : 1 ≤ 2 * M := by omega
  obtain ⟨q_E, _, _, _, hqE_ge3, _, hqE_fmp, _⟩ :=
    exists_isFirstMissingOddPrimeLiliu_native h2M_ge1
  have h_max_eq : max q_E 3 = q_E := by omega
  have h_fmp :
      ∀ p0 : ℕ, IsPrimeNat p0 → p0 % 2 = 1 → p0 < max q_E 3 → (2 * M) % p0 = 0 := by
    rw [h_max_eq]
    exact hqE_fmp.2.2.2
  have h_resc :=
    unconditional_strict_sqrt_owner_lt_rescued_lower_mur_survivors_liliu M q_E k h_fmp
  have h1 := h_resc.1
  have h2 := h_resc.2.1
  rw [h_max_eq] at h1 h2
  refine ⟨q_E, hqE_ge3, hqE_fmp, h1, h2, ?_, ?_⟩
  · intro hM_le
    have hM_le_max : M ≤ 2 * max q_E 3 + 3 := by
      rw [h_max_eq]
      exact hM_le
    have h_glob :=
      (step198_step209_global_rescued_survivor_to_binary_goldbach_liliu hM_le_max h_fmp).2.1
    rw [h_max_eq] at h_glob
    exact h_glob
  · intro hqE_lt_M h_sq
    have h_sqrt_le : Nat.sqrt (2 * M) + 1 ≤ q_E :=
      sqrt_add_one_le_of_lt_sq_liliu h_sq
    have h_col := liliu_sqrt_succ_horizon_collapses_all_blocks_and_composite_tail h_sqrt_le
    have hqE_mem_above : q_E ∈ liliuAboveSqrtLowerMURPrimesCutoff M q_E := by
      rw [liliuAboveSqrtLowerMURPrimesCutoff, mem_filter, mem_range]
      exact ⟨hqE_lt_M, hqE_fmp.1, hqE_fmp.2.1, by omega, h_sq⟩
    have h_above_pos : 0 < (liliuAboveSqrtLowerMURPrimesCutoff M q_E).card :=
      card_pos.mpr ⟨q_E, hqE_mem_above⟩
    have h_rough_pos : 0 < (liliuRoughSurvivorSet (liliuFullLowerMURUpper M) q_E).card := by omega
    have h_prime_ge1 : 1 ≤ (liliuPrimeSurvivorSet (liliuFullLowerMURUpper M) q_E).card := by
      rw [← h_col.2.1]
      omega
    exact ⟨h_col.1, h_prime_ge1, h_col.2.2 h_rough_pos⟩

/-- **Master Theorem 3.1 (`master_73module_unconditional_first_missing_prime_and_goldbach_lean_capstone`):**
    Complete 73-Module Master Capstone uniting `Goldbach.one_plus_one_nine_count` (`D19 N`) with:
    1. Unconditional Existence & Uniqueness of the First Missing Odd Prime `q_E` of `N`
       paired with its Factorial Lighthouse upper prime `P > max N 2`,
    2. Unconditional `Step209` + `Step198` Rescued-MUR Pincer (`h_fmp` discharged unconditionally!),
    3. Unconditional `Step212` Zero-Sum Frontier Collapse at the constructed `q_E` when `N < q_E * (q_E + 2) + 2`,
    4. Signature-Operator Quotient-One Non-Divisibility & `Step217` Factorial Wavelength Shift, and
    5. Unconditional `r ∣ N` Singleton Fiber Bound (`(liliuTight3PrimeFiber N r).card ≤ 1`). -/
theorem master_73module_unconditional_first_missing_prime_and_goldbach_lean_capstone :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (∃ q_E P : ℕ,
        max N 2 < P ∧
        IsPrimeNat P ∧
        3 ≤ q_E ∧
        q_E ≤ P ∧
        IsFirstMissingOddPrimeLiliu N q_E ∧
        (∀ q' : ℕ, IsFirstMissingOddPrimeLiliu N q' → q' = q_E) ∧
        (liliuSqrtActiveOwnerPrimes (N / 2) q_E).card +
          (liliuAboveSqrtLowerMURPrimesCutoff (N / 2) q_E).card ≤
          (liliuRoughSurvivorSet (liliuFullLowerMURUpper (N / 2)) q_E).card ∧
        (N / 2 ≤ 2 * q_E + 3 →
          (liliuAboveSqrtLowerMURPrimesCutoff (N / 2) q_E).card ≤
            (liliuPrimeSurvivorSet (liliuFullLowerMURUpper (N / 2)) q_E).card) ∧
        (N < q_E * (q_E + 2) + 2 →
          (∑ r ∈ pinchedOddPrimes919 N, (liliuTargetSieved3PrimeFiber N r q_E).card) = 0 ∧
          (fiveupPinchedQRSubfilter 9 10 N).card ≤ q_E ∧
          (((q_E : ℝ) ≤ liuMainTerm0004 N) →
            ∃ p q p_next' : ℕ,
              Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next' ∧ IsPrimeNat p_next'))) ∧
      (∀ r m_sieve : ℕ, IsPrimeNat r → N % r = 0 →
        (liliuTight3PrimeFiber N r).card ≤ 1 ∧
        (liliuTargetSieved3PrimeFiber N r m_sieve).card ≤ 1) := by
  obtain ⟨K, hK4, hCap71⟩ := master_71module_complete_es_zeros_and_goldbach_lean_capstone
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven
  have hM := hCap71 N hNK hEven
  have hN4 : 4 ≤ N := Nat.le_trans hK4 hNK
  have hN1 : 1 ≤ N := by omega
  rcases hEven with ⟨m, hm⟩
  have hN_eq_2M : 2 * (N / 2) = N := by omega
  obtain ⟨q_E, P, hP_gt, hP_isp, hqE_ge3, hqE_le_P, hqE_fmp, _⟩ :=
    exists_isFirstMissingOddPrimeLiliu_native hN1
  have h_max_eq : max q_E 3 = q_E := by omega
  have h_fmp_2M :
      ∀ p0 : ℕ, IsPrimeNat p0 → p0 % 2 = 1 → p0 < max q_E 3 → (2 * (N / 2)) % p0 = 0 := by
    rw [h_max_eq, hN_eq_2M]
    exact hqE_fmp.2.2.2
  have h_resc :=
    unconditional_strict_sqrt_owner_lt_rescued_lower_mur_survivors_liliu (N / 2) q_E 0 h_fmp_2M
  have h_resc1 := h_resc.1
  rw [h_max_eq] at h_resc1
  refine ⟨hM.1, ⟨q_E, P, hP_gt, hP_isp, hqE_ge3, hqE_le_P, hqE_fmp, ?_, h_resc1, ?_, ?_⟩, hM.2.2.2.1⟩
  · intro q' hq'
    exact isFirstMissingOddPrimeLiliu_unique hq' hqE_fmp
  · intro h_le
    have h_le_max : N / 2 ≤ 2 * max q_E 3 + 3 := by
      rw [h_max_eq]
      exact h_le
    have h_ab := hM.2.1 q_E h_le_max h_fmp_2M
    rw [h_max_eq] at h_ab
    exact h_ab
  · intro hN_lt
    exact hM.2.2.2.2.2 q_E hqE_fmp hN_lt

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.exists_isFirstMissingOddPrimeLiliu_native
#print axioms WuPaper.ESZerosBridge.isFirstMissingOddPrimeLiliu_unique
#print axioms WuPaper.ESZerosBridge.unconditional_first_missing_prime_rescued_mur_pincer_liliu
#print axioms WuPaper.ESZerosBridge.master_73module_unconditional_first_missing_prime_and_goldbach_lean_capstone
