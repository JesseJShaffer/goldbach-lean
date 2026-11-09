import WR2Step250LiLiuNativeFirstMissingPrimeAnd73ModuleMasterCapstone

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step252LiLiuFiberSpaceConcreteKbAnd75ModuleMasterCapstone.lean — `FiberSpace` Track A `concreteKb` Carrier (`Step24` & `Step207`) Non-Self-Obstruction & Master 75-Module `D19 N` Capstone
-/

def liliuConcreteKbRadii (M : ℕ) : Finset ℕ :=
  (range (M - 2)).filter (fun R : ℕ =>
    1 ≤ R ∧
    1 ≤ (M - R) % 2 ∧
    IsPrimeNat (M - R) ∧
    1 ≤ M % (M - R))

def liliuConcreteKbUpper (M : ℕ) : Finset ℕ :=
  (liliuConcreteKbRadii M).image (fun R : ℕ => M + R)

theorem liliuConcreteKbUpper_subset_fullLowerMURUpper_and_non_self_obstructing (M : ℕ) :
    liliuConcreteKbRadii M ⊆ liliuFullLowerMURPrimeRadii M ∧
    liliuConcreteKbUpper M ⊆ liliuFullLowerMURUpper M ∧
    (liliuConcreteKbUpper M).card ≤ (liliuFullLowerMURUpper M).card ∧
    (∀ u ∈ liliuConcreteKbUpper M,
      let p := 2 * M - u
      IsPrimeNat p ∧ 1 ≤ M % p ∧ 1 ≤ (2 * M) % p ∧ 1 ≤ u % p) := by
  have h_rad_sub : liliuConcreteKbRadii M ⊆ liliuFullLowerMURPrimeRadii M := by
    intro R hR
    rw [liliuConcreteKbRadii, mem_filter] at hR
    rw [liliuFullLowerMURPrimeRadii, mem_filter]
    exact ⟨hR.1, hR.2.1, hR.2.2.1, hR.2.2.2.1⟩
  have h_up_sub : liliuConcreteKbUpper M ⊆ liliuFullLowerMURUpper M := by
    intro u hu
    rw [liliuConcreteKbUpper, mem_image] at hu
    obtain ⟨R, hR, rfl⟩ := hu
    rw [liliuFullLowerMURUpper, mem_image]
    exact ⟨R, h_rad_sub hR, rfl⟩
  have h_card_le : (liliuConcreteKbUpper M).card ≤ (liliuFullLowerMURUpper M).card :=
    card_le_card h_up_sub
  refine ⟨h_rad_sub, h_up_sub, h_card_le, ?_⟩
  intro u hu
  dsimp only
  rw [liliuConcreteKbUpper, mem_image] at hu
  obtain ⟨R, hR, rfl⟩ := hu
  rw [liliuConcreteKbRadii, mem_filter, mem_range] at hR
  obtain ⟨hR_lt, hR1, hMR_npv2, hMR_isp, hM_npv⟩ := hR
  have h_sub_eq : 2 * M - (M + R) = M - R := by omega
  rw [h_sub_eq]
  set p := M - R
  have hp_two : 2 ≤ p := hMR_isp.1
  have hp_pos : 0 < p := by omega
  have hp_mod2_lt : p % 2 < 2 := Nat.mod_lt p (by omega : 0 < 2)
  have hp_odd : p % 2 = 1 := by omega
  have hM_mod_lt : M % p < p := Nat.mod_lt M hp_pos
  have hM_div : M = p * (M / p) + M % p := (Nat.div_add_mod M p).symm
  have h_sig := (liliu_sig_mul_operator_sound (a := 2) hM_div).2
  have h_sig_eval : (liliuSigMulOperator 2 p (M / p) (M % p)).2 = (2 * (M % p)) % p := rfl
  have h_2rem_pos : 1 ≤ (2 * (M % p)) % p :=
    two_mul_rem_mod_pos_of_odd_liliu hp_odd hM_npv hM_mod_lt
  have h_2M_pos : 1 ≤ (2 * M) % p := by
    rw [h_sig, h_sig_eval]
    exact h_2rem_pos
  have h_2M_decomp : p * 1 + (M + R) = 2 * M := by omega
  have h_mod_eq : (2 * M) % p = (M + R) % p := by
    rw [← h_2M_decomp]
    exact mul_add_mod_self_left_liliu p 1 (M + R)
  have h_u_pos : 1 ≤ (M + R) % p := by
    rw [← h_mod_eq]
    exact h_2M_pos
  exact ⟨hMR_isp, hM_npv, h_2M_pos, h_u_pos⟩

theorem liliu_mirror_mem_concreteKbUpper_of_nondividing_two_mul_M
    {M p : ℕ} (hp_isp : IsPrimeNat p) (hp_odd : p % 2 = 1)
    (hp_lt_M : p < M) (h2M_npv : 1 ≤ (2 * M) % p) :
    1 ≤ M % p ∧ liliuMirrorUpperFromLowerPrime M p ∈ liliuConcreteKbUpper M := by
  have hp2 : 2 ≤ p := hp_isp.1
  have hp3 : 3 ≤ p := by omega
  have hp_pos : 0 < p := by omega
  have hM_dvd_2M : M ∣ 2 * M := ⟨2, Nat.mul_comm 2 M⟩
  have hM_npv : 1 ≤ M % p :=
    (nonPVen_divisor_inheritance_liliu hp_pos hM_dvd_2M h2M_npv).1
  refine ⟨hM_npv, ?_⟩
  rw [liliuConcreteKbUpper, mem_image]
  refine ⟨M - p, ?_, ?_⟩
  · rw [liliuConcreteKbRadii, mem_filter, mem_range]
    have h_sub : M - (M - p) = p := by omega
    rw [h_sub]
    exact ⟨by omega, by omega, by omega, hp_isp, hM_npv⟩
  · unfold liliuMirrorUpperFromLowerPrime
    omega

theorem liliuRoughSurvivorSet_concreteKbUpper_subset_fullLowerMURUpper (M q : ℕ) :
    liliuRoughSurvivorSet (liliuConcreteKbUpper M) q ⊆
      liliuRoughSurvivorSet (liliuFullLowerMURUpper M) q ∧
    liliuPrimeSurvivorSet (liliuConcreteKbUpper M) q ⊆
      liliuPrimeSurvivorSet (liliuFullLowerMURUpper M) q ∧
    (liliuRoughSurvivorSet (liliuConcreteKbUpper M) q).card ≤
      (liliuRoughSurvivorSet (liliuFullLowerMURUpper M) q).card := by
  have h_kb_sub := (liliuConcreteKbUpper_subset_fullLowerMURUpper_and_non_self_obstructing M).2.1
  have h_rough_sub :
      liliuRoughSurvivorSet (liliuConcreteKbUpper M) q ⊆
        liliuRoughSurvivorSet (liliuFullLowerMURUpper M) q := by
    intro u hu
    rw [liliuRoughSurvivorSet, mem_filter] at hu ⊢
    exact ⟨h_kb_sub hu.1, hu.2⟩
  have h_prime_sub :
      liliuPrimeSurvivorSet (liliuConcreteKbUpper M) q ⊆
        liliuPrimeSurvivorSet (liliuFullLowerMURUpper M) q := by
    intro u hu
    rw [liliuPrimeSurvivorSet, mem_filter] at hu ⊢
    exact ⟨h_kb_sub hu.1, hu.2⟩
  exact ⟨h_rough_sub, h_prime_sub, card_le_card h_rough_sub⟩

theorem master_75module_fiberspace_concreteKb_and_goldbach_lean_capstone :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (liliuConcreteKbUpper (N / 2) ⊆ liliuFullLowerMURUpper (N / 2) ∧
       ∀ u ∈ liliuConcreteKbUpper (N / 2),
         1 ≤ (N / 2) % (2 * (N / 2) - u) ∧
         1 ≤ (2 * (N / 2)) % (2 * (N / 2) - u) ∧
         1 ≤ u % (2 * (N / 2) - u)) ∧
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
  obtain ⟨K, hK4, hCap73⟩ := master_73module_unconditional_first_missing_prime_and_goldbach_lean_capstone
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven
  have hM := hCap73 N hNK hEven
  have h_kb := liliuConcreteKbUpper_subset_fullLowerMURUpper_and_non_self_obstructing (N / 2)
  refine ⟨hM.1, ⟨h_kb.2.1, ?_⟩, hM.2.1, hM.2.2⟩
  intro u hu
  have h_u := h_kb.2.2.2 u hu
  exact ⟨h_u.2.1, h_u.2.2.1, h_u.2.2.2⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.liliuConcreteKbUpper_subset_fullLowerMURUpper_and_non_self_obstructing
#print axioms WuPaper.ESZerosBridge.liliu_mirror_mem_concreteKbUpper_of_nondividing_two_mul_M
#print axioms WuPaper.ESZerosBridge.liliuRoughSurvivorSet_concreteKbUpper_subset_fullLowerMURUpper
#print axioms WuPaper.ESZerosBridge.master_75module_fiberspace_concreteKb_and_goldbach_lean_capstone
