import WR2Step242LiLiuPreArgonStep217And65ModuleMasterCapstone

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step244LiLiuRescuedLowerMURSurvivorAnd67ModuleCapstone.lean — `Step209` Rescued Lower-MUR Survivor Injection into `liliuRoughSurvivorSet`, Unconditional Strict Inequality & Master 67-Module `D19 N` Capstone

Ports the final `Step209` Section 3b theorem (`unconditional_strict_sqrt_owner_lt_rescued_lower_mur_survivors`)
onto Track 2 (`D19 N`) and welds the complete 67-module suite into the `Goldbach.All` Master Capstone.
-/

def liliuRescuedLowerMURPrimes (M q : ℕ) : Finset ℕ :=
  (range M).filter (fun p : ℕ =>
    IsPrimeNat p ∧ p % 2 = 1 ∧ max q 3 ≤ p)

def liliuAboveSqrtLowerMURPrimesCutoff (M q : ℕ) : Finset ℕ :=
  (range M).filter (fun p : ℕ =>
    IsPrimeNat p ∧ p % 2 = 1 ∧ max q 3 ≤ p ∧ 2 * M < p * p)

/-- **Theorem 1.1 (`liliu_mirror_mem_roughSurvivorSet_of_first_missing_prime`):**
    If every odd prime `p0 < max q 3` divides `2 * M` (`(2 * M) % p0 = 0`), then for every
    lower-MUR prime `p ∈ liliuRescuedLowerMURPrimes M q`, its reflected upper partner
    `liliuMirrorUpperFromLowerPrime M p = 2 * M - p` belongs to
    `liliuRoughSurvivorSet (liliuFullLowerMURUpper M) (max q 3)`. -/
theorem liliu_mirror_mem_roughSurvivorSet_of_first_missing_prime
    {M q p : ℕ}
    (h_fmp : ∀ p0 : ℕ, IsPrimeNat p0 → p0 % 2 = 1 → p0 < max q 3 → (2 * M) % p0 = 0)
    (hp : p ∈ liliuRescuedLowerMURPrimes M q) :
    p < M ∧
    liliuMirrorUpperFromLowerPrime M p ∈
      liliuRoughSurvivorSet (liliuFullLowerMURUpper M) (max q 3) := by
  rw [liliuRescuedLowerMURPrimes, mem_filter, mem_range] at hp
  obtain ⟨hp_lt_M, hp_isp, hp_odd, hq3_le_p⟩ := hp
  have hp3 : 3 ≤ p := by omega
  have hu_full : liliuMirrorUpperFromLowerPrime M p ∈ liliuFullLowerMURUpper M := by
    rw [liliuFullLowerMURUpper, mem_image]
    refine ⟨M - p, ?_, ?_⟩
    · rw [liliuFullLowerMURPrimeRadii, mem_filter, mem_range]
      have h_sub : M - (M - p) = p := by omega
      rw [h_sub]
      exact ⟨by omega, by omega, by omega, hp_isp⟩
    · unfold liliuMirrorUpperFromLowerPrime
      omega
  have hu_props := liliuFullLowerMURUpper_mem_props hu_full
  have hu2 : 2 ≤ liliuMirrorUpperFromLowerPrime M p := by omega
  have hu_odd : (liliuMirrorUpperFromLowerPrime M p) % 2 = 1 := hu_props.2.2.2.1
  have hu_npv2 : 1 ≤ (liliuMirrorUpperFromLowerPrime M p) % 2 := by omega
  have h_sub_u : 2 * M - liliuMirrorUpperFromLowerPrime M p = p := by
    unfold liliuMirrorUpperFromLowerPrime
    omega
  refine ⟨hp_lt_M, ?_⟩
  rw [liliuRoughSurvivorSet, mem_filter]
  refine ⟨hu_full, hu2, ?_⟩
  intro d hd_range hd2
  rw [mem_range] at hd_range
  obtain ⟨p0, hp0_isp, hp0_dvd_d⟩ :=
    exists_prime_divisor_aux d d hd2 (Nat.le_refl d)
  have hd_pos : 0 < d := by omega
  have hp0_pos : 0 < p0 := isPrimeNat_pos hp0_isp
  have hp0_le_d : p0 ≤ d := dvd_le_of_pos hp0_dvd_d hd_pos
  have hp0_lt_q3 : p0 < max q 3 := Nat.lt_of_le_of_lt hp0_le_d hd_range
  have hu_npv_p0 : 1 ≤ (liliuMirrorUpperFromLowerPrime M p) % p0 := by
    rcases isPrimeNat_eq_two_or_odd_liliu hp0_isp with hp0_eq2 | hp0_odd
    · rw [hp0_eq2]
      exact hu_npv2
    · have h2M_mod_p0 : (2 * M) % p0 = 0 := h_fmp p0 hp0_isp hp0_odd hp0_lt_q3
      have hp0_ne_p : p0 ≠ 2 * M - liliuMirrorUpperFromLowerPrime M p := by
        rw [h_sub_u]
        omega
      exact (liliuFullLowerMURUpper_shielded_from_target_prime_divisors
        hu_full hp0_isp h2M_mod_p0 hp0_ne_p).1
  if hu_mod_d0 : (liliuMirrorUpperFromLowerPrime M p) % d = 0 then
    have hd_dvd_u : d ∣ liliuMirrorUpperFromLowerPrime M p := by
      have h_div :
          d * (liliuMirrorUpperFromLowerPrime M p / d) +
            (liliuMirrorUpperFromLowerPrime M p) % d =
          liliuMirrorUpperFromLowerPrime M p :=
        Nat.div_add_mod (liliuMirrorUpperFromLowerPrime M p) d
      exact ⟨liliuMirrorUpperFromLowerPrime M p / d, by omega⟩
    have hp0_dvd_u : p0 ∣ liliuMirrorUpperFromLowerPrime M p :=
      Nat.dvd_trans hp0_dvd_d hd_dvd_u
    have hu_mod_p0_0 : (liliuMirrorUpperFromLowerPrime M p) % p0 = 0 :=
      (mod_eq_zero_and_mul_div_of_dvd_liliu hp0_pos hp0_dvd_u).1
    omega
  else
    omega

theorem disjoint_liliuSqrtActiveOwnerPrimes_aboveSqrtCutoff (M q : ℕ) :
    Disjoint (liliuSqrtActiveOwnerPrimes M (max q 3)) (liliuAboveSqrtLowerMURPrimesCutoff M q) := by
  apply Finset.disjoint_left.mpr
  intro p h_le h_gt
  rw [liliuSqrtActiveOwnerPrimes, mem_filter] at h_le
  rw [liliuAboveSqrtLowerMURPrimesCutoff, mem_filter] at h_gt
  have h1 : p * p ≤ 2 * M := h_le.2.2.2.2
  have h2 : 2 * M < p * p := h_gt.2.2.2.2
  omega

theorem liliuSqrtActiveOwnerPrimes_subset_rescuedLowerMURPrimes (M q : ℕ) :
    liliuSqrtActiveOwnerPrimes M (max q 3) ⊆ liliuRescuedLowerMURPrimes M q := by
  intro p hp
  have hp_lt_M : p < M := (liliuSqrtActiveOwnerPrimes_mirror_mem_fullLowerMURUpper hp).1
  rw [liliuSqrtActiveOwnerPrimes, mem_filter] at hp
  rw [liliuRescuedLowerMURPrimes, mem_filter, mem_range]
  exact ⟨hp_lt_M, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩

theorem liliuAboveSqrtCutoff_subset_rescuedLowerMURPrimes (M q : ℕ) :
    liliuAboveSqrtLowerMURPrimesCutoff M q ⊆ liliuRescuedLowerMURPrimes M q := by
  intro p hp
  rw [liliuAboveSqrtLowerMURPrimesCutoff, mem_filter] at hp
  rw [liliuRescuedLowerMURPrimes, mem_filter]
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩

/-- **Theorem 2.1 (`unconditional_strict_sqrt_owner_lt_rescued_lower_mur_survivors_liliu`):**
    Ports `Step209` Section 3b (`unconditional_strict_sqrt_owner_lt_rescued_lower_mur_survivors`)
    onto Track 2 (`D19 N`). -/
theorem unconditional_strict_sqrt_owner_lt_rescued_lower_mur_survivors_liliu
    (M q k : ℕ)
    (h_fmp : ∀ p0 : ℕ, IsPrimeNat p0 → p0 % 2 = 1 → p0 < max q 3 → (2 * M) % p0 = 0) :
    (liliuSqrtActiveOwnerPrimes M (max q 3)).card +
      (liliuAboveSqrtLowerMURPrimesCutoff M q).card ≤
      (liliuRoughSurvivorSet (liliuFullLowerMURUpper M) (max q 3)).card ∧
    (liliuPn1RoughCompositeTail
      (liliuSubTwoQBlock (liliuFullLowerMURUpper M) (max q 3) k) (max q 3)).card +
      (liliuAboveSqrtLowerMURPrimesCutoff M q).card ≤
      (liliuRoughSurvivorSet (liliuFullLowerMURUpper M) (max q 3)).card ∧
    ((∃ p : ℕ, IsPrimeNat p ∧ p % 2 = 1 ∧ p < M ∧ 2 * M < p * p ∧ (2 * M) % p ≠ 0) →
      1 ≤ (liliuAboveSqrtLowerMURPrimesCutoff M q).card ∧
      (liliuSqrtActiveOwnerPrimes M (max q 3)).card <
        (liliuRoughSurvivorSet (liliuFullLowerMURUpper M) (max q 3)).card ∧
      (liliuPn1RoughCompositeTail
        (liliuSubTwoQBlock (liliuFullLowerMURUpper M) (max q 3) k) (max q 3)).card <
        (liliuRoughSurvivorSet (liliuFullLowerMURUpper M) (max q 3)).card) := by
  set U_resc := liliuSqrtActiveOwnerPrimes M (max q 3) ∪ liliuAboveSqrtLowerMURPrimesCutoff M q
  have h_u_card :
      U_resc.card =
        (liliuSqrtActiveOwnerPrimes M (max q 3)).card +
          (liliuAboveSqrtLowerMURPrimesCutoff M q).card :=
    card_union_of_disjoint (disjoint_liliuSqrtActiveOwnerPrimes_aboveSqrtCutoff M q)
  have h_u_sub_resc : U_resc ⊆ liliuRescuedLowerMURPrimes M q :=
    union_subset
      (liliuSqrtActiveOwnerPrimes_subset_rescuedLowerMURPrimes M q)
      (liliuAboveSqrtCutoff_subset_rescuedLowerMURPrimes M q)
  have h_sub_rough :
      U_resc.image (liliuMirrorUpperFromLowerPrime M) ⊆
        liliuRoughSurvivorSet (liliuFullLowerMURUpper M) (max q 3) := by
    intro u hu
    rw [mem_image] at hu
    obtain ⟨p, hp_u, rfl⟩ := hu
    exact (liliu_mirror_mem_roughSurvivorSet_of_first_missing_prime h_fmp (h_u_sub_resc hp_u)).2
  have h_inj : Set.InjOn (liliuMirrorUpperFromLowerPrime M) (↑U_resc : Set ℕ) := by
    intro a ha b hb h_eq
    rw [mem_coe] at ha hb
    have ha_lt : a < M :=
      (liliu_mirror_mem_roughSurvivorSet_of_first_missing_prime h_fmp (h_u_sub_resc ha)).1
    have hb_lt : b < M :=
      (liliu_mirror_mem_roughSurvivorSet_of_first_missing_prime h_fmp (h_u_sub_resc hb)).1
    unfold liliuMirrorUpperFromLowerPrime at h_eq
    omega
  have h_img_card :
      (U_resc.image (liliuMirrorUpperFromLowerPrime M)).card = U_resc.card :=
    Finset.card_image_of_injOn h_inj
  have h_sum_le :
      (liliuSqrtActiveOwnerPrimes M (max q 3)).card +
        (liliuAboveSqrtLowerMURPrimesCutoff M q).card ≤
      (liliuRoughSurvivorSet (liliuFullLowerMURUpper M) (max q 3)).card := by
    rw [← h_u_card, ← h_img_card]
    exact card_le_card h_sub_rough
  have h_tail_le :=
    liliuSubTwoQBlock_roughCompositeTail_card_le_sqrtActiveOwnerPrimes M (max q 3) k
  refine ⟨h_sum_le, by omega, ?_⟩
  intro h_ex
  obtain ⟨p, hp_isp, hp_odd, hp_lt_M, hp_sq, hp_nmod⟩ := h_ex
  have hq3_le_p : max q 3 ≤ p := by
    match Nat.lt_or_ge p (max q 3) with
    | Or.inr hge => exact hge
    | Or.inl hlt =>
      have h0 := h_fmp p hp_isp hp_odd hlt
      exact False.elim (hp_nmod h0)
  have hp_mem : p ∈ liliuAboveSqrtLowerMURPrimesCutoff M q := by
    rw [liliuAboveSqrtLowerMURPrimesCutoff, mem_filter, mem_range]
    exact ⟨hp_lt_M, hp_isp, hp_odd, hq3_le_p, hp_sq⟩
  have h_pos : 0 < (liliuAboveSqrtLowerMURPrimesCutoff M q).card :=
    card_pos.mpr ⟨p, hp_mem⟩
  exact ⟨by omega, by omega, by omega⟩

/-- **Master Theorem 3.1 (`master_67module_complete_step208_to_step217_rescued_survivor_capstone`):**
    Complete 67-Module Master Capstone uniting `Goldbach.one_plus_one_nine_count` (`D19 N`),
    the `Step209` Rescued Lower-MUR Survivor Injection into `liliuRoughSurvivorSet` &
    Unconditional Strict Inequality (`unconditional_strict_sqrt_owner_lt_rescued_lower_mur_survivors_liliu`),
    the `Step217` Factorial Wavelength Shift & Unconditional `r ∣ N` Singleton Fiber Bound,
    the `Step215` & `Step216` OMC Reflection & Difference-of-Squares Shell Packing,
    the `Step211` Local Sub-`2q` Single-Block Goldbach Closure, and
    the `Step212` First-Missing-Prime `q_E` Zero-Sum Collapse. -/
theorem master_67module_complete_step208_to_step217_rescued_survivor_capstone :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (∀ q k : ℕ,
        (∀ p0 : ℕ, IsPrimeNat p0 → p0 % 2 = 1 → p0 < max q 3 → (2 * (N / 2)) % p0 = 0) →
        (liliuPn1RoughCompositeTail
          (liliuSubTwoQBlock (liliuFullLowerMURUpper (N / 2)) (max q 3) k) (max q 3)).card +
          (liliuAboveSqrtLowerMURPrimesCutoff (N / 2) q).card ≤
          (liliuRoughSurvivorSet (liliuFullLowerMURUpper (N / 2)) (max q 3)).card) ∧
      (∀ r m_sieve : ℕ, IsPrimeNat r → N % r = 0 →
        (liliuTight3PrimeFiber N r).card ≤ 1 ∧
        (liliuTargetSieved3PrimeFiber N r m_sieve).card ≤ 1) ∧
      (∀ q k : ℕ,
        (liliuSqrtActiveOwnerPrimes (N / 2) q).card <
          (liliuRoughSurvivorSet
            (liliuSubTwoQBlock (liliuFullLowerMURUpper (N / 2)) q k) q).card →
          ∃ p q' p_next' : ℕ,
            Nat.Prime p ∧ Nat.Prime q' ∧ 2 * (N / 2) = p + q' ∧
            p < p_next' ∧ IsPrimeNat p_next') ∧
      (∀ q_E : ℕ, IsFirstMissingOddPrimeLiliu N q_E → N < q_E * (q_E + 2) + 2 →
        (∑ r ∈ pinchedOddPrimes919 N, (liliuTargetSieved3PrimeFiber N r q_E).card) = 0 ∧
        (fiveupPinchedQRSubfilter 9 10 N).card ≤ q_E ∧
        (((q_E : ℝ) ≤ liuMainTerm0004 N) →
          ∃ p q p_next' : ℕ,
            Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next' ∧ IsPrimeNat p_next')) := by
  obtain ⟨K, hK4, hCap65⟩ := master_65module_complete_step208_to_step217_goldbach_lean_capstone
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven
  have hM := hCap65 N hNK hEven
  refine ⟨hM.1, ?_, hM.2.1, hM.2.2.2.2.1, hM.2.2.2.2.2⟩
  intro q k h_fmp
  exact (unconditional_strict_sqrt_owner_lt_rescued_lower_mur_survivors_liliu
    (N / 2) q k h_fmp).2.1

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.liliu_mirror_mem_roughSurvivorSet_of_first_missing_prime
#print axioms WuPaper.ESZerosBridge.unconditional_strict_sqrt_owner_lt_rescued_lower_mur_survivors_liliu
#print axioms WuPaper.ESZerosBridge.master_67module_complete_step208_to_step217_rescued_survivor_capstone
