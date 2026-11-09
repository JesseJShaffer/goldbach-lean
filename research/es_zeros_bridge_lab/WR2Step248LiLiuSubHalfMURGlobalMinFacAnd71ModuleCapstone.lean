import WR2Step246LiLiuUpperHalfIntervalAnd69ModuleMasterCapstone

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step248LiLiuSubHalfMURGlobalMinFacAnd71ModuleCapstone.lean — `Step197`/`Step198` Sub-Half-MUR Global `Nat.minFac` Bijection, End-to-End `Step209` Rescued-Survivor Goldbach Closure & Master 71-Module `D19 N` Capstone

Ports the global `M - 4` diameter bound on `liliuFullLowerMURUpper M`, the global
Sub-Half-MUR `Nat.minFac` bijection (`M ≤ 2 * q + 3`), and the end-to-end `Step209`
Rescued-Survivor Goldbach extractor onto Track 2 (`D19 N`), welding all 71 modules into
the `Goldbach.All` Master Capstone.
-/

/-- **Lemma 1.1 (`liliuFullLowerMURUpper_diameter_le_M_sub_four`):**
    Every pair `a0, b0 ∈ liliuFullLowerMURUpper M` with `a0 ≤ b0` satisfies
    `M + 1 ≤ a0`, `b0 ≤ 2 * M - 3`, and `b0 - a0 ≤ M - 4`. -/
theorem liliuFullLowerMURUpper_diameter_le_M_sub_four
    {M a0 b0 : ℕ} (ha0 : a0 ∈ liliuFullLowerMURUpper M) (hb0 : b0 ∈ liliuFullLowerMURUpper M) :
    M + 1 ≤ a0 ∧ b0 ≤ 2 * M - 3 ∧ b0 - a0 ≤ M - 4 := by
  have ha := liliuFullLowerMURUpper_mem_props ha0
  have hb := liliuFullLowerMURUpper_mem_props hb0
  exact ⟨ha.1, hb.2.1, by omega⟩

theorem liliu_global_roughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes
    {M q u : ℕ}
    (hu : u ∈ liliuPn1RoughCompositeTail (liliuFullLowerMURUpper M) q) :
    u.minFac ∈ liliuSqrtActiveOwnerPrimes M q ∧
    q ≤ u.minFac ∧
    u % u.minFac = 0 ∧
    u.minFac % 2 = 1 ∧
    u % 2 = 1 := by
  rw [liliuPn1RoughCompositeTail, mem_filter] at hu
  obtain ⟨hu_full, hu2, hu_rough, hu_comp⟩ := hu
  have hu_props := liliuFullLowerMURUpper_mem_props hu_full
  have hu_lt_2M : u < 2 * M := hu_props.2.2.1
  have hu_odd : u % 2 = 1 := hu_props.2.2.2.1
  have hu_npv2 : 1 ≤ u % 2 := by omega
  have h_mf := minFac_mul_self_le_of_not_isPrimeNat_liliu hu2 hu_comp
  have h_mf_isp : IsPrimeNat u.minFac := h_mf.1
  have h_mf_mod0 : u % u.minFac = 0 := h_mf.2.1
  have h_mf_le_u : u.minFac ≤ u := h_mf.2.2.1
  have h_mf_sq_le : u.minFac * u.minFac ≤ u := h_mf.2.2.2
  have h_mf_two : 2 ≤ u.minFac := h_mf_isp.1
  have h_mf_npv2 : 1 ≤ u.minFac % 2 :=
    (nonPVen_divisor_inheritance_liliu (by omega : 0 < 2) (Nat.minFac_dvd u) hu_npv2).1
  have h_mf_lt_2 : u.minFac % 2 < 2 := Nat.mod_lt u.minFac (by omega : 0 < 2)
  have h_mf_odd : u.minFac % 2 = 1 := by omega
  have h_q_le_mf : q ≤ u.minFac := by
    match Nat.lt_or_ge u.minFac q with
    | Or.inr hge => exact hge
    | Or.inl hlt =>
      have h_pos := hu_rough u.minFac (mem_range.mpr hlt) h_mf_two
      omega
  have h_mf_lt_2M : u.minFac < 2 * M := Nat.lt_of_le_of_lt h_mf_le_u hu_lt_2M
  have h_mf_lt_range : u.minFac < 2 * M + 1 :=
    Nat.lt_trans h_mf_lt_2M (Nat.lt_succ_self (2 * M))
  have h_mf_sq_2M : u.minFac * u.minFac ≤ 2 * M :=
    Nat.le_of_lt (Nat.lt_of_le_of_lt h_mf_sq_le hu_lt_2M)
  refine ⟨?_, h_q_le_mf, h_mf_mod0, h_mf_odd, hu_odd⟩
  rw [liliuSqrtActiveOwnerPrimes, mem_filter, mem_range]
  exact ⟨h_mf_lt_range, h_mf_isp, h_mf_odd, h_q_le_mf, h_mf_sq_2M⟩

/-- **Theorem 2.1 (`liliuFullLowerMURUpper_roughCompositeTail_card_le_sqrtOwners_of_M_le`):**
    Global Sub-Half-MUR `Nat.minFac` Injection (`Step197`/`Step198`) on Track 2:
    Whenever `M ≤ 2 * q + 3`:
    1. `(liliuPn1RoughCompositeTail (liliuFullLowerMURUpper M) q).card ≤ (liliuSqrtActiveOwnerPrimes M q).card`, and
    2. `(liliuRoughSurvivorSet (liliuFullLowerMURUpper M) q).card - (liliuSqrtActiveOwnerPrimes M q).card ≤ (liliuPrimeSurvivorSet (liliuFullLowerMURUpper M) q).card`. -/
theorem liliuFullLowerMURUpper_roughCompositeTail_card_le_sqrtOwners_of_M_le
    {M q : ℕ} (hM_le : M ≤ 2 * q + 3) :
    (liliuPn1RoughCompositeTail (liliuFullLowerMURUpper M) q).card ≤
      (liliuSqrtActiveOwnerPrimes M q).card ∧
    (liliuRoughSurvivorSet (liliuFullLowerMURUpper M) q).card -
      (liliuSqrtActiveOwnerPrimes M q).card ≤
      (liliuPrimeSurvivorSet (liliuFullLowerMURUpper M) q).card := by
  have h_sub :
      (liliuPn1RoughCompositeTail (liliuFullLowerMURUpper M) q).image Nat.minFac ⊆
        liliuSqrtActiveOwnerPrimes M q := by
    intro p hp
    rw [mem_image] at hp
    obtain ⟨u, hu, rfl⟩ := hp
    exact (liliu_global_roughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes hu).1
  have h_inj :
      Set.InjOn Nat.minFac
        (↑(liliuPn1RoughCompositeTail (liliuFullLowerMURUpper M) q) : Set ℕ) := by
    intro a0 ha0 b0 hb0 h_mf_eq
    rw [mem_coe] at ha0 hb0
    have ha_props := liliu_global_roughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes ha0
    have hb_props := liliu_global_roughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes hb0
    have ha_full : a0 ∈ liliuFullLowerMURUpper M := by
      rw [liliuPn1RoughCompositeTail, mem_filter] at ha0
      exact ha0.1
    have hb_full : b0 ∈ liliuFullLowerMURUpper M := by
      rw [liliuPn1RoughCompositeTail, mem_filter] at hb0
      exact hb0.1
    have hp_odd : a0.minFac % 2 = 1 := ha_props.2.2.2.1
    have ha_odd : a0 % 2 = 1 := ha_props.2.2.2.2
    have hb_odd : b0 % 2 = 1 := hb_props.2.2.2.2
    have ha_mod_p : a0 % a0.minFac = 0 := ha_props.2.2.1
    have hb_mod_p : b0 % a0.minFac = 0 := by
      rw [h_mf_eq]
      exact hb_props.2.2.1
    have h_mod_eq : a0 % a0.minFac = b0 % a0.minFac := by rw [ha_mod_p, hb_mod_p]
    have hq_le_p : q ≤ a0.minFac := ha_props.2.1
    have hp_ge2 : 2 ≤ a0.minFac := by
      have hp_mem := ha_props.1
      rw [liliuSqrtActiveOwnerPrimes, mem_filter] at hp_mem
      exact hp_mem.2.1.1
    have h_2q_le_2p : 2 * q ≤ 2 * max a0.minFac 1 := by
      have h_le_max : q ≤ max a0.minFac 1 := by omega
      exact Nat.mul_le_mul_left 2 h_le_max
    match Nat.lt_or_ge a0 b0 with
    | Or.inl hlt =>
      have hle : a0 ≤ b0 := Nat.le_of_lt hlt
      have h_diam := (liliuFullLowerMURUpper_diameter_le_M_sub_four ha_full hb_full).2.2
      have h_a0_ge : M + 1 ≤ a0 := (liliuFullLowerMURUpper_diameter_le_M_sub_four ha_full hb_full).1
      have h_b0_le : b0 ≤ 2 * M - 3 := (liliuFullLowerMURUpper_diameter_le_M_sub_four ha_full hb_full).2.1
      have h_M4 : 4 ≤ M := by omega
      have h_d_p : b0 - a0 < 2 * max a0.minFac 1 := by omega
      exact eq_of_sub_lt_two_max_of_odd_of_mod_eq_liliu hp_odd hle h_d_p ha_odd hb_odd h_mod_eq
    | Or.inr hge =>
      have h_diam := (liliuFullLowerMURUpper_diameter_le_M_sub_four hb_full ha_full).2.2
      have h_b0_ge : M + 1 ≤ b0 := (liliuFullLowerMURUpper_diameter_le_M_sub_four hb_full ha_full).1
      have h_a0_le : a0 ≤ 2 * M - 3 := (liliuFullLowerMURUpper_diameter_le_M_sub_four hb_full ha_full).2.1
      have h_M4 : 4 ≤ M := by omega
      have h_d_p : a0 - b0 < 2 * max a0.minFac 1 := by omega
      exact (eq_of_sub_lt_two_max_of_odd_of_mod_eq_liliu hp_odd hge h_d_p hb_odd ha_odd h_mod_eq.symm).symm
  have h_card_img :
      ((liliuPn1RoughCompositeTail (liliuFullLowerMURUpper M) q).image Nat.minFac).card =
        (liliuPn1RoughCompositeTail (liliuFullLowerMURUpper M) q).card :=
    Finset.card_image_of_injOn h_inj
  have h_tail_le :
      (liliuPn1RoughCompositeTail (liliuFullLowerMURUpper M) q).card ≤
        (liliuSqrtActiveOwnerPrimes M q).card := by
    rw [← h_card_img]
    exact card_le_card h_sub
  have h_part :=
    liliuRoughSurvivorSet_card_eq_primeSurvivors_add_compositeTail (liliuFullLowerMURUpper M) q
  exact ⟨h_tail_le, by omega⟩

/-- **Theorem 2.2 (`step198_step209_global_rescued_survivor_to_binary_goldbach_liliu`):**
    End-to-End Global Rescued-Survivor Pincer (`Step198` + `Step209`) on Track 2:
    Whenever `M ≤ 2 * max q 3 + 3` and `h_fmp : ∀ p0 : ℕ, IsPrimeNat p0 → p0 % 2 = 1 → p0 < max q 3 → (2 * M) % p0 = 0`:
    1. `(liliuPn1RoughCompositeTail (liliuFullLowerMURUpper M) (max q 3)).card ≤ (liliuSqrtActiveOwnerPrimes M (max q 3)).card`,
    2. `(liliuAboveSqrtLowerMURPrimesCutoff M q).card ≤ (liliuPrimeSurvivorSet (liliuFullLowerMURUpper M) (max q 3)).card`, and
    3. Given `4 ≤ M`, `M ≠ 5`, and `h_bertrand : 6 ≤ M → ∃ p : ℕ, IsPrimeNat p ∧ M / 2 < p ∧ p ≤ 2 * (M / 2)`,
       `1 ≤ (liliuPrimeSurvivorSet (liliuFullLowerMURUpper M) (max q 3)).card` holds unconditionally
       and extracts a Binary Goldbach partition `2 * M = p + q'` paired with `p < p_next'`! -/
theorem step198_step209_global_rescued_survivor_to_binary_goldbach_liliu
    {M q : ℕ}
    (hM_le : M ≤ 2 * max q 3 + 3)
    (h_fmp : ∀ p0 : ℕ, IsPrimeNat p0 → p0 % 2 = 1 → p0 < max q 3 → (2 * M) % p0 = 0) :
    (liliuPn1RoughCompositeTail (liliuFullLowerMURUpper M) (max q 3)).card ≤
      (liliuSqrtActiveOwnerPrimes M (max q 3)).card ∧
    (liliuAboveSqrtLowerMURPrimesCutoff M q).card ≤
      (liliuPrimeSurvivorSet (liliuFullLowerMURUpper M) (max q 3)).card ∧
    (4 ≤ M → M ≠ 5 →
      (6 ≤ M → ∃ p : ℕ, IsPrimeNat p ∧ M / 2 < p ∧ p ≤ 2 * (M / 2)) →
      1 ≤ (liliuPrimeSurvivorSet (liliuFullLowerMURUpper M) (max q 3)).card ∧
      ∃ p q' p_next' : ℕ,
        Nat.Prime p ∧ Nat.Prime q' ∧ 2 * M = p + q' ∧
        p < p_next' ∧ IsPrimeNat p_next') := by
  have h_glob := liliuFullLowerMURUpper_roughCompositeTail_card_le_sqrtOwners_of_M_le hM_le
  have h_resc :=
    unconditional_strict_sqrt_owner_lt_rescued_lower_mur_survivors_liliu M q 0 h_fmp
  have h_part :=
    liliuRoughSurvivorSet_card_eq_primeSurvivors_add_compositeTail
      (liliuFullLowerMURUpper M) (max q 3)
  have h_above_le_prime :
      (liliuAboveSqrtLowerMURPrimesCutoff M q).card ≤
        (liliuPrimeSurvivorSet (liliuFullLowerMURUpper M) (max q 3)).card := by
    have h1 := h_glob.1
    have h2 := h_resc.1
    omega
  refine ⟨h_glob.1, h_above_le_prime, ?_⟩
  intro hM4 hM_ne5 h_bert
  have h_pin :=
    bertrand_upper_half_prime_discharges_step209_strict_pincer_liliu
      (k := 0) hM4 hM_ne5 h_bert h_fmp
  have h_above_ge1 : 1 ≤ (liliuAboveSqrtLowerMURPrimesCutoff M q).card := h_pin.1
  have h_prime_ge1 : 1 ≤ (liliuPrimeSurvivorSet (liliuFullLowerMURUpper M) (max q 3)).card :=
    Nat.le_trans h_above_ge1 h_above_le_prime
  have h_prime_pos : 0 < (liliuPrimeSurvivorSet (liliuFullLowerMURUpper M) (max q 3)).card := by omega
  refine ⟨h_prime_ge1, ?_⟩
  obtain ⟨u, hu⟩ := card_pos.mp h_prime_pos
  rw [liliuPrimeSurvivorSet, mem_filter] at hu
  obtain ⟨hu_full, _, _, hu_isp⟩ := hu
  have h_props := liliuFullLowerMURUpper_mem_props hu_full
  have hp_nat : Nat.Prime (2 * M - u) := isPrimeNat_to_natPrime_liliu h_props.2.2.2.2.1
  have hu_nat : Nat.Prime u := isPrimeNat_to_natPrime_liliu hu_isp
  obtain ⟨p_next', hp_lt, hp_next_isp⟩ :=
    hasNextPrimeConnection_unconditional (2 * M - u)
  exact ⟨2 * M - u, u, p_next', hp_nat, hu_nat, h_props.2.2.2.2.2.symm,
    hp_lt, hp_next_isp⟩

/-- **Master Theorem 3.1 (`master_71module_complete_es_zeros_and_goldbach_lean_capstone`):**
    Complete 71-Module Master Capstone uniting `Goldbach.one_plus_one_nine_count` (`D19 N`),
    the `Step197`/`Step198` Sub-Half-MUR Global `Nat.minFac` Bijection & End-to-End `Step209`
    Rescued-Survivor Goldbach Closure (`step198_step209_global_rescued_survivor_to_binary_goldbach_liliu`),
    the Signature-Operator Quotient-One Non-Divisibility Law,
    the `Step217` Factorial Wavelength Shift & Unconditional `r ∣ N` Singleton Fiber Bound,
    the `Step215` & `Step216` OMC Reflection & Difference-of-Squares Shell Packing,
    the `Step211` Local Sub-`2q` Single-Block Goldbach Closure, and
    the `Step212` First-Missing-Prime `q_E` Zero-Sum Collapse. -/
theorem master_71module_complete_es_zeros_and_goldbach_lean_capstone :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (∀ q : ℕ, N / 2 ≤ 2 * max q 3 + 3 →
        (∀ p0 : ℕ, IsPrimeNat p0 → p0 % 2 = 1 → p0 < max q 3 → (2 * (N / 2)) % p0 = 0) →
        (liliuAboveSqrtLowerMURPrimesCutoff (N / 2) q).card ≤
          (liliuPrimeSurvivorSet (liliuFullLowerMURUpper (N / 2)) (max q 3)).card) ∧
      (∀ p : ℕ, p % 2 = 1 → p < N / 2 → N / 2 < 2 * p →
        1 ≤ (N / 2) % p ∧
        (2 * (N / 2)) % p = (liliuSigMulOperator 2 p 1 ((N / 2) % p)).2 ∧
        1 ≤ (2 * (N / 2)) % p) ∧
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
  obtain ⟨K, hK4, hCap69⟩ := master_69module_complete_es_zeros_and_goldbach_lean_capstone
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven
  have hM := hCap69 N hNK hEven
  refine ⟨hM.1, ?_, hM.2.1, hM.2.2.2.1, hM.2.2.2.2.1, hM.2.2.2.2.2⟩
  intro q hM_le h_fmp
  exact (step198_step209_global_rescued_survivor_to_binary_goldbach_liliu hM_le h_fmp).2.1

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.liliuFullLowerMURUpper_diameter_le_M_sub_four
#print axioms WuPaper.ESZerosBridge.liliuFullLowerMURUpper_roughCompositeTail_card_le_sqrtOwners_of_M_le
#print axioms WuPaper.ESZerosBridge.step198_step209_global_rescued_survivor_to_binary_goldbach_liliu
#print axioms WuPaper.ESZerosBridge.master_71module_complete_es_zeros_and_goldbach_lean_capstone
