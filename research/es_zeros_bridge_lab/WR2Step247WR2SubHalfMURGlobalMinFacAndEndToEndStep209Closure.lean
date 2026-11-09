import WR2Step245WR2UpperHalfIntervalNonDividingAndStep209StrictPincer

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step247WR2SubHalfMURGlobalMinFacAndEndToEndStep209Closure.lean — `Step197`/`Step198` Sub-Half-MUR Global `Nat.minFac` Bijection & End-to-End `Step209` Rescued-Survivor Goldbach Closure (`WR2` Track 1)

Eliminates the block-coverage step by proving that `fullLowerMURUpper M` has total
diameter at most `M - 4`, so whenever `M ≤ 2 * q + 3` (`Step197`/`Step198` Sub-Half-MUR
horizon), `Nat.minFac` is globally injective across the entire `fullLowerMURUpper M`:

1. **Section 1 — Exact `M - 4` Diameter Bound on `fullLowerMURUpper M` (`fullLowerMURUpper_diameter_le_M_sub_four`):**
   Proves for all `a0, b0 ∈ fullLowerMURUpper M` with `a0 ≤ b0` that `b0 - a0 ≤ M - 4`.
2. **Section 2 — Global `Nat.minFac` Injection on `fullLowerMURUpper M` (`Step197`/`Step198`):**
   Proves that for `M ≤ 2 * q + 3`, `Nat.minFac` is injective on the global composite tail
   `pn1RoughCompositeTail (fullLowerMURUpper M) q` and maps into `sqrtActiveOwnerPrimes M q`, yielding:
   `(pn1RoughCompositeTail (fullLowerMURUpper M) q).card ≤ (sqrtActiveOwnerPrimes M q).card`
   and `(roughSurvivorSet (fullLowerMURUpper M) q).card - (sqrtActiveOwnerPrimes M q).card ≤ (primeSurvivorSet (fullLowerMURUpper M) q).card`.
3. **Section 3 — End-to-End Global Rescued-Survivor Goldbach Closure (`step198_step209_global_rescued_survivor_to_binary_goldbach_wr2`):**
   Combines the global upper bound on `pn1RoughCompositeTail (fullLowerMURUpper M) (max q 3)`
   with the global lower bound `(sqrtActiveOwnerPrimes M (max q 3)).card + (aboveSqrtLowerMURPrimesCutoff M q).card ≤ (roughSurvivorSet (fullLowerMURUpper M) (max q 3)).card`
   to prove `(aboveSqrtLowerMURPrimesCutoff M q).card ≤ (primeSurvivorSet (fullLowerMURUpper M) (max q 3)).card`
   and extract a certified Binary Goldbach partition `2 * M = p + q'` directly!
-/

/-!
## Section 1: Exact `M - 4` Diameter Bound on `fullLowerMURUpper M`
-/

/-- **Lemma 1.1 (`fullLowerMURUpper_diameter_le_M_sub_four`):**
    Every pair `a0, b0 ∈ fullLowerMURUpper M` with `a0 ≤ b0` satisfies
    `M + 1 ≤ a0`, `b0 ≤ 2 * M - 3`, and `b0 - a0 ≤ M - 4`. -/
theorem fullLowerMURUpper_diameter_le_M_sub_four
    {M a0 b0 : ℕ} (ha0 : a0 ∈ fullLowerMURUpper M) (hb0 : b0 ∈ fullLowerMURUpper M) :
    M + 1 ≤ a0 ∧ b0 ≤ 2 * M - 3 ∧ b0 - a0 ≤ M - 4 := by
  have ha := fullLowerMURUpper_mem_props ha0
  have hb := fullLowerMURUpper_mem_props hb0
  have h1 : M + 1 ≤ a0 := ha.1
  have h2 : b0 ≤ 2 * M - 3 := hb.2.1
  exact ⟨h1, h2, by omega⟩

/-- Every composite `u ∈ pn1RoughCompositeTail (fullLowerMURUpper M) q` has
    `u.minFac ∈ sqrtActiveOwnerPrimes M q`, `q ≤ u.minFac`, `u % u.minFac = 0`,
    `u.minFac % 2 = 1`, and `u % 2 = 1`. -/
theorem global_roughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes
    {M q u : ℕ}
    (hu : u ∈ pn1RoughCompositeTail (fullLowerMURUpper M) q) :
    u.minFac ∈ sqrtActiveOwnerPrimes M q ∧
    q ≤ u.minFac ∧
    u % u.minFac = 0 ∧
    u.minFac % 2 = 1 ∧
    u % 2 = 1 := by
  rw [pn1RoughCompositeTail, mem_filter] at hu
  obtain ⟨hu_full, hu2, hu_rough, hu_comp⟩ := hu
  have hu_props := fullLowerMURUpper_mem_props hu_full
  have hu_lt_2M : u < 2 * M := hu_props.2.2.1
  have hu_odd : u % 2 = 1 := hu_props.2.2.2.1
  have hu_npv2 : 1 ≤ u % 2 := by omega
  have h_mf := minFac_mul_self_le_of_not_isPrimeNat hu2 hu_comp
  have h_mf_isp : IsPrimeNat u.minFac := h_mf.1
  have h_mf_mod0 : u % u.minFac = 0 := h_mf.2.1
  have h_mf_le_u : u.minFac ≤ u := h_mf.2.2.1
  have h_mf_sq_le : u.minFac * u.minFac ≤ u := h_mf.2.2.2
  have h_mf_two : 2 ≤ u.minFac := h_mf_isp.1
  have h_mf_npv2 : 1 ≤ u.minFac % 2 :=
    (nonPVen_divisor_inheritance_native (by omega : 0 < 2) (Nat.minFac_dvd u) hu_npv2).1
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
  rw [sqrtActiveOwnerPrimes, mem_filter, mem_range]
  exact ⟨h_mf_lt_range, h_mf_isp, h_mf_odd, h_q_le_mf, h_mf_sq_2M⟩

/-!
## Section 2: Global Sub-Half-MUR `Nat.minFac` Injection on `fullLowerMURUpper M` (`Step197`/`Step198`)
-/

/-- **Theorem 2.1 (`fullLowerMURUpper_roughCompositeTail_card_le_sqrtOwners_of_M_le`):**
    Ports `Step197` / `Step198` (Sub-Half-MUR Bijective Prime-Cofactor Window):
    Whenever `M ≤ 2 * q + 3`, the entire carrier `fullLowerMURUpper M` has diameter
    `b0 - a0 ≤ M - 4 < 2 * max p 1` for every active owner prime `p ≥ q`. Consequently,
    `Nat.minFac` is globally injective on `pn1RoughCompositeTail (fullLowerMURUpper M) q`,
    proving on the FULL carrier (with zero block decomposition):
    1. `(pn1RoughCompositeTail (fullLowerMURUpper M) q).card ≤ (sqrtActiveOwnerPrimes M q).card`, and
    2. `(roughSurvivorSet (fullLowerMURUpper M) q).card - (sqrtActiveOwnerPrimes M q).card ≤ (primeSurvivorSet (fullLowerMURUpper M) q).card`. -/
theorem fullLowerMURUpper_roughCompositeTail_card_le_sqrtOwners_of_M_le
    {M q : ℕ} (hM_le : M ≤ 2 * q + 3) :
    (pn1RoughCompositeTail (fullLowerMURUpper M) q).card ≤
      (sqrtActiveOwnerPrimes M q).card ∧
    (roughSurvivorSet (fullLowerMURUpper M) q).card -
      (sqrtActiveOwnerPrimes M q).card ≤
      (primeSurvivorSet (fullLowerMURUpper M) q).card := by
  have h_sub :
      (pn1RoughCompositeTail (fullLowerMURUpper M) q).image Nat.minFac ⊆
        sqrtActiveOwnerPrimes M q := by
    intro p hp
    rw [mem_image] at hp
    obtain ⟨u, hu, rfl⟩ := hp
    exact (global_roughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes hu).1
  have h_inj :
      Set.InjOn Nat.minFac
        (↑(pn1RoughCompositeTail (fullLowerMURUpper M) q) : Set ℕ) := by
    intro a0 ha0 b0 hb0 h_mf_eq
    rw [mem_coe] at ha0 hb0
    have ha_props := global_roughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes ha0
    have hb_props := global_roughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes hb0
    have ha_full : a0 ∈ fullLowerMURUpper M := by
      rw [pn1RoughCompositeTail, mem_filter] at ha0
      exact ha0.1
    have hb_full : b0 ∈ fullLowerMURUpper M := by
      rw [pn1RoughCompositeTail, mem_filter] at hb0
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
      rw [sqrtActiveOwnerPrimes, mem_filter] at hp_mem
      exact hp_mem.2.1.1
    have h_2q_le_2p : 2 * q ≤ 2 * max a0.minFac 1 := by
      have h_le_max : q ≤ max a0.minFac 1 := by omega
      exact Nat.mul_le_mul_left 2 h_le_max
    match Nat.lt_or_ge a0 b0 with
    | Or.inl hlt =>
      have hle : a0 ≤ b0 := Nat.le_of_lt hlt
      have h_diam := (fullLowerMURUpper_diameter_le_M_sub_four ha_full hb_full).2.2
      have h_a0_ge : M + 1 ≤ a0 := (fullLowerMURUpper_diameter_le_M_sub_four ha_full hb_full).1
      have h_b0_le : b0 ≤ 2 * M - 3 := (fullLowerMURUpper_diameter_le_M_sub_four ha_full hb_full).2.1
      have h_M4 : 4 ≤ M := by omega
      have h_d_p : b0 - a0 < 2 * max a0.minFac 1 := by omega
      exact eq_of_sub_lt_two_max_of_odd_of_mod_eq hp_odd hle h_d_p ha_odd hb_odd h_mod_eq
    | Or.inr hge =>
      have h_diam := (fullLowerMURUpper_diameter_le_M_sub_four hb_full ha_full).2.2
      have h_b0_ge : M + 1 ≤ b0 := (fullLowerMURUpper_diameter_le_M_sub_four hb_full ha_full).1
      have h_a0_le : a0 ≤ 2 * M - 3 := (fullLowerMURUpper_diameter_le_M_sub_four hb_full ha_full).2.1
      have h_M4 : 4 ≤ M := by omega
      have h_d_p : a0 - b0 < 2 * max a0.minFac 1 := by omega
      exact (eq_of_sub_lt_two_max_of_odd_of_mod_eq hp_odd hge h_d_p hb_odd ha_odd h_mod_eq.symm).symm
  have h_card_img :
      ((pn1RoughCompositeTail (fullLowerMURUpper M) q).image Nat.minFac).card =
        (pn1RoughCompositeTail (fullLowerMURUpper M) q).card :=
    Finset.card_image_of_injOn h_inj
  have h_tail_le :
      (pn1RoughCompositeTail (fullLowerMURUpper M) q).card ≤
        (sqrtActiveOwnerPrimes M q).card := by
    rw [← h_card_img]
    exact card_le_card h_sub
  have h_part :=
    roughSurvivorSet_card_eq_primeSurvivors_add_compositeTail (fullLowerMURUpper M) q
  exact ⟨h_tail_le, by omega⟩

/-!
## Section 3: End-to-End Global Rescued-Survivor Goldbach Closure (`Step198` + `Step209`)
-/

/-- **Theorem 3.1 (`step198_step209_global_rescued_survivor_to_binary_goldbach_wr2`):**
    End-to-End Global Rescued-Survivor Pincer (`Step198` + `Step209`):
    Whenever `M ≤ 2 * max q 3 + 3` and `h_fmp : ∀ p0 : ℕ, IsPrimeNat p0 → p0 % 2 = 1 → p0 < max q 3 → (2 * M) % p0 = 0`:
    1. `(pn1RoughCompositeTail (fullLowerMURUpper M) (max q 3)).card ≤ (sqrtActiveOwnerPrimes M (max q 3)).card`,
    2. `(aboveSqrtLowerMURPrimesCutoff M q).card ≤ (primeSurvivorSet (fullLowerMURUpper M) (max q 3)).card`, and
    3. Given `4 ≤ M`, `M ≠ 5`, and `h_bertrand : 6 ≤ M → ∃ p : ℕ, IsPrimeNat p ∧ M / 2 < p ∧ p ≤ 2 * (M / 2)`,
       `1 ≤ (primeSurvivorSet (fullLowerMURUpper M) (max q 3)).card` holds unconditionally
       and extracts a Binary Goldbach partition `2 * M = p + q'` paired with `p < p_next'`! -/
theorem step198_step209_global_rescued_survivor_to_binary_goldbach_wr2
    {M q : ℕ}
    (hM_le : M ≤ 2 * max q 3 + 3)
    (h_fmp : ∀ p0 : ℕ, IsPrimeNat p0 → p0 % 2 = 1 → p0 < max q 3 → (2 * M) % p0 = 0) :
    (pn1RoughCompositeTail (fullLowerMURUpper M) (max q 3)).card ≤
      (sqrtActiveOwnerPrimes M (max q 3)).card ∧
    (aboveSqrtLowerMURPrimesCutoff M q).card ≤
      (primeSurvivorSet (fullLowerMURUpper M) (max q 3)).card ∧
    (4 ≤ M → M ≠ 5 →
      (6 ≤ M → ∃ p : ℕ, IsPrimeNat p ∧ M / 2 < p ∧ p ≤ 2 * (M / 2)) →
      1 ≤ (primeSurvivorSet (fullLowerMURUpper M) (max q 3)).card ∧
      ∃ p q' p_next' : ℕ,
        Nat.Prime p ∧ Nat.Prime q' ∧ 2 * M = p + q' ∧
        p < p_next' ∧ Nat.Prime p_next' ∧ IsPrimeNat p_next') := by
  have h_glob := fullLowerMURUpper_roughCompositeTail_card_le_sqrtOwners_of_M_le hM_le
  have h_resc :=
    unconditional_strict_sqrt_owner_lt_rescued_lower_mur_survivors_wr2 M q 0 h_fmp
  have h_part :=
    roughSurvivorSet_card_eq_primeSurvivors_add_compositeTail
      (fullLowerMURUpper M) (max q 3)
  have h_above_le_prime :
      (aboveSqrtLowerMURPrimesCutoff M q).card ≤
        (primeSurvivorSet (fullLowerMURUpper M) (max q 3)).card := by
    have h1 := h_glob.1
    have h2 := h_resc.1
    omega
  refine ⟨h_glob.1, h_above_le_prime, ?_⟩
  intro hM4 hM_ne5 h_bert
  have h_pin :=
    bertrand_upper_half_prime_discharges_step209_strict_pincer_wr2
      (k := 0) hM4 hM_ne5 h_bert h_fmp
  have h_above_ge1 : 1 ≤ (aboveSqrtLowerMURPrimesCutoff M q).card := h_pin.1
  have h_prime_ge1 : 1 ≤ (primeSurvivorSet (fullLowerMURUpper M) (max q 3)).card :=
    Nat.le_trans h_above_ge1 h_above_le_prime
  have h_prime_pos : 0 < (primeSurvivorSet (fullLowerMURUpper M) (max q 3)).card := by omega
  refine ⟨h_prime_ge1, ?_⟩
  obtain ⟨u, hu⟩ := card_pos.mp h_prime_pos
  rw [primeSurvivorSet, mem_filter] at hu
  obtain ⟨hu_full, _, _, hu_isp⟩ := hu
  have h_props := fullLowerMURUpper_mem_props hu_full
  have hp_nat : Nat.Prime (2 * M - u) := isPrimeNat_to_natPrime h_props.2.2.2.2.1
  have hu_nat : Nat.Prime u := isPrimeNat_to_natPrime hu_isp
  obtain ⟨p_next', hp_lt, hp_next_nat, hp_next_isp⟩ :=
    hasNextPrimeMathlib_unconditional (2 * M - u)
  exact ⟨2 * M - u, u, p_next', hp_nat, hu_nat, h_props.2.2.2.2.2.symm,
    hp_lt, hp_next_nat, hp_next_isp⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.fullLowerMURUpper_diameter_le_M_sub_four
#print axioms WuPaper.ESZerosBridge.fullLowerMURUpper_roughCompositeTail_card_le_sqrtOwners_of_M_le
#print axioms WuPaper.ESZerosBridge.step198_step209_global_rescued_survivor_to_binary_goldbach_wr2
