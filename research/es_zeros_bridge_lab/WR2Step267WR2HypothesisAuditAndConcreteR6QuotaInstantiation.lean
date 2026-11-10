import WR2Step265WR2RawCatalogZeroExcessLossAndVaryingGPFTranslation

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step267WR2HypothesisAuditAndConcreteR6QuotaInstantiation.lean — Unconditional `M : ℕ` Species Balance, Concrete R6 Quotas & Merged Route B Conservation Identity (Zero Solution Hypotheses, `WR2` Track 1)

Merges the proven formulations from `WR2Step255`–`WR2Step265` with zero unproved hypotheses:

1. **Section 1 — Eliminating `hM1 : 1 ≤ M` via the `M = 0` Zero Absorber:**
   - `two_mul_M_lt_sqrtMidpointCutoff_cube_all_M`: proves `0 * M = 0` and
     `2 * M < (sqrtMidpointCutoff M) ^ 3` unconditionally for ALL `M : ℕ`.
   - `screenedConcreteKbUpper_exact_sq1_p2_balance_all_M`: proves the R1/R2 species balance
     unconditionally for ALL `M : ℕ`.
2. **Section 2 — Unconditional Concrete R6 Quotas & First-Strike Credits on `rawSq1Catalog M` & `rawP2Catalog M`:**
   - Proves `(rawSq1Catalog M).card ≤ rawSq1BlockQuota M`,
     `(rawP2Catalog M).card ≤ rawP2MinQuotaSum M`,
     `rawSq1FirstStrikeCreditSum M = (rejectedByLowerComposite M (rawSq1Catalog M)).card`, and
     `rawP2FirstStrikeCreditSum M = (rejectedByLowerComposite M (rawP2Catalog M)).card`
     unconditionally for ALL `M : ℕ`.
3. **Section 3 — Unconditional Merged Route B Conservation Identity & Quota Inequality (`concrete_rawCatalog_exact_routeB_balance_and_quota_inequality_all_M`):**
   - Merges `WR2Step255`, `WR2Step263`, and `WR2Step265` to prove unconditionally for ALL `M : ℕ`:
     `(screenedConcreteKbRadii M).card + rawSq1FirstStrikeCreditSum M + rawP2FirstStrikeCreditSum M = (primeSurvivorSet (fullLowerMURUpper M) (sqrtMidpointCutoff M)).card + (rawSq1Catalog M).card + (rawP2Catalog M).card`
     and
     `(screenedConcreteKbRadii M).card + rawSq1FirstStrikeCreditSum M + rawP2FirstStrikeCreditSum M ≤ (primeSurvivorSet (fullLowerMURUpper M) (sqrtMidpointCutoff M)).card + rawSq1BlockQuota M + rawP2MinQuotaSum M`.
-/

/-!
## Section 1: Eliminating `hM1 : 1 ≤ M` via the `M = 0` Zero Absorber
-/

/-- **Theorem 1.1 (`two_mul_M_lt_sqrtMidpointCutoff_cube_all_M`):**
    For EVERY `M : ℕ` (including the zero absorber `M = 0`),
    `0 * M = 0` and `2 * M < (sqrtMidpointCutoff M) ^ 3`. -/
theorem two_mul_M_lt_sqrtMidpointCutoff_cube_all_M (M : ℕ) :
    0 * M = 0 ∧ 2 * M < (sqrtMidpointCutoff M) ^ 3 := by
  refine ⟨Nat.zero_mul M, ?_⟩
  match Nat.eq_zero_or_pos M with
  | Or.inl h0 =>
    rw [h0, Nat.mul_zero]
    have h_pos : 0 < sqrtMidpointCutoff 0 := Nat.succ_pos (Nat.sqrt 0)
    exact nat_pow_pos h_pos 3
  | Or.inr hpos =>
    exact (two_mul_M_lt_sqrtMidpointCutoff_cube hpos).2

/-- **Theorem 1.2 (`screenedConcreteKbUpper_exact_sq1_p2_balance_all_M`):**
    Unconditional R1/R2 Species Balance for ALL `M : ℕ` (with `hM1 : 1 ≤ M` eliminated). -/
theorem screenedConcreteKbUpper_exact_sq1_p2_balance_all_M (M : ℕ) :
    (higherSpeciesTailSet (concreteKbUpper M) (sqrtMidpointCutoff M)).card = 0 ∧
    (pn1RoughCompositeTail (concreteKbUpper M) (sqrtMidpointCutoff M)).card =
      (sq1TailSet (concreteKbUpper M) (sqrtMidpointCutoff M)).card +
        (p2TailSet (concreteKbUpper M) (sqrtMidpointCutoff M)).card ∧
    (screenedConcreteKbRadii M).card =
      (primeSurvivorSet (concreteKbUpper M) (sqrtMidpointCutoff M)).card +
        (sq1TailSet (concreteKbUpper M) (sqrtMidpointCutoff M)).card +
        (p2TailSet (concreteKbUpper M) (sqrtMidpointCutoff M)).card := by
  have h_cube_bound : ∀ u ∈ concreteKbUpper M, u < (sqrtMidpointCutoff M) ^ 3 := by
    intro u hu
    have hu_full :=
      (concreteKbUpper_subset_fullLowerMURUpper_and_non_self_obstructing M).2.1 hu
    have hu_lt_2M : u < 2 * M := (fullLowerMURUpper_mem_props hu_full).2.2.1
    have h_2M_lt := (two_mul_M_lt_sqrtMidpointCutoff_cube_all_M M).2
    exact Nat.lt_trans hu_lt_2M h_2M_lt
  have h_empty := higherSpeciesTailSet_eq_empty_below_cube h_cube_bound
  have h_part :=
    (exact_species_three_way_composite_tail_partition
      (concreteKbUpper M) (sqrtMidpointCutoff M)).2
  have h_card_eq := (screenedConcreteKb_image_and_card_eq M).2
  unfold screenedConcreteKbUpper at h_card_eq
  exact ⟨h_empty.1, h_empty.2, by omega⟩

/-!
## Section 2: Concrete R6 Quotas & First-Strike Credits on `rawSq1Catalog M` and `rawP2Catalog M`
-/

theorem rawUpperInterval_mem_props {M u : ℕ} (hu : u ∈ rawUpperInterval M) :
    M + 1 ≤ u ∧
    u ≤ 2 * M - 3 ∧
    u < 2 * M ∧
    u % 2 = 1 ∧
    1 ≤ (2 * M - u) % 2 ∧
    1 ≤ M % (2 * M - u) := by
  rw [rawUpperInterval, mem_filter, mem_range] at hu
  obtain ⟨hu_lt, hu_ge, hu_le, hu_npv2, hu_cop⟩ := hu
  exact ⟨hu_ge, hu_le, hu_lt, by omega, hu_npv2, hu_cop⟩

def rawSq1BlockQuota (M : ℕ) : ℕ :=
  (subTwoQBlockIndices (rawUpperInterval M) (sqrtMidpointCutoff M)).card

def rawP2MinQuotaSum (M : ℕ) : ℕ :=
  ∑ r ∈ p2ActiveOwnerPrimes M (sqrtMidpointCutoff M),
    min ((subTwoQBlockIndices (rawUpperInterval M) (sqrtMidpointCutoff M)).card)
        ((primeCofactorWindow M r).card)

def rawSq1FirstStrikeCreditSum (M : ℕ) : ℕ :=
  ∑ s ∈ activeRejectionMinFacOwners M (rawSq1Catalog M),
    (rejectionByMinFacFiber M (rawSq1Catalog M) s).card

def rawP2FirstStrikeCreditSum (M : ℕ) : ℕ :=
  ∑ s ∈ activeRejectionMinFacOwners M (rawP2Catalog M),
    (rejectionByMinFacFiber M (rawP2Catalog M) s).card

theorem rawUpperInterval_roughCompositeTail_minFac_props
    {M q u : ℕ}
    (hu : u ∈ pn1RoughCompositeTail (rawUpperInterval M) q) :
    u.minFac ∈ sqrtActiveOwnerPrimes M q ∧
    q ≤ u.minFac ∧
    u % u.minFac = 0 ∧
    u.minFac % 2 = 1 ∧
    u % 2 = 1 := by
  rw [pn1RoughCompositeTail, mem_filter] at hu
  obtain ⟨hu_raw, hu2, hu_rough, hu_comp⟩ := hu
  have hu_props := rawUpperInterval_mem_props hu_raw
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

theorem rawUpperInterval_p2OwnerFiber_le_min_quota (M q r : ℕ) :
    (p2OwnerFiber (rawUpperInterval M) q r).card ≤
      min ((subTwoQBlockIndices (rawUpperInterval M) q).card)
          ((primeCofactorWindow M r).card) := by
  set R_up := rawUpperInterval M
  have h_sub_cof :
      (p2OwnerFiber R_up q r).image (fun u : ℕ => u / r) ⊆ primeCofactorWindow M r := by
    intro q2 hq2
    rw [mem_image] at hq2
    obtain ⟨u, hu, rfl⟩ := hq2
    rw [p2OwnerFiber, mem_filter, p2TailSet, mem_filter,
        nonSqTailSet, mem_filter, pn1RoughCompositeTail, mem_filter] at hu
    obtain ⟨⟨⟨⟨hu_R, hu2, _, hu_comp⟩, h_nsq⟩, h_p2_isp⟩, hr_eq⟩ := hu
    have hu_props := rawUpperInterval_mem_props hu_R
    have hu_ge_M1 : M + 1 ≤ u := hu_props.1
    have hu_le_2M3 : u ≤ 2 * M - 3 := hu_props.2.1
    have hu_lt_2M : u < 2 * M := hu_props.2.2.1
    have hu_odd : u % 2 = 1 := hu_props.2.2.2.1
    have hu_npv2 : 1 ≤ u % 2 := by omega
    have h_mf := minFac_mul_self_le_of_not_isPrimeNat hu2 hu_comp
    have hr_isp : IsPrimeNat r := by
      rw [← hr_eq]
      exact h_mf.1
    have hr_two : 2 ≤ r := hr_isp.1
    have hr_pos : 0 < r := by omega
    have hr_dvd_u : r ∣ u := by
      rw [← hr_eq]
      exact Nat.minFac_dvd u
    have h_rq2_eq : r * (u / r) = u :=
      (mod_eq_zero_and_mul_div_of_dvd_native hr_pos hr_dvd_u).2
    have h_q2_isp : IsPrimeNat (u / r) := by
      rw [← hr_eq]
      exact h_p2_isp
    have hq2_dvd_u : (u / r) ∣ u := ⟨r, by rw [Nat.mul_comm (u / r) r]; exact h_rq2_eq.symm⟩
    have hr_npv2 : 1 ≤ r % 2 :=
      (nonPVen_divisor_inheritance_native (by omega : 0 < 2) hr_dvd_u hu_npv2).1
    have hq2_npv2 : 1 ≤ (u / r) % 2 :=
      (nonPVen_divisor_inheritance_native (by omega : 0 < 2) hq2_dvd_u hu_npv2).1
    have hr_lt2 : r % 2 < 2 := Nat.mod_lt r (by omega : 0 < 2)
    have hq2_lt2 : (u / r) % 2 < 2 := Nat.mod_lt (u / r) (by omega : 0 < 2)
    have hr_odd : r % 2 = 1 := by omega
    have hq2_odd : (u / r) % 2 = 1 := by omega
    have hr_sq_le : r * r ≤ r * (u / r) := by
      rw [h_rq2_eq, ← hr_eq]
      exact h_mf.2.2.2
    have hr_le_q2 : r ≤ u / r := le_of_mul_le_mul_left_pos_wr2 hr_pos hr_sq_le
    have hr_ne_q2 : r ≠ u / r := by
      intro h_eq_rq
      have h_sq_eq : u.minFac * u.minFac = u := by
        rw [hr_eq]
        calc r * r
          _ = r * (u / r) := congrArg (fun x => r * x) h_eq_rq
          _ = u := h_rq2_eq
      exact h_nsq h_sq_eq
    have hr_div2 : 2 * (r / 2) + r % 2 = r := Nat.div_add_mod r 2
    have hq2_div2 : 2 * ((u / r) / 2) + (u / r) % 2 = u / r := Nat.div_add_mod (u / r) 2
    have hr2_le_q2 : r + 2 ≤ u / r := by omega
    have hq2_le_u : u / r ≤ u := dvd_le_of_pos hq2_dvd_u (by omega : 0 < u)
    have hq2_lt_range : u / r < 2 * M + 1 := by omega
    rw [primeCofactorWindow, mem_filter, mem_range]
    rw [h_rq2_eq]
    exact ⟨hq2_lt_range, h_q2_isp, hq2_odd, hr2_le_q2, hu_ge_M1, hu_le_2M3⟩
  have h_inj_cof : Set.InjOn (fun u : ℕ => u / r) (↑(p2OwnerFiber R_up q r) : Set ℕ) := by
    intro a0 ha0 b0 hb0 h_div_eq
    rw [mem_coe, p2OwnerFiber, mem_filter, p2TailSet, mem_filter,
        nonSqTailSet, mem_filter, pn1RoughCompositeTail, mem_filter] at ha0 hb0
    have ha2 : 2 ≤ a0 := ha0.1.1.1.2.1
    have ha_comp : ¬ IsPrimeNat a0 := ha0.1.1.1.2.2.2
    have hr_eq_a : a0.minFac = r := ha0.2
    have hr_eq_b : b0.minFac = r := hb0.2
    have h_mf_a := minFac_mul_self_le_of_not_isPrimeNat ha2 ha_comp
    have hr_two : 2 ≤ r := by
      rw [← hr_eq_a]
      exact h_mf_a.1.1
    have hr_pos : 0 < r := by omega
    have hr_dvd_a : r ∣ a0 := by
      rw [← hr_eq_a]
      exact Nat.minFac_dvd a0
    have hr_dvd_b : r ∣ b0 := by
      rw [← hr_eq_b]
      exact Nat.minFac_dvd b0
    have ha_mul : r * (a0 / r) = a0 :=
      (mod_eq_zero_and_mul_div_of_dvd_native hr_pos hr_dvd_a).2
    have hb_mul : r * (b0 / r) = b0 :=
      (mod_eq_zero_and_mul_div_of_dvd_native hr_pos hr_dvd_b).2
    dsimp only at h_div_eq
    rw [← ha_mul, ← hb_mul, h_div_eq]
  have h_card_cof :
      (p2OwnerFiber R_up q r).card ≤ (primeCofactorWindow M r).card := by
    rw [← Finset.card_image_of_injOn h_inj_cof]
    exact card_le_card h_sub_cof
  have h_sub_blocks :
      (p2OwnerFiber R_up q r).image (fun u : ℕ => u / (2 * max q 1)) ⊆
        subTwoQBlockIndices R_up q := by
    intro k hk
    rw [mem_image] at hk
    obtain ⟨u, hu, rfl⟩ := hk
    rw [p2OwnerFiber, mem_filter, p2TailSet, mem_filter,
        nonSqTailSet, mem_filter, pn1RoughCompositeTail, mem_filter] at hu
    rw [subTwoQBlockIndices, mem_image]
    exact ⟨u, hu.1.1.1.1, rfl⟩
  have h_inj_blocks :
      Set.InjOn (fun u : ℕ => u / (2 * max q 1)) (↑(p2OwnerFiber R_up q r) : Set ℕ) := by
    intro a0 ha0 b0 hb0 hk_eq
    rw [mem_coe, p2OwnerFiber, mem_filter, p2TailSet, mem_filter,
        nonSqTailSet, mem_filter] at ha0 hb0
    have ha_tail := ha0.1.1.1
    have hb_tail := hb0.1.1.1
    have h_mf_eq : a0.minFac = b0.minFac := by rw [ha0.2, hb0.2]
    dsimp only at hk_eq
    set k := a0 / (2 * max q 1)
    have ha_props := rawUpperInterval_roughCompositeTail_minFac_props ha_tail
    have hb_props := rawUpperInterval_roughCompositeTail_minFac_props hb_tail
    rw [pn1RoughCompositeTail, mem_filter] at ha_tail hb_tail
    have ha_blk : a0 ∈ subTwoQBlock R_up q k := by
      rw [subTwoQBlock, mem_filter]
      exact ⟨ha_tail.1, rfl⟩
    have hb_blk : b0 ∈ subTwoQBlock R_up q k := by
      rw [subTwoQBlock, mem_filter]
      exact ⟨hb_tail.1, hk_eq.symm⟩
    have h_diam_fn := (subTwoQBlock_unconditional_partition_and_diameter R_up q).2.2.2 k
    have hp_odd : a0.minFac % 2 = 1 := ha_props.2.2.2.1
    have ha_odd : a0 % 2 = 1 := ha_props.2.2.2.2
    have hb_odd : b0 % 2 = 1 := hb_props.2.2.2.2
    have ha_mod_p : a0 % a0.minFac = 0 := ha_props.2.2.1
    have hb_mod_p : b0 % a0.minFac = 0 := by
      rw [h_mf_eq]
      exact hb_props.2.2.1
    have h_mod_eq : a0 % a0.minFac = b0 % a0.minFac := by rw [ha_mod_p, hb_mod_p]
    have hq_le_p : q ≤ a0.minFac := ha_props.2.1
    have h_max_le1 : max q 1 ≤ max a0.minFac 1 := by omega
    have h_max_le : 2 * max q 1 ≤ 2 * max a0.minFac 1 :=
      Nat.mul_le_mul_left 2 h_max_le1
    match Nat.lt_or_ge a0 b0 with
    | Or.inl hlt =>
      have hle : a0 ≤ b0 := Nat.le_of_lt hlt
      have h_d_q : b0 - a0 < 2 * max q 1 := h_diam_fn a0 b0 ha_blk hb_blk hle
      have h_d_p : b0 - a0 < 2 * max a0.minFac 1 := Nat.lt_of_lt_of_le h_d_q h_max_le
      exact eq_of_sub_lt_two_max_of_odd_of_mod_eq hp_odd hle h_d_p ha_odd hb_odd h_mod_eq
    | Or.inr hge =>
      have h_d_q : a0 - b0 < 2 * max q 1 := h_diam_fn b0 a0 hb_blk ha_blk hge
      have h_d_p : a0 - b0 < 2 * max a0.minFac 1 := Nat.lt_of_lt_of_le h_d_q h_max_le
      exact (eq_of_sub_lt_two_max_of_odd_of_mod_eq hp_odd hge h_d_p hb_odd ha_odd h_mod_eq.symm).symm
  have h_card_blk :
      (p2OwnerFiber R_up q r).card ≤ (subTwoQBlockIndices R_up q).card := by
    rw [← Finset.card_image_of_injOn h_inj_blocks]
    exact card_le_card h_sub_blocks
  exact Nat.le_min.mpr ⟨h_card_blk, h_card_cof⟩

theorem rawCatalog_r6_quotas_and_first_strike_credits_unconditional (M : ℕ) :
    sq1TailSet (concreteKbUpper M) (sqrtMidpointCutoff M) ⊆ rawSq1Catalog M ∧
    p2TailSet (concreteKbUpper M) (sqrtMidpointCutoff M) ⊆ rawP2Catalog M ∧
    (rawSq1Catalog M).card ≤ rawSq1BlockQuota M ∧
    (rawP2Catalog M).card ≤ rawP2MinQuotaSum M ∧
    rawSq1FirstStrikeCreditSum M =
      (rejectedByLowerComposite M (rawSq1Catalog M)).card ∧
    rawP2FirstStrikeCreditSum M =
      (rejectedByLowerComposite M (rawP2Catalog M)).card := by
  have h_raw := rawSq1_and_rawP2_retained_eq_exact_tails_and_zero_excess_loss M
  set R_up := rawUpperInterval M
  set q_b := sqrtMidpointCutoff M
  have h_disj_sq1 :
      (↑(subTwoQBlockIndices R_up q_b) : Set ℕ).PairwiseDisjoint
        (fun k : ℕ => sq1TailSet (subTwoQBlock R_up q_b k) q_b) := by
    intro k₁ _ k₂ _ hne
    exact sq1TailSet_subTwoQBlock_disjoint_of_ne R_up q_b hne
  have h_sq1_sum :
      (rawSq1Catalog M).card =
        ∑ k ∈ subTwoQBlockIndices R_up q_b,
          (sq1TailSet (subTwoQBlock R_up q_b k) q_b).card := by
    unfold rawSq1Catalog
    conv_lhs => rw [sq1TailSet_eq_biUnion_subTwoQBlocks R_up q_b]
    exact card_biUnion h_disj_sq1
  have h_sq1_quota : (rawSq1Catalog M).card ≤ rawSq1BlockQuota M := by
    unfold rawSq1BlockQuota
    rw [h_sq1_sum]
    have h_s1 :
        ∑ k ∈ subTwoQBlockIndices R_up q_b,
          (sq1TailSet (subTwoQBlock R_up q_b k) q_b).card ≤
        ∑ _k ∈ subTwoQBlockIndices R_up q_b, 1 := by
      apply sum_le_sum
      intro k _
      exact sq1TailSet_subTwoQBlock_card_le_one R_up q_b k
    rw [sum_const, smul_eq_mul, Nat.mul_one] at h_s1
    exact h_s1
  have h_bi_p2 :
      rawP2Catalog M =
        (p2ActiveOwnerPrimes M q_b).biUnion (fun r : ℕ => p2OwnerFiber R_up q_b r) := by
    ext u
    rw [mem_biUnion]
    constructor
    · intro hu
      refine ⟨u.minFac, ?_, ?_⟩
      · have hu_copy := hu
        rw [rawP2Catalog, p2TailSet, mem_filter, nonSqTailSet, mem_filter] at hu_copy
        obtain ⟨⟨hu_tail, h_not_sq⟩, _⟩ := hu_copy
        have h_sqrt_mem := (rawUpperInterval_roughCompositeTail_minFac_props hu_tail).1
        have hu_odd : u % 2 = 1 :=
          (rawUpperInterval_roughCompositeTail_minFac_props hu_tail).2.2.2.2
        have hp1_odd : u.minFac % 2 = 1 :=
          (rawUpperInterval_roughCompositeTail_minFac_props hu_tail).2.2.2.1
        rw [pn1RoughCompositeTail, mem_filter] at hu_tail
        have hu_le_2M3 : u ≤ 2 * M - 3 := (rawUpperInterval_mem_props hu_tail.1).2.1
        set p1 := u.minFac
        set p2 := u / p1
        have hp1_pos : 0 < p1 := by omega
        have h_p1p2_eq : p1 * p2 = u :=
          (mod_eq_zero_and_mul_div_of_dvd_native hp1_pos (Nat.minFac_dvd u)).2
        have hp1_sq_le : p1 * p1 ≤ p1 * p2 := by
          rw [h_p1p2_eq]
          exact (minFac_mul_self_le_of_not_isPrimeNat hu_tail.2.1 hu_tail.2.2.2).2.2.2
        have hp1_le_p2 : p1 ≤ p2 := le_of_mul_le_mul_left_pos_wr2 hp1_pos hp1_sq_le
        have hp1_ne_p2 : p1 ≠ p2 := by
          intro h_eq
          rw [← h_eq] at h_p1p2_eq
          exact h_not_sq h_p1p2_eq
        have hp2_dvd_u : p2 ∣ u := ⟨p1, by rw [Nat.mul_comm p2 p1]; exact h_p1p2_eq.symm⟩
        have hu_npv2 : 1 ≤ u % 2 := by omega
        have hp2_npv2 : 1 ≤ p2 % 2 :=
          (nonPVen_divisor_inheritance_native (by omega : 0 < 2) hp2_dvd_u hu_npv2).1
        have hp2_lt2 : p2 % 2 < 2 := Nat.mod_lt p2 (by omega : 0 < 2)
        have hp2_odd : p2 % 2 = 1 := by omega
        have hp1_div2 : 2 * (p1 / 2) + p1 % 2 = p1 := Nat.div_add_mod p1 2
        have hp2_div2 : 2 * (p2 / 2) + p2 % 2 = p2 := Nat.div_add_mod p2 2
        have hp1_add2_le_p2 : p1 + 2 ≤ p2 := by omega
        have h_mul_p12 : p1 * (p1 + 2) ≤ u := by
          rw [← h_p1p2_eq]
          exact Nat.mul_le_mul_left p1 hp1_add2_le_p2
        rw [p2ActiveOwnerPrimes, mem_filter]
        exact ⟨h_sqrt_mem, by omega⟩
      · rw [p2OwnerFiber, mem_filter]
        exact ⟨hu, rfl⟩
    · rintro ⟨r, _, hu_fib⟩
      rw [p2OwnerFiber, mem_filter] at hu_fib
      exact hu_fib.1
  have h_disj_p2 :
      (↑(p2ActiveOwnerPrimes M q_b) : Set ℕ).PairwiseDisjoint
        (fun r : ℕ => p2OwnerFiber R_up q_b r) := by
    intro r₁ _ r₂ _ hne
    exact p2OwnerFiber_disjoint_of_ne R_up q_b hne
  have h_p2_sum :
      (rawP2Catalog M).card =
        ∑ r ∈ p2ActiveOwnerPrimes M q_b, (p2OwnerFiber R_up q_b r).card := by
    conv_lhs => rw [h_bi_p2]
    exact card_biUnion h_disj_p2
  have h_p2_quota : (rawP2Catalog M).card ≤ rawP2MinQuotaSum M := by
    unfold rawP2MinQuotaSum
    rw [h_p2_sum]
    apply sum_le_sum
    intro r _
    exact rawUpperInterval_p2OwnerFiber_le_min_quota M q_b r
  have h_c1 :=
    (rejectedByLowerComposite_eq_sum_rejectionByMinFacFiber M (rawSq1Catalog M)).2.symm
  have h_c2 :=
    (rejectedByLowerComposite_eq_sum_rejectionByMinFacFiber M (rawP2Catalog M)).2.symm
  exact ⟨h_raw.2.2.1, h_raw.2.2.2.1, h_sq1_quota, h_p2_quota, h_c1, h_c2⟩

/-!
## Section 3: Unconditional Merged Route B Conservation Identity & Quota Inequality (Zero Hypotheses)
-/

theorem merged_routeB_raw_catalog_conservation_and_quota_le
    {K P_kb P_full S1 S2 H1 H2 R1 R2 C1 C2 Q1 Q2 : ℕ}
    (h_bal : K = P_kb + S1 + S2)
    (h_p_eq : P_kb = P_full)
    (h_raw1 : H1 = S1 + R1)
    (h_raw2 : H2 = S2 + R2)
    (h_c1 : C1 = R1)
    (h_c2 : C2 = R2)
    (h_q1 : H1 ≤ Q1)
    (h_q2 : H2 ≤ Q2) :
    K + C1 + C2 = P_full + H1 + H2 ∧
    K + C1 + C2 ≤ P_full + Q1 + Q2 := by
  omega

/-- **Theorem 3.1 (`concrete_rawCatalog_exact_routeB_balance_and_quota_inequality_all_M`):**
    Unconditional synthesis of `WR2Step255`, `WR2Step263`, `WR2Step265`, and `WR2Step267`
    for ALL `M : ℕ` (with ZERO hypotheses on the solution):
    1. Exact Cancellation / Conservation Identity:
       `(screenedConcreteKbRadii M).card + rawSq1FirstStrikeCreditSum M + rawP2FirstStrikeCreditSum M = (primeSurvivorSet (fullLowerMURUpper M) (sqrtMidpointCutoff M)).card + (rawSq1Catalog M).card + (rawP2Catalog M).card`, and
    2. Unconditional R6 Quota Upper Inequality:
       `(screenedConcreteKbRadii M).card + rawSq1FirstStrikeCreditSum M + rawP2FirstStrikeCreditSum M ≤ (primeSurvivorSet (fullLowerMURUpper M) (sqrtMidpointCutoff M)).card + rawSq1BlockQuota M + rawP2MinQuotaSum M`! -/
theorem concrete_rawCatalog_exact_routeB_balance_and_quota_inequality_all_M (M : ℕ) :
    (screenedConcreteKbRadii M).card +
      rawSq1FirstStrikeCreditSum M +
      rawP2FirstStrikeCreditSum M =
    (primeSurvivorSet (fullLowerMURUpper M) (sqrtMidpointCutoff M)).card +
      (rawSq1Catalog M).card +
      (rawP2Catalog M).card ∧
    (screenedConcreteKbRadii M).card +
      rawSq1FirstStrikeCreditSum M +
      rawP2FirstStrikeCreditSum M ≤
    (primeSurvivorSet (fullLowerMURUpper M) (sqrtMidpointCutoff M)).card +
      rawSq1BlockQuota M +
      rawP2MinQuotaSum M := by
  have h_bal := (screenedConcreteKbUpper_exact_sq1_p2_balance_all_M M).2.2
  have h_p_eq :=
    (dropped_source_rows_are_composite_and_primeSurvivorSet_eq M (sqrtMidpointCutoff M)).2.2.1
  have h_raw := rawSq1_and_rawP2_retained_eq_exact_tails_and_zero_excess_loss M
  have h_inst := rawCatalog_r6_quotas_and_first_strike_credits_unconditional M
  exact merged_routeB_raw_catalog_conservation_and_quota_le
    h_bal h_p_eq h_raw.2.2.2.2.1 h_raw.2.2.2.2.2
    h_inst.2.2.2.2.1 h_inst.2.2.2.2.2 h_inst.2.2.1 h_inst.2.2.2.1

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.two_mul_M_lt_sqrtMidpointCutoff_cube_all_M
#print axioms WuPaper.ESZerosBridge.screenedConcreteKbUpper_exact_sq1_p2_balance_all_M
#print axioms WuPaper.ESZerosBridge.rawCatalog_r6_quotas_and_first_strike_credits_unconditional
#print axioms WuPaper.ESZerosBridge.concrete_rawCatalog_exact_routeB_balance_and_quota_inequality_all_M
