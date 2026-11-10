import WR2Step260LiLiuBC14ResidualFamilyAnd83ModuleMasterCapstone

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step262LiLiuR6MultiBlockSpeciesPlacementAnd85ModuleCapstone.lean — Recommendation R6 Implementation on Track 2 (`D19 N`): Multi-Block Exact-Species Placement Sums, `BC17` LPF–GPF Cell Singleton Cap, `Step191`–`Step192` Prime-Cofactor Window Quota, Block-Summed Route B Receiver & Master 85-Module Capstone

Ports Recommendation R6 onto Track 2 (`D19 N`) and welds all 85 modules into the
complete R1–R10 `Goldbach.All` Master Capstone.
-/

/-!
## Section 1: Multi-Block Exact-Species Partition & Summed Block Placement Bounds
-/

theorem liliuSq1TailSet_eq_biUnion_subTwoQBlocks (I : Finset ℕ) (q : ℕ) :
    liliuSq1TailSet I q =
      (liliuSubTwoQBlockIndices I q).biUnion (fun k : ℕ =>
        liliuSq1TailSet (liliuSubTwoQBlock I q k) q) := by
  ext u
  rw [mem_biUnion]
  constructor
  · intro hu
    rw [liliuSq1TailSet, mem_filter] at hu
    obtain ⟨hu_tail, hu_sq⟩ := hu
    have hu_bi := hu_tail
    rw [liliuPn1RoughCompositeTail_eq_biUnion_subTwoQBlocks I q, mem_biUnion] at hu_bi
    obtain ⟨k, hk_idx, hu_blk_tail⟩ := hu_bi
    refine ⟨k, hk_idx, ?_⟩
    rw [liliuSq1TailSet, mem_filter]
    exact ⟨hu_blk_tail, hu_sq⟩
  · rintro ⟨k, _, hu_blk⟩
    rw [liliuSq1TailSet, mem_filter] at hu_blk ⊢
    obtain ⟨hu_blk_tail, hu_sq⟩ := hu_blk
    rw [liliuPn1RoughCompositeTail, mem_filter, liliuSubTwoQBlock, mem_filter] at hu_blk_tail
    rw [liliuPn1RoughCompositeTail, mem_filter]
    exact ⟨⟨hu_blk_tail.1.1, hu_blk_tail.2⟩, hu_sq⟩

theorem liliuP2TailSet_eq_biUnion_subTwoQBlocks (I : Finset ℕ) (q : ℕ) :
    liliuP2TailSet I q =
      (liliuSubTwoQBlockIndices I q).biUnion (fun k : ℕ =>
        liliuP2TailSet (liliuSubTwoQBlock I q k) q) := by
  ext u
  rw [mem_biUnion]
  constructor
  · intro hu
    rw [liliuP2TailSet, mem_filter, liliuNonSqTailSet, mem_filter] at hu
    obtain ⟨⟨hu_tail, hu_nsq⟩, hu_p2⟩ := hu
    have hu_bi := hu_tail
    rw [liliuPn1RoughCompositeTail_eq_biUnion_subTwoQBlocks I q, mem_biUnion] at hu_bi
    obtain ⟨k, hk_idx, hu_blk_tail⟩ := hu_bi
    refine ⟨k, hk_idx, ?_⟩
    rw [liliuP2TailSet, mem_filter, liliuNonSqTailSet, mem_filter]
    exact ⟨⟨hu_blk_tail, hu_nsq⟩, hu_p2⟩
  · rintro ⟨k, _, hu_blk⟩
    rw [liliuP2TailSet, mem_filter, liliuNonSqTailSet, mem_filter] at hu_blk ⊢
    obtain ⟨⟨hu_blk_tail, hu_nsq⟩, hu_p2⟩ := hu_blk
    rw [liliuPn1RoughCompositeTail, mem_filter, liliuSubTwoQBlock, mem_filter] at hu_blk_tail
    rw [liliuPn1RoughCompositeTail, mem_filter]
    exact ⟨⟨⟨hu_blk_tail.1.1, hu_blk_tail.2⟩, hu_nsq⟩, hu_p2⟩

theorem liliuSq1TailSet_subTwoQBlock_disjoint_of_ne
    (I : Finset ℕ) (q : ℕ) {k₁ k₂ : ℕ} (hne : k₁ ≠ k₂) :
    Disjoint (liliuSq1TailSet (liliuSubTwoQBlock I q k₁) q)
             (liliuSq1TailSet (liliuSubTwoQBlock I q k₂) q) := by
  apply Finset.disjoint_left.mpr
  intro u hu1 hu2
  rw [liliuSq1TailSet, mem_filter] at hu1 hu2
  exact Finset.disjoint_left.mp
    (liliuPn1RoughCompositeTail_subTwoQBlock_disjoint_of_ne I q hne) hu1.1 hu2.1

theorem liliuP2TailSet_subTwoQBlock_disjoint_of_ne
    (I : Finset ℕ) (q : ℕ) {k₁ k₂ : ℕ} (hne : k₁ ≠ k₂) :
    Disjoint (liliuP2TailSet (liliuSubTwoQBlock I q k₁) q)
             (liliuP2TailSet (liliuSubTwoQBlock I q k₂) q) := by
  apply Finset.disjoint_left.mpr
  intro u hu1 hu2
  rw [liliuP2TailSet, mem_filter, liliuNonSqTailSet, mem_filter] at hu1 hu2
  exact Finset.disjoint_left.mp
    (liliuPn1RoughCompositeTail_subTwoQBlock_disjoint_of_ne I q hne) hu1.1.1 hu2.1.1

/-- **Theorem 1.1 (`liliu_multi_block_exact_species_sq1_and_p2_sum_bounds` — R6):**
    Multi-Block Exact-Species Placement Bounds on Track 2 (`D19 N`). -/
theorem liliu_multi_block_exact_species_sq1_and_p2_sum_bounds (M q : ℕ) :
    let U := liliuFullLowerMURUpper M
    let B := liliuSubTwoQBlockIndices U q
    (liliuSq1TailSet U q).card = ∑ k ∈ B, (liliuSq1TailSet (liliuSubTwoQBlock U q k) q).card ∧
    (liliuP2TailSet U q).card = ∑ k ∈ B, (liliuP2TailSet (liliuSubTwoQBlock U q k) q).card ∧
    (liliuSq1TailSet U q).card ≤ B.card ∧
    (liliuP2TailSet U q).card ≤ B.card * (liliuP2ActiveOwnerPrimes M q).card := by
  dsimp only
  set U := liliuFullLowerMURUpper M
  set B := liliuSubTwoQBlockIndices U q
  have h_disj_sq1 :
      (↑B : Set ℕ).PairwiseDisjoint (fun k : ℕ => liliuSq1TailSet (liliuSubTwoQBlock U q k) q) := by
    intro k₁ _ k₂ _ hne
    exact liliuSq1TailSet_subTwoQBlock_disjoint_of_ne U q hne
  have h_disj_p2 :
      (↑B : Set ℕ).PairwiseDisjoint (fun k : ℕ => liliuP2TailSet (liliuSubTwoQBlock U q k) q) := by
    intro k₁ _ k₂ _ hne
    exact liliuP2TailSet_subTwoQBlock_disjoint_of_ne U q hne
  have h_sq1_eq :
      (liliuSq1TailSet U q).card = ∑ k ∈ B, (liliuSq1TailSet (liliuSubTwoQBlock U q k) q).card := by
    conv_lhs => rw [liliuSq1TailSet_eq_biUnion_subTwoQBlocks U q]
    exact card_biUnion h_disj_sq1
  have h_p2_eq :
      (liliuP2TailSet U q).card = ∑ k ∈ B, (liliuP2TailSet (liliuSubTwoQBlock U q k) q).card := by
    conv_lhs => rw [liliuP2TailSet_eq_biUnion_subTwoQBlocks U q]
    exact card_biUnion h_disj_p2
  have h_sq1_le : (liliuSq1TailSet U q).card ≤ B.card := by
    rw [h_sq1_eq]
    have h_sum1 :
        ∑ k ∈ B, (liliuSq1TailSet (liliuSubTwoQBlock U q k) q).card ≤ ∑ _k ∈ B, 1 := by
      apply sum_le_sum
      intro k _
      exact liliuSq1TailSet_subTwoQBlock_card_le_one U q k
    rw [sum_const, smul_eq_mul, Nat.mul_one] at h_sum1
    exact h_sum1
  have h_p2_le : (liliuP2TailSet U q).card ≤ B.card * (liliuP2ActiveOwnerPrimes M q).card := by
    rw [h_p2_eq]
    have h_sum2 :
        ∑ k ∈ B, (liliuP2TailSet (liliuSubTwoQBlock U q k) q).card ≤
          ∑ _k ∈ B, (liliuP2ActiveOwnerPrimes M q).card := by
      apply sum_le_sum
      intro k _
      exact (liliuP2TailSet_subTwoQBlock_card_le_p2ActiveOwnerPrimes M q k).1
    rw [sum_const, smul_eq_mul] at h_sum2
    exact h_sum2
  exact ⟨h_sq1_eq, h_p2_eq, h_sq1_le, h_p2_le⟩

/-!
## Section 2: `BC17` LPF–GPF Cell Singleton Cap, `Step191`–`Step192` Prime-Cofactor Window Quota & Global Summed Sharper Bound
-/

def liliuP2OwnerFiber (S : Finset ℕ) (q r : ℕ) : Finset ℕ :=
  (liliuP2TailSet S q).filter (fun u : ℕ => u.minFac = r)

def liliuLpfGpfCell (S : Finset ℕ) (q r q2 : ℕ) : Finset ℕ :=
  (liliuP2OwnerFiber S q r).filter (fun u : ℕ => u / r = q2)

def liliuPrimeCofactorWindow (M r : ℕ) : Finset ℕ :=
  (range (2 * M + 1)).filter (fun q2 : ℕ =>
    IsPrimeNat q2 ∧ q2 % 2 = 1 ∧ r + 2 ≤ q2 ∧ M + 1 ≤ r * q2 ∧ r * q2 ≤ 2 * M - 3)

theorem liliuLpfGpfCell_subset_singleton_and_card_le_one (S : Finset ℕ) (q r q2 : ℕ) :
    liliuLpfGpfCell S q r q2 ⊆ {r * q2} ∧
    (liliuLpfGpfCell S q r q2).card ≤ 1 := by
  have h_sub : liliuLpfGpfCell S q r q2 ⊆ {r * q2} := by
    intro u hu
    rw [liliuLpfGpfCell, mem_filter, liliuP2OwnerFiber, mem_filter,
        liliuP2TailSet, mem_filter, liliuNonSqTailSet, mem_filter,
        liliuPn1RoughCompositeTail, mem_filter] at hu
    obtain ⟨⟨⟨⟨⟨_, hu2, _, hu_comp⟩, _⟩, _⟩, hr_eq⟩, hq2_eq⟩ := hu
    have h_mf := minFac_mul_self_le_of_not_isPrimeNat_liliu hu2 hu_comp
    have hr_two : 2 ≤ r := by
      rw [← hr_eq]
      exact h_mf.1.1
    have hr_pos : 0 < r := by omega
    have hr_dvd : r ∣ u := by
      rw [← hr_eq]
      exact Nat.minFac_dvd u
    have h_mul : r * (u / r) = u :=
      (mod_eq_zero_and_mul_div_of_dvd_liliu hr_pos hr_dvd).2
    rw [hq2_eq] at h_mul
    rw [mem_singleton]
    exact h_mul.symm
  have h_card : (liliuLpfGpfCell S q r q2).card ≤ 1 := by
    have h1 := card_le_card h_sub
    rw [card_singleton] at h1
    exact h1
  exact ⟨h_sub, h_card⟩

/-- **Theorem 2.1 (`liliuP2OwnerFiber_sharper_of_block_and_cofactor_quota` — R6):**
    The R6 Sharper-of-Two-Bounds Law on Track 2 (`D19 N`). -/
theorem liliuP2OwnerFiber_sharper_of_block_and_cofactor_quota (M q r : ℕ) :
    (liliuP2OwnerFiber (liliuFullLowerMURUpper M) q r).card ≤
      (liliuPrimeCofactorWindow M r).card ∧
    (liliuP2OwnerFiber (liliuFullLowerMURUpper M) q r).card ≤
      (liliuSubTwoQBlockIndices (liliuFullLowerMURUpper M) q).card ∧
    (liliuP2OwnerFiber (liliuFullLowerMURUpper M) q r).card ≤
      min ((liliuSubTwoQBlockIndices (liliuFullLowerMURUpper M) q).card)
          ((liliuPrimeCofactorWindow M r).card) := by
  set U := liliuFullLowerMURUpper M
  have h_sub_cof :
      (liliuP2OwnerFiber U q r).image (fun u : ℕ => u / r) ⊆ liliuPrimeCofactorWindow M r := by
    intro q2 hq2
    rw [mem_image] at hq2
    obtain ⟨u, hu, rfl⟩ := hq2
    rw [liliuP2OwnerFiber, mem_filter, liliuP2TailSet, mem_filter,
        liliuNonSqTailSet, mem_filter, liliuPn1RoughCompositeTail, mem_filter] at hu
    obtain ⟨⟨⟨⟨hu_U, hu2, _, hu_comp⟩, h_nsq⟩, h_p2_isp⟩, hr_eq⟩ := hu
    have hu_props := liliuFullLowerMURUpper_mem_props hu_U
    have hu_ge_M1 : M + 1 ≤ u := hu_props.1
    have hu_le_2M3 : u ≤ 2 * M - 3 := hu_props.2.1
    have hu_lt_2M : u < 2 * M := hu_props.2.2.1
    have hu_odd : u % 2 = 1 := hu_props.2.2.2.1
    have hu_npv2 : 1 ≤ u % 2 := by omega
    have h_mf := minFac_mul_self_le_of_not_isPrimeNat_liliu hu2 hu_comp
    have hr_isp : IsPrimeNat r := by
      rw [← hr_eq]
      exact h_mf.1
    have hr_two : 2 ≤ r := hr_isp.1
    have hr_pos : 0 < r := by omega
    have hr_dvd_u : r ∣ u := by
      rw [← hr_eq]
      exact Nat.minFac_dvd u
    have h_rq2_eq : r * (u / r) = u :=
      (mod_eq_zero_and_mul_div_of_dvd_liliu hr_pos hr_dvd_u).2
    have h_q2_isp : IsPrimeNat (u / r) := by
      rw [← hr_eq]
      exact h_p2_isp
    have hq2_dvd_u : (u / r) ∣ u := ⟨r, by rw [Nat.mul_comm (u / r) r]; exact h_rq2_eq.symm⟩
    have hr_npv2 : 1 ≤ r % 2 :=
      (nonPVen_divisor_inheritance_liliu (by omega : 0 < 2) hr_dvd_u hu_npv2).1
    have hq2_npv2 : 1 ≤ (u / r) % 2 :=
      (nonPVen_divisor_inheritance_liliu (by omega : 0 < 2) hq2_dvd_u hu_npv2).1
    have hr_lt2 : r % 2 < 2 := Nat.mod_lt r (by omega : 0 < 2)
    have hq2_lt2 : (u / r) % 2 < 2 := Nat.mod_lt (u / r) (by omega : 0 < 2)
    have hr_odd : r % 2 = 1 := by omega
    have hq2_odd : (u / r) % 2 = 1 := by omega
    have hr_sq_le : r * r ≤ r * (u / r) := by
      rw [h_rq2_eq, ← hr_eq]
      exact h_mf.2.2.2
    have hr_le_q2 : r ≤ u / r := le_of_mul_le_mul_left_pos_liliu hr_pos hr_sq_le
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
    rw [liliuPrimeCofactorWindow, mem_filter, mem_range]
    rw [h_rq2_eq]
    exact ⟨hq2_lt_range, h_q2_isp, hq2_odd, hr2_le_q2, hu_ge_M1, hu_le_2M3⟩
  have h_inj_cof : Set.InjOn (fun u : ℕ => u / r) (↑(liliuP2OwnerFiber U q r) : Set ℕ) := by
    intro a0 ha0 b0 hb0 h_div_eq
    rw [mem_coe, liliuP2OwnerFiber, mem_filter, liliuP2TailSet, mem_filter,
        liliuNonSqTailSet, mem_filter, liliuPn1RoughCompositeTail, mem_filter] at ha0 hb0
    have ha2 : 2 ≤ a0 := ha0.1.1.1.2.1
    have ha_comp : ¬ IsPrimeNat a0 := ha0.1.1.1.2.2.2
    have hr_eq_a : a0.minFac = r := ha0.2
    have hr_eq_b : b0.minFac = r := hb0.2
    have h_mf_a := minFac_mul_self_le_of_not_isPrimeNat_liliu ha2 ha_comp
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
      (mod_eq_zero_and_mul_div_of_dvd_liliu hr_pos hr_dvd_a).2
    have hb_mul : r * (b0 / r) = b0 :=
      (mod_eq_zero_and_mul_div_of_dvd_liliu hr_pos hr_dvd_b).2
    dsimp only at h_div_eq
    rw [← ha_mul, ← hb_mul, h_div_eq]
  have h_card_cof :
      (liliuP2OwnerFiber U q r).card ≤ (liliuPrimeCofactorWindow M r).card := by
    rw [← Finset.card_image_of_injOn h_inj_cof]
    exact card_le_card h_sub_cof
  have h_sub_blocks :
      (liliuP2OwnerFiber U q r).image (fun u : ℕ => u / (2 * max q 1)) ⊆
        liliuSubTwoQBlockIndices U q := by
    intro k hk
    rw [mem_image] at hk
    obtain ⟨u, hu, rfl⟩ := hk
    rw [liliuP2OwnerFiber, mem_filter, liliuP2TailSet, mem_filter,
        liliuNonSqTailSet, mem_filter, liliuPn1RoughCompositeTail, mem_filter] at hu
    rw [liliuSubTwoQBlockIndices, mem_image]
    exact ⟨u, hu.1.1.1.1, rfl⟩
  have h_inj_blocks :
      Set.InjOn (fun u : ℕ => u / (2 * max q 1)) (↑(liliuP2OwnerFiber U q r) : Set ℕ) := by
    intro a0 ha0 b0 hb0 hk_eq
    rw [mem_coe, liliuP2OwnerFiber, mem_filter, liliuP2TailSet, mem_filter,
        liliuNonSqTailSet, mem_filter] at ha0 hb0
    have ha_tail := ha0.1.1.1
    have hb_tail := hb0.1.1.1
    have h_mf_eq : a0.minFac = b0.minFac := by rw [ha0.2, hb0.2]
    dsimp only at hk_eq
    set k := a0 / (2 * max q 1)
    have ha_blk_tail : a0 ∈ liliuPn1RoughCompositeTail (liliuSubTwoQBlock U q k) q := by
      rw [liliuPn1RoughCompositeTail, mem_filter] at ha_tail ⊢
      rw [liliuSubTwoQBlock, mem_filter]
      exact ⟨⟨ha_tail.1, rfl⟩, ha_tail.2⟩
    have hb_blk_tail : b0 ∈ liliuPn1RoughCompositeTail (liliuSubTwoQBlock U q k) q := by
      rw [liliuPn1RoughCompositeTail, mem_filter] at hb_tail ⊢
      rw [liliuSubTwoQBlock, mem_filter]
      exact ⟨⟨hb_tail.1, hk_eq.symm⟩, hb_tail.2⟩
    have ha_props := liliuRoughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes ha_blk_tail
    have hb_props := liliuRoughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes hb_blk_tail
    rw [liliuPn1RoughCompositeTail, mem_filter] at ha_blk_tail hb_blk_tail
    have h_diam_fn := (liliuSubTwoQBlock_unconditional_partition_and_diameter U q).2.2.2 k
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
      have h_d_q : b0 - a0 < 2 * max q 1 := h_diam_fn a0 b0 ha_blk_tail.1 hb_blk_tail.1 hle
      have h_d_p : b0 - a0 < 2 * max a0.minFac 1 := Nat.lt_of_lt_of_le h_d_q h_max_le
      exact eq_of_sub_lt_two_max_of_odd_of_mod_eq_liliu hp_odd hle h_d_p ha_odd hb_odd h_mod_eq
    | Or.inr hge =>
      have h_d_q : a0 - b0 < 2 * max q 1 := h_diam_fn b0 a0 hb_blk_tail.1 ha_blk_tail.1 hge
      have h_d_p : a0 - b0 < 2 * max a0.minFac 1 := Nat.lt_of_lt_of_le h_d_q h_max_le
      exact (eq_of_sub_lt_two_max_of_odd_of_mod_eq_liliu hp_odd hge h_d_p hb_odd ha_odd h_mod_eq.symm).symm
  have h_card_blk :
      (liliuP2OwnerFiber U q r).card ≤ (liliuSubTwoQBlockIndices U q).card := by
    rw [← Finset.card_image_of_injOn h_inj_blocks]
    exact card_le_card h_sub_blocks
  exact ⟨h_card_cof, h_card_blk, Nat.le_min.mpr ⟨h_card_blk, h_card_cof⟩⟩

theorem liliuP2OwnerFiber_disjoint_of_ne
    (S : Finset ℕ) (q : ℕ) {r₁ r₂ : ℕ} (hne : r₁ ≠ r₂) :
    Disjoint (liliuP2OwnerFiber S q r₁) (liliuP2OwnerFiber S q r₂) := by
  apply Finset.disjoint_left.mpr
  intro u hu1 hu2
  rw [liliuP2OwnerFiber, mem_filter] at hu1 hu2
  have h1 : u.minFac = r₁ := hu1.2
  have h2 : u.minFac = r₂ := hu2.2
  omega

/-- **Theorem 2.2 (`liliu_p2TailSet_card_eq_sum_p2OwnerFiber_and_le_sum_min_quota` — R6):**
    Global Owner-Summed Sharper-of-Two-Bounds Law on Track 2 (`D19 N`). -/
theorem liliu_p2TailSet_card_eq_sum_p2OwnerFiber_and_le_sum_min_quota (M q : ℕ) :
    let U := liliuFullLowerMURUpper M
    (liliuP2TailSet U q).card =
      ∑ r ∈ liliuP2ActiveOwnerPrimes M q, (liliuP2OwnerFiber U q r).card ∧
    (liliuP2TailSet U q).card ≤
      ∑ r ∈ liliuP2ActiveOwnerPrimes M q,
        min ((liliuSubTwoQBlockIndices U q).card) ((liliuPrimeCofactorWindow M r).card) := by
  dsimp only
  set U := liliuFullLowerMURUpper M
  have h_bi :
      liliuP2TailSet U q =
        (liliuP2ActiveOwnerPrimes M q).biUnion (fun r : ℕ => liliuP2OwnerFiber U q r) := by
    ext u
    rw [mem_biUnion]
    constructor
    · intro hu
      refine ⟨u.minFac, ?_, ?_⟩
      · have hu_copy := hu
        rw [liliuP2TailSet, mem_filter, liliuNonSqTailSet, mem_filter] at hu_copy
        obtain ⟨⟨hu_tail, h_not_sq⟩, _⟩ := hu_copy
        have h_sqrt_mem := (liliu_global_roughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes hu_tail).1
        have hu_odd : u % 2 = 1 :=
          (liliu_global_roughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes hu_tail).2.2.2.2
        have hp1_odd : u.minFac % 2 = 1 :=
          (liliu_global_roughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes hu_tail).2.2.2.1
        rw [liliuPn1RoughCompositeTail, mem_filter] at hu_tail
        have hu_le_2M3 : u ≤ 2 * M - 3 := (liliuFullLowerMURUpper_mem_props hu_tail.1).2.1
        have hu_ge_M1 : M + 1 ≤ u := (liliuFullLowerMURUpper_mem_props hu_tail.1).1
        set p1 := u.minFac
        set p2 := u / p1
        have hp1_pos : 0 < p1 := by omega
        have h_p1p2_eq : p1 * p2 = u :=
          (mod_eq_zero_and_mul_div_of_dvd_liliu hp1_pos (Nat.minFac_dvd u)).2
        have hp1_sq_le : p1 * p1 ≤ p1 * p2 := by
          rw [h_p1p2_eq]
          exact (minFac_mul_self_le_of_not_isPrimeNat_liliu hu_tail.2.1 hu_tail.2.2.2).2.2.2
        have hp1_le_p2 : p1 ≤ p2 := le_of_mul_le_mul_left_pos_liliu hp1_pos hp1_sq_le
        have hp1_ne_p2 : p1 ≠ p2 := by
          intro h_eq
          rw [← h_eq] at h_p1p2_eq
          exact h_not_sq h_p1p2_eq
        have hp2_dvd_u : p2 ∣ u := ⟨p1, by rw [Nat.mul_comm p2 p1]; exact h_p1p2_eq.symm⟩
        have hu_npv2 : 1 ≤ u % 2 := by omega
        have hp2_npv2 : 1 ≤ p2 % 2 :=
          (nonPVen_divisor_inheritance_liliu (by omega : 0 < 2) hp2_dvd_u hu_npv2).1
        have hp2_lt2 : p2 % 2 < 2 := Nat.mod_lt p2 (by omega : 0 < 2)
        have hp2_odd : p2 % 2 = 1 := by omega
        have hp1_div2 : 2 * (p1 / 2) + p1 % 2 = p1 := Nat.div_add_mod p1 2
        have hp2_div2 : 2 * (p2 / 2) + p2 % 2 = p2 := Nat.div_add_mod p2 2
        have hp1_add2_le_p2 : p1 + 2 ≤ p2 := by omega
        have h_mul_p12 : p1 * (p1 + 2) ≤ u := by
          rw [← h_p1p2_eq]
          exact Nat.mul_le_mul_left p1 hp1_add2_le_p2
        rw [liliuP2ActiveOwnerPrimes, mem_filter]
        exact ⟨h_sqrt_mem, by omega⟩
      · rw [liliuP2OwnerFiber, mem_filter]
        exact ⟨hu, rfl⟩
    · rintro ⟨r, _, hu_fib⟩
      rw [liliuP2OwnerFiber, mem_filter] at hu_fib
      exact hu_fib.1
  have h_disj :
      (↑(liliuP2ActiveOwnerPrimes M q) : Set ℕ).PairwiseDisjoint
        (fun r : ℕ => liliuP2OwnerFiber U q r) := by
    intro r₁ _ r₂ _ hne
    exact liliuP2OwnerFiber_disjoint_of_ne U q hne
  have h_sum_eq :
      (liliuP2TailSet U q).card =
        ∑ r ∈ liliuP2ActiveOwnerPrimes M q, (liliuP2OwnerFiber U q r).card := by
    conv_lhs => rw [h_bi]
    exact card_biUnion h_disj
  have h_sum_le :
      ∑ r ∈ liliuP2ActiveOwnerPrimes M q, (liliuP2OwnerFiber U q r).card ≤
        ∑ r ∈ liliuP2ActiveOwnerPrimes M q,
          min ((liliuSubTwoQBlockIndices U q).card) ((liliuPrimeCofactorWindow M r).card) := by
    apply sum_le_sum
    intro r _
    exact (liliuP2OwnerFiber_sharper_of_block_and_cofactor_quota M q r).2.2
  rw [← h_sum_eq] at h_sum_le
  exact ⟨h_sum_eq, h_sum_le⟩

/-!
## Section 3: Block-Summed Route B Receiver & Complete 85-Module R1–R10 Master Capstone
-/

theorem block_summed_routeB_credit_receiver_liliu
    {M : ℕ} (hM1 : 1 ≤ M)
    {H_SQ1 H_P2 B : Finset ℕ}
    (h_cov_sq1 : liliuSq1TailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M) ⊆ H_SQ1)
    (h_cov_p2 : liliuP2TailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M) ⊆ H_P2)
    {Q_SQ1 Q_P2 C_SQ1 C_P2 : ℕ → ℕ} {L : ℕ}
    (hQ1 : H_SQ1.card ≤ ∑ k ∈ B, Q_SQ1 k)
    (hQ2 : H_P2.card ≤ ∑ k ∈ B, Q_P2 k)
    (hC1 : ∑ k ∈ B, C_SQ1 k ≤ (liliuRejectedByLowerComposite M H_SQ1).card)
    (hC2 : ∑ k ∈ B, C_P2 k ≤ (liliuRejectedByLowerComposite M H_P2).card)
    (hL : L ≤ (liliuScreenedConcreteKbRadii M).card)
    (h_block_star :
      (∑ k ∈ B, Q_SQ1 k) + (∑ k ∈ B, Q_P2 k) + 1 ≤
        L + (∑ k ∈ B, C_SQ1 k) + (∑ k ∈ B, C_P2 k)) :
    1 ≤ (liliuPrimeSurvivorSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M)).card ∧
    ∃ p q' p_next' : ℕ,
      Nat.Prime p ∧ Nat.Prime q' ∧ p < q' ∧ 2 * M = p + q' ∧
      p < p_next' ∧ IsPrimeNat p_next' :=
  (routeB_species_credit_inequality_to_binary_goldbach_liliu hM1 h_cov_sq1 h_cov_p2).2.2
    (∑ k ∈ B, Q_SQ1 k) (∑ k ∈ B, Q_P2 k)
    (∑ k ∈ B, C_SQ1 k) (∑ k ∈ B, C_P2 k)
    L hQ1 hQ2 hC1 hC2 hL h_block_star

/-- **Master Theorem 3.1 (`master_85module_complete_r1_to_r10_including_r6_capstone`):**
    Complete 85-Module Master Capstone uniting `Goldbach.one_plus_one_nine_count` (`D19 N`)
    with ALL TEN Recommendations R1–R10 (including R6 Multi-Block Species Sums, `BC17`
    LPF–GPF Cell Singleton Cap, and Global Summed Sharper-of-Two-Bounds Quota). -/
theorem master_85module_complete_r1_to_r10_including_r6_capstone :
    (∀ N : ℕ, 4 ≤ N → Even N → ¬ IsResidualMidpointLiliu (N / 2) →
      ∃ p q p_next' : ℕ,
        Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next' ∧ IsPrimeNat p_next') ∧
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (∀ q r q2 : ℕ,
        (liliuLpfGpfCell (liliuFullLowerMURUpper (N / 2)) q r q2).card ≤ 1 ∧
        (liliuP2OwnerFiber (liliuFullLowerMURUpper (N / 2)) q r).card ≤
          min ((liliuSubTwoQBlockIndices (liliuFullLowerMURUpper (N / 2)) q).card)
              ((liliuPrimeCofactorWindow (N / 2) r).card)) ∧
      (∀ q : ℕ,
        (liliuSq1TailSet (liliuFullLowerMURUpper (N / 2)) q).card ≤
          (liliuSubTwoQBlockIndices (liliuFullLowerMURUpper (N / 2)) q).card ∧
        (liliuP2TailSet (liliuFullLowerMURUpper (N / 2)) q).card ≤
          ∑ r ∈ liliuP2ActiveOwnerPrimes (N / 2) q,
            min ((liliuSubTwoQBlockIndices (liliuFullLowerMURUpper (N / 2)) q).card)
                ((liliuPrimeCofactorWindow (N / 2) r).card)) ∧
      (∀ r : ℕ, IsPrimeNat r →
        liliuSubCubicStrikeFiber
          (liliuConcreteKbUpper (N / 2)) (liliuSqrtMidpointCutoff (N / 2)) r =
        liliuLpfOwnerFiber
          (liliuConcreteKbUpper (N / 2)) (liliuSqrtMidpointCutoff (N / 2)) r) ∧
      (∀ H_SQ1 H_P2 : Finset ℕ,
        liliuSq1TailSet (liliuConcreteKbUpper (N / 2)) (liliuSqrtMidpointCutoff (N / 2)) ⊆ H_SQ1 →
        liliuP2TailSet (liliuConcreteKbUpper (N / 2)) (liliuSqrtMidpointCutoff (N / 2)) ⊆ H_P2 →
        ∀ Q_SQ1 Q_P2 C_SQ1 C_P2 L : ℕ,
          H_SQ1.card ≤ Q_SQ1 →
          H_P2.card ≤ Q_P2 →
          C_SQ1 ≤ (liliuRejectedByLowerComposite (N / 2) H_SQ1).card →
          C_P2 ≤ (liliuRejectedByLowerComposite (N / 2) H_P2).card →
          L ≤ (liliuScreenedConcreteKbRadii (N / 2)).card →
          Q_SQ1 + Q_P2 + 1 ≤ L + C_SQ1 + C_P2 →
          ∃ p q' p_next' : ℕ,
            Nat.Prime p ∧ Nat.Prime q' ∧ p < q' ∧ 2 * (N / 2) = p + q' ∧
            p < p_next' ∧ IsPrimeNat p_next') := by
  obtain ⟨h_non_res, ⟨K, hK4, hCap83⟩⟩ :=
    master_83module_complete_r1_to_r10_all_even_architecture_capstone
  refine ⟨h_non_res, ⟨K, hK4, ?_⟩⟩
  intro N hNK hEven
  have hM := hCap83 N hNK hEven
  refine ⟨hM.1, ?_, ?_, hM.2.1, hM.2.2⟩
  · intro q r q2
    exact ⟨(liliuLpfGpfCell_subset_singleton_and_card_le_one
              (liliuFullLowerMURUpper (N / 2)) q r q2).2,
           (liliuP2OwnerFiber_sharper_of_block_and_cofactor_quota (N / 2) q r).2.2⟩
  · intro q
    exact ⟨(liliu_multi_block_exact_species_sq1_and_p2_sum_bounds (N / 2) q).2.2.1,
           (liliu_p2TailSet_card_eq_sum_p2OwnerFiber_and_le_sum_min_quota (N / 2) q).2⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.liliu_multi_block_exact_species_sq1_and_p2_sum_bounds
#print axioms WuPaper.ESZerosBridge.liliuLpfGpfCell_subset_singleton_and_card_le_one
#print axioms WuPaper.ESZerosBridge.liliuP2OwnerFiber_sharper_of_block_and_cofactor_quota
#print axioms WuPaper.ESZerosBridge.liliu_p2TailSet_card_eq_sum_p2OwnerFiber_and_le_sum_min_quota
#print axioms WuPaper.ESZerosBridge.block_summed_routeB_credit_receiver_liliu
#print axioms WuPaper.ESZerosBridge.master_85module_complete_r1_to_r10_including_r6_capstone
