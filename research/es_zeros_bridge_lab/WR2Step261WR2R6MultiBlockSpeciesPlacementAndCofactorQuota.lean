import WR2Step259WR2BC14ResidualFamilyAndAllEvenDomainAssembly

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step261WR2R6MultiBlockSpeciesPlacementAndCofactorQuota.lean — Recommendation R6 Implementation: Multi-Block Exact-Species Placement Sums, `BC17` LPF–GPF Cell Singleton Cap, `Step191`–`Step192` Prime-Cofactor Window Quota & Block-Summed Route B Receiver (`WR2` Track 1)

Implements Recommendation R6 (and Table Rows 6–7) of the November 9 closure plan:

1. **Section 1 — Multi-Block Exact-Species Partition & Summed Block Placement Bounds:**
   - Proves `sq1TailSet_subTwoQBlock_disjoint_of_ne` and `p2TailSet_subTwoQBlock_disjoint_of_ne`.
   - Proves `(sq1TailSet U q).card ≤ (subTwoQBlockIndices U q).card` (at most 1 `SQ-1`
     square per sub-`2q` block) and
     `(p2TailSet U q).card ≤ (subTwoQBlockIndices U q).card * (p2ActiveOwnerPrimes M q).card`.
2. **Section 2 — `BC17` LPF–GPF Cell Singleton Cap, `Step191`–`Step192` Prime-Cofactor Window Quota
   & Global Summed Sharper-of-Two-Bounds Law:**
   - Proves `lpfGpfCell S q r q2 ⊆ {r * q2}` and `(lpfGpfCell S q r q2).card ≤ 1`.
   - Proves for every owner prime `r`:
     `(p2OwnerFiber U q r).card ≤ min ((subTwoQBlockIndices U q).card) ((primeCofactorWindow M r).card)`.
   - Proves the global owner-summed sharper bound:
     `(p2TailSet U q).card = ∑ r ∈ p2ActiveOwnerPrimes M q, (p2OwnerFiber U q r).card` and
     `(p2TailSet U q).card ≤ ∑ r ∈ p2ActiveOwnerPrimes M q, min ((subTwoQBlockIndices U q).card) ((primeCofactorWindow M r).card)`.
3. **Section 3 — Block-Summed Route B Credit Receiver (`∑ k, Q_k + 1 ≤ L + ∑ k, C_k`):**
   - Proves that summing per-block catalog bounds `Q_k` and per-block rejected credits `C_k`
     discharges the Route B receiver when `∑ k, Q_k + 1 ≤ L + ∑ k, C_k`.
-/

/-!
## Section 1: Multi-Block Exact-Species Partition & Summed Block Placement Bounds
-/

theorem sq1TailSet_eq_biUnion_subTwoQBlocks (I : Finset ℕ) (q : ℕ) :
    sq1TailSet I q =
      (subTwoQBlockIndices I q).biUnion (fun k : ℕ =>
        sq1TailSet (subTwoQBlock I q k) q) := by
  ext u
  rw [mem_biUnion]
  constructor
  · intro hu
    rw [sq1TailSet, mem_filter] at hu
    obtain ⟨hu_tail, hu_sq⟩ := hu
    have hu_bi := hu_tail
    rw [pn1RoughCompositeTail_eq_biUnion_subTwoQBlocks I q, mem_biUnion] at hu_bi
    obtain ⟨k, hk_idx, hu_blk_tail⟩ := hu_bi
    refine ⟨k, hk_idx, ?_⟩
    rw [sq1TailSet, mem_filter]
    exact ⟨hu_blk_tail, hu_sq⟩
  · rintro ⟨k, _, hu_blk⟩
    rw [sq1TailSet, mem_filter] at hu_blk ⊢
    obtain ⟨hu_blk_tail, hu_sq⟩ := hu_blk
    rw [pn1RoughCompositeTail, mem_filter, subTwoQBlock, mem_filter] at hu_blk_tail
    rw [pn1RoughCompositeTail, mem_filter]
    exact ⟨⟨hu_blk_tail.1.1, hu_blk_tail.2⟩, hu_sq⟩

theorem p2TailSet_eq_biUnion_subTwoQBlocks (I : Finset ℕ) (q : ℕ) :
    p2TailSet I q =
      (subTwoQBlockIndices I q).biUnion (fun k : ℕ =>
        p2TailSet (subTwoQBlock I q k) q) := by
  ext u
  rw [mem_biUnion]
  constructor
  · intro hu
    rw [p2TailSet, mem_filter, nonSqTailSet, mem_filter] at hu
    obtain ⟨⟨hu_tail, hu_nsq⟩, hu_p2⟩ := hu
    have hu_bi := hu_tail
    rw [pn1RoughCompositeTail_eq_biUnion_subTwoQBlocks I q, mem_biUnion] at hu_bi
    obtain ⟨k, hk_idx, hu_blk_tail⟩ := hu_bi
    refine ⟨k, hk_idx, ?_⟩
    rw [p2TailSet, mem_filter, nonSqTailSet, mem_filter]
    exact ⟨⟨hu_blk_tail, hu_nsq⟩, hu_p2⟩
  · rintro ⟨k, _, hu_blk⟩
    rw [p2TailSet, mem_filter, nonSqTailSet, mem_filter] at hu_blk ⊢
    obtain ⟨⟨hu_blk_tail, hu_nsq⟩, hu_p2⟩ := hu_blk
    rw [pn1RoughCompositeTail, mem_filter, subTwoQBlock, mem_filter] at hu_blk_tail
    rw [pn1RoughCompositeTail, mem_filter]
    exact ⟨⟨⟨hu_blk_tail.1.1, hu_blk_tail.2⟩, hu_nsq⟩, hu_p2⟩

theorem sq1TailSet_subTwoQBlock_disjoint_of_ne
    (I : Finset ℕ) (q : ℕ) {k₁ k₂ : ℕ} (hne : k₁ ≠ k₂) :
    Disjoint (sq1TailSet (subTwoQBlock I q k₁) q)
             (sq1TailSet (subTwoQBlock I q k₂) q) := by
  apply Finset.disjoint_left.mpr
  intro u hu1 hu2
  rw [sq1TailSet, mem_filter] at hu1 hu2
  exact Finset.disjoint_left.mp
    (pn1RoughCompositeTail_subTwoQBlock_disjoint_of_ne I q hne) hu1.1 hu2.1

theorem p2TailSet_subTwoQBlock_disjoint_of_ne
    (I : Finset ℕ) (q : ℕ) {k₁ k₂ : ℕ} (hne : k₁ ≠ k₂) :
    Disjoint (p2TailSet (subTwoQBlock I q k₁) q)
             (p2TailSet (subTwoQBlock I q k₂) q) := by
  apply Finset.disjoint_left.mpr
  intro u hu1 hu2
  rw [p2TailSet, mem_filter, nonSqTailSet, mem_filter] at hu1 hu2
  exact Finset.disjoint_left.mp
    (pn1RoughCompositeTail_subTwoQBlock_disjoint_of_ne I q hne) hu1.1.1 hu2.1.1

/-- **Theorem 1.1 (`multi_block_exact_species_sq1_and_p2_sum_bounds` — R6):**
    Multi-Block Exact-Species Placement Bounds:
    For all `M, q : ℕ`, let `U := fullLowerMURUpper M` and `B := subTwoQBlockIndices U q`.
    1. `(sq1TailSet U q).card = ∑ k ∈ B, (sq1TailSet (subTwoQBlock U q k) q).card`,
    2. `(p2TailSet U q).card = ∑ k ∈ B, (p2TailSet (subTwoQBlock U q k) q).card`,
    3. `(sq1TailSet U q).card ≤ B.card` (at most 1 `SQ-1` square per sub-`2q` block), and
    4. `(p2TailSet U q).card ≤ B.card * (p2ActiveOwnerPrimes M q).card`! -/
theorem multi_block_exact_species_sq1_and_p2_sum_bounds (M q : ℕ) :
    let U := fullLowerMURUpper M
    let B := subTwoQBlockIndices U q
    (sq1TailSet U q).card = ∑ k ∈ B, (sq1TailSet (subTwoQBlock U q k) q).card ∧
    (p2TailSet U q).card = ∑ k ∈ B, (p2TailSet (subTwoQBlock U q k) q).card ∧
    (sq1TailSet U q).card ≤ B.card ∧
    (p2TailSet U q).card ≤ B.card * (p2ActiveOwnerPrimes M q).card := by
  dsimp only
  set U := fullLowerMURUpper M
  set B := subTwoQBlockIndices U q
  have h_disj_sq1 :
      (↑B : Set ℕ).PairwiseDisjoint (fun k : ℕ => sq1TailSet (subTwoQBlock U q k) q) := by
    intro k₁ _ k₂ _ hne
    exact sq1TailSet_subTwoQBlock_disjoint_of_ne U q hne
  have h_disj_p2 :
      (↑B : Set ℕ).PairwiseDisjoint (fun k : ℕ => p2TailSet (subTwoQBlock U q k) q) := by
    intro k₁ _ k₂ _ hne
    exact p2TailSet_subTwoQBlock_disjoint_of_ne U q hne
  have h_sq1_eq :
      (sq1TailSet U q).card = ∑ k ∈ B, (sq1TailSet (subTwoQBlock U q k) q).card := by
    conv_lhs => rw [sq1TailSet_eq_biUnion_subTwoQBlocks U q]
    exact card_biUnion h_disj_sq1
  have h_p2_eq :
      (p2TailSet U q).card = ∑ k ∈ B, (p2TailSet (subTwoQBlock U q k) q).card := by
    conv_lhs => rw [p2TailSet_eq_biUnion_subTwoQBlocks U q]
    exact card_biUnion h_disj_p2
  have h_sq1_le : (sq1TailSet U q).card ≤ B.card := by
    rw [h_sq1_eq]
    have h_sum1 :
        ∑ k ∈ B, (sq1TailSet (subTwoQBlock U q k) q).card ≤ ∑ _k ∈ B, 1 := by
      apply sum_le_sum
      intro k _
      exact sq1TailSet_subTwoQBlock_card_le_one U q k
    rw [sum_const, smul_eq_mul, Nat.mul_one] at h_sum1
    exact h_sum1
  have h_p2_le : (p2TailSet U q).card ≤ B.card * (p2ActiveOwnerPrimes M q).card := by
    rw [h_p2_eq]
    have h_sum2 :
        ∑ k ∈ B, (p2TailSet (subTwoQBlock U q k) q).card ≤
          ∑ _k ∈ B, (p2ActiveOwnerPrimes M q).card := by
      apply sum_le_sum
      intro k _
      exact (p2TailSet_subTwoQBlock_card_le_p2ActiveOwnerPrimes M q k).1
    rw [sum_const, smul_eq_mul] at h_sum2
    exact h_sum2
  exact ⟨h_sq1_eq, h_p2_eq, h_sq1_le, h_p2_le⟩

/-!
## Section 2: `BC17` LPF–GPF Cell Singleton Cap, `Step191`–`Step192` Prime-Cofactor Window Quota & Global Summed Sharper Bound
-/

/-- Per-prime `P-2` owner fiber `p2OwnerFiber S q r = {u ∈ p2TailSet S q | u.minFac = r}` (`Step191`). -/
def p2OwnerFiber (S : Finset ℕ) (q r : ℕ) : Finset ℕ :=
  (p2TailSet S q).filter (fun u : ℕ => u.minFac = r)

/-- Exact `BC17` LPF–GPF joint pattern cell for ordered prime pair `(r, q2)` on `p2TailSet S q` (R5 & R6). -/
def lpfGpfCell (S : Finset ℕ) (q r q2 : ℕ) : Finset ℕ :=
  (p2OwnerFiber S q r).filter (fun u : ℕ => u / r = q2)

/-- Prime-Cofactor Window for owner prime `r` on `fullLowerMURUpper M` (`Step191` & `Step192`):
    odd primes `q2 ≥ r + 2` whose product `r * q2` lies in `[M + 1, 2 * M - 3]`. -/
def primeCofactorWindow (M r : ℕ) : Finset ℕ :=
  (range (2 * M + 1)).filter (fun q2 : ℕ =>
    IsPrimeNat q2 ∧ q2 % 2 = 1 ∧ r + 2 ≤ q2 ∧ M + 1 ≤ r * q2 ∧ r * q2 ≤ 2 * M - 3)

/-- **Theorem 2.1 (`lpfGpfCell_subset_singleton_and_card_le_one` — R5 & R6 `BC17` Cell Cap):**
    Every `BC17` LPF–GPF cell `lpfGpfCell S q r q2` is a subset of `{r * q2}` and has
    cardinality at most `1`! -/
theorem lpfGpfCell_subset_singleton_and_card_le_one (S : Finset ℕ) (q r q2 : ℕ) :
    lpfGpfCell S q r q2 ⊆ {r * q2} ∧
    (lpfGpfCell S q r q2).card ≤ 1 := by
  have h_sub : lpfGpfCell S q r q2 ⊆ {r * q2} := by
    intro u hu
    rw [lpfGpfCell, mem_filter, p2OwnerFiber, mem_filter,
        p2TailSet, mem_filter, nonSqTailSet, mem_filter,
        pn1RoughCompositeTail, mem_filter] at hu
    obtain ⟨⟨⟨⟨⟨_, hu2, _, hu_comp⟩, _⟩, _⟩, hr_eq⟩, hq2_eq⟩ := hu
    have h_mf := minFac_mul_self_le_of_not_isPrimeNat hu2 hu_comp
    have hr_two : 2 ≤ r := by
      rw [← hr_eq]
      exact h_mf.1.1
    have hr_pos : 0 < r := by omega
    have hr_dvd : r ∣ u := by
      rw [← hr_eq]
      exact Nat.minFac_dvd u
    have h_mul : r * (u / r) = u :=
      (mod_eq_zero_and_mul_div_of_dvd_native hr_pos hr_dvd).2
    rw [hq2_eq] at h_mul
    rw [mem_singleton]
    exact h_mul.symm
  have h_card : (lpfGpfCell S q r q2).card ≤ 1 := by
    have h1 := card_le_card h_sub
    rw [card_singleton] at h1
    exact h1
  exact ⟨h_sub, h_card⟩

/-- **Theorem 2.2 (`p2OwnerFiber_sharper_of_block_and_cofactor_quota` — R6):**
    For EVERY `M, q, r : ℕ`, the per-prime `P-2` owner fiber `p2OwnerFiber (fullLowerMURUpper M) q r`
    satisfies BOTH the Prime-Cofactor Window Quota and the Sub-`2q` Block-Count Quota:
    `(p2OwnerFiber (fullLowerMURUpper M) q r).card ≤ min ((subTwoQBlockIndices (fullLowerMURUpper M) q).card) ((primeCofactorWindow M r).card)`! -/
theorem p2OwnerFiber_sharper_of_block_and_cofactor_quota (M q r : ℕ) :
    (p2OwnerFiber (fullLowerMURUpper M) q r).card ≤
      (primeCofactorWindow M r).card ∧
    (p2OwnerFiber (fullLowerMURUpper M) q r).card ≤
      (subTwoQBlockIndices (fullLowerMURUpper M) q).card ∧
    (p2OwnerFiber (fullLowerMURUpper M) q r).card ≤
      min ((subTwoQBlockIndices (fullLowerMURUpper M) q).card)
          ((primeCofactorWindow M r).card) := by
  set U := fullLowerMURUpper M
  have h_sub_cof :
      (p2OwnerFiber U q r).image (fun u : ℕ => u / r) ⊆ primeCofactorWindow M r := by
    intro q2 hq2
    rw [mem_image] at hq2
    obtain ⟨u, hu, rfl⟩ := hq2
    rw [p2OwnerFiber, mem_filter, p2TailSet, mem_filter,
        nonSqTailSet, mem_filter, pn1RoughCompositeTail, mem_filter] at hu
    obtain ⟨⟨⟨⟨hu_U, hu2, _, hu_comp⟩, h_nsq⟩, h_p2_isp⟩, hr_eq⟩ := hu
    have hu_props := fullLowerMURUpper_mem_props hu_U
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
  have h_inj_cof : Set.InjOn (fun u : ℕ => u / r) (↑(p2OwnerFiber U q r) : Set ℕ) := by
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
      (p2OwnerFiber U q r).card ≤ (primeCofactorWindow M r).card := by
    rw [← Finset.card_image_of_injOn h_inj_cof]
    exact card_le_card h_sub_cof
  have h_sub_blocks :
      (p2OwnerFiber U q r).image (fun u : ℕ => u / (2 * max q 1)) ⊆
        subTwoQBlockIndices U q := by
    intro k hk
    rw [mem_image] at hk
    obtain ⟨u, hu, rfl⟩ := hk
    rw [p2OwnerFiber, mem_filter, p2TailSet, mem_filter,
        nonSqTailSet, mem_filter, pn1RoughCompositeTail, mem_filter] at hu
    rw [subTwoQBlockIndices, mem_image]
    exact ⟨u, hu.1.1.1.1, rfl⟩
  have h_inj_blocks :
      Set.InjOn (fun u : ℕ => u / (2 * max q 1)) (↑(p2OwnerFiber U q r) : Set ℕ) := by
    intro a0 ha0 b0 hb0 hk_eq
    rw [mem_coe, p2OwnerFiber, mem_filter, p2TailSet, mem_filter,
        nonSqTailSet, mem_filter] at ha0 hb0
    have ha_tail := ha0.1.1.1
    have hb_tail := hb0.1.1.1
    have h_mf_eq : a0.minFac = b0.minFac := by rw [ha0.2, hb0.2]
    dsimp only at hk_eq
    set k := a0 / (2 * max q 1)
    have ha_blk_tail : a0 ∈ pn1RoughCompositeTail (subTwoQBlock U q k) q := by
      rw [pn1RoughCompositeTail, mem_filter] at ha_tail ⊢
      rw [subTwoQBlock, mem_filter]
      exact ⟨⟨ha_tail.1, rfl⟩, ha_tail.2⟩
    have hb_blk_tail : b0 ∈ pn1RoughCompositeTail (subTwoQBlock U q k) q := by
      rw [pn1RoughCompositeTail, mem_filter] at hb_tail ⊢
      rw [subTwoQBlock, mem_filter]
      exact ⟨⟨hb_tail.1, hk_eq.symm⟩, hb_tail.2⟩
    have ha_props := roughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes ha_blk_tail
    have hb_props := roughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes hb_blk_tail
    rw [pn1RoughCompositeTail, mem_filter] at ha_blk_tail hb_blk_tail
    have h_diam_fn := (subTwoQBlock_unconditional_partition_and_diameter U q).2.2.2 k
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
      exact eq_of_sub_lt_two_max_of_odd_of_mod_eq hp_odd hle h_d_p ha_odd hb_odd h_mod_eq
    | Or.inr hge =>
      have h_d_q : a0 - b0 < 2 * max q 1 := h_diam_fn b0 a0 hb_blk_tail.1 ha_blk_tail.1 hge
      have h_d_p : a0 - b0 < 2 * max a0.minFac 1 := Nat.lt_of_lt_of_le h_d_q h_max_le
      exact (eq_of_sub_lt_two_max_of_odd_of_mod_eq hp_odd hge h_d_p hb_odd ha_odd h_mod_eq.symm).symm
  have h_card_blk :
      (p2OwnerFiber U q r).card ≤ (subTwoQBlockIndices U q).card := by
    rw [← Finset.card_image_of_injOn h_inj_blocks]
    exact card_le_card h_sub_blocks
  exact ⟨h_card_cof, h_card_blk, Nat.le_min.mpr ⟨h_card_blk, h_card_cof⟩⟩

theorem p2OwnerFiber_disjoint_of_ne
    (S : Finset ℕ) (q : ℕ) {r₁ r₂ : ℕ} (hne : r₁ ≠ r₂) :
    Disjoint (p2OwnerFiber S q r₁) (p2OwnerFiber S q r₂) := by
  apply Finset.disjoint_left.mpr
  intro u hu1 hu2
  rw [p2OwnerFiber, mem_filter] at hu1 hu2
  have h1 : u.minFac = r₁ := hu1.2
  have h2 : u.minFac = r₂ := hu2.2
  omega

/-- **Theorem 2.3 (`p2TailSet_card_eq_sum_p2OwnerFiber_and_le_sum_min_quota` — R6):**
    Global Owner-Summed Sharper-of-Two-Bounds Law on `p2TailSet (fullLowerMURUpper M) q`:
    1. `(p2TailSet (fullLowerMURUpper M) q).card = ∑ r ∈ p2ActiveOwnerPrimes M q, (p2OwnerFiber (fullLowerMURUpper M) q r).card`, and
    2. `(p2TailSet (fullLowerMURUpper M) q).card ≤ ∑ r ∈ p2ActiveOwnerPrimes M q, min ((subTwoQBlockIndices (fullLowerMURUpper M) q).card) ((primeCofactorWindow M r).card)`! -/
theorem p2TailSet_card_eq_sum_p2OwnerFiber_and_le_sum_min_quota (M q : ℕ) :
    let U := fullLowerMURUpper M
    (p2TailSet U q).card =
      ∑ r ∈ p2ActiveOwnerPrimes M q, (p2OwnerFiber U q r).card ∧
    (p2TailSet U q).card ≤
      ∑ r ∈ p2ActiveOwnerPrimes M q,
        min ((subTwoQBlockIndices U q).card) ((primeCofactorWindow M r).card) := by
  dsimp only
  set U := fullLowerMURUpper M
  have h_bi :
      p2TailSet U q =
        (p2ActiveOwnerPrimes M q).biUnion (fun r : ℕ => p2OwnerFiber U q r) := by
    ext u
    rw [mem_biUnion]
    constructor
    · intro hu
      refine ⟨u.minFac, ?_, ?_⟩
      · have hu_copy := hu
        rw [p2TailSet, mem_filter, nonSqTailSet, mem_filter] at hu_copy
        obtain ⟨⟨hu_tail, h_not_sq⟩, _⟩ := hu_copy
        have h_sqrt_mem := (global_roughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes hu_tail).1
        have hu_odd : u % 2 = 1 :=
          (global_roughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes hu_tail).2.2.2.2
        have hp1_odd : u.minFac % 2 = 1 :=
          (global_roughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes hu_tail).2.2.2.1
        rw [pn1RoughCompositeTail, mem_filter] at hu_tail
        have hu_le_2M3 : u ≤ 2 * M - 3 := (fullLowerMURUpper_mem_props hu_tail.1).2.1
        have hu_ge_M1 : M + 1 ≤ u := (fullLowerMURUpper_mem_props hu_tail.1).1
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
  have h_disj :
      (↑(p2ActiveOwnerPrimes M q) : Set ℕ).PairwiseDisjoint
        (fun r : ℕ => p2OwnerFiber U q r) := by
    intro r₁ _ r₂ _ hne
    exact p2OwnerFiber_disjoint_of_ne U q hne
  have h_sum_eq :
      (p2TailSet U q).card =
        ∑ r ∈ p2ActiveOwnerPrimes M q, (p2OwnerFiber U q r).card := by
    conv_lhs => rw [h_bi]
    exact card_biUnion h_disj
  have h_sum_le :
      ∑ r ∈ p2ActiveOwnerPrimes M q, (p2OwnerFiber U q r).card ≤
        ∑ r ∈ p2ActiveOwnerPrimes M q,
          min ((subTwoQBlockIndices U q).card) ((primeCofactorWindow M r).card) := by
    apply sum_le_sum
    intro r _
    exact (p2OwnerFiber_sharper_of_block_and_cofactor_quota M q r).2.2
  rw [← h_sum_eq] at h_sum_le
  exact ⟨h_sum_eq, h_sum_le⟩

/-!
## Section 3: Compatible Block-Summed Route B Credit Receiver (`∑ k, Q_k + 1 ≤ L + ∑ k, C_k`)
-/

/-- **Theorem 3.1 (`block_summed_routeB_credit_receiver_wr2` — R6 & R9):**
    Compatible Block-Summed Route B Credit Receiver on Track 1 (`WR2`). -/
theorem block_summed_routeB_credit_receiver_wr2
    {M : ℕ} (hM1 : 1 ≤ M)
    {H_SQ1 H_P2 B : Finset ℕ}
    (h_cov_sq1 : sq1TailSet (concreteKbUpper M) (sqrtMidpointCutoff M) ⊆ H_SQ1)
    (h_cov_p2 : p2TailSet (concreteKbUpper M) (sqrtMidpointCutoff M) ⊆ H_P2)
    {Q_SQ1 Q_P2 C_SQ1 C_P2 : ℕ → ℕ} {L : ℕ}
    (hQ1 : H_SQ1.card ≤ ∑ k ∈ B, Q_SQ1 k)
    (hQ2 : H_P2.card ≤ ∑ k ∈ B, Q_P2 k)
    (hC1 : ∑ k ∈ B, C_SQ1 k ≤ (rejectedByLowerComposite M H_SQ1).card)
    (hC2 : ∑ k ∈ B, C_P2 k ≤ (rejectedByLowerComposite M H_P2).card)
    (hL : L ≤ (screenedConcreteKbRadii M).card)
    (h_block_star :
      (∑ k ∈ B, Q_SQ1 k) + (∑ k ∈ B, Q_P2 k) + 1 ≤
        L + (∑ k ∈ B, C_SQ1 k) + (∑ k ∈ B, C_P2 k)) :
    1 ≤ (primeSurvivorSet (concreteKbUpper M) (sqrtMidpointCutoff M)).card ∧
    ∃ p q' p_next' : ℕ,
      Nat.Prime p ∧ Nat.Prime q' ∧ p < q' ∧ 2 * M = p + q' ∧
      p < p_next' ∧ Nat.Prime p_next' ∧ IsPrimeNat p_next' :=
  (routeB_species_credit_inequality_to_binary_goldbach_wr2 hM1 h_cov_sq1 h_cov_p2).2.2
    (∑ k ∈ B, Q_SQ1 k) (∑ k ∈ B, Q_P2 k)
    (∑ k ∈ B, C_SQ1 k) (∑ k ∈ B, C_P2 k)
    L hQ1 hQ2 hC1 hC2 hL h_block_star

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.multi_block_exact_species_sq1_and_p2_sum_bounds
#print axioms WuPaper.ESZerosBridge.lpfGpfCell_subset_singleton_and_card_le_one
#print axioms WuPaper.ESZerosBridge.p2OwnerFiber_sharper_of_block_and_cofactor_quota
#print axioms WuPaper.ESZerosBridge.p2TailSet_card_eq_sum_p2OwnerFiber_and_le_sum_min_quota
#print axioms WuPaper.ESZerosBridge.block_summed_routeB_credit_receiver_wr2
