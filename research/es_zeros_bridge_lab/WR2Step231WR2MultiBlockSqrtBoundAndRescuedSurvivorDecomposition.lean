import WR2Step229WR2OptimalM3Plus1CutoffAndSqrtOwnerInjection

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step231WR2MultiBlockSqrtBoundAndRescuedSurvivorDecomposition.lean — Multi-Block Global `√(2M)` Bound & Rescued Prime Survivor Pincer (`Step208` + `Step209` on `WR2` Track 1)

1. **Exact Disjoint Partition of `roughSurvivorSet S q` (`primeSurvivorSet`,
   `roughSurvivorSet_card_eq_primeSurvivors_add_compositeTail`):**
   Partitions `roughSurvivorSet S q` into `primeSurvivorSet S q` (`IsPrimeNat u`) and
   `pn1RoughCompositeTail S q` (`¬ IsPrimeNat u`).
2. **Global Multi-Block `√(2M)` Upper Bound on `fullLowerMURUpper M`
   (`fullLowerMURUpper_roughCompositeTail_card_le_blocks_mul_sqrtOwners`):**
   Sums `subTwoQBlock_roughCompositeTail_card_le_sqrtActiveOwnerPrimes` over all Quotient
   Wave Shear blocks `subTwoQBlockIndices (fullLowerMURUpper M) q`, proving unconditionally:
   `(pn1RoughCompositeTail (fullLowerMURUpper M) q).card ≤ (subTwoQBlockIndices (fullLowerMURUpper M) q).card * (sqrtActiveOwnerPrimes M q).card`.
3. **Direct Survivor Margin to Binary Goldbach Theorem (`fullLowerMUR_sqrt_margin_to_binary_goldbach`):**
   Whenever `(subTwoQBlockIndices (fullLowerMURUpper M) q).card * (sqrtActiveOwnerPrimes M q).card < (roughSurvivorSet (fullLowerMURUpper M) q).card`,
   `0 < (primeSurvivorSet (fullLowerMURUpper M) q).card` holds immediately and yields a
   certified Binary Goldbach partition `2 * M = p + q` paired with its Factorial Lighthouse next prime!
-/

/-!
## Section 1: Exact Disjoint Partition of `roughSurvivorSet S q`
-/

/-- The `q`-rough prime survivor subset of `S : Finset ℕ`. -/
def primeSurvivorSet (S : Finset ℕ) (q : ℕ) : Finset ℕ :=
  S.filter (fun u : ℕ =>
    2 ≤ u ∧
    (∀ d ∈ range q, 2 ≤ d → 1 ≤ u % d) ∧
    IsPrimeNat u)

theorem disjoint_primeSurvivorSet_pn1RoughCompositeTail (S : Finset ℕ) (q : ℕ) :
    Disjoint (primeSurvivorSet S q) (pn1RoughCompositeTail S q) := by
  apply Finset.disjoint_left.mpr
  intro u hp hc
  rw [primeSurvivorSet, mem_filter] at hp
  rw [pn1RoughCompositeTail, mem_filter] at hc
  exact hc.2.2.2 hp.2.2.2

theorem roughSurvivorSet_eq_primeSurvivors_union_compositeTail (S : Finset ℕ) (q : ℕ) :
    roughSurvivorSet S q = primeSurvivorSet S q ∪ pn1RoughCompositeTail S q := by
  ext u
  simp only [mem_union, roughSurvivorSet, primeSurvivorSet, pn1RoughCompositeTail, mem_filter]
  constructor
  · intro hu
    cases Classical.em (IsPrimeNat u) with
    | inl h_isp => exact Or.inl ⟨hu.1, hu.2.1, hu.2.2, h_isp⟩
    | inr h_comp => exact Or.inr ⟨hu.1, hu.2.1, hu.2.2, h_comp⟩
  · intro hor
    cases hor with
    | inl hp => exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
    | inr hc => exact ⟨hc.1, hc.2.1, hc.2.2.1⟩

/-- **Theorem 1.1 (`roughSurvivorSet_card_eq_primeSurvivors_add_compositeTail`):**
    Exact additive decomposition of `roughSurvivorSet S q` into `primeSurvivorSet S q`
    and `pn1RoughCompositeTail S q` for every `S : Finset ℕ` and `q : ℕ`. -/
theorem roughSurvivorSet_card_eq_primeSurvivors_add_compositeTail (S : Finset ℕ) (q : ℕ) :
    (roughSurvivorSet S q).card =
      (primeSurvivorSet S q).card + (pn1RoughCompositeTail S q).card := by
  conv_lhs => rw [roughSurvivorSet_eq_primeSurvivors_union_compositeTail S q]
  exact card_union_of_disjoint (disjoint_primeSurvivorSet_pn1RoughCompositeTail S q)

/-!
## Section 2: Global Multi-Block `√(2M)` Upper Bound & Direct Goldbach Extraction
-/

/-- Block decomposition of `pn1RoughCompositeTail I q` across `subTwoQBlockIndices I q`. -/
theorem pn1RoughCompositeTail_eq_biUnion_subTwoQBlocks (I : Finset ℕ) (q : ℕ) :
    pn1RoughCompositeTail I q =
      (subTwoQBlockIndices I q).biUnion (fun k : ℕ =>
        pn1RoughCompositeTail (subTwoQBlock I q k) q) := by
  ext u
  rw [mem_biUnion]
  constructor
  · intro hu
    rw [pn1RoughCompositeTail, mem_filter] at hu
    refine ⟨u / (2 * max q 1), ?_, ?_⟩
    · rw [subTwoQBlockIndices, mem_image]
      exact ⟨u, hu.1, rfl⟩
    · rw [pn1RoughCompositeTail, mem_filter, subTwoQBlock, mem_filter]
      exact ⟨⟨hu.1, rfl⟩, hu.2⟩
  · intro hbi
    obtain ⟨k, _, hu_blk⟩ := hbi
    rw [pn1RoughCompositeTail, mem_filter, subTwoQBlock, mem_filter] at hu_blk
    rw [pn1RoughCompositeTail, mem_filter]
    exact ⟨hu_blk.1.1, hu_blk.2⟩

theorem pn1RoughCompositeTail_subTwoQBlock_disjoint_of_ne
    (I : Finset ℕ) (q : ℕ) {k₁ k₂ : ℕ} (hne : k₁ ≠ k₂) :
    Disjoint (pn1RoughCompositeTail (subTwoQBlock I q k₁) q)
             (pn1RoughCompositeTail (subTwoQBlock I q k₂) q) := by
  apply Finset.disjoint_left.mpr
  intro u hu1 hu2
  rw [pn1RoughCompositeTail, mem_filter, subTwoQBlock, mem_filter] at hu1 hu2
  have hk1 : u / (2 * max q 1) = k₁ := hu1.1.2
  have hk2 : u / (2 * max q 1) = k₂ := hu2.1.2
  omega

/-- **Theorem 2.1 (`fullLowerMURUpper_roughCompositeTail_card_le_blocks_mul_sqrtOwners`):**
    Global Multi-Block `√(2M)` Upper Bound (`Step208` + `Step209`):
    For ALL `M, q : ℕ`,
    `(pn1RoughCompositeTail (fullLowerMURUpper M) q).card ≤ (subTwoQBlockIndices (fullLowerMURUpper M) q).card * (sqrtActiveOwnerPrimes M q).card`. -/
theorem fullLowerMURUpper_roughCompositeTail_card_le_blocks_mul_sqrtOwners (M q : ℕ) :
    (pn1RoughCompositeTail (fullLowerMURUpper M) q).card ≤
      (subTwoQBlockIndices (fullLowerMURUpper M) q).card *
        (sqrtActiveOwnerPrimes M q).card := by
  have h_disj :
      (↑(subTwoQBlockIndices (fullLowerMURUpper M) q) : Set ℕ).PairwiseDisjoint
        (fun k : ℕ => pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) q k) q) := by
    intro k₁ _ k₂ _ hne
    exact pn1RoughCompositeTail_subTwoQBlock_disjoint_of_ne (fullLowerMURUpper M) q hne
  have h_card_eq :
      (pn1RoughCompositeTail (fullLowerMURUpper M) q).card =
        ∑ k ∈ subTwoQBlockIndices (fullLowerMURUpper M) q,
          (pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) q k) q).card := by
    conv_lhs => rw [pn1RoughCompositeTail_eq_biUnion_subTwoQBlocks (fullLowerMURUpper M) q]
    exact card_biUnion h_disj
  rw [h_card_eq]
  have h_sum_le :
      ∑ k ∈ subTwoQBlockIndices (fullLowerMURUpper M) q,
          (pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) q k) q).card ≤
        ∑ _k ∈ subTwoQBlockIndices (fullLowerMURUpper M) q,
          (sqrtActiveOwnerPrimes M q).card := by
    apply sum_le_sum
    intro k _
    exact subTwoQBlock_roughCompositeTail_card_le_sqrtActiveOwnerPrimes M q k
  rw [sum_const, smul_eq_mul] at h_sum_le
  exact h_sum_le

/-- **Theorem 2.2 (`fullLowerMUR_sqrt_margin_to_binary_goldbach`):**
    Unconditional `Step209` Survivor-Margin Goldbach Extractor on `WR2`:
    Whenever `(subTwoQBlockIndices (fullLowerMURUpper M) q).card * (sqrtActiveOwnerPrimes M q).card < (roughSurvivorSet (fullLowerMURUpper M) q).card`,
    `0 < (primeSurvivorSet (fullLowerMURUpper M) q).card` holds immediately and produces
    a certified Binary Goldbach partition `2 * M = p + q'` paired with `p < p_next'`. -/
theorem fullLowerMUR_sqrt_margin_to_binary_goldbach
    {M q : ℕ}
    (h_margin :
      (subTwoQBlockIndices (fullLowerMURUpper M) q).card *
        (sqrtActiveOwnerPrimes M q).card <
      (roughSurvivorSet (fullLowerMURUpper M) q).card) :
    0 < (primeSurvivorSet (fullLowerMURUpper M) q).card ∧
    ∃ p q' p_next' : ℕ,
      Nat.Prime p ∧ Nat.Prime q' ∧ 2 * M = p + q' ∧
      p < p_next' ∧ Nat.Prime p_next' ∧ IsPrimeNat p_next' := by
  have h_part :=
    roughSurvivorSet_card_eq_primeSurvivors_add_compositeTail (fullLowerMURUpper M) q
  have h_comp_le :=
    fullLowerMURUpper_roughCompositeTail_card_le_blocks_mul_sqrtOwners M q
  have h_pos : 0 < (primeSurvivorSet (fullLowerMURUpper M) q).card := by omega
  refine ⟨h_pos, ?_⟩
  obtain ⟨u, hu⟩ := card_pos.mp h_pos
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

#print axioms WuPaper.ESZerosBridge.roughSurvivorSet_card_eq_primeSurvivors_add_compositeTail
#print axioms WuPaper.ESZerosBridge.fullLowerMURUpper_roughCompositeTail_card_le_blocks_mul_sqrtOwners
#print axioms WuPaper.ESZerosBridge.fullLowerMUR_sqrt_margin_to_binary_goldbach
