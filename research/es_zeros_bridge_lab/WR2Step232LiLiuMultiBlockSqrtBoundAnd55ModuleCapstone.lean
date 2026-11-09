import WR2Step230LiLiuOptimalM3Plus1And53ModuleCapstone

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step232LiLiuMultiBlockSqrtBoundAnd55ModuleCapstone.lean — Multi-Block Global `√(2M)` Bound, Rescued Prime Survivor Pincer & Master 55-Module `D19 N` Capstone

Completes the 55-Module `goldbach-lean` x `ES_Zeros` verification suite by welding:
1. The Exact Disjoint Partition of `liliuRoughSurvivorSet S q` into `liliuPrimeSurvivorSet S q`
   and `liliuPn1RoughCompositeTail S q`,
2. The Global Multi-Block `√(2M)` Upper Bound across `liliuFullLowerMURUpper M`
   (`liliuFullLowerMURUpper_roughCompositeTail_card_le_blocks_mul_sqrtOwners`), and
3. The Direct Survivor-Margin Binary Goldbach Extractor (`liliuFullLowerMUR_sqrt_margin_to_binary_goldbach`)
into the 55-Module `Goldbach.All` (`D19 N`) Master Capstone.
-/

/-!
## Section 1: Exact Disjoint Partition of `liliuRoughSurvivorSet S q`
-/

def liliuPrimeSurvivorSet (S : Finset ℕ) (q : ℕ) : Finset ℕ :=
  S.filter (fun u : ℕ =>
    2 ≤ u ∧
    (∀ d ∈ range q, 2 ≤ d → 1 ≤ u % d) ∧
    IsPrimeNat u)

theorem disjoint_liliuPrimeSurvivorSet_compositeTail (S : Finset ℕ) (q : ℕ) :
    Disjoint (liliuPrimeSurvivorSet S q) (liliuPn1RoughCompositeTail S q) := by
  apply Finset.disjoint_left.mpr
  intro u hp hc
  rw [liliuPrimeSurvivorSet, mem_filter] at hp
  rw [liliuPn1RoughCompositeTail, mem_filter] at hc
  exact hc.2.2.2 hp.2.2.2

theorem liliuRoughSurvivorSet_eq_primeSurvivors_union_compositeTail (S : Finset ℕ) (q : ℕ) :
    liliuRoughSurvivorSet S q = liliuPrimeSurvivorSet S q ∪ liliuPn1RoughCompositeTail S q := by
  ext u
  simp only [mem_union, liliuRoughSurvivorSet, liliuPrimeSurvivorSet, liliuPn1RoughCompositeTail, mem_filter]
  constructor
  · intro hu
    cases Classical.em (IsPrimeNat u) with
    | inl h_isp => exact Or.inl ⟨hu.1, hu.2.1, hu.2.2, h_isp⟩
    | inr h_comp => exact Or.inr ⟨hu.1, hu.2.1, hu.2.2, h_comp⟩
  · intro hor
    cases hor with
    | inl hp => exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
    | inr hc => exact ⟨hc.1, hc.2.1, hc.2.2.1⟩

theorem liliuRoughSurvivorSet_card_eq_primeSurvivors_add_compositeTail (S : Finset ℕ) (q : ℕ) :
    (liliuRoughSurvivorSet S q).card =
      (liliuPrimeSurvivorSet S q).card + (liliuPn1RoughCompositeTail S q).card := by
  conv_lhs => rw [liliuRoughSurvivorSet_eq_primeSurvivors_union_compositeTail S q]
  exact card_union_of_disjoint (disjoint_liliuPrimeSurvivorSet_compositeTail S q)

/-!
## Section 2: Global Multi-Block `√(2M)` Upper Bound & Master 55-Module Capstone
-/

theorem liliuPn1RoughCompositeTail_eq_biUnion_subTwoQBlocks (I : Finset ℕ) (q : ℕ) :
    liliuPn1RoughCompositeTail I q =
      (liliuSubTwoQBlockIndices I q).biUnion (fun k : ℕ =>
        liliuPn1RoughCompositeTail (liliuSubTwoQBlock I q k) q) := by
  ext u
  rw [mem_biUnion]
  constructor
  · intro hu
    rw [liliuPn1RoughCompositeTail, mem_filter] at hu
    refine ⟨u / (2 * max q 1), ?_, ?_⟩
    · rw [liliuSubTwoQBlockIndices, mem_image]
      exact ⟨u, hu.1, rfl⟩
    · rw [liliuPn1RoughCompositeTail, mem_filter, liliuSubTwoQBlock, mem_filter]
      exact ⟨⟨hu.1, rfl⟩, hu.2⟩
  · intro hbi
    obtain ⟨k, _, hu_blk⟩ := hbi
    rw [liliuPn1RoughCompositeTail, mem_filter, liliuSubTwoQBlock, mem_filter] at hu_blk
    rw [liliuPn1RoughCompositeTail, mem_filter]
    exact ⟨hu_blk.1.1, hu_blk.2⟩

theorem liliuPn1RoughCompositeTail_subTwoQBlock_disjoint_of_ne
    (I : Finset ℕ) (q : ℕ) {k₁ k₂ : ℕ} (hne : k₁ ≠ k₂) :
    Disjoint (liliuPn1RoughCompositeTail (liliuSubTwoQBlock I q k₁) q)
             (liliuPn1RoughCompositeTail (liliuSubTwoQBlock I q k₂) q) := by
  apply Finset.disjoint_left.mpr
  intro u hu1 hu2
  rw [liliuPn1RoughCompositeTail, mem_filter, liliuSubTwoQBlock, mem_filter] at hu1 hu2
  have hk1 : u / (2 * max q 1) = k₁ := hu1.1.2
  have hk2 : u / (2 * max q 1) = k₂ := hu2.1.2
  omega

/-- **Theorem 2.1 (`liliuFullLowerMURUpper_roughCompositeTail_card_le_blocks_mul_sqrtOwners`):**
    Global Multi-Block `√(2M)` Upper Bound (`Step208` + `Step209`) on Track 2:
    For ALL `M, q : ℕ`,
    `(liliuPn1RoughCompositeTail (liliuFullLowerMURUpper M) q).card ≤ (liliuSubTwoQBlockIndices (liliuFullLowerMURUpper M) q).card * (liliuSqrtActiveOwnerPrimes M q).card`. -/
theorem liliuFullLowerMURUpper_roughCompositeTail_card_le_blocks_mul_sqrtOwners (M q : ℕ) :
    (liliuPn1RoughCompositeTail (liliuFullLowerMURUpper M) q).card ≤
      (liliuSubTwoQBlockIndices (liliuFullLowerMURUpper M) q).card *
        (liliuSqrtActiveOwnerPrimes M q).card := by
  have h_disj :
      (↑(liliuSubTwoQBlockIndices (liliuFullLowerMURUpper M) q) : Set ℕ).PairwiseDisjoint
        (fun k : ℕ => liliuPn1RoughCompositeTail (liliuSubTwoQBlock (liliuFullLowerMURUpper M) q k) q) := by
    intro k₁ _ k₂ _ hne
    exact liliuPn1RoughCompositeTail_subTwoQBlock_disjoint_of_ne (liliuFullLowerMURUpper M) q hne
  have h_card_eq :
      (liliuPn1RoughCompositeTail (liliuFullLowerMURUpper M) q).card =
        ∑ k ∈ liliuSubTwoQBlockIndices (liliuFullLowerMURUpper M) q,
          (liliuPn1RoughCompositeTail (liliuSubTwoQBlock (liliuFullLowerMURUpper M) q k) q).card := by
    conv_lhs => rw [liliuPn1RoughCompositeTail_eq_biUnion_subTwoQBlocks (liliuFullLowerMURUpper M) q]
    exact card_biUnion h_disj
  rw [h_card_eq]
  have h_sum_le :
      ∑ k ∈ liliuSubTwoQBlockIndices (liliuFullLowerMURUpper M) q,
          (liliuPn1RoughCompositeTail (liliuSubTwoQBlock (liliuFullLowerMURUpper M) q k) q).card ≤
        ∑ _k ∈ liliuSubTwoQBlockIndices (liliuFullLowerMURUpper M) q,
          (liliuSqrtActiveOwnerPrimes M q).card := by
    apply sum_le_sum
    intro k _
    exact liliuSubTwoQBlock_roughCompositeTail_card_le_sqrtActiveOwnerPrimes M q k
  rw [sum_const, smul_eq_mul] at h_sum_le
  exact h_sum_le

/-- **Theorem 2.2 (`liliuFullLowerMUR_sqrt_margin_to_binary_goldbach`):**
    Unconditional `Step209` Survivor-Margin Goldbach Extractor on Track 2. -/
theorem liliuFullLowerMUR_sqrt_margin_to_binary_goldbach
    {M q : ℕ}
    (h_margin :
      (liliuSubTwoQBlockIndices (liliuFullLowerMURUpper M) q).card *
        (liliuSqrtActiveOwnerPrimes M q).card <
      (liliuRoughSurvivorSet (liliuFullLowerMURUpper M) q).card) :
    0 < (liliuPrimeSurvivorSet (liliuFullLowerMURUpper M) q).card ∧
    ∃ p q' p_next' : ℕ,
      Nat.Prime p ∧ Nat.Prime q' ∧ 2 * M = p + q' ∧
      p < p_next' ∧ IsPrimeNat p_next' := by
  have h_part :=
    liliuRoughSurvivorSet_card_eq_primeSurvivors_add_compositeTail (liliuFullLowerMURUpper M) q
  have h_comp_le :=
    liliuFullLowerMURUpper_roughCompositeTail_card_le_blocks_mul_sqrtOwners M q
  have h_pos : 0 < (liliuPrimeSurvivorSet (liliuFullLowerMURUpper M) q).card := by omega
  refine ⟨h_pos, ?_⟩
  obtain ⟨u, hu⟩ := card_pos.mp h_pos
  rw [liliuPrimeSurvivorSet, mem_filter] at hu
  obtain ⟨hu_full, _, _, hu_isp⟩ := hu
  have h_props := liliuFullLowerMURUpper_mem_props hu_full
  have hp_nat : Nat.Prime (2 * M - u) := isPrimeNat_to_natPrime_liliu h_props.2.2.2.2.1
  have hu_nat : Nat.Prime u := isPrimeNat_to_natPrime_liliu hu_isp
  obtain ⟨p_next', hp_lt, hp_next_isp⟩ :=
    hasNextPrimeConnection_unconditional (2 * M - u)
  exact ⟨2 * M - u, u, p_next', hp_nat, hu_nat, h_props.2.2.2.2.2.symm,
    hp_lt, hp_next_isp⟩

/-- **Master Theorem 3.1 (`master_55module_complete_step208_step209_step212_goldbach_lean_capstone`):**
    Complete 55-Module Master Capstone uniting `Goldbach.one_plus_one_nine_count` (`D19 N`),
    the `Step209` Optimal `M_3 + 1` Zero-Tail Cutoff,
    the `Step208` + `Step209` Global Multi-Block `√(2M)` Upper Bound & Direct Goldbach Extractor,
    and the `Step212` First-Missing-Prime `q_E` Zero-Sum Collapse. -/
theorem master_55module_complete_step208_step209_step212_goldbach_lean_capstone :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (liliuPn1RoughCompositeTail
        (liliuFullLowerMURUpper (max (N / 2) 3))
        (liliuOptimalUpperCutoff (N / 2))).card = 0 ∧
      (∀ q : ℕ,
        (liliuPn1RoughCompositeTail (liliuFullLowerMURUpper (N / 2)) q).card ≤
          (liliuSubTwoQBlockIndices (liliuFullLowerMURUpper (N / 2)) q).card *
            (liliuSqrtActiveOwnerPrimes (N / 2) q).card) ∧
      (∀ q : ℕ,
        (liliuSubTwoQBlockIndices (liliuFullLowerMURUpper (N / 2)) q).card *
          (liliuSqrtActiveOwnerPrimes (N / 2) q).card <
        (liliuRoughSurvivorSet (liliuFullLowerMURUpper (N / 2)) q).card →
          ∃ p q' p_next' : ℕ,
            Nat.Prime p ∧ Nat.Prime q' ∧ 2 * (N / 2) = p + q' ∧
            p < p_next' ∧ IsPrimeNat p_next') ∧
      (∀ q_E : ℕ, IsFirstMissingOddPrimeLiliu N q_E → N < q_E * (q_E + 2) + 2 →
        (∑ r ∈ pinchedOddPrimes919 N, (liliuTargetSieved3PrimeFiber N r q_E).card) = 0 ∧
        (fiveupPinchedQRSubfilter 9 10 N).card ≤ q_E ∧
        (((q_E : ℝ) ≤ liuMainTerm0004 N) →
          ∃ p q p_next' : ℕ,
            Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next' ∧ IsPrimeNat p_next')) := by
  obtain ⟨K, hK4, hCap53⟩ := master_53module_step208_step209_step212_and_goldbach_lean_capstone
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven
  have hM := hCap53 N hNK hEven
  exact ⟨hM.1,
         hM.2.1,
         fun q => liliuFullLowerMURUpper_roughCompositeTail_card_le_blocks_mul_sqrtOwners (N / 2) q,
         fun q h_m => (liliuFullLowerMUR_sqrt_margin_to_binary_goldbach h_m).2,
         hM.2.2.2⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.liliuRoughSurvivorSet_card_eq_primeSurvivors_add_compositeTail
#print axioms WuPaper.ESZerosBridge.liliuFullLowerMURUpper_roughCompositeTail_card_le_blocks_mul_sqrtOwners
#print axioms WuPaper.ESZerosBridge.liliuFullLowerMUR_sqrt_margin_to_binary_goldbach
#print axioms WuPaper.ESZerosBridge.master_55module_complete_step208_step209_step212_goldbach_lean_capstone
