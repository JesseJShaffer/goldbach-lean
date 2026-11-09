import WR2Step232LiLiuMultiBlockSqrtBoundAnd55ModuleCapstone

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step234LiLiuSqrtHorizonCollapseAnd57ModuleCapstone.lean — Unconditional `√(2M) + 1` Multi-Block Tail Collapse, Strict Lower-MUR Reflection Inequality (`Step209` §3b) & Master 57-Module `D19 N` Capstone

Completes the 57-Module `goldbach-lean` x `ES_Zeros` verification suite by welding:
1. Unconditional Global Multi-Block Tail Collapse at `Nat.sqrt (2 * M) + 1 ≤ q`
   (`liliu_sqrt_succ_horizon_collapses_all_blocks_and_composite_tail`), and
2. Disjoint Lower-MUR Prime Reflection & Strict Inequality (`Step209` §3b —
   `liliu_unconditional_sqrt_and_aboveSqrt_card_le_fullLowerMURUpper`)
into the 57-Module `Goldbach.All` (`D19 N`) Master Capstone.
-/

/-!
## Section 1: Unconditional Global Tail Collapse at the `√(2M) + 1` Horizon
-/

theorem liliuSqrtActiveOwnerPrimes_eq_empty_of_sqrt_succ_le
    {M q : ℕ} (hq : Nat.sqrt (2 * M) + 1 ≤ q) :
    (liliuSqrtActiveOwnerPrimes M q).card = 0 := by
  match Nat.eq_zero_or_pos (liliuSqrtActiveOwnerPrimes M q).card with
  | Or.inl h0 => exact h0
  | Or.inr hpos =>
    obtain ⟨p, hp⟩ := card_pos.mp hpos
    rw [liliuSqrtActiveOwnerPrimes, mem_filter] at hp
    obtain ⟨_, _, _, hq_le_p, hp_sq_le⟩ := hp
    have h_sqrt_le_p : Nat.sqrt (2 * M) + 1 ≤ p := Nat.le_trans hq hq_le_p
    have h_sq_mono :
        (Nat.sqrt (2 * M) + 1) * (Nat.sqrt (2 * M) + 1) ≤ p * p :=
      Nat.mul_le_mul h_sqrt_le_p h_sqrt_le_p
    have h_lt_succ : 2 * M < (Nat.sqrt (2 * M) + 1) * (Nat.sqrt (2 * M) + 1) :=
      Nat.lt_succ_sqrt (2 * M)
    have h_2M_lt_p2 : 2 * M < p * p := Nat.lt_of_lt_of_le h_lt_succ h_sq_mono
    exact False.elim (Nat.lt_irrefl (2 * M) (Nat.lt_of_lt_of_le h_2M_lt_p2 hp_sq_le))

/-- **Theorem 1.1 (`liliu_sqrt_succ_horizon_collapses_all_blocks_and_composite_tail`):**
    Unconditional Global Multi-Block Tail Collapse at `Nat.sqrt (2 * M) + 1 ≤ q` on Track 2. -/
theorem liliu_sqrt_succ_horizon_collapses_all_blocks_and_composite_tail
    {M q : ℕ} (hq : Nat.sqrt (2 * M) + 1 ≤ q) :
    (liliuPn1RoughCompositeTail (liliuFullLowerMURUpper M) q).card = 0 ∧
    (liliuRoughSurvivorSet (liliuFullLowerMURUpper M) q).card =
      (liliuPrimeSurvivorSet (liliuFullLowerMURUpper M) q).card ∧
    (0 < (liliuRoughSurvivorSet (liliuFullLowerMURUpper M) q).card →
      ∃ p q' p_next' : ℕ,
        Nat.Prime p ∧ Nat.Prime q' ∧ 2 * M = p + q' ∧
        p < p_next' ∧ IsPrimeNat p_next') := by
  have h_own_zero : (liliuSqrtActiveOwnerPrimes M q).card = 0 :=
    liliuSqrtActiveOwnerPrimes_eq_empty_of_sqrt_succ_le hq
  have h_mb := liliuFullLowerMURUpper_roughCompositeTail_card_le_blocks_mul_sqrtOwners M q
  rw [h_own_zero, Nat.mul_zero] at h_mb
  have h_tail_zero : (liliuPn1RoughCompositeTail (liliuFullLowerMURUpper M) q).card = 0 := by omega
  have h_part :=
    liliuRoughSurvivorSet_card_eq_primeSurvivors_add_compositeTail (liliuFullLowerMURUpper M) q
  have h_eq_surv :
      (liliuRoughSurvivorSet (liliuFullLowerMURUpper M) q).card =
        (liliuPrimeSurvivorSet (liliuFullLowerMURUpper M) q).card := by omega
  refine ⟨h_tail_zero, h_eq_surv, ?_⟩
  intro h_pos
  have h_margin :
      (liliuSubTwoQBlockIndices (liliuFullLowerMURUpper M) q).card *
        (liliuSqrtActiveOwnerPrimes M q).card <
      (liliuRoughSurvivorSet (liliuFullLowerMURUpper M) q).card := by
    rw [h_own_zero, Nat.mul_zero]
    exact h_pos
  exact (liliuFullLowerMUR_sqrt_margin_to_binary_goldbach h_margin).2

/-!
## Section 2: Disjoint Lower-MUR Prime Reflection & Strict Inequality (`Step209` §3b)
-/

def liliuAboveSqrtLowerMURPrimes (M : ℕ) : Finset ℕ :=
  (range M).filter (fun p : ℕ =>
    IsPrimeNat p ∧ p % 2 = 1 ∧ 2 * M < p * p)

theorem disjoint_liliuSqrtActiveOwnerPrimes_aboveSqrt (M q : ℕ) :
    Disjoint (liliuSqrtActiveOwnerPrimes M q) (liliuAboveSqrtLowerMURPrimes M) := by
  apply Finset.disjoint_left.mpr
  intro p h_le h_gt
  rw [liliuSqrtActiveOwnerPrimes, mem_filter] at h_le
  rw [liliuAboveSqrtLowerMURPrimes, mem_filter] at h_gt
  have h1 : p * p ≤ 2 * M := h_le.2.2.2.2
  have h2 : 2 * M < p * p := h_gt.2.2.2
  omega

def liliuMirrorUpperFromLowerPrime (M p : ℕ) : ℕ :=
  2 * M - p

theorem liliuSqrtActiveOwnerPrimes_mirror_mem_fullLowerMURUpper
    {M q p : ℕ} (hp : p ∈ liliuSqrtActiveOwnerPrimes M q) :
    p < M ∧ liliuMirrorUpperFromLowerPrime M p ∈ liliuFullLowerMURUpper M := by
  rw [liliuSqrtActiveOwnerPrimes, mem_filter] at hp
  obtain ⟨_, hp_isp, hp_odd, _, hp_sq⟩ := hp
  have hp2 : 2 ≤ p := hp_isp.1
  have hp3 : 3 ≤ p := by omega
  have h_p3_le_p2 : p * 3 ≤ p * p := Nat.mul_le_mul_left p hp3
  have h_3p_le_2M : 3 * p ≤ 2 * M := by
    rw [Nat.mul_comm 3 p]
    exact Nat.le_trans h_p3_le_p2 hp_sq
  have hp_lt_M : p < M := by omega
  refine ⟨hp_lt_M, ?_⟩
  rw [liliuFullLowerMURUpper, mem_image]
  refine ⟨M - p, ?_, ?_⟩
  · rw [liliuFullLowerMURPrimeRadii, mem_filter, mem_range]
    have h_sub : M - (M - p) = p := by omega
    rw [h_sub]
    exact ⟨by omega, by omega, by omega, hp_isp⟩
  · unfold liliuMirrorUpperFromLowerPrime
    omega

theorem liliuAboveSqrtLowerMURPrimes_mirror_mem_fullLowerMURUpper
    {M p : ℕ} (hp : p ∈ liliuAboveSqrtLowerMURPrimes M) :
    p < M ∧ liliuMirrorUpperFromLowerPrime M p ∈ liliuFullLowerMURUpper M := by
  rw [liliuAboveSqrtLowerMURPrimes, mem_filter, mem_range] at hp
  obtain ⟨hp_lt_M, hp_isp, hp_odd, _⟩ := hp
  have hp2 : 2 ≤ p := hp_isp.1
  have hp3 : 3 ≤ p := by omega
  refine ⟨hp_lt_M, ?_⟩
  rw [liliuFullLowerMURUpper, mem_image]
  refine ⟨M - p, ?_, ?_⟩
  · rw [liliuFullLowerMURPrimeRadii, mem_filter, mem_range]
    have h_sub : M - (M - p) = p := by omega
    rw [h_sub]
    exact ⟨by omega, by omega, by omega, hp_isp⟩
  · unfold liliuMirrorUpperFromLowerPrime
    omega

/-- **Theorem 2.1 (`liliu_unconditional_sqrt_and_aboveSqrt_card_le_fullLowerMURUpper`):**
    Unconditional `Step209` Section 3b Lower-MUR Reflection & Strict Inequality on Track 2. -/
theorem liliu_unconditional_sqrt_and_aboveSqrt_card_le_fullLowerMURUpper (M q k : ℕ) :
    (liliuSqrtActiveOwnerPrimes M q).card + (liliuAboveSqrtLowerMURPrimes M).card ≤
      (liliuFullLowerMURUpper M).card ∧
    (liliuPn1RoughCompositeTail (liliuSubTwoQBlock (liliuFullLowerMURUpper M) q k) q).card +
      (liliuAboveSqrtLowerMURPrimes M).card ≤
      (liliuFullLowerMURUpper M).card ∧
    (0 < (liliuAboveSqrtLowerMURPrimes M).card →
      (liliuPn1RoughCompositeTail (liliuSubTwoQBlock (liliuFullLowerMURUpper M) q k) q).card <
        (liliuFullLowerMURUpper M).card) := by
  set U_primes := liliuSqrtActiveOwnerPrimes M q ∪ liliuAboveSqrtLowerMURPrimes M
  have h_u_card :
      U_primes.card =
        (liliuSqrtActiveOwnerPrimes M q).card + (liliuAboveSqrtLowerMURPrimes M).card :=
    card_union_of_disjoint (disjoint_liliuSqrtActiveOwnerPrimes_aboveSqrt M q)
  have h_sub :
      U_primes.image (liliuMirrorUpperFromLowerPrime M) ⊆ liliuFullLowerMURUpper M := by
    intro u hu
    rw [mem_image] at hu
    obtain ⟨p, hp_u, rfl⟩ := hu
    rw [mem_union] at hp_u
    cases hp_u with
    | inl hp_sq => exact (liliuSqrtActiveOwnerPrimes_mirror_mem_fullLowerMURUpper hp_sq).2
    | inr hp_ab => exact (liliuAboveSqrtLowerMURPrimes_mirror_mem_fullLowerMURUpper hp_ab).2
  have h_inj : Set.InjOn (liliuMirrorUpperFromLowerPrime M) (↑U_primes : Set ℕ) := by
    intro a ha b hb h_eq
    rw [mem_coe, mem_union] at ha hb
    have ha_lt : a < M := by
      cases ha with
      | inl h1 => exact (liliuSqrtActiveOwnerPrimes_mirror_mem_fullLowerMURUpper h1).1
      | inr h2 => exact (liliuAboveSqrtLowerMURPrimes_mirror_mem_fullLowerMURUpper h2).1
    have hb_lt : b < M := by
      cases hb with
      | inl h1 => exact (liliuSqrtActiveOwnerPrimes_mirror_mem_fullLowerMURUpper h1).1
      | inr h2 => exact (liliuAboveSqrtLowerMURPrimes_mirror_mem_fullLowerMURUpper h2).1
    unfold liliuMirrorUpperFromLowerPrime at h_eq
    omega
  have h_img_card :
      (U_primes.image (liliuMirrorUpperFromLowerPrime M)).card = U_primes.card :=
    Finset.card_image_of_injOn h_inj
  have h_sum_le :
      (liliuSqrtActiveOwnerPrimes M q).card + (liliuAboveSqrtLowerMURPrimes M).card ≤
        (liliuFullLowerMURUpper M).card := by
    rw [← h_u_card, ← h_img_card]
    exact card_le_card h_sub
  have h_tail_le :=
    liliuSubTwoQBlock_roughCompositeTail_card_le_sqrtActiveOwnerPrimes M q k
  exact ⟨h_sum_le, by omega, fun h_pos => by omega⟩

/-- **Master Theorem 3.1 (`master_57module_complete_sqrt_horizon_and_step209_goldbach_lean_capstone`):**
    Complete 57-Module Master Capstone uniting `Goldbach.one_plus_one_nine_count` (`D19 N`),
    the Unconditional `√(2M) + 1` Multi-Block Composite-Tail Collapse,
    the `Step209` Section 3b Disjoint Lower-MUR Reflection & Strict Inequality,
    and the `Step212` First-Missing-Prime `q_E` Zero-Sum Collapse. -/
theorem master_57module_complete_sqrt_horizon_and_step209_goldbach_lean_capstone :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (∀ q : ℕ, Nat.sqrt (2 * (N / 2)) + 1 ≤ q →
        (liliuPn1RoughCompositeTail (liliuFullLowerMURUpper (N / 2)) q).card = 0 ∧
        (liliuRoughSurvivorSet (liliuFullLowerMURUpper (N / 2)) q).card =
          (liliuPrimeSurvivorSet (liliuFullLowerMURUpper (N / 2)) q).card) ∧
      (∀ q k : ℕ,
        (liliuPn1RoughCompositeTail
          (liliuSubTwoQBlock (liliuFullLowerMURUpper (N / 2)) q k) q).card +
          (liliuAboveSqrtLowerMURPrimes (N / 2)).card ≤
          (liliuFullLowerMURUpper (N / 2)).card) ∧
      (∀ q_E : ℕ, IsFirstMissingOddPrimeLiliu N q_E → N < q_E * (q_E + 2) + 2 →
        (∑ r ∈ pinchedOddPrimes919 N, (liliuTargetSieved3PrimeFiber N r q_E).card) = 0 ∧
        (fiveupPinchedQRSubfilter 9 10 N).card ≤ q_E ∧
        (((q_E : ℝ) ≤ liuMainTerm0004 N) →
          ∃ p q p_next' : ℕ,
            Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next' ∧ IsPrimeNat p_next')) := by
  obtain ⟨K, hK4, hCap55⟩ := master_55module_complete_step208_step209_step212_goldbach_lean_capstone
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven
  have hM := hCap55 N hNK hEven
  refine ⟨hM.1, ?_, ?_, hM.2.2.2.2⟩
  · intro q hq
    have h_col := liliu_sqrt_succ_horizon_collapses_all_blocks_and_composite_tail hq
    exact ⟨h_col.1, h_col.2.1⟩
  · intro q k
    exact (liliu_unconditional_sqrt_and_aboveSqrt_card_le_fullLowerMURUpper (N / 2) q k).2.1

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.liliuSqrtActiveOwnerPrimes_eq_empty_of_sqrt_succ_le
#print axioms WuPaper.ESZerosBridge.liliu_sqrt_succ_horizon_collapses_all_blocks_and_composite_tail
#print axioms WuPaper.ESZerosBridge.liliu_unconditional_sqrt_and_aboveSqrt_card_le_fullLowerMURUpper
#print axioms WuPaper.ESZerosBridge.master_57module_complete_sqrt_horizon_and_step209_goldbach_lean_capstone
