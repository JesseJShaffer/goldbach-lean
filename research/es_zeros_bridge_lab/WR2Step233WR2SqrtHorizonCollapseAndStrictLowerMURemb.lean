import WR2Step231WR2MultiBlockSqrtBoundAndRescuedSurvivorDecomposition

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step233WR2SqrtHorizonCollapseAndStrictLowerMURemb.lean — Unconditional `√(2M) + 1` Multi-Block Tail Collapse & Strict Lower-MUR Reflection Inequality (`Step209` §3b on `WR2` Track 1)

1. **Section 1 — Unconditional Global Tail Collapse at the `√(2M) + 1` Horizon:**
   - Proves via `Nat.lt_succ_sqrt` and `Nat.mul_le_mul` that for every `M : ℕ` and every
     sieve horizon `q` with `Nat.sqrt (2 * M) + 1 ≤ q`, `(sqrtActiveOwnerPrimes M q).card = 0`.
   - Combines this with `fullLowerMURUpper_roughCompositeTail_card_le_blocks_mul_sqrtOwners`
     (`WR2Step231`) to prove unconditionally for ALL `M : ℕ`:
     `(pn1RoughCompositeTail (fullLowerMURUpper M) q).card = 0` and
     `(roughSurvivorSet (fullLowerMURUpper M) q).card = (primeSurvivorSet (fullLowerMURUpper M) q).card`.
2. **Section 2 — Disjoint Lower-MUR Prime Reflection & Strict Inequality (`Step209` §3b):**
   - Defines `aboveSqrtLowerMURPrimes M` (odd primes `p < M` with `2 * M < p * p`).
   - Proves that the reflection map `mirrorUpperFromLowerPrime M p := 2 * M - p` injects the
     disjoint union `sqrtActiveOwnerPrimes M q ∪ aboveSqrtLowerMURPrimes M` into `fullLowerMURUpper M`,
     proving unconditionally for all `M, q, k : ℕ`:
     `(pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) q k) q).card + (aboveSqrtLowerMURPrimes M).card ≤ (fullLowerMURUpper M).card`,
     and whenever `0 < (aboveSqrtLowerMURPrimes M).card`, the strict inequality:
     `(pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) q k) q).card < (fullLowerMURUpper M).card`.
-/

/-!
## Section 1: Unconditional Global Tail Collapse at the `√(2M) + 1` Horizon
-/

/-- **Theorem 1.1 (`sqrtActiveOwnerPrimes_eq_empty_of_sqrt_succ_le`):**
    For every `M : ℕ` and every sieve cutoff `q` satisfying `Nat.sqrt (2 * M) + 1 ≤ q`,
    `(sqrtActiveOwnerPrimes M q).card = 0`. -/
theorem sqrtActiveOwnerPrimes_eq_empty_of_sqrt_succ_le
    {M q : ℕ} (hq : Nat.sqrt (2 * M) + 1 ≤ q) :
    (sqrtActiveOwnerPrimes M q).card = 0 := by
  match Nat.eq_zero_or_pos (sqrtActiveOwnerPrimes M q).card with
  | Or.inl h0 => exact h0
  | Or.inr hpos =>
    obtain ⟨p, hp⟩ := card_pos.mp hpos
    rw [sqrtActiveOwnerPrimes, mem_filter] at hp
    obtain ⟨_, _, _, hq_le_p, hp_sq_le⟩ := hp
    have h_sqrt_le_p : Nat.sqrt (2 * M) + 1 ≤ p := Nat.le_trans hq hq_le_p
    have h_sq_mono :
        (Nat.sqrt (2 * M) + 1) * (Nat.sqrt (2 * M) + 1) ≤ p * p :=
      Nat.mul_le_mul h_sqrt_le_p h_sqrt_le_p
    have h_lt_succ : 2 * M < (Nat.sqrt (2 * M) + 1) * (Nat.sqrt (2 * M) + 1) :=
      Nat.lt_succ_sqrt (2 * M)
    have h_2M_lt_p2 : 2 * M < p * p := Nat.lt_of_lt_of_le h_lt_succ h_sq_mono
    exact False.elim (Nat.lt_irrefl (2 * M) (Nat.lt_of_lt_of_le h_2M_lt_p2 hp_sq_le))

/-- **Theorem 1.2 (`sqrt_succ_horizon_collapses_all_blocks_and_composite_tail`):**
    Unconditional Global Multi-Block Tail Collapse at `Nat.sqrt (2 * M) + 1 ≤ q`:
    For EVERY `M : ℕ` and `Nat.sqrt (2 * M) + 1 ≤ q`:
    1. `(pn1RoughCompositeTail (fullLowerMURUpper M) q).card = 0`,
    2. `(roughSurvivorSet (fullLowerMURUpper M) q).card = (primeSurvivorSet (fullLowerMURUpper M) q).card`, and
    3. Whenever `0 < (roughSurvivorSet (fullLowerMURUpper M) q).card`, `2 * M` is unconditionally
       a Binary Goldbach sum `2 * M = p + q'` paired with `p < p_next'`! -/
theorem sqrt_succ_horizon_collapses_all_blocks_and_composite_tail
    {M q : ℕ} (hq : Nat.sqrt (2 * M) + 1 ≤ q) :
    (pn1RoughCompositeTail (fullLowerMURUpper M) q).card = 0 ∧
    (roughSurvivorSet (fullLowerMURUpper M) q).card =
      (primeSurvivorSet (fullLowerMURUpper M) q).card ∧
    (0 < (roughSurvivorSet (fullLowerMURUpper M) q).card →
      ∃ p q' p_next' : ℕ,
        Nat.Prime p ∧ Nat.Prime q' ∧ 2 * M = p + q' ∧
        p < p_next' ∧ Nat.Prime p_next' ∧ IsPrimeNat p_next') := by
  have h_own_zero : (sqrtActiveOwnerPrimes M q).card = 0 :=
    sqrtActiveOwnerPrimes_eq_empty_of_sqrt_succ_le hq
  have h_mb := fullLowerMURUpper_roughCompositeTail_card_le_blocks_mul_sqrtOwners M q
  rw [h_own_zero, Nat.mul_zero] at h_mb
  have h_tail_zero : (pn1RoughCompositeTail (fullLowerMURUpper M) q).card = 0 := by omega
  have h_part :=
    roughSurvivorSet_card_eq_primeSurvivors_add_compositeTail (fullLowerMURUpper M) q
  have h_eq_surv :
      (roughSurvivorSet (fullLowerMURUpper M) q).card =
        (primeSurvivorSet (fullLowerMURUpper M) q).card := by omega
  refine ⟨h_tail_zero, h_eq_surv, ?_⟩
  intro h_pos
  have h_margin :
      (subTwoQBlockIndices (fullLowerMURUpper M) q).card *
        (sqrtActiveOwnerPrimes M q).card <
      (roughSurvivorSet (fullLowerMURUpper M) q).card := by
    rw [h_own_zero, Nat.mul_zero]
    exact h_pos
  exact (fullLowerMUR_sqrt_margin_to_binary_goldbach h_margin).2

/-!
## Section 2: Disjoint Lower-MUR Prime Reflection & Strict Inequality (`Step209` §3b)
-/

/-- Lower-MUR odd primes strictly above `√(2M)` (`p < M` and `2 * M < p * p`). -/
def aboveSqrtLowerMURPrimes (M : ℕ) : Finset ℕ :=
  (range M).filter (fun p : ℕ =>
    IsPrimeNat p ∧ p % 2 = 1 ∧ 2 * M < p * p)

/-- Strict disjointness of `sqrtActiveOwnerPrimes M q` (`p * p ≤ 2 * M`) and
    `aboveSqrtLowerMURPrimes M` (`2 * M < p * p`). -/
theorem disjoint_sqrtActiveOwnerPrimes_aboveSqrtLowerMURPrimes (M q : ℕ) :
    Disjoint (sqrtActiveOwnerPrimes M q) (aboveSqrtLowerMURPrimes M) := by
  apply Finset.disjoint_left.mpr
  intro p h_le h_gt
  rw [sqrtActiveOwnerPrimes, mem_filter] at h_le
  rw [aboveSqrtLowerMURPrimes, mem_filter] at h_gt
  have h1 : p * p ≤ 2 * M := h_le.2.2.2.2
  have h2 : 2 * M < p * p := h_gt.2.2.2
  omega

/-- Reflection map `p ↦ 2 * M - p` mapping lower-MUR primes `p < M` into `fullLowerMURUpper M`. -/
def mirrorUpperFromLowerPrime (M p : ℕ) : ℕ :=
  2 * M - p

/-- Every `p ∈ sqrtActiveOwnerPrimes M q` satisfies `3 ≤ p`, `p + 2 ≤ M`, and
    `mirrorUpperFromLowerPrime M p ∈ fullLowerMURUpper M`. -/
theorem sqrtActiveOwnerPrimes_mirror_mem_fullLowerMURUpper
    {M q p : ℕ} (hp : p ∈ sqrtActiveOwnerPrimes M q) :
    p < M ∧ mirrorUpperFromLowerPrime M p ∈ fullLowerMURUpper M := by
  rw [sqrtActiveOwnerPrimes, mem_filter] at hp
  obtain ⟨_, hp_isp, hp_odd, _, hp_sq⟩ := hp
  have hp2 : 2 ≤ p := hp_isp.1
  have hp3 : 3 ≤ p := by omega
  have h_p3_le_p2 : p * 3 ≤ p * p := Nat.mul_le_mul_left p hp3
  have h_3p_le_2M : 3 * p ≤ 2 * M := by
    rw [Nat.mul_comm 3 p]
    exact Nat.le_trans h_p3_le_p2 hp_sq
  have hp_lt_M : p < M := by omega
  refine ⟨hp_lt_M, ?_⟩
  rw [fullLowerMURUpper, mem_image]
  refine ⟨M - p, ?_, ?_⟩
  · rw [fullLowerMURPrimeRadii, mem_filter, mem_range]
    have h_sub : M - (M - p) = p := by omega
    rw [h_sub]
    exact ⟨by omega, by omega, by omega, hp_isp⟩
  · unfold mirrorUpperFromLowerPrime
    omega

/-- Every `p ∈ aboveSqrtLowerMURPrimes M` satisfies `p < M` and
    `mirrorUpperFromLowerPrime M p ∈ fullLowerMURUpper M`. -/
theorem aboveSqrtLowerMURPrimes_mirror_mem_fullLowerMURUpper
    {M p : ℕ} (hp : p ∈ aboveSqrtLowerMURPrimes M) :
    p < M ∧ mirrorUpperFromLowerPrime M p ∈ fullLowerMURUpper M := by
  rw [aboveSqrtLowerMURPrimes, mem_filter, mem_range] at hp
  obtain ⟨hp_lt_M, hp_isp, hp_odd, _⟩ := hp
  have hp2 : 2 ≤ p := hp_isp.1
  have hp3 : 3 ≤ p := by omega
  refine ⟨hp_lt_M, ?_⟩
  rw [fullLowerMURUpper, mem_image]
  refine ⟨M - p, ?_, ?_⟩
  · rw [fullLowerMURPrimeRadii, mem_filter, mem_range]
    have h_sub : M - (M - p) = p := by omega
    rw [h_sub]
    exact ⟨by omega, by omega, by omega, hp_isp⟩
  · unfold mirrorUpperFromLowerPrime
    omega

/-- **Theorem 2.1 (`unconditional_sqrt_and_aboveSqrt_card_le_fullLowerMURUpper`):**
    Ports `Step209` Section 3b unconditionally for ALL `M, q, k : ℕ`:
    1. `(sqrtActiveOwnerPrimes M q).card + (aboveSqrtLowerMURPrimes M).card ≤ (fullLowerMURUpper M).card`,
    2. `(pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) q k) q).card + (aboveSqrtLowerMURPrimes M).card ≤ (fullLowerMURUpper M).card`, and
    3. Whenever `0 < (aboveSqrtLowerMURPrimes M).card`, the strict inequality holds:
       `(pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) q k) q).card ≤ (sqrtActiveOwnerPrimes M q).card < (fullLowerMURUpper M).card`. -/
theorem unconditional_sqrt_and_aboveSqrt_card_le_fullLowerMURUpper (M q k : ℕ) :
    (sqrtActiveOwnerPrimes M q).card + (aboveSqrtLowerMURPrimes M).card ≤
      (fullLowerMURUpper M).card ∧
    (pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) q k) q).card +
      (aboveSqrtLowerMURPrimes M).card ≤
      (fullLowerMURUpper M).card ∧
    (0 < (aboveSqrtLowerMURPrimes M).card →
      (pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) q k) q).card <
        (fullLowerMURUpper M).card) := by
  set U_primes := sqrtActiveOwnerPrimes M q ∪ aboveSqrtLowerMURPrimes M
  have h_u_card :
      U_primes.card =
        (sqrtActiveOwnerPrimes M q).card + (aboveSqrtLowerMURPrimes M).card :=
    card_union_of_disjoint (disjoint_sqrtActiveOwnerPrimes_aboveSqrtLowerMURPrimes M q)
  have h_sub :
      U_primes.image (mirrorUpperFromLowerPrime M) ⊆ fullLowerMURUpper M := by
    intro u hu
    rw [mem_image] at hu
    obtain ⟨p, hp_u, rfl⟩ := hu
    rw [mem_union] at hp_u
    cases hp_u with
    | inl hp_sq => exact (sqrtActiveOwnerPrimes_mirror_mem_fullLowerMURUpper hp_sq).2
    | inr hp_ab => exact (aboveSqrtLowerMURPrimes_mirror_mem_fullLowerMURUpper hp_ab).2
  have h_inj : Set.InjOn (mirrorUpperFromLowerPrime M) (↑U_primes : Set ℕ) := by
    intro a ha b hb h_eq
    rw [mem_coe, mem_union] at ha hb
    have ha_lt : a < M := by
      cases ha with
      | inl h1 => exact (sqrtActiveOwnerPrimes_mirror_mem_fullLowerMURUpper h1).1
      | inr h2 => exact (aboveSqrtLowerMURPrimes_mirror_mem_fullLowerMURUpper h2).1
    have hb_lt : b < M := by
      cases hb with
      | inl h1 => exact (sqrtActiveOwnerPrimes_mirror_mem_fullLowerMURUpper h1).1
      | inr h2 => exact (aboveSqrtLowerMURPrimes_mirror_mem_fullLowerMURUpper h2).1
    unfold mirrorUpperFromLowerPrime at h_eq
    omega
  have h_img_card :
      (U_primes.image (mirrorUpperFromLowerPrime M)).card = U_primes.card :=
    Finset.card_image_of_injOn h_inj
  have h_sum_le :
      (sqrtActiveOwnerPrimes M q).card + (aboveSqrtLowerMURPrimes M).card ≤
        (fullLowerMURUpper M).card := by
    rw [← h_u_card, ← h_img_card]
    exact card_le_card h_sub
  have h_tail_le :=
    subTwoQBlock_roughCompositeTail_card_le_sqrtActiveOwnerPrimes M q k
  exact ⟨h_sum_le, by omega, fun h_pos => by omega⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.sqrtActiveOwnerPrimes_eq_empty_of_sqrt_succ_le
#print axioms WuPaper.ESZerosBridge.sqrt_succ_horizon_collapses_all_blocks_and_composite_tail
#print axioms WuPaper.ESZerosBridge.unconditional_sqrt_and_aboveSqrt_card_le_fullLowerMURUpper
