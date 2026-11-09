import WR2Step219WR2OuterPinchedPrimeBiUnionProductBound

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step221WR2ExactSpeciesLowTargetPartitionAndFullFiberBound.lean — Disjoint Low-Target Boundary Partition & Full Unsplit Fiber Contraction

Partitions the full unsplit fiber `wr2FloorSubfiber N r L` at any sieve level `m_sieve` into:
- `wr2LowTargetBoundarySubfiber N r m_sieve L` (`N - r * q ≤ m_sieve`), and
- `wr2TargetSievedFloorSubfiber N r m_sieve L` (`m_sieve < N - r * q`),
with explicit membership equivalences, native `Ω`-species connections (`nativeOmegaCofactorSpecies r = 2`),
and constructive target-prime division `(N - p) / r = q`.
-/

/-!
## Section 1: Pure Native Multiplicative-Division Cancellation (`(r * q) / r = q`)
-/

/-- Pure native proof of `(r * q) / r = q` for `0 < r`, connected directly to
    `le_div_of_mul_le_native` (`WR2Step197`) and `le_of_mul_le_mul_left_pos_wr2` (`WR2Step201`). -/
theorem mul_div_cancel_left_native {r q : ℕ} (hr_pos : 0 < r) :
    (r * q) / r = q := by
  have h_ge : q ≤ (r * q) / r := le_div_of_mul_le_native hr_pos (Nat.le_refl (r * q))
  have h_div_mod : r * ((r * q) / r) + (r * q) % r = r * q := Nat.div_add_mod (r * q) r
  have h_mul_le : r * ((r * q) / r) ≤ r * q := by omega
  have h_le : (r * q) / r ≤ q := le_of_mul_le_mul_left_pos_wr2 hr_pos h_mul_le
  exact Nat.le_antisymm h_le h_ge

/-!
## Section 2: Explicit Sub-Fiber Membership Equivalences & Disjoint Partition
-/

/-- The low-target boundary sub-fiber `{q ∈ wr2FloorSubfiber N r L | N - r * q ≤ m_sieve}`. -/
def wr2LowTargetBoundarySubfiber (N r m_sieve L : ℕ) : Finset ℕ :=
  (wr2FloorSubfiber N r L).filter (fun q : ℕ => N - r * q ≤ m_sieve)

/-- Explicit membership equivalence for `wr2FloorSubfiber N r L`. -/
theorem mem_wr2FloorSubfiber_iff {N r L q : ℕ} :
    q ∈ wr2FloorSubfiber N r L ↔ q ∈ wr2ShearContractedFiber N r ∧ L ≤ q := by
  rw [wr2FloorSubfiber, mem_filter]

/-- Explicit membership equivalence for `wr2LowTargetBoundarySubfiber N r m_sieve L`. -/
theorem mem_wr2LowTargetBoundarySubfiber_iff {N r m_sieve L q : ℕ} :
    q ∈ wr2LowTargetBoundarySubfiber N r m_sieve L ↔
      (q ∈ wr2ShearContractedFiber N r ∧ L ≤ q) ∧ N - r * q ≤ m_sieve := by
  rw [wr2LowTargetBoundarySubfiber, mem_filter, mem_wr2FloorSubfiber_iff]

/-- Explicit membership equivalence for `wr2TargetSievedFloorSubfiber N r m_sieve L`. -/
theorem mem_wr2TargetSievedFloorSubfiber_iff {N r m_sieve L q : ℕ} :
    q ∈ wr2TargetSievedFloorSubfiber N r m_sieve L ↔
      (q ∈ wr2ShearContractedFiber N r ∧ m_sieve < N - r * q) ∧ L ≤ q := by
  rw [wr2TargetSievedFloorSubfiber, mem_filter, wr2TargetSievedFiber, mem_filter]

/-- Strict disjointness of `wr2LowTargetBoundarySubfiber` and `wr2TargetSievedFloorSubfiber`. -/
theorem disjoint_wr2LowTarget_targetSievedFloor (N r m_sieve L : ℕ) :
    Disjoint (wr2LowTargetBoundarySubfiber N r m_sieve L)
             (wr2TargetSievedFloorSubfiber N r m_sieve L) := by
  rw [Finset.disjoint_left]
  intro q hlow hts
  rw [mem_wr2LowTargetBoundarySubfiber_iff] at hlow
  rw [mem_wr2TargetSievedFloorSubfiber_iff] at hts
  have h1 : N - r * q ≤ m_sieve := hlow.2
  have h2 : m_sieve < N - r * q := hts.1.2
  omega

/-- Exact union identity partitioning `wr2FloorSubfiber N r L` at `m_sieve`. -/
theorem wr2FloorSubfiber_eq_lowTarget_union_targetSieved (N r m_sieve L : ℕ) :
    wr2FloorSubfiber N r L =
      wr2LowTargetBoundarySubfiber N r m_sieve L ∪
      wr2TargetSievedFloorSubfiber N r m_sieve L := by
  ext q
  rw [mem_union, mem_wr2FloorSubfiber_iff,
      mem_wr2LowTargetBoundarySubfiber_iff,
      mem_wr2TargetSievedFloorSubfiber_iff]
  constructor
  · intro hq
    match Nat.lt_or_ge m_sieve (N - r * q) with
    | Or.inl hgt => exact Or.inr ⟨⟨hq.1, hgt⟩, hq.2⟩
    | Or.inr hle => exact Or.inl ⟨hq, hle⟩
  · intro hor
    cases hor with
    | inl hlow => exact hlow.1
    | inr hts => exact ⟨hts.1.1, hts.2⟩

/-- **Theorem 2.1 (`wr2FloorSubfiber_card_eq_lowTarget_add_targetSieved`):**
    Exact additive decomposition of `wr2FloorSubfiber N r L` across any sieve horizon `m_sieve`. -/
theorem wr2FloorSubfiber_card_eq_lowTarget_add_targetSieved (N r m_sieve L : ℕ) :
    (wr2FloorSubfiber N r L).card =
      (wr2LowTargetBoundarySubfiber N r m_sieve L).card +
      (wr2TargetSievedFloorSubfiber N r m_sieve L).card := by
  conv_lhs => rw [wr2FloorSubfiber_eq_lowTarget_union_targetSieved N r m_sieve L]
  exact card_union_of_disjoint (disjoint_wr2LowTarget_targetSievedFloor N r m_sieve L)

/-- **Theorem 2.2 (`wr2FloorSubfiber_exact_species_and_next_prime`):**
    Explicitly connects every `q ∈ wr2FloorSubfiber N r L` (with `IsPrimeNat r`) to
    `nativeOmegaCofactorSpecies r = 2` (`WR2Step194`), `IsPrimeNat q`, `IsPrimeNat (N - r * q)`,
    `hasNextPrimeConnection_unconditional`, and the exact binary dichotomy between
    `wr2LowTargetBoundarySubfiber` and `wr2TargetSievedFloorSubfiber`. -/
theorem wr2FloorSubfiber_exact_species_and_next_prime
    {N r m_sieve L q : ℕ} (hr : IsPrimeNat r) (hq : q ∈ wr2FloorSubfiber N r L) :
    nativeOmegaCofactorSpecies r = 2 ∧
    IsPrimeNat q ∧
    IsPrimeNat (N - r * q) ∧
    (q ∈ wr2LowTargetBoundarySubfiber N r m_sieve L ∨
     q ∈ wr2TargetSievedFloorSubfiber N r m_sieve L) ∧
    (∃ q_next : ℕ, q < q_next ∧ IsPrimeNat q_next) ∧
    (∃ p_next : ℕ, (N - r * q) < p_next ∧ IsPrimeNat p_next) := by
  have h_om : nativeOmegaCofactorSpecies r = 2 :=
    nativeOmegaCofactorSpecies_eq_two_of_prime hr
  have hq_copy := hq
  rw [mem_wr2FloorSubfiber_iff] at hq_copy
  have hq_hyp := (wr2ShearContractedFiber_to_hyperbolic_and_sum hq_copy.1).1
  rw [hyperbolicPrimeFiber, mem_filter] at hq_hyp
  have hq_isp : IsPrimeNat q := hq_hyp.2.1
  have hp_isp : IsPrimeNat (N - r * q) := hq_hyp.2.2.2.2.2.1
  have h_dich :
      q ∈ wr2LowTargetBoundarySubfiber N r m_sieve L ∨
      q ∈ wr2TargetSievedFloorSubfiber N r m_sieve L := by
    rw [← mem_union, ← wr2FloorSubfiber_eq_lowTarget_union_targetSieved N r m_sieve L]
    exact hq
  exact ⟨h_om, hq_isp, hp_isp, h_dich,
    hasNextPrimeConnection_unconditional q,
    hasNextPrimeConnection_unconditional (N - r * q)⟩

/-!
## Section 3: Target-Prime Reconstruction & Full Unsplit Mod-8190 Fiber Contraction
-/

/-- Set of low target primes `p ≤ m_sieve` (`2 ≤ p ≤ m_sieve`). -/
def lowTargetPrimes (m_sieve : ℕ) : Finset ℕ :=
  (range (m_sieve + 1)).filter IsPrimeNat

/-- Inverse reconstruction map `p ↦ (N - p) / r` recovering `q` from `p = N - r * q`. -/
def reconstructQFromTargetPrime (N r p : ℕ) : ℕ :=
  (N - p) / r

/-- Shift map `k ↦ k + 2` mapping `range (m_sieve - 1)` onto `{2, ..., m_sieve}`. -/
def shiftAddTwoNat (k : ℕ) : ℕ :=
  k + 2

/-- Cardinality bound `(lowTargetPrimes m_sieve).card ≤ m_sieve - 1`. -/
theorem lowTargetPrimes_card_le_sub_one (m_sieve : ℕ) :
    (lowTargetPrimes m_sieve).card ≤ m_sieve - 1 := by
  have h_sub : lowTargetPrimes m_sieve ⊆ (range (m_sieve - 1)).image shiftAddTwoNat := by
    intro p hp
    rw [lowTargetPrimes, mem_filter, mem_range] at hp
    have hp2 : 2 ≤ p := hp.2.1
    rw [mem_image]
    refine ⟨p - 2, ?_, ?_⟩
    · rw [mem_range]; omega
    · unfold shiftAddTwoNat; omega
  have h1 := Nat.le_trans (card_le_card h_sub) card_image_le
  rw [card_range] at h1
  exact h1

/-- **Theorem 3.1 (`wr2LowTargetBoundarySubfiber_card_le`):**
    For every `r > 0`, `wr2LowTargetBoundarySubfiber N r m_sieve L` is contained in the
    image of `lowTargetPrimes m_sieve` under `reconstructQFromTargetPrime N r`, so its
    cardinality is at most `(lowTargetPrimes m_sieve).card ≤ m_sieve - 1`. -/
theorem wr2LowTargetBoundarySubfiber_card_le
    {N r m_sieve L : ℕ} (hr_pos : 0 < r) :
    (wr2LowTargetBoundarySubfiber N r m_sieve L).card ≤ (lowTargetPrimes m_sieve).card ∧
    (wr2LowTargetBoundarySubfiber N r m_sieve L).card ≤ m_sieve - 1 := by
  have h_sub :
      wr2LowTargetBoundarySubfiber N r m_sieve L ⊆
        (lowTargetPrimes m_sieve).image (reconstructQFromTargetPrime N r) := by
    intro q hq
    rw [mem_wr2LowTargetBoundarySubfiber_iff] at hq
    obtain ⟨⟨hq_shear, _⟩, h_p_le⟩ := hq
    have h_props := wr2ShearContractedFiber_to_hyperbolic_and_sum hq_shear
    have hq_hyp := h_props.1
    have h_sum := h_props.2.2.2
    rw [hyperbolicPrimeFiber, mem_filter] at hq_hyp
    have h_pp : IsPrimeNat (N - r * q) := hq_hyp.2.2.2.2.2.1
    have h_sub_eq : N - (N - r * q) = r * q := by omega
    rw [mem_image]
    refine ⟨N - r * q, ?_, ?_⟩
    · rw [lowTargetPrimes, mem_filter, mem_range]
      exact ⟨by omega, h_pp⟩
    · unfold reconstructQFromTargetPrime
      rw [h_sub_eq, mul_div_cancel_left_native hr_pos]
  have h_c1 := Nat.le_trans (card_le_card h_sub) card_image_le
  have h_c2 := Nat.le_trans h_c1 (lowTargetPrimes_card_le_sub_one m_sieve)
  exact ⟨h_c1, h_c2⟩

/-- **Master Theorem 3.2 (`wr2FloorSubfiber_full_card_le_12_add_1728_and_990_stride`):**
    Full Unsplit Per-Fiber Mod-8190 Contraction on `WR2`:
    For every prime `r ≥ 13` and certified floor `L : ℕ`:
    1. `(wr2FloorSubfiber N r L).card ≤ 12 + 1728 * ((((N - 2) / r) / 8190 - L / 8190) + 1)`, and
    2. Under Mod-5, Mod-7, and Mod-13 target collisions,
       `(wr2FloorSubfiber N r L).card ≤ 12 + 990 * ((((N - 2) / r) / 8190 - L / 8190) + 1)`. -/
theorem wr2FloorSubfiber_full_card_le_12_add_1728_and_990_stride
    {N r L : ℕ} (hr13 : 13 ≤ r) :
    (wr2FloorSubfiber N r L).card ≤
      12 + 1728 * ((((N - 2) / r) / 8190 - L / 8190) + 1) ∧
    (∀ c₅ c₇ c₁₃ : ℕ,
      1 ≤ c₅ → c₅ < 5 → (r * c₅) % 5 = N % 5 →
      1 ≤ c₇ → c₇ < 7 → (r * c₇) % 7 = N % 7 →
      1 ≤ c₁₃ → c₁₃ < 13 → (r * c₁₃) % 13 = N % 13 →
      (wr2FloorSubfiber N r L).card ≤
        12 + 990 * ((((N - 2) / r) / 8190 - L / 8190) + 1)) := by
  have hr_pos : 0 < r := by omega
  have h_part := wr2FloorSubfiber_card_eq_lowTarget_add_targetSieved N r 13 L
  have h_low := (wr2LowTargetBoundarySubfiber_card_le (N := N) (m_sieve := 13) (L := L) hr_pos).2
  have h_ts := wr2TargetSievedFloorSubfiber_card_le_1728_and_990_stride (N := N) (L := L) hr13
  have h_1728 := h_ts.1
  refine ⟨by omega, ?_⟩
  intro c₅ c₇ c₁₃ hc5_pos hc5_lt h_c5 hc7_pos hc7_lt h_c7 hc13_pos hc13_lt h_c13
  have h_990 := h_ts.2 c₅ c₇ c₁₃ hc5_pos hc5_lt h_c5 hc7_pos hc7_lt h_c7 hc13_pos hc13_lt h_c13
  omega

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.mul_div_cancel_left_native
#print axioms WuPaper.ESZerosBridge.wr2FloorSubfiber_card_eq_lowTarget_add_targetSieved
#print axioms WuPaper.ESZerosBridge.wr2FloorSubfiber_exact_species_and_next_prime
#print axioms WuPaper.ESZerosBridge.wr2LowTargetBoundarySubfiber_card_le
#print axioms WuPaper.ESZerosBridge.wr2FloorSubfiber_full_card_le_12_add_1728_and_990_stride
