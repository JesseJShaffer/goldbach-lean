import WR2Step220LiLiuOuterPinched919BiUnionAndMod8190ProductCapstone

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step222LiLiuExactSpeciesLowTargetPartitionAndD19Capstone.lean — Full Unsplit Fiber Mod-8190 Contraction & Master 45-Module `D19 N` Capstone

Completes the low-target boundary partition (`N - r * q ≤ m_sieve` vs. `m_sieve < N - r * q`)
on `liliuFloorSubfiber N r L` with explicit membership equivalences, native `Ω`-species
and next-prime associations, and welds the full unsplit per-fiber Mod-8190 bounds
(`12 + 1728 * (((N / r) / 8190 - L / 8190) + 1)` and `12 + 990 * ...`) directly into the
45-Module `Goldbach.All` (`D19 N`) Master Capstone.
-/

/-- Pure native proof of `(r * q) / r = q` for `0 < r`. -/
theorem mul_div_cancel_left_liliu {r q : ℕ} (hr_pos : 0 < r) :
    (r * q) / r = q := by
  have h_ge : q ≤ (r * q) / r := le_div_of_mul_le_liliu hr_pos (Nat.le_refl (r * q))
  have h_div_mod : r * ((r * q) / r) + (r * q) % r = r * q := Nat.div_add_mod (r * q) r
  have h_mul_le : r * ((r * q) / r) ≤ r * q := by omega
  have h_le : (r * q) / r ≤ q := le_of_mul_le_mul_left_pos_liliu hr_pos h_mul_le
  exact Nat.le_antisymm h_le h_ge

/-- The low-target boundary sub-fiber `{q ∈ liliuFloorSubfiber N r L | N - r * q ≤ m_sieve}`. -/
def liliuLowTargetBoundarySubfiber (N r m_sieve L : ℕ) : Finset ℕ :=
  (liliuFloorSubfiber N r L).filter (fun q : ℕ => N - r * q ≤ m_sieve)

/-- Explicit membership equivalence for `liliuFloorSubfiber N r L`. -/
theorem mem_liliuFloorSubfiber_iff {N r L q : ℕ} :
    q ∈ liliuFloorSubfiber N r L ↔ q ∈ liliuTight3PrimeFiber N r ∧ L ≤ q := by
  rw [liliuFloorSubfiber, mem_filter]

/-- Explicit membership equivalence for `liliuLowTargetBoundarySubfiber N r m_sieve L`. -/
theorem mem_liliuLowTargetBoundarySubfiber_iff {N r m_sieve L q : ℕ} :
    q ∈ liliuLowTargetBoundarySubfiber N r m_sieve L ↔
      (q ∈ liliuTight3PrimeFiber N r ∧ L ≤ q) ∧ N - r * q ≤ m_sieve := by
  rw [liliuLowTargetBoundarySubfiber, mem_filter, mem_liliuFloorSubfiber_iff]

/-- Explicit membership equivalence for `liliuTargetSievedFloorSubfiber N r m_sieve L`. -/
theorem mem_liliuTargetSievedFloorSubfiber_iff {N r m_sieve L q : ℕ} :
    q ∈ liliuTargetSievedFloorSubfiber N r m_sieve L ↔
      (q ∈ liliuTight3PrimeFiber N r ∧ m_sieve < N - r * q) ∧ L ≤ q := by
  rw [liliuTargetSievedFloorSubfiber, mem_filter, liliuTargetSieved3PrimeFiber, mem_filter]

theorem disjoint_liliuLowTarget_targetSievedFloor (N r m_sieve L : ℕ) :
    Disjoint (liliuLowTargetBoundarySubfiber N r m_sieve L)
             (liliuTargetSievedFloorSubfiber N r m_sieve L) := by
  rw [Finset.disjoint_left]
  intro q hlow hts
  rw [mem_liliuLowTargetBoundarySubfiber_iff] at hlow
  rw [mem_liliuTargetSievedFloorSubfiber_iff] at hts
  have h1 : N - r * q ≤ m_sieve := hlow.2
  have h2 : m_sieve < N - r * q := hts.1.2
  omega

theorem liliuFloorSubfiber_eq_lowTarget_union_targetSieved (N r m_sieve L : ℕ) :
    liliuFloorSubfiber N r L =
      liliuLowTargetBoundarySubfiber N r m_sieve L ∪
      liliuTargetSievedFloorSubfiber N r m_sieve L := by
  ext q
  rw [mem_union, mem_liliuFloorSubfiber_iff,
      mem_liliuLowTargetBoundarySubfiber_iff,
      mem_liliuTargetSievedFloorSubfiber_iff]
  constructor
  · intro hq
    match Nat.lt_or_ge m_sieve (N - r * q) with
    | Or.inl hgt => exact Or.inr ⟨⟨hq.1, hgt⟩, hq.2⟩
    | Or.inr hle => exact Or.inl ⟨hq, hle⟩
  · intro hor
    cases hor with
    | inl hlow => exact hlow.1
    | inr hts => exact ⟨hts.1.1, hts.2⟩

/-- Exact additive decomposition of `liliuFloorSubfiber N r L` across any sieve horizon `m_sieve`. -/
theorem liliuFloorSubfiber_card_eq_lowTarget_add_targetSieved (N r m_sieve L : ℕ) :
    (liliuFloorSubfiber N r L).card =
      (liliuLowTargetBoundarySubfiber N r m_sieve L).card +
      (liliuTargetSievedFloorSubfiber N r m_sieve L).card := by
  conv_lhs => rw [liliuFloorSubfiber_eq_lowTarget_union_targetSieved N r m_sieve L]
  exact card_union_of_disjoint (disjoint_liliuLowTarget_targetSievedFloor N r m_sieve L)

/-- Explicit connection of every `q ∈ liliuFloorSubfiber N r L` to `liliuTight3PrimeFiber_next_prime_connections`
    (`WR2Step206`) and the disjoint ExactSpecies low-target / target-sieved dichotomy. -/
theorem liliuFloorSubfiber_exact_species_and_next_prime
    {N r m_sieve L q : ℕ} (hq : q ∈ liliuFloorSubfiber N r L) :
    IsPrimeNat q ∧
    IsPrimeNat (N - r * q) ∧
    (q ∈ liliuLowTargetBoundarySubfiber N r m_sieve L ∨
     q ∈ liliuTargetSievedFloorSubfiber N r m_sieve L) ∧
    (∃ q_next : ℕ, q < q_next ∧ IsPrimeNat q_next) ∧
    (∃ p_next : ℕ, (N - r * q) < p_next ∧ IsPrimeNat p_next) := by
  have hq_copy := hq
  rw [mem_liliuFloorSubfiber_iff] at hq_copy
  have h_np := liliuTight3PrimeFiber_next_prime_connections hq_copy.1
  have h_dich :
      q ∈ liliuLowTargetBoundarySubfiber N r m_sieve L ∨
      q ∈ liliuTargetSievedFloorSubfiber N r m_sieve L := by
    rw [← mem_union, ← liliuFloorSubfiber_eq_lowTarget_union_targetSieved N r m_sieve L]
    exact hq
  exact ⟨h_np.1, h_np.2.1, h_dich, h_np.2.2.2.2.1, h_np.2.2.2.2.2⟩

def liliuLowTargetPrimes (m_sieve : ℕ) : Finset ℕ :=
  (range (m_sieve + 1)).filter IsPrimeNat

def liliuReconstructQFromTargetPrime (N r p : ℕ) : ℕ :=
  (N - p) / r

def liliuShiftAddTwoNat (k : ℕ) : ℕ :=
  k + 2

theorem liliuLowTargetPrimes_card_le_sub_one (m_sieve : ℕ) :
    (liliuLowTargetPrimes m_sieve).card ≤ m_sieve - 1 := by
  have h_sub : liliuLowTargetPrimes m_sieve ⊆ (range (m_sieve - 1)).image liliuShiftAddTwoNat := by
    intro p hp
    rw [liliuLowTargetPrimes, mem_filter, mem_range] at hp
    have hp2 : 2 ≤ p := hp.2.1
    rw [mem_image]
    refine ⟨p - 2, ?_, ?_⟩
    · rw [mem_range]; omega
    · unfold liliuShiftAddTwoNat; omega
  have h1 := Nat.le_trans (card_le_card h_sub) card_image_le
  rw [card_range] at h1
  exact h1

/-- **Theorem 1.1 (`liliuLowTargetBoundarySubfiber_card_le`):**
    For every `r > 0`, `(liliuLowTargetBoundarySubfiber N r m_sieve L).card ≤ m_sieve - 1`. -/
theorem liliuLowTargetBoundarySubfiber_card_le
    {N r m_sieve L : ℕ} (hr_pos : 0 < r) :
    (liliuLowTargetBoundarySubfiber N r m_sieve L).card ≤ (liliuLowTargetPrimes m_sieve).card ∧
    (liliuLowTargetBoundarySubfiber N r m_sieve L).card ≤ m_sieve - 1 := by
  have h_sub :
      liliuLowTargetBoundarySubfiber N r m_sieve L ⊆
        (liliuLowTargetPrimes m_sieve).image (liliuReconstructQFromTargetPrime N r) := by
    intro q hq
    rw [mem_liliuLowTargetBoundarySubfiber_iff] at hq
    obtain ⟨⟨hq_tight, _⟩, h_p_le⟩ := hq
    have h_props := liliuTight3PrimeFiber_mem_props hq_tight
    have h_pp : IsPrimeNat (N - r * q) := h_props.2.2.2.2.1
    have h_sum : r * q + (N - r * q) = N := h_props.2.2.2.2.2
    have h_sub_eq : N - (N - r * q) = r * q := by omega
    rw [mem_image]
    refine ⟨N - r * q, ?_, ?_⟩
    · rw [liliuLowTargetPrimes, mem_filter, mem_range]
      exact ⟨by omega, h_pp⟩
    · unfold liliuReconstructQFromTargetPrime
      rw [h_sub_eq, mul_div_cancel_left_liliu hr_pos]
  have h_c1 := Nat.le_trans (card_le_card h_sub) card_image_le
  have h_c2 := Nat.le_trans h_c1 (liliuLowTargetPrimes_card_le_sub_one m_sieve)
  exact ⟨h_c1, h_c2⟩

/-- **Theorem 2.1 (`liliuFloorSubfiber_full_card_le_12_add_1728_and_990_stride`):**
    Full Unsplit Per-Fiber Mod-8190 Contraction on `D19 N`:
    For every prime `r ≥ 13` and certified floor `L : ℕ`:
    1. `(liliuFloorSubfiber N r L).card ≤ 12 + 1728 * (((N / r) / 8190 - L / 8190) + 1)`, and
    2. Under Mod-5, Mod-7, and Mod-13 target collisions,
       `(liliuFloorSubfiber N r L).card ≤ 12 + 990 * (((N / r) / 8190 - L / 8190) + 1)`. -/
theorem liliuFloorSubfiber_full_card_le_12_add_1728_and_990_stride
    {N r L : ℕ} (hr13 : 13 ≤ r) :
    (liliuFloorSubfiber N r L).card ≤
      12 + 1728 * (((N / r) / 8190 - L / 8190) + 1) ∧
    (∀ c₅ c₇ c₁₃ : ℕ,
      1 ≤ c₅ → c₅ < 5 → (r * c₅) % 5 = N % 5 →
      1 ≤ c₇ → c₇ < 7 → (r * c₇) % 7 = N % 7 →
      1 ≤ c₁₃ → c₁₃ < 13 → (r * c₁₃) % 13 = N % 13 →
      (liliuFloorSubfiber N r L).card ≤
        12 + 990 * (((N / r) / 8190 - L / 8190) + 1)) := by
  have hr_pos : 0 < r := by omega
  have h_part := liliuFloorSubfiber_card_eq_lowTarget_add_targetSieved N r 13 L
  have h_low := (liliuLowTargetBoundarySubfiber_card_le (N := N) (m_sieve := 13) (L := L) hr_pos).2
  have h_ts := liliuTargetSievedFloorSubfiber_card_le_1728_and_990_stride (N := N) (L := L) hr13
  have h_1728 := h_ts.1
  refine ⟨by omega, ?_⟩
  intro c₅ c₇ c₁₃ hc5_pos hc5_lt h_c5 hc7_pos hc7_lt h_c7 hc13_pos hc13_lt h_c13
  have h_990 := h_ts.2 c₅ c₇ c₁₃ hc5_pos hc5_lt h_c5 hc7_pos hc7_lt h_c7 hc13_pos hc13_lt h_c13
  omega

/-- **Master 45-Module Capstone (`master_45module_D19_full_unsplit_fiber_mod8190_capstone`):**
    Complete 45-Module Capstone uniting `Goldbach.one_plus_one_nine_count` (`liuMainTerm0004 N < (D19 N : ℝ)`),
    the Full Unsplit Per-Fiber Mod-8190 Contraction (`12 + 1728 * ...` and `12 + 990 * ...`),
    the `108` Paired RSC Involution Orbits,
    the Outer `9/19`-Pinched Prime Product Bound,
    and the Factorial Lighthouse Next-Prime Generator (`hasNextPrimeConnection_unconditional`). -/
theorem master_45module_D19_full_unsplit_fiber_mod8190_capstone :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (∀ r : ℕ, 13 ≤ r →
        ((liliuShearContractedFiber N r).image liliuRscPairedOrbitMod8190).card ≤ 108) ∧
      (∀ r L : ℕ, 13 ≤ r →
        (liliuFloorSubfiber N r L).card ≤
          12 + 1728 * (((N / r) / 8190 - L / 8190) + 1) ∧
        ∀ c₅ c₇ c₁₃ : ℕ,
          1 ≤ c₅ → c₅ < 5 → (r * c₅) % 5 = N % 5 →
          1 ≤ c₇ → c₇ < 7 → (r * c₇) % 7 = N % 7 →
          1 ≤ c₁₃ → c₁₃ < 13 → (r * c₁₃) % 13 = N % 13 →
          (liliuFloorSubfiber N r L).card ≤
            12 + 990 * (((N / r) / 8190 - L / 8190) + 1)) ∧
      ((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).card ≤
        (pinchedOddPrimes919 N).card * (liliuOddPrimesUpToThird N).card ∧
      (fiveupPinchedQRSubfilter 9 10 N).card ≤
        1 + ((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).card ∧
      ((((1 + ((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).card : ℕ) : ℝ) ≤
          liuMainTerm0004 N) →
        ∃ p q p_next' : ℕ,
          Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next' ∧ IsPrimeNat p_next') := by
  obtain ⟨K, hK4, hCap43⟩ := master_43module_D19_mod8190_1728_990_stride_and_involution_capstone
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven
  have hM := hCap43 N hNK hEven
  refine ⟨hM.1,
          hM.2.1,
          fun r L hr13 => liliuFloorSubfiber_full_card_le_12_add_1728_and_990_stride hr13,
          hM.2.2.2.1,
          hM.2.2.2.2.1,
          hM.2.2.2.2.2⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.mul_div_cancel_left_liliu
#print axioms WuPaper.ESZerosBridge.liliuFloorSubfiber_card_eq_lowTarget_add_targetSieved
#print axioms WuPaper.ESZerosBridge.liliuFloorSubfiber_exact_species_and_next_prime
#print axioms WuPaper.ESZerosBridge.liliuLowTargetBoundarySubfiber_card_le
#print axioms WuPaper.ESZerosBridge.liliuFloorSubfiber_full_card_le_12_add_1728_and_990_stride
#print axioms WuPaper.ESZerosBridge.master_45module_D19_full_unsplit_fiber_mod8190_capstone
