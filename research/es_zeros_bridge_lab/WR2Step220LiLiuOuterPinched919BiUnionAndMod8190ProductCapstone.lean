import WR2Step218LiLiuRSCInvolutionOrbitPairingAndD19Capstone

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step220LiLiuOuterPinched919BiUnionAndMod8190ProductCapstone.lean — Explicit `1728` / `990` Mod-8190 Target-Sieved Fiber Bounds & Master 43-Module `D19 N` Capstone

Welds the Explicit `1728`-Stride and `990`-Stride Target-Sieved Floor Subfiber Bounds
(`liliuTargetSievedFloorSubfiber_card_le_1728_and_990_stride`) and the Outer `9/19`-Pinched
Prime Product Bound (`liliuPinched919BiUnion_card_le_pinched_mul_third`) directly into the
43-Module `Goldbach.All` (`D19 N`) Master Capstone.
-/

/-- The target-sieved and floor-bounded sub-fiber `{q ∈ liliuTargetSieved3PrimeFiber N r m_sieve | L ≤ q}`. -/
def liliuTargetSievedFloorSubfiber (N r m_sieve L : ℕ) : Finset ℕ :=
  (liliuTargetSieved3PrimeFiber N r m_sieve).filter (fun q : ℕ => L ≤ q)

/-- Constructive 2D product bound on `liliuTargetSievedFloorSubfiber N r m_sieve L` for any `m > 0`. -/
theorem liliuTargetSievedFloorSubfiber_card_le_admissible_mul_stride
    {N r m_sieve L m : ℕ} (hm_pos : 0 < m) :
    (liliuTargetSievedFloorSubfiber N r m_sieve L).card ≤
      ((liliuTargetSieved3PrimeFiber N r m_sieve).image (fun q : ℕ => q % m)).card *
        (((N / r) / m - L / m) + 1) := by
  have h_sub :
      liliuTargetSievedFloorSubfiber N r m_sieve L ⊆
        ((liliuTargetSieved3PrimeFiber N r m_sieve).image (fun q : ℕ => q % m) ×ˢ
         range (((N / r) / m - L / m) + 1)).image
          (liliuReconstructResidueAndQuotientPair m (L / m)) := by
    intro q hq
    rw [liliuTargetSievedFloorSubfiber, mem_filter] at hq
    obtain ⟨hq_ts, h_L_le_q⟩ := hq
    have hq_tight : q ∈ liliuTight3PrimeFiber N r := by
      rw [liliuTargetSieved3PrimeFiber, mem_filter] at hq_ts
      exact hq_ts.1
    have h_q_le : q ≤ N / r := (liliuTight3PrimeFiber_mem_props hq_tight).2.2.1
    have h_q_div_ge : L / m ≤ q / m := div_le_div_right_liliu hm_pos h_L_le_q
    have h_q_div_le : q / m ≤ (N / r) / m := div_le_div_right_liliu hm_pos h_q_le
    have h_div_mod : m * (q / m) + q % m = q := Nat.div_add_mod q m
    have h_add_sub : L / m + (q / m - L / m) = q / m := by omega
    rw [mem_image]
    refine ⟨(q % m, q / m - L / m), ?_, ?_⟩
    · rw [mem_product, mem_image, mem_range]
      exact ⟨⟨q, hq_ts, rfl⟩, by omega⟩
    · unfold liliuReconstructResidueAndQuotientPair
      dsimp only
      rw [h_add_sub]
      omega
  have h1 := Nat.le_trans (card_le_card h_sub) card_image_le
  rw [card_product, card_range] at h1
  exact h1

/-- **Theorem 1.1 (`liliuTargetSievedFloorSubfiber_card_le_1728_and_990_stride`):**
    For every prime `r ≥ 13` and floor `L : ℕ`:
    1. `(liliuTargetSievedFloorSubfiber N r 13 L).card ≤ 1728 * (((N / r) / 8190 - L / 8190) + 1)`, and
    2. Under non-zero Mod-5, Mod-7, and Mod-13 target collision lanes `c₅, c₇, c₁₃`,
       `(liliuTargetSievedFloorSubfiber N r 13 L).card ≤ 990 * (((N / r) / 8190 - L / 8190) + 1)`. -/
theorem liliuTargetSievedFloorSubfiber_card_le_1728_and_990_stride
    {N r L : ℕ} (hr13 : 13 ≤ r) :
    (liliuTargetSievedFloorSubfiber N r 13 L).card ≤
      1728 * (((N / r) / 8190 - L / 8190) + 1) ∧
    (∀ c₅ c₇ c₁₃ : ℕ,
      1 ≤ c₅ → c₅ < 5 → (r * c₅) % 5 = N % 5 →
      1 ≤ c₇ → c₇ < 7 → (r * c₇) % 7 = N % 7 →
      1 ≤ c₁₃ → c₁₃ < 13 → (r * c₁₃) % 13 = N % 13 →
      (liliuTargetSievedFloorSubfiber N r 13 L).card ≤
        990 * (((N / r) / 8190 - L / 8190) + 1)) := by
  have h_base :=
    liliuTargetSievedFloorSubfiber_card_le_admissible_mul_stride
      (N := N) (r := r) (m_sieve := 13) (L := L) (by omega : 0 < 8190)
  have h8190 := liliuTargetSieved13_mod8190_card_bounds (N := N) hr13
  have h_mul1728 :=
    Nat.mul_le_mul_right (((N / r) / 8190 - L / 8190) + 1) h8190.1
  refine ⟨Nat.le_trans h_base h_mul1728, ?_⟩
  intro c₅ c₇ c₁₃ hc5_pos hc5_lt h_c5 hc7_pos hc7_lt h_c7 hc13_pos hc13_lt h_c13
  have h_990 := h8190.2 c₅ c₇ c₁₃ hc5_pos hc5_lt h_c5 hc7_pos hc7_lt h_c7 hc13_pos hc13_lt h_c13
  have h_mul990 :=
    Nat.mul_le_mul_right (((N / r) / 8190 - L / 8190) + 1) h_990
  exact Nat.le_trans h_base h_mul990

/-- 1D `Finset` of odd primes `q ≤ N / 3` on the Li–Liu stack. -/
def liliuOddPrimesUpToThird (N : ℕ) : Finset ℕ :=
  (range (N / 3 + 1)).filter (fun q : ℕ => IsPrimeNat q ∧ q % 2 = 1)

/-- **Theorem 2.1 (`liliuPinched919BiUnion_card_le_pinched_mul_third`):**
    Outer `9/19`-Pinched Prime Product Bound:
    `((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).card ≤ (pinchedOddPrimes919 N).card * (liliuOddPrimesUpToThird N).card`. -/
theorem liliuPinched919BiUnion_card_le_pinched_mul_third (N : ℕ) :
    ((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).card ≤
      (pinchedOddPrimes919 N).card * (liliuOddPrimesUpToThird N).card := by
  have h_sub :
      (pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N) ⊆
        pinchedOddPrimes919 N ×ˢ liliuOddPrimesUpToThird N := by
    intro rq hrq
    rw [mem_biUnion] at hrq
    obtain ⟨r, hr_pinch, hrq_pair⟩ := hrq
    rw [liliuTight3PrimeFiberPairs, mem_image] at hrq_pair
    obtain ⟨q, hq_tight, h_pair_eq⟩ := hrq_pair
    subst h_pair_eq
    have hr_copy := hr_pinch
    rw [pinchedOddPrimes919, mem_filter] at hr_copy
    have hr_two : 2 ≤ r := hr_copy.2.1.1
    have hr_odd : r % 2 = 1 := hr_copy.2.2.1
    have hr_ge3 : 3 ≤ r := by omega
    have h_props := liliuTight3PrimeFiber_mem_props hq_tight
    have hq_hyp := h_props.2.1
    have h_rq_sub2 := h_props.2.2.2.1
    rw [liliuHyperbolicPrimeFiber, mem_filter] at hq_hyp
    have h_3q_le : 3 * q ≤ r * q := Nat.mul_le_mul_right q hr_ge3
    have h_q_le_div3 : q ≤ N / 3 := by omega
    rw [mem_product, liliuOddPrimesUpToThird, mem_filter, mem_range]
    exact ⟨hr_pinch, ⟨by omega, hq_hyp.2.1, hq_hyp.2.2.1⟩⟩
  have h1 := card_le_card h_sub
  rw [card_product] at h1
  exact h1

/-- **Master 43-Module Capstone (`master_43module_D19_mod8190_1728_990_stride_and_involution_capstone`):**
    Complete 43-Module Capstone uniting `Goldbach.one_plus_one_nine_count` (`liuMainTerm0004 N < (D19 N : ℝ)`),
    the Universal Odd-Modulus Square Involution Orbit Theorem,
    the `108` Paired RSC Involution Orbits,
    the `1728`-Stride and `990`-Stride Target-Sieved Floor Subfiber Bounds,
    the Outer `9/19`-Pinched Prime Product Bound,
    and the Factorial Lighthouse Next-Prime Generator (`hasNextPrimeConnection_unconditional`). -/
theorem master_43module_D19_mod8190_1728_990_stride_and_involution_capstone :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (∀ r : ℕ, 13 ≤ r →
        ((liliuShearContractedFiber N r).image liliuRscPairedOrbitMod8190).card ≤ 108) ∧
      (∀ r L : ℕ, 13 ≤ r →
        (liliuTargetSievedFloorSubfiber N r 13 L).card ≤
          1728 * (((N / r) / 8190 - L / 8190) + 1) ∧
        ∀ c₅ c₇ c₁₃ : ℕ,
          1 ≤ c₅ → c₅ < 5 → (r * c₅) % 5 = N % 5 →
          1 ≤ c₇ → c₇ < 7 → (r * c₇) % 7 = N % 7 →
          1 ≤ c₁₃ → c₁₃ < 13 → (r * c₁₃) % 13 = N % 13 →
          (liliuTargetSievedFloorSubfiber N r 13 L).card ≤
            990 * (((N / r) / 8190 - L / 8190) + 1)) ∧
      ((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).card ≤
        (pinchedOddPrimes919 N).card * (liliuOddPrimesUpToThird N).card ∧
      (fiveupPinchedQRSubfilter 9 10 N).card ≤
        1 + ((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).card ∧
      ((((1 + ((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).card : ℕ) : ℝ) ≤
          liuMainTerm0004 N) →
        ∃ p q p_next' : ℕ,
          Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next' ∧ IsPrimeNat p_next') := by
  obtain ⟨K, hK4, hCap41⟩ := master_41module_D19_rsc_involution_orbit_pairing_capstone
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven
  have hM := hCap41 N hNK hEven
  refine ⟨hM.1,
          fun r hr13 => (hM.2.2.2.1 r hr13).2.2,
          fun r L hr13 => liliuTargetSievedFloorSubfiber_card_le_1728_and_990_stride hr13,
          liliuPinched919BiUnion_card_le_pinched_mul_third N,
          hM.2.2.2.2.2.1,
          hM.2.2.2.2.2.2⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.liliuTargetSievedFloorSubfiber_card_le_admissible_mul_stride
#print axioms WuPaper.ESZerosBridge.liliuTargetSievedFloorSubfiber_card_le_1728_and_990_stride
#print axioms WuPaper.ESZerosBridge.liliuPinched919BiUnion_card_le_pinched_mul_third
#print axioms WuPaper.ESZerosBridge.master_43module_D19_mod8190_1728_990_stride_and_involution_capstone
