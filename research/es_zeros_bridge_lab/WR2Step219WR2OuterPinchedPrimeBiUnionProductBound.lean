import WR2Step217WR2RSCInvolutionOrbitPairingAndChannelContraction

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step219WR2OuterPinchedPrimeBiUnionProductBound.lean — Explicit `1728` / `990` Mod-8190 Target-Sieved Fiber Bounds & Outer Pinched-Prime Product Bound

1. **Explicit `1728`-Stride and `990`-Stride Cardinality Bounds on Target-Sieved Floor Subfibers
   (`wr2TargetSievedFloorSubfiber`, `wr2TargetSievedFloorSubfiber_card_le_1728_and_990_stride`):**
   Combines `targetSieved13_mod8190_admissible_card_bounds` (`WR2Step215`) with the
   2D residue-and-quotient reconstruction map (`reconstructFromResidueAndQuotientPair 8190`)
   to prove that for every prime `r ≥ 13` and floor `L : ℕ`:
   - `(wr2TargetSievedFloorSubfiber N r 13 L).card ≤ 1728 * ((((N - 2) / r) / 8190 - L / 8190) + 1)`, and
   - Under Mod-5, Mod-7, and Mod-13 target collisions,
     `(wr2TargetSievedFloorSubfiber N r 13 L).card ≤ 990 * ((((N - 2) / r) / 8190 - L / 8190) + 1)`.
2. **Explicit Prime & Next-Prime Connections on `wr2ShearContractedFiber`
   (`wr2ShearContractedFiber_mem_explicit_connections`,
   `wr2PinchedShearBiUnion_card_le_pinched_mul_third`):**
   Explicitly connects every `r ∈ wr2PinchedOddPrimes p_next N` and `q ∈ wr2ShearContractedFiber N r`
   to `IsPrimeNat r`, `IsPrimeNat q`, `predictedNextPrime r`, `predictedNextPrime q`, and
   `q ∈ oddPrimesUpToThird N`, proving the outer product bound
   `((wr2PinchedOddPrimes p_next N).biUnion (wr2ShearContractedFiberPairs N)).card ≤ (wr2PinchedOddPrimes p_next N).card * (oddPrimesUpToThird N).card`.
-/

/-- The target-sieved and floor-bounded sub-fiber `{q ∈ wr2TargetSievedFiber N r m_sieve | L ≤ q}`. -/
def wr2TargetSievedFloorSubfiber (N r m_sieve L : ℕ) : Finset ℕ :=
  (wr2TargetSievedFiber N r m_sieve).filter (fun q : ℕ => L ≤ q)

/-- Inclusion `wr2TargetSievedFloorSubfiber N r m_sieve L ⊆ wr2TargetSievedFiber N r m_sieve`. -/
theorem wr2TargetSievedFloorSubfiber_subset_targetSieved (N r m_sieve L : ℕ) :
    wr2TargetSievedFloorSubfiber N r m_sieve L ⊆ wr2TargetSievedFiber N r m_sieve :=
  filter_subset _ _

/-- Constructive 2D product bound on `wr2TargetSievedFloorSubfiber N r m_sieve L` for any modulus `m > 0`. -/
theorem wr2TargetSievedFloorSubfiber_card_le_admissible_mul_stride
    {N r m_sieve L m : ℕ} (hm_pos : 0 < m) :
    (wr2TargetSievedFloorSubfiber N r m_sieve L).card ≤
      (admissibleFiberResidues (wr2TargetSievedFiber N r m_sieve) m).card *
        ((((N - 2) / r) / m - L / m) + 1) := by
  have h_sub :
      wr2TargetSievedFloorSubfiber N r m_sieve L ⊆
        (admissibleFiberResidues (wr2TargetSievedFiber N r m_sieve) m ×ˢ
         range ((((N - 2) / r) / m - L / m) + 1)).image
          (reconstructFromResidueAndQuotientPair m (L / m)) := by
    intro q hq
    rw [wr2TargetSievedFloorSubfiber, mem_filter] at hq
    obtain ⟨hq_ts, h_L_le_q⟩ := hq
    have hq_fiber : q ∈ wr2ShearContractedFiber N r := by
      rw [wr2TargetSievedFiber, mem_filter] at hq_ts
      exact hq_ts.1
    have h_q_le : q ≤ (N - 2) / r :=
      (wr2ShearContractedFiber_to_hyperbolic_and_sum hq_fiber).2.1
    have h_q_div_ge : L / m ≤ q / m := div_le_div_right_native hm_pos h_L_le_q
    have h_q_div_le : q / m ≤ ((N - 2) / r) / m := div_le_div_right_native hm_pos h_q_le
    have h_div_mod : m * (q / m) + q % m = q := Nat.div_add_mod q m
    have h_add_sub : L / m + (q / m - L / m) = q / m := by omega
    rw [mem_image]
    refine ⟨(q % m, q / m - L / m), ?_, ?_⟩
    · rw [mem_product, admissibleFiberResidues, mem_image, mem_range]
      exact ⟨⟨q, hq_ts, rfl⟩, by omega⟩
    · unfold reconstructFromResidueAndQuotientPair
      dsimp only
      rw [h_add_sub]
      omega
  have h1 := Nat.le_trans (card_le_card h_sub) card_image_le
  rw [card_product, card_range] at h1
  exact h1

/-- **Theorem 1.1 (`wr2TargetSievedFloorSubfiber_card_le_1728_and_990_stride`):**
    For every prime `r ≥ 13` and floor `L : ℕ`:
    1. `(wr2TargetSievedFloorSubfiber N r 13 L).card ≤ 1728 * ((((N - 2) / r) / 8190 - L / 8190) + 1)`, and
    2. Under non-zero Mod-5, Mod-7, and Mod-13 target collision lanes `c₅, c₇, c₁₃`,
       `(wr2TargetSievedFloorSubfiber N r 13 L).card ≤ 990 * ((((N - 2) / r) / 8190 - L / 8190) + 1)`. -/
theorem wr2TargetSievedFloorSubfiber_card_le_1728_and_990_stride
    {N r L : ℕ} (hr13 : 13 ≤ r) :
    (wr2TargetSievedFloorSubfiber N r 13 L).card ≤
      1728 * ((((N - 2) / r) / 8190 - L / 8190) + 1) ∧
    (∀ c₅ c₇ c₁₃ : ℕ,
      1 ≤ c₅ → c₅ < 5 → (r * c₅) % 5 = N % 5 →
      1 ≤ c₇ → c₇ < 7 → (r * c₇) % 7 = N % 7 →
      1 ≤ c₁₃ → c₁₃ < 13 → (r * c₁₃) % 13 = N % 13 →
      (wr2TargetSievedFloorSubfiber N r 13 L).card ≤
        990 * ((((N - 2) / r) / 8190 - L / 8190) + 1)) := by
  have h_base :=
    wr2TargetSievedFloorSubfiber_card_le_admissible_mul_stride
      (N := N) (r := r) (m_sieve := 13) (L := L) (by omega : 0 < 8190)
  have h8190 := targetSieved13_mod8190_admissible_card_bounds (N := N) hr13
  have h_mul1728 :=
    Nat.mul_le_mul_right ((((N - 2) / r) / 8190 - L / 8190) + 1) h8190.1
  refine ⟨Nat.le_trans h_base h_mul1728, ?_⟩
  intro c₅ c₇ c₁₃ hc5_pos hc5_lt h_c5 hc7_pos hc7_lt h_c7 hc13_pos hc13_lt h_c13
  have h_990 := h8190.2 c₅ c₇ c₁₃ hc5_pos hc5_lt h_c5 hc7_pos hc7_lt h_c7 hc13_pos hc13_lt h_c13
  have h_mul990 :=
    Nat.mul_le_mul_right ((((N - 2) / r) / 8190 - L / 8190) + 1) h_990
  exact Nat.le_trans h_base h_mul990

/-- **Theorem 2.1 (`wr2ShearContractedFiber_mem_explicit_connections`):**
    Explicitly connects every `r ∈ wr2PinchedOddPrimes p_next N` and `q ∈ wr2ShearContractedFiber N r`
    to `IsPrimeNat r`, `IsPrimeNat q`, `q ∈ oddPrimesUpToThird N`, and our native prime
    generator `predictedNextPrime r` and `predictedNextPrime q`. -/
theorem wr2ShearContractedFiber_mem_explicit_connections
    {p_next N r q : ℕ}
    (hr_pinch : r ∈ wr2PinchedOddPrimes p_next N)
    (hq_shear : q ∈ wr2ShearContractedFiber N r) :
    IsPrimeNat r ∧
    r % 2 = 1 ∧
    3 ≤ r ∧
    r < p_next ∧
    IsPrimeNat q ∧
    q % 2 = 1 ∧
    q ≤ N / 3 ∧
    q ∈ oddPrimesUpToThird N ∧
    predictedNextPrime r = nextPrimeBoundedAux (r + 1) (factorialNat r + 1) ∧
    predictedNextPrime q = nextPrimeBoundedAux (q + 1) (factorialNat q + 1) := by
  have hr_copy := hr_pinch
  rw [wr2PinchedOddPrimes, mem_filter, oddPrimesBelow, mem_filter, mem_range] at hr_copy
  obtain ⟨⟨hr_lt_pn, hr_isp, hr_odd⟩, _⟩ := hr_copy
  have hr_two : 2 ≤ r := hr_isp.1
  have hr_ge3 : 3 ≤ r := by omega
  have h_props := wr2ShearContractedFiber_to_hyperbolic_and_sum hq_shear
  have hq_hyp := h_props.1
  have h_rq_sub2 := h_props.2.2.1
  rw [hyperbolicPrimeFiber, mem_filter] at hq_hyp
  obtain ⟨_, hq_isp, hq_odd, _⟩ := hq_hyp
  have h_3q_le : 3 * q ≤ r * q := Nat.mul_le_mul_right q hr_ge3
  have h_q_le_div3 : q ≤ N / 3 := by omega
  have hq_mem_third : q ∈ oddPrimesUpToThird N := by
    rw [oddPrimesUpToThird, mem_filter, mem_range]
    exact ⟨by omega, hq_isp, hq_odd⟩
  exact ⟨hr_isp, hr_odd, hr_ge3, hr_lt_pn, hq_isp, hq_odd,
    h_q_le_div3, hq_mem_third, rfl, rfl⟩

/-- **Theorem 2.2 (`wr2PinchedShearBiUnion_card_le_pinched_mul_third`):**
    Outer Pinched-Prime Union Bound: the union of `wr2ShearContractedFiberPairs N r` over
    `r ∈ wr2PinchedOddPrimes p_next N` is bounded by
    `(wr2PinchedOddPrimes p_next N).card * (oddPrimesUpToThird N).card`. -/
theorem wr2PinchedShearBiUnion_card_le_pinched_mul_third (p_next N : ℕ) :
    ((wr2PinchedOddPrimes p_next N).biUnion (wr2ShearContractedFiberPairs N)).card ≤
      (wr2PinchedOddPrimes p_next N).card * (oddPrimesUpToThird N).card := by
  have h_sub :
      (wr2PinchedOddPrimes p_next N).biUnion (wr2ShearContractedFiberPairs N) ⊆
        wr2PinchedOddPrimes p_next N ×ˢ oddPrimesUpToThird N := by
    intro rq hrq
    rw [mem_biUnion] at hrq
    obtain ⟨r, hr_pinch, hrq_pair⟩ := hrq
    rw [wr2ShearContractedFiberPairs, mem_image] at hrq_pair
    obtain ⟨q, hq_shear, h_pair_eq⟩ := hrq_pair
    subst h_pair_eq
    have h_conn := wr2ShearContractedFiber_mem_explicit_connections hr_pinch hq_shear
    rw [mem_product]
    exact ⟨hr_pinch, h_conn.2.2.2.2.2.2.2.1⟩
  have h1 := card_le_card h_sub
  rw [card_product] at h1
  exact h1

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.wr2TargetSievedFloorSubfiber_card_le_admissible_mul_stride
#print axioms WuPaper.ESZerosBridge.wr2TargetSievedFloorSubfiber_card_le_1728_and_990_stride
#print axioms WuPaper.ESZerosBridge.wr2ShearContractedFiber_mem_explicit_connections
#print axioms WuPaper.ESZerosBridge.wr2PinchedShearBiUnion_card_le_pinched_mul_third
