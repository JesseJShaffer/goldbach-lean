import WR2Step197WR2HyperbolicPerPrimeFiberDecomposition

set_option exponentiation.threshold 10000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step199WR2PinchCutoffAndReciprocalShearFiberContraction.lean — `4469/9469` Pinch Cutoff & Shear-Locked Fibers

Links the `WR2` homogeneous exponent pinch (`r ^ 9469 ≤ (r * q) ^ 4469`) and the 5UP
Reciprocal Shear + Triple-QR locks directly into each per-prime hyperbolic fiber:

1. **Intrinsic `4469/9469` Exponent-Pinch Upper Cutoff (`hyperbolicPrimeFiber_pinch_cutoff_and_shear`):**
   Every `q ∈ hyperbolicPrimeFiber N r` satisfies `r * q ≤ N - 2` and `r ^ 9469 ≤ (r * q) ^ 4469`,
   which forces `r ^ 9469 ≤ (N - 2) ^ 4469` and `r ^ 9469 ≤ N ^ 4469`.
2. **Identical Vanishing Above the Pinch Cutoff (`hyperbolicPrimeFiber_card_eq_zero_of_gt_pinch`):**
   Whenever `(N - 2) ^ 4469 < r ^ 9469`, `(hyperbolicPrimeFiber N r).card = 0` and
   `(hyperbolicFiberPairs N r).card = 0`.
3. **5UP Reciprocal Shear & Triple-QR Fiber Contraction (`lowPrimeFactorBox_eq_biUnion_pinched_shearContractedFibers`):**
   Contracts the outer index set to `wr2PinchedOddPrimes p_next N` (`r ^ 9469 ≤ (N - 2) ^ 4469`)
   and locks every per-prime fiber to `wr2ShearContractedFiber N r` (carrying the division-free
   5UP Reciprocal Shear congruence for all `m` and the Mod-63/64/65 Triple-QR identities).
-/

/-!
## Section 1: Intrinsic `4469/9469` Pinch Cutoff & Half-Chord Triple-QR Identity on Fibers
-/

/-- Pure native half-chord square identity for odd `r ≤ q`:
    `((q + r) / 2) ^ 2 = r * q + ((q - r) / 2) ^ 2`. -/
theorem odd_pair_half_chord_sq_eq
    {r q : ℕ} (hle : r ≤ q) (hr_odd : r % 2 = 1) (hq_odd : q % 2 = 1) :
    ((q + r) / 2) ^ 2 = r * q + ((q - r) / 2) ^ 2 := by
  have h_a_eq : (q + r) / 2 = r + (q - r) / 2 := by omega
  have h_q_eq : q = r + 2 * ((q - r) / 2) := by omega
  rw [nat_sq_eq_mul ((q + r) / 2), nat_sq_eq_mul ((q - r) / 2)]
  have h_id := half_chord_hyperbola_add_wr2 r ((q - r) / 2)
  rw [← h_a_eq, ← h_q_eq] at h_id
  exact h_id

/-- **Theorem 1.1 (`hyperbolicPrimeFiber_pinch_cutoff_and_shear`):**
    Every `q ∈ hyperbolicPrimeFiber N r` satisfies:
    1. `r * q ≤ N - 2` and `r * q ≤ N`,
    2. `r ^ 9469 ≤ (N - 2) ^ 4469` and `r ^ 9469 ≤ N ^ 4469`,
    3. Division-free 5UP Reciprocal Shear congruence `((r + q) * r) % m = (r * r + r * q) % m` for all `m`,
    4. When `r % 2 = 1`, the Triple-QR (Mod 63, Mod 64, Mod 65) half-chord square locks. -/
theorem hyperbolicPrimeFiber_pinch_cutoff_and_shear
    {N r q : ℕ} (hq : q ∈ hyperbolicPrimeFiber N r) :
    r * q ≤ N - 2 ∧
    r ^ 9469 ≤ (N - 2) ^ 4469 ∧
    r ^ 9469 ≤ N ^ 4469 ∧
    (∀ m : ℕ, ((r + q) * r) % m = (r * r + r * q) % m) ∧
    (r % 2 = 1 →
      (((q + r) / 2) ^ 2) % 63 = (r * q + ((q - r) / 2) ^ 2) % 63 ∧
      (((q + r) / 2) ^ 2) % 64 = (r * q + ((q - r) / 2) ^ 2) % 64 ∧
      (((q + r) / 2) ^ 2) % 65 = (r * q + ((q - r) / 2) ^ 2) % 65) := by
  rw [hyperbolicPrimeFiber, mem_filter] at hq
  obtain ⟨_, _, hq_odd, h_r2_le_q, h_rq_le_N, h_pp, h_homog⟩ := hq
  have hp_two : 2 ≤ N - r * q := h_pp.1
  have h_rq_le_sub2 : r * q ≤ N - 2 := by omega
  have h_pow_sub2 : (r * q) ^ 4469 ≤ (N - 2) ^ 4469 :=
    nat_pow_le_pow_left h_rq_le_sub2 4469
  have h_pow_N : (r * q) ^ 4469 ≤ N ^ 4469 :=
    nat_pow_le_pow_left h_rq_le_N 4469
  have h_pinch_sub2 : r ^ 9469 ≤ (N - 2) ^ 4469 :=
    Nat.le_trans h_homog h_pow_sub2
  have h_pinch_N : r ^ 9469 ≤ N ^ 4469 :=
    Nat.le_trans h_homog h_pow_N
  refine ⟨h_rq_le_sub2, h_pinch_sub2, h_pinch_N, ?_, ?_⟩
  · intro m
    rw [Nat.right_distrib r q r, Nat.mul_comm q r]
  · intro hr_odd
    have h_le : r ≤ q := by omega
    have h_hc := odd_pair_half_chord_sq_eq h_le hr_odd hq_odd
    rw [h_hc]
    exact ⟨rfl, rfl, rfl⟩

/-- **Theorem 1.2 (`hyperbolicPrimeFiber_card_eq_zero_of_gt_pinch`):**
    If `(N - 2) ^ 4469 < r ^ 9469`, then both `hyperbolicPrimeFiber N r` and
    `hyperbolicFiberPairs N r` have cardinality `0`. -/
theorem hyperbolicPrimeFiber_card_eq_zero_of_gt_pinch
    {N r : ℕ} (h_gt : (N - 2) ^ 4469 < r ^ 9469) :
    (hyperbolicPrimeFiber N r).card = 0 ∧
    (hyperbolicFiberPairs N r).card = 0 := by
  have h0 : (hyperbolicPrimeFiber N r).card = 0 := by
    match Nat.eq_zero_or_pos (hyperbolicPrimeFiber N r).card with
    | Or.inl h_z => exact h_z
    | Or.inr h_pos =>
      obtain ⟨q, hq⟩ := card_pos.mp h_pos
      have h_pinch := (hyperbolicPrimeFiber_pinch_cutoff_and_shear hq).2.1
      omega
  have h_pairs : (hyperbolicFiberPairs N r).card = 0 := by
    rw [hyperbolicFiberPairs_card_eq N r, h0]
  exact ⟨h0, h_pairs⟩

/-!
## Section 2: Contracting the Index Set & Fibers via 5UP Reciprocal Shear + Triple-QR
-/

/-- The pinched odd prime index set `wr2PinchedOddPrimes p_next N`:
    restricts `oddPrimesBelow p_next` to primes satisfying `r ^ 9469 ≤ (N - 2) ^ 4469`. -/
def wr2PinchedOddPrimes (p_next N : ℕ) : Finset ℕ :=
  (oddPrimesBelow p_next).filter (fun r : ℕ => r ^ 9469 ≤ (N - 2) ^ 4469)

/-- The 5UP Shear & Triple-QR Contracted Hyperbolic Fiber above `r`. -/
def wr2ShearContractedFiber (N r : ℕ) : Finset ℕ :=
  (hyperbolicPrimeFiber N r).filter (fun q : ℕ =>
    r ^ 9469 ≤ (N - 2) ^ 4469 ∧
    (∀ m : ℕ, ((r + q) * r) % m = (r * r + r * q) % m) ∧
    (((q + r) / 2) ^ 2) % 63 = (r * q + ((q - r) / 2) ^ 2) % 63 ∧
    (((q + r) / 2) ^ 2) % 64 = (r * q + ((q - r) / 2) ^ 2) % 64 ∧
    (((q + r) / 2) ^ 2) % 65 = (r * q + ((q - r) / 2) ^ 2) % 65)

/-- The 2D fiber slice `{(r, q) | q ∈ wr2ShearContractedFiber N r}`. -/
def wr2ShearContractedFiberPairs (N r : ℕ) : Finset (ℕ × ℕ) :=
  (wr2ShearContractedFiber N r).image (fun q : ℕ => (r, q))

/-- For every odd `r` (`r % 2 = 1`), `wr2ShearContractedFiber N r = hyperbolicPrimeFiber N r`. -/
theorem wr2ShearContractedFiber_eq_of_odd {N r : ℕ} (hr_odd : r % 2 = 1) :
    wr2ShearContractedFiber N r = hyperbolicPrimeFiber N r := by
  ext q
  rw [wr2ShearContractedFiber, mem_filter]
  constructor
  · intro h; exact h.1
  · intro hq
    have h_all := hyperbolicPrimeFiber_pinch_cutoff_and_shear hq
    have h_qr := h_all.2.2.2.2 hr_odd
    exact ⟨hq, h_all.2.1, h_all.2.2.2.1, h_qr.1, h_qr.2.1, h_qr.2.2⟩

/-- **Theorem 2.1 (`lowPrimeFactorBox_eq_biUnion_pinched_shearContractedFibers`):**
    Exact decomposition of `lowPrimeFactorBox p_next N` over the pinched prime index set
    `wr2PinchedOddPrimes p_next N` and the 5UP Shear + Triple-QR contracted fibers
    `wr2ShearContractedFiberPairs N`. -/
theorem lowPrimeFactorBox_eq_biUnion_pinched_shearContractedFibers (p_next N : ℕ) :
    lowPrimeFactorBox p_next N =
      (wr2PinchedOddPrimes p_next N).biUnion (wr2ShearContractedFiberPairs N) := by
  rw [lowPrimeFactorBox_eq_biUnion_hyperbolicFiberPairs p_next N]
  ext rq
  rw [mem_biUnion, mem_biUnion]
  constructor
  · intro h
    obtain ⟨r, hr_mem, hrq_mem⟩ := h
    have hr_copy := hr_mem
    rw [oddPrimesBelow, mem_filter] at hr_copy
    have hr_odd : r % 2 = 1 := hr_copy.2.2
    rw [hyperbolicFiberPairs, mem_image] at hrq_mem
    obtain ⟨q, hq_mem, h_eq⟩ := hrq_mem
    have h_all := hyperbolicPrimeFiber_pinch_cutoff_and_shear hq_mem
    refine ⟨r, ?_, ?_⟩
    · rw [wr2PinchedOddPrimes, mem_filter]
      exact ⟨hr_mem, h_all.2.1⟩
    · rw [wr2ShearContractedFiberPairs, wr2ShearContractedFiber_eq_of_odd hr_odd, mem_image]
      exact ⟨q, hq_mem, h_eq⟩
  · intro h
    obtain ⟨r, hr_pinch, hrq_shear⟩ := h
    rw [wr2PinchedOddPrimes, mem_filter] at hr_pinch
    have hr_copy := hr_pinch.1
    rw [oddPrimesBelow, mem_filter] at hr_copy
    have hr_odd : r % 2 = 1 := hr_copy.2.2
    rw [wr2ShearContractedFiberPairs, wr2ShearContractedFiber_eq_of_odd hr_odd] at hrq_shear
    exact ⟨r, hr_pinch.1, hrq_shear⟩

/-- **Master Theorem 2.2 (`wr2_cutline_card_le_pinched_shear_fibers_on_wave_segment`):**
    Across any wave segment `N ≤ (p_next + 1) ^ 2` with `N % 2 = 0`,
    `(wr2CutlineSemiprimePrimes N).card` is bounded by `1` plus the union of the
    5UP Shear & Triple-QR contracted fibers over `wr2PinchedOddPrimes p_next N`. -/
theorem wr2_cutline_card_le_pinched_shear_fibers_on_wave_segment
    {p_next N : ℕ} (hEven : N % 2 = 0) (hN_le : N ≤ (p_next + 1) ^ 2) :
    (lowPrimeTightChiralBox p_next N).card =
      ((wr2PinchedOddPrimes p_next N).biUnion (wr2ShearContractedFiberPairs N)).card ∧
    (wr2CutlineSemiprimePrimes N).card ≤
      1 + ((wr2PinchedOddPrimes p_next N).biUnion (wr2ShearContractedFiberPairs N)).card := by
  have h_base := wr2_lowPrimeTightChiralBox_eq_biUnion_hyperbolic_fibers hEven hN_le
  have h_bi := lowPrimeFactorBox_eq_biUnion_hyperbolicFiberPairs p_next N
  have h_pinch := lowPrimeFactorBox_eq_biUnion_pinched_shearContractedFibers p_next N
  rw [← h_bi, h_pinch] at h_base
  exact h_base

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.hyperbolicPrimeFiber_pinch_cutoff_and_shear
#print axioms WuPaper.ESZerosBridge.hyperbolicPrimeFiber_card_eq_zero_of_gt_pinch
#print axioms WuPaper.ESZerosBridge.lowPrimeFactorBox_eq_biUnion_pinched_shearContractedFibers
#print axioms WuPaper.ESZerosBridge.wr2_cutline_card_le_pinched_shear_fibers_on_wave_segment
