import WR2Step203WR2ShiftedWindowStrideAndFiberBiUnion

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step205WR2BilateralOMCLaneExclusionAndGeneralFloorStride.lean — Bilateral OMC Target-Lane Exclusion & Arbitrary-Floor Stride

Strengthens the `WR2` per-prime fiber decomposition (`WR2Step203`) with two explicit theorems:

1. **Division-Free Bilateral OMC Target-Side Exclusion (`bilateral_omc_target_lane_ne_native`,
   `targetSievedFiber_admissible_subset_bilateralOMCResidues`):**
   Proves in pure `Init` Euclidean arithmetic (`eq_zero_of_mul_add_eq_mul_of_lt`) that whenever
   `r * q + p = N`, `0 < m`, and `1 ≤ p % m`, we have `(r * (q % m)) % m ≠ N % m`.
   Explicitly connects `wr2ShearContractedFiber` to `hyperbolicPrimeFiber_pinch_cutoff_and_shear`
   (`WR2Step199`) to prove that on `wr2TargetSievedFiber N r m` (`2 ≤ m ≤ r` and `m < N - r * q`),
   every populated residue class `c = q % m` belongs to
   `bilateralOMCResidues N r m = {c ∈ range m | 1 ≤ c ∧ (r * c) % m ≠ N % m}`.
2. **Arbitrary Certified Lower-Floor Shifted-Window Quotient Bounds
   (`wr2FloorSubfiber_slice_card_le_shifted_quotient_diff`,
   `wr2FloorSubfiber_shifted_slice_card_le_window_div`):**
   Generalizes the shifted-window stride bounds from `L = r + 2` to ANY lower floor `L : ℕ`
   (including the `5000/4469` lower-pinch floor `L_pinch`), proving
   `card ≤ (((N - 2) / r) / m - L / m) + 1` and `card ≤ ((N - 2) / r - L) / m + 1`.
-/

/-!
## Section 1: Pure Native Euclidean Cancellation & Bilateral OMC Target-Side Exclusion
-/

/-- Pure native additive-subtractive identity in isolated context: `a ≤ b - 2 → a + (b - a) = b`. -/
theorem add_sub_cancel_of_le_sub2_native {a b : ℕ} (h : a ≤ b - 2) :
    a + (b - a) = b := by
  omega

/-- Pure native Euclidean remainder cancellation using `Nat.lt_or_ge`:
    if `r_rem < m` and `m * K1 + r_rem = m * K2`, then `r_rem = 0`. -/
theorem eq_zero_of_mul_add_eq_mul_of_lt
    {m K1 K2 r_rem : ℕ} (h_lt : r_rem < m) (h_eq : m * K1 + r_rem = m * K2) :
    r_rem = 0 := by
  match Nat.lt_or_ge K1 K2 with
  | Or.inl h_gt =>
    have h_succ : K1 + 1 ≤ K2 := h_gt
    have h_mul : m * (K1 + 1) ≤ m * K2 := Nat.mul_le_mul_left m h_succ
    rw [Nat.left_distrib m K1 1, Nat.mul_one] at h_mul
    omega
  | Or.inr h_le =>
    have h_mul : m * K2 ≤ m * K1 := Nat.mul_le_mul_left m h_le
    omega

/-- **Theorem 1.1 (`bilateral_omc_target_lane_ne_native`):**
    Division-free target-side OMC exclusion in pure `Init` arithmetic:
    if `r * q + p = N`, `0 < m`, and `1 ≤ p % m`, then `(r * (q % m)) % m ≠ N % m`. -/
theorem bilateral_omc_target_lane_ne_native
    {N r q p m : ℕ} (h_sum : r * q + p = N) (hm_pos : 0 < m) (hp_mod_pos : 1 ≤ p % m) :
    (r * (q % m)) % m ≠ N % m := by
  intro h_same
  have hq_div : m * (q / m) + q % m = q := Nat.div_add_mod q m
  have hrc_div : m * ((r * (q % m)) / m) + (r * (q % m)) % m = r * (q % m) :=
    Nat.div_add_mod (r * (q % m)) m
  have hp_div : m * (p / m) + p % m = p := Nat.div_add_mod p m
  have hN_div : m * (N / m) + N % m = N := Nat.div_add_mod N m
  have hrq_expand : r * q = m * (r * (q / m)) + r * (q % m) := by
    calc r * q
      _ = r * (m * (q / m) + q % m) := by rw [hq_div]
      _ = r * (m * (q / m)) + r * (q % m) := Nat.left_distrib r (m * (q / m)) (q % m)
      _ = (r * m) * (q / m) + r * (q % m) := by rw [← Nat.mul_assoc r m (q / m)]
      _ = (m * r) * (q / m) + r * (q % m) := by rw [Nat.mul_comm r m]
      _ = m * (r * (q / m)) + r * (q % m) := by rw [Nat.mul_assoc m r (q / m)]
  have hK1_expand :
      m * (r * (q / m) + (r * (q % m)) / m + p / m) =
        m * (r * (q / m)) + m * ((r * (q % m)) / m) + m * (p / m) := by
    rw [Nat.left_distrib m (r * (q / m) + (r * (q % m)) / m) (p / m),
        Nat.left_distrib m (r * (q / m)) ((r * (q % m)) / m)]
  have h_mul_eq :
      m * (r * (q / m) + (r * (q % m)) / m + p / m) + p % m = m * (N / m) := by
    omega
  have hp_lt_m : p % m < m := Nat.mod_lt p hm_pos
  have hp_zero : p % m = 0 := eq_zero_of_mul_add_eq_mul_of_lt hp_lt_m h_mul_eq
  omega

/-- Explicit bridge connecting `q ∈ wr2ShearContractedFiber N r` directly to
    `hyperbolicPrimeFiber_pinch_cutoff_and_shear` (`WR2Step199`) without unfolding
    large exponent terms into `omega`. -/
theorem wr2ShearContractedFiber_to_hyperbolic_and_sum
    {N r q : ℕ} (hq : q ∈ wr2ShearContractedFiber N r) :
    q ∈ hyperbolicPrimeFiber N r ∧
    q ≤ (N - 2) / r ∧
    r * q ≤ N - 2 ∧
    r * q + (N - r * q) = N := by
  have hq_hyp : q ∈ hyperbolicPrimeFiber N r := by
    rw [wr2ShearContractedFiber, mem_filter] at hq
    exact hq.1
  have h_rq_sub2 : r * q ≤ N - 2 :=
    (hyperbolicPrimeFiber_pinch_cutoff_and_shear hq_hyp).1
  have h_sum : r * q + (N - r * q) = N :=
    add_sub_cancel_of_le_sub2_native h_rq_sub2
  have h_q_le : q ≤ (N - 2) / r := by
    rw [hyperbolicPrimeFiber, mem_filter, mem_range] at hq_hyp
    have h_lt : q < (N - 2) / r + 1 := hq_hyp.1
    omega
  exact ⟨hq_hyp, h_q_le, h_rq_sub2, h_sum⟩

/-- Target-sieved sub-fiber of `wr2ShearContractedFiber N r` where `m < N - r * q`. -/
def wr2TargetSievedFiber (N r m : ℕ) : Finset ℕ :=
  (wr2ShearContractedFiber N r).filter (fun q : ℕ => m < N - r * q)

/-- Bilateral OMC admissible residue set modulo `m`:
    excludes both the factor-side zero lane (`c = 0`) and the target-side lane (`(r * c) % m = N % m`). -/
def bilateralOMCResidues (N r m : ℕ) : Finset ℕ :=
  (range m).filter (fun c : ℕ => 1 ≤ c ∧ (r * c) % m ≠ N % m)

/-- **Theorem 1.2 (`targetSievedFiber_admissible_subset_bilateralOMCResidues`):**
    For every auxiliary modulus `m` with `2 ≤ m ≤ r`, the active residue classes of
    `wr2TargetSievedFiber N r m` are strictly contained in `bilateralOMCResidues N r m`. -/
theorem targetSievedFiber_admissible_subset_bilateralOMCResidues
    {N r m : ℕ} (hm2 : 2 ≤ m) (hmr : m ≤ r) :
    admissibleFiberResidues (wr2TargetSievedFiber N r m) m ⊆
      bilateralOMCResidues N r m := by
  intro c hc
  rw [admissibleFiberResidues, mem_image] at hc
  obtain ⟨q, hq, rfl⟩ := hc
  rw [wr2TargetSievedFiber, mem_filter] at hq
  obtain ⟨hq_fiber, hm_lt_p⟩ := hq
  have hm_pos : 0 < m := by omega
  have hr_pos : 0 < r := by omega
  have h_omc := wr2ShearContractedFiber_lower_pinch_and_bilateral_omc hr_pos hq_fiber
  have hq_mod_pos : 1 ≤ q % m := h_omc.2.1 m hm2 hmr
  have hp_mod_pos : 1 ≤ (N - r * q) % m := h_omc.2.2 m hm2 hm_lt_p
  have h_sum : r * q + (N - r * q) = N :=
    (wr2ShearContractedFiber_to_hyperbolic_and_sum hq_fiber).2.2.2
  have h_target_ne : (r * (q % m)) % m ≠ N % m :=
    bilateral_omc_target_lane_ne_native h_sum hm_pos hp_mod_pos
  have h_mod_lt : q % m < m := Nat.mod_lt q hm_pos
  rw [bilateralOMCResidues, mem_filter, mem_range]
  exact ⟨h_mod_lt, hq_mod_pos, h_target_ne⟩

/-!
## Section 2: Arbitrary Lower-Floor Shifted-Window Stride Bounds (`L ≤ q`)
-/

/-- Sub-fiber of `wr2ShearContractedFiber N r` bounded below by an arbitrary floor `L`
    (such as `L = r + 2` or the `5000/4469` lower-pinch floor `L_pinch`). -/
def wr2FloorSubfiber (N r L : ℕ) : Finset ℕ :=
  (wr2ShearContractedFiber N r).filter (fun q : ℕ => L ≤ q)

/-- **Theorem 2.1 (`wr2FloorSubfiber_slice_card_le_shifted_quotient_diff`):**
    For ANY floor `L : ℕ`, modulus `m > 0`, and residue class `c : ℕ`,
    `(residueClassSlice (wr2FloorSubfiber N r L) m c).card ≤ (((N - 2) / r) / m - L / m) + 1`. -/
theorem wr2FloorSubfiber_slice_card_le_shifted_quotient_diff
    {N r L m : ℕ} (hm_pos : 0 < m) (c : ℕ) :
    (residueClassSlice (wr2FloorSubfiber N r L) m c).card ≤
      (((N - 2) / r) / m - L / m) + 1 := by
  have h_sub :
      residueClassSlice (wr2FloorSubfiber N r L) m c ⊆
        (range ((((N - 2) / r) / m - L / m) + 1)).image
          (reconstructFromShiftedQuotient m (L / m) c) := by
    intro q hq
    rw [residueClassSlice, mem_filter, wr2FloorSubfiber, mem_filter] at hq
    obtain ⟨⟨hq_fiber, h_L_le_q⟩, h_mod_eq⟩ := hq
    have h_q_le : q ≤ (N - 2) / r :=
      (wr2ShearContractedFiber_to_hyperbolic_and_sum hq_fiber).2.1
    have h_q_div_ge : L / m ≤ q / m := div_le_div_right_native hm_pos h_L_le_q
    have h_q_div_le : q / m ≤ ((N - 2) / r) / m := div_le_div_right_native hm_pos h_q_le
    have h_div_mod : m * (q / m) + q % m = q := Nat.div_add_mod q m
    have h_add_sub : L / m + (q / m - L / m) = q / m := by omega
    rw [mem_image]
    refine ⟨q / m - L / m, ?_, ?_⟩
    · rw [mem_range]
      omega
    · unfold reconstructFromShiftedQuotient
      rw [h_add_sub]
      omega
  have h_card := Nat.le_trans (card_le_card h_sub) card_image_le
  rw [card_range] at h_card
  exact h_card

/-- **Theorem 2.2 (`wr2FloorSubfiber_shifted_slice_card_le_window_div`):**
    For ANY floor `L : ℕ`, modulus `m > 0`, and shifted remainder `s : ℕ`,
    `(shiftedResidueSlice (wr2FloorSubfiber N r L) L m s).card ≤ ((N - 2) / r - L) / m + 1`. -/
theorem wr2FloorSubfiber_shifted_slice_card_le_window_div
    {N r L m : ℕ} (hm_pos : 0 < m) (s : ℕ) :
    (shiftedResidueSlice (wr2FloorSubfiber N r L) L m s).card ≤
      ((N - 2) / r - L) / m + 1 := by
  have h_sub :
      shiftedResidueSlice (wr2FloorSubfiber N r L) L m s ⊆
        (range (((N - 2) / r - L) / m + 1)).image
          (reconstructFromWindowQuotient L m s) := by
    intro q hq
    rw [shiftedResidueSlice, mem_filter, wr2FloorSubfiber, mem_filter] at hq
    obtain ⟨⟨hq_fiber, h_L_le_q⟩, h_shift_mod⟩ := hq
    have h_q_le : q ≤ (N - 2) / r :=
      (wr2ShearContractedFiber_to_hyperbolic_and_sum hq_fiber).2.1
    have h_diff_le : q - L ≤ (N - 2) / r - L := by omega
    have h_div_mod : m * ((q - L) / m) + (q - L) % m = q - L :=
      Nat.div_add_mod (q - L) m
    have h_mul_le : m * ((q - L) / m) ≤ (N - 2) / r - L := by omega
    have h_quot_le : (q - L) / m ≤ ((N - 2) / r - L) / m :=
      le_div_of_mul_le_native hm_pos h_mul_le
    rw [mem_image]
    refine ⟨(q - L) / m, ?_, ?_⟩
    · rw [mem_range]
      omega
    · unfold reconstructFromWindowQuotient
      omega
  have h_card := Nat.le_trans (card_le_card h_sub) card_image_le
  rw [card_range] at h_card
  exact h_card

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.eq_zero_of_mul_add_eq_mul_of_lt
#print axioms WuPaper.ESZerosBridge.bilateral_omc_target_lane_ne_native
#print axioms WuPaper.ESZerosBridge.targetSievedFiber_admissible_subset_bilateralOMCResidues
#print axioms WuPaper.ESZerosBridge.wr2FloorSubfiber_slice_card_le_shifted_quotient_diff
#print axioms WuPaper.ESZerosBridge.wr2FloorSubfiber_shifted_slice_card_le_window_div
