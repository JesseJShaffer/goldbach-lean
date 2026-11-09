import WR2Step201WR2LowerPinchCancellationAndQuotientStrideBound

set_option exponentiation.threshold 10000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step203WR2ShiftedWindowStrideAndFiberBiUnion.lean — Shifted-Window Quotient Stride & Admissible Fiber `biUnion`

Tightens the per-prime fiber stride bounds from `WR2Step201` by subtracting the lower
floor `L = r + 2` before dividing by the modulus stride `m`, and decomposes each fiber
across its admissible residue classes:

1. **Monotonic Native Division (`div_le_div_right_native`):**
   Proves `L ≤ q → L / m ≤ q / m` in 3 lines using `Nat.div_add_mod` and `le_div_of_mul_le_native`.
2. **Shifted Quotient-Difference Slice Bound (`wr2ShearContractedFiber_slice_card_le_shifted_quotient_diff`):**
   Maps `q ∈ residueClassSlice (wr2ShearContractedFiber N r) m c` to the shifted quotient
   `j = q / m - (r + 2) / m`, proving
   `(residueClassSlice (wr2ShearContractedFiber N r) m c).card ≤ (((N - 2) / r) / m - (r + 2) / m) + 1`.
3. **Shifted-Origin Window Slice Bound (`wr2ShearContractedFiber_shifted_slice_card_le_window_div`):**
   Maps `q` with `(q - (r + 2)) % m = s` to `k = (q - (r + 2)) / m`, proving
   `(shiftedResidueSlice (wr2ShearContractedFiber N r) (r + 2) m s).card ≤ ((N - 2) / r - (r + 2)) / m + 1`
   and tightening the odd-prime fiber bound to `((N - 2) / r - (r + 2)) / 2 + 1`.
4. **Admissible Residue `Finset.biUnion` Decomposition (`fiber_eq_biUnion_admissible_slices`,
   `admissibleFiberResidues_subset_nonZeroResidues`):**
   Decomposes `wr2ShearContractedFiber N r` as the union over `admissibleFiberResidues` and
   proves that for all `2 ≤ m ≤ r`, `0` is excluded (`card ≤ m - 1`).
-/

/-!
## Section 1: Pure Native Monotonic Division & Shifted Quotient-Difference Slice Bound
-/

/-- Pure native proof that `0 < m` and `L ≤ q` implies `L / m ≤ q / m`, directly connected
    to `Nat.div_add_mod` and `le_div_of_mul_le_native` (`WR2Step197`). -/
theorem div_le_div_right_native {L q m : ℕ} (hm_pos : 0 < m) (hle : L ≤ q) :
    L / m ≤ q / m := by
  have h_div_mod : m * (L / m) + L % m = L := Nat.div_add_mod L m
  have h_mul_le : m * (L / m) ≤ q := by omega
  exact le_div_of_mul_le_native hm_pos h_mul_le

/-- Shifted quotient reconstruction map `j ↦ m * (L_div + j) + c`. -/
def reconstructFromShiftedQuotient (m L_div c j : ℕ) : ℕ :=
  m * (L_div + j) + c

/-- **Theorem 1.1 (`wr2ShearContractedFiber_slice_card_le_shifted_quotient_diff`):**
    For every modulus `m > 0` and residue class `c`, the cardinality of
    `residueClassSlice (wr2ShearContractedFiber N r) m c` is bounded by the shifted
    quotient difference `(((N - 2) / r) / m - (r + 2) / m) + 1`. -/
theorem wr2ShearContractedFiber_slice_card_le_shifted_quotient_diff
    {N r m : ℕ} (hm_pos : 0 < m) (c : ℕ) :
    (residueClassSlice (wr2ShearContractedFiber N r) m c).card ≤
      (((N - 2) / r) / m - (r + 2) / m) + 1 := by
  have h_sub :
      residueClassSlice (wr2ShearContractedFiber N r) m c ⊆
        (range ((((N - 2) / r) / m - (r + 2) / m) + 1)).image
          (reconstructFromShiftedQuotient m ((r + 2) / m) c) := by
    intro q hq
    rw [residueClassSlice, mem_filter, wr2ShearContractedFiber, mem_filter,
        hyperbolicPrimeFiber, mem_filter, mem_range] at hq
    obtain ⟨⟨⟨hq_lt_div, _, _, h_r2_le_q, _⟩, _⟩, h_mod_eq⟩ := hq
    have h_q_le : q ≤ (N - 2) / r := by omega
    have h_q_div_ge : (r + 2) / m ≤ q / m := div_le_div_right_native hm_pos h_r2_le_q
    have h_q_div_le : q / m ≤ ((N - 2) / r) / m := div_le_div_right_native hm_pos h_q_le
    have h_div_mod : m * (q / m) + q % m = q := Nat.div_add_mod q m
    have h_add_sub : (r + 2) / m + (q / m - (r + 2) / m) = q / m := by omega
    rw [mem_image]
    refine ⟨q / m - (r + 2) / m, ?_, ?_⟩
    · rw [mem_range]
      omega
    · unfold reconstructFromShiftedQuotient
      rw [h_add_sub]
      omega
  have h_card := Nat.le_trans (card_le_card h_sub) card_image_le
  rw [card_range] at h_card
  exact h_card

/-!
## Section 2: Shifted-Origin Window Slice Bound (`((N - 2) / r - (r + 2)) / m + 1`)
-/

/-- The shifted-origin residue slice `{q ∈ S | (q - L) % m = s}`. -/
def shiftedResidueSlice (S : Finset ℕ) (L m s : ℕ) : Finset ℕ :=
  S.filter (fun q : ℕ => (q - L) % m = s)

/-- Window quotient reconstruction map `k ↦ L + (m * k + s)`. -/
def reconstructFromWindowQuotient (L m s k : ℕ) : ℕ :=
  L + (m * k + s)

/-- **Theorem 2.1 (`wr2ShearContractedFiber_shifted_slice_card_le_window_div`):**
    For every modulus `m > 0` and shifted remainder `s`,
    `(shiftedResidueSlice (wr2ShearContractedFiber N r) (r + 2) m s).card ≤ ((N - 2) / r - (r + 2)) / m + 1`. -/
theorem wr2ShearContractedFiber_shifted_slice_card_le_window_div
    {N r m : ℕ} (hm_pos : 0 < m) (s : ℕ) :
    (shiftedResidueSlice (wr2ShearContractedFiber N r) (r + 2) m s).card ≤
      ((N - 2) / r - (r + 2)) / m + 1 := by
  have h_sub :
      shiftedResidueSlice (wr2ShearContractedFiber N r) (r + 2) m s ⊆
        (range (((N - 2) / r - (r + 2)) / m + 1)).image
          (reconstructFromWindowQuotient (r + 2) m s) := by
    intro q hq
    rw [shiftedResidueSlice, mem_filter, wr2ShearContractedFiber, mem_filter,
        hyperbolicPrimeFiber, mem_filter, mem_range] at hq
    obtain ⟨⟨⟨hq_lt_div, _, _, h_r2_le_q, _⟩, _⟩, h_shift_mod⟩ := hq
    have h_q_le : q ≤ (N - 2) / r := by omega
    have h_diff_le : q - (r + 2) ≤ (N - 2) / r - (r + 2) := by omega
    have h_div_mod : m * ((q - (r + 2)) / m) + (q - (r + 2)) % m = q - (r + 2) :=
      Nat.div_add_mod (q - (r + 2)) m
    have h_mul_le : m * ((q - (r + 2)) / m) ≤ (N - 2) / r - (r + 2) := by omega
    have h_quot_le : (q - (r + 2)) / m ≤ ((N - 2) / r - (r + 2)) / m :=
      le_div_of_mul_le_native hm_pos h_mul_le
    rw [mem_image]
    refine ⟨(q - (r + 2)) / m, ?_, ?_⟩
    · rw [mem_range]
      omega
    · unfold reconstructFromWindowQuotient
      omega
  have h_card := Nat.le_trans (card_le_card h_sub) card_image_le
  rw [card_range] at h_card
  exact h_card

/-- **Theorem 2.2 (`wr2ShearContractedFiber_card_le_shifted_half_window`):**
    When `r` is odd (`r % 2 = 1`), every `q ∈ wr2ShearContractedFiber N r` is odd (`q % 2 = 1`),
    so `(q - (r + 2)) % 2 = 0`, tightening the whole fiber bound to
    `(wr2ShearContractedFiber N r).card ≤ ((N - 2) / r - (r + 2)) / 2 + 1`. -/
theorem wr2ShearContractedFiber_card_le_shifted_half_window
    {N r : ℕ} (hr_odd : r % 2 = 1) :
    (wr2ShearContractedFiber N r).card ≤ ((N - 2) / r - (r + 2)) / 2 + 1 := by
  have h_eq :
      wr2ShearContractedFiber N r =
        shiftedResidueSlice (wr2ShearContractedFiber N r) (r + 2) 2 0 := by
    ext q
    rw [shiftedResidueSlice, mem_filter]
    constructor
    · intro hq
      have hq_copy := hq
      rw [wr2ShearContractedFiber, mem_filter, hyperbolicPrimeFiber, mem_filter] at hq_copy
      have hq_odd : q % 2 = 1 := hq_copy.1.2.2.1
      have h_r2_le_q : r + 2 ≤ q := hq_copy.1.2.2.2.1
      exact ⟨hq, by omega⟩
    · intro hq
      exact hq.1
  rw [h_eq]
  exact wr2ShearContractedFiber_shifted_slice_card_le_window_div (by omega : 0 < 2) 0

/-!
## Section 3: Admissible Residue `Finset.biUnion` Decomposition & Non-Zero Lane Contraction
-/

/-- The active residue classes `c = q % m` populated by a `Finset ℕ`. -/
def admissibleFiberResidues (S : Finset ℕ) (m : ℕ) : Finset ℕ :=
  S.image (fun q : ℕ => q % m)

/-- The `m - 1` non-zero residue classes `{1, 2, ..., m - 1}` modulo `m`. -/
def nonZeroResidues (m : ℕ) : Finset ℕ :=
  (range m).filter (fun c : ℕ => 1 ≤ c)

/-- **Theorem 3.1 (`fiber_eq_biUnion_admissible_slices`):**
    Exact decomposition of any fiber `S : Finset ℕ` into the union of its populated
    residue progression slices over `admissibleFiberResidues S m`. -/
theorem fiber_eq_biUnion_admissible_slices (S : Finset ℕ) (m : ℕ) :
    S = (admissibleFiberResidues S m).biUnion (residueClassSlice S m) := by
  ext q
  rw [mem_biUnion]
  constructor
  · intro hq
    refine ⟨q % m, ?_, ?_⟩
    · rw [admissibleFiberResidues, mem_image]
      exact ⟨q, hq, rfl⟩
    · rw [residueClassSlice, mem_filter]
      exact ⟨hq, rfl⟩
  · intro hbi
    obtain ⟨_, _, hq_slice⟩ := hbi
    rw [residueClassSlice, mem_filter] at hq_slice
    exact hq_slice.1

/-- **Theorem 3.2 (`admissibleFiberResidues_subset_nonZeroResidues`):**
    For every auxiliary modulus `m` with `2 ≤ m ≤ r`, `0` is excluded by OMC and
    `admissibleFiberResidues (wr2ShearContractedFiber N r) m ⊆ nonZeroResidues m`. -/
theorem admissibleFiberResidues_subset_nonZeroResidues
    {N r m : ℕ} (hm2 : 2 ≤ m) (hmr : m ≤ r) :
    admissibleFiberResidues (wr2ShearContractedFiber N r) m ⊆ nonZeroResidues m := by
  intro c hc
  rw [admissibleFiberResidues, mem_image] at hc
  obtain ⟨q, hq, rfl⟩ := hc
  have hm_pos : 0 < m := by omega
  have hr_pos : 0 < r := by omega
  have h_mod_lt : q % m < m := Nat.mod_lt q hm_pos
  have h_mod_pos : 1 ≤ q % m :=
    (wr2ShearContractedFiber_lower_pinch_and_bilateral_omc hr_pos hq).2.1 m hm2 hmr
  rw [nonZeroResidues, mem_filter, mem_range]
  exact ⟨h_mod_lt, h_mod_pos⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.div_le_div_right_native
#print axioms WuPaper.ESZerosBridge.wr2ShearContractedFiber_slice_card_le_shifted_quotient_diff
#print axioms WuPaper.ESZerosBridge.wr2ShearContractedFiber_shifted_slice_card_le_window_div
#print axioms WuPaper.ESZerosBridge.wr2ShearContractedFiber_card_le_shifted_half_window
#print axioms WuPaper.ESZerosBridge.fiber_eq_biUnion_admissible_slices
#print axioms WuPaper.ESZerosBridge.admissibleFiberResidues_subset_nonZeroResidues
