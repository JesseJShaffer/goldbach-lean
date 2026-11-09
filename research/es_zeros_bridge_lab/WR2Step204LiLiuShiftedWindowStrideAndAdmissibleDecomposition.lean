import WR2Step202LiLiuLowerPinchAndMod65QuotientStrideWeld

set_option exponentiation.threshold 10000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step204LiLiuShiftedWindowStrideAndAdmissibleDecomposition.lean — Shifted-Window Stride & Admissible Fiber Decomposition for `D19 N`

Welds the Shifted-Window Quotient Stride (`(N / r - (r + 2)) / m + 1` and
`(N / r) / m - (r + 2) / m + 1`) and the Admissible Residue `Finset.biUnion` decomposition
directly into the `Goldbach.All` (`D19 N`) branch:

1. **Shifted Quotient-Difference & Window Stride Bounds on `liliuShearContractedFiber`
   (`liliuResidueSlice_card_le_shifted_quotient_diff`,
   `liliuShiftedResidueSlice_card_le_window_div`):**
   Subtracts the lower floor `r + 2` from the hyperbolic ceiling `N / r` before dividing by `m`.
2. **Tightened Odd-Prime Half-Window Fiber Bound (`liliuShearContractedFiber_card_le_shifted_half_window`):**
   Proves that for every odd `r` (`r % 2 = 1`),
   `(liliuShearContractedFiber N r).card ≤ (N / r - (r + 2)) / 2 + 1`.
3. **Admissible Residue `Finset.biUnion` Decomposition & OMC Exclusion
   (`liliuFiber_eq_biUnion_admissible_slices`, `liliuAdmissibleResidues_subset_nonZero`):**
   Decomposes `liliuShearContractedFiber N r` across `liliuAdmissibleResidues N r m` and
   eliminates `c = 0` for all `2 ≤ m ≤ r`.
4. **Master 27-Module Capstone (`master_27module_D19_shifted_window_and_admissible_fiber_capstone`):**
   Unites `Goldbach.one_plus_one_nine_count` (`liuMainTerm0004 N < (D19 N : ℝ)`), the
   shifted-window stride bounds, the admissible residue `biUnion` decomposition, and the
   Factorial Lighthouse next-prime generator.
-/

/-!
## Section 1: Monotonic Native Division & Shifted-Window Stride Bounds for Li–Liu (`9, 10`)
-/

/-- Pure native proof that `0 < m` and `L ≤ q` implies `L / m ≤ q / m`. -/
theorem div_le_div_right_liliu {L q m : ℕ} (hm_pos : 0 < m) (hle : L ≤ q) :
    L / m ≤ q / m := by
  have h_div_mod : m * (L / m) + L % m = L := Nat.div_add_mod L m
  have h_mul_le : m * (L / m) ≤ q := by omega
  exact le_div_of_mul_le_liliu hm_pos h_mul_le

/-- Shifted quotient reconstruction map `j ↦ m * (L_div + j) + c`. -/
def liliuReconstructShiftedQuotient (m L_div c j : ℕ) : ℕ :=
  m * (L_div + j) + c

/-- **Theorem 1.1 (`liliuResidueSlice_card_le_shifted_quotient_diff`):**
    For every modulus `m > 0` and residue class `c`,
    `(liliuResidueSlice N r m c).card ≤ ((N / r) / m - (r + 2) / m) + 1`. -/
theorem liliuResidueSlice_card_le_shifted_quotient_diff
    {N r m : ℕ} (hm_pos : 0 < m) (c : ℕ) :
    (liliuResidueSlice N r m c).card ≤ ((N / r) / m - (r + 2) / m) + 1 := by
  have h_sub :
      liliuResidueSlice N r m c ⊆
        (range (((N / r) / m - (r + 2) / m) + 1)).image
          (liliuReconstructShiftedQuotient m ((r + 2) / m) c) := by
    intro q hq
    rw [liliuResidueSlice, mem_filter, liliuShearContractedFiber, mem_filter,
        liliuHyperbolicPrimeFiber, mem_filter, mem_range] at hq
    obtain ⟨⟨⟨hq_lt_div, _, _, h_r2_le_q, _⟩, _⟩, h_mod_eq⟩ := hq
    have h_q_le : q ≤ N / r := by omega
    have h_q_div_ge : (r + 2) / m ≤ q / m := div_le_div_right_liliu hm_pos h_r2_le_q
    have h_q_div_le : q / m ≤ (N / r) / m := div_le_div_right_liliu hm_pos h_q_le
    have h_div_mod : m * (q / m) + q % m = q := Nat.div_add_mod q m
    have h_add_sub : (r + 2) / m + (q / m - (r + 2) / m) = q / m := by omega
    rw [mem_image]
    refine ⟨q / m - (r + 2) / m, ?_, ?_⟩
    · rw [mem_range]
      omega
    · unfold liliuReconstructShiftedQuotient
      rw [h_add_sub]
      omega
  have h_card := Nat.le_trans (card_le_card h_sub) card_image_le
  rw [card_range] at h_card
  exact h_card

/-- Shifted-origin residue slice `{q ∈ liliuShearContractedFiber N r | (q - (r + 2)) % m = s}`. -/
def liliuShiftedResidueSlice (N r m s : ℕ) : Finset ℕ :=
  (liliuShearContractedFiber N r).filter (fun q : ℕ => (q - (r + 2)) % m = s)

/-- Window quotient reconstruction map `k ↦ (r + 2) + (m * k + s)`. -/
def liliuReconstructWindowQuotient (r m s k : ℕ) : ℕ :=
  (r + 2) + (m * k + s)

/-- **Theorem 1.2 (`liliuShiftedResidueSlice_card_le_window_div`):**
    For every modulus `m > 0` and shifted remainder `s`,
    `(liliuShiftedResidueSlice N r m s).card ≤ (N / r - (r + 2)) / m + 1`. -/
theorem liliuShiftedResidueSlice_card_le_window_div
    {N r m : ℕ} (hm_pos : 0 < m) (s : ℕ) :
    (liliuShiftedResidueSlice N r m s).card ≤ (N / r - (r + 2)) / m + 1 := by
  have h_sub :
      liliuShiftedResidueSlice N r m s ⊆
        (range ((N / r - (r + 2)) / m + 1)).image
          (liliuReconstructWindowQuotient r m s) := by
    intro q hq
    rw [liliuShiftedResidueSlice, mem_filter, liliuShearContractedFiber, mem_filter,
        liliuHyperbolicPrimeFiber, mem_filter, mem_range] at hq
    obtain ⟨⟨⟨hq_lt_div, _, _, h_r2_le_q, _⟩, _⟩, h_shift_mod⟩ := hq
    have h_q_le : q ≤ N / r := by omega
    have h_diff_le : q - (r + 2) ≤ N / r - (r + 2) := by omega
    have h_div_mod : m * ((q - (r + 2)) / m) + (q - (r + 2)) % m = q - (r + 2) :=
      Nat.div_add_mod (q - (r + 2)) m
    have h_mul_le : m * ((q - (r + 2)) / m) ≤ N / r - (r + 2) := by omega
    have h_quot_le : (q - (r + 2)) / m ≤ (N / r - (r + 2)) / m :=
      le_div_of_mul_le_liliu hm_pos h_mul_le
    rw [mem_image]
    refine ⟨(q - (r + 2)) / m, ?_, ?_⟩
    · rw [mem_range]
      omega
    · unfold liliuReconstructWindowQuotient
      omega
  have h_card := Nat.le_trans (card_le_card h_sub) card_image_le
  rw [card_range] at h_card
  exact h_card

/-- **Theorem 1.3 (`liliuShearContractedFiber_card_le_shifted_half_window`):**
    For every odd `r` (`r % 2 = 1`),
    `(liliuShearContractedFiber N r).card ≤ (N / r - (r + 2)) / 2 + 1`. -/
theorem liliuShearContractedFiber_card_le_shifted_half_window
    {N r : ℕ} (hr_odd : r % 2 = 1) :
    (liliuShearContractedFiber N r).card ≤ (N / r - (r + 2)) / 2 + 1 := by
  have h_eq :
      liliuShearContractedFiber N r = liliuShiftedResidueSlice N r 2 0 := by
    ext q
    rw [liliuShiftedResidueSlice, mem_filter]
    constructor
    · intro hq
      have hq_copy := hq
      rw [liliuShearContractedFiber, mem_filter, liliuHyperbolicPrimeFiber, mem_filter] at hq_copy
      have hq_odd : q % 2 = 1 := hq_copy.1.2.2.1
      have h_r2_le_q : r + 2 ≤ q := hq_copy.1.2.2.2.1
      exact ⟨hq, by omega⟩
    · intro hq
      exact hq.1
  rw [h_eq]
  exact liliuShiftedResidueSlice_card_le_window_div (by omega : 0 < 2) 0

/-!
## Section 2: Admissible Residue `Finset.biUnion` Decomposition & OMC Lane Exclusion
-/

/-- The active residue classes `c = q % m` populated by `liliuShearContractedFiber N r`. -/
def liliuAdmissibleResidues (N r m : ℕ) : Finset ℕ :=
  (liliuShearContractedFiber N r).image (fun q : ℕ => q % m)

/-- The `m - 1` non-zero residue classes `{1, ..., m - 1}` modulo `m`. -/
def liliuNonZeroResidues (m : ℕ) : Finset ℕ :=
  (range m).filter (fun c : ℕ => 1 ≤ c)

/-- **Theorem 2.1 (`liliuFiber_eq_biUnion_admissible_slices`):**
    Exact decomposition of `liliuShearContractedFiber N r` across `liliuAdmissibleResidues N r m`. -/
theorem liliuFiber_eq_biUnion_admissible_slices (N r m : ℕ) :
    liliuShearContractedFiber N r =
      (liliuAdmissibleResidues N r m).biUnion (liliuResidueSlice N r m) := by
  ext q
  rw [mem_biUnion]
  constructor
  · intro hq
    refine ⟨q % m, ?_, ?_⟩
    · rw [liliuAdmissibleResidues, mem_image]
      exact ⟨q, hq, rfl⟩
    · rw [liliuResidueSlice, mem_filter]
      exact ⟨hq, rfl⟩
  · intro hbi
    obtain ⟨_, _, hq_slice⟩ := hbi
    rw [liliuResidueSlice, mem_filter] at hq_slice
    exact hq_slice.1

/-- **Theorem 2.2 (`liliuAdmissibleResidues_subset_nonZero`):**
    For every modulus `m` with `2 ≤ m ≤ r`, `0` is excluded from `liliuAdmissibleResidues N r m`. -/
theorem liliuAdmissibleResidues_subset_nonZero
    {N r m : ℕ} (hm2 : 2 ≤ m) (hmr : m ≤ r) :
    liliuAdmissibleResidues N r m ⊆ liliuNonZeroResidues m := by
  intro c hc
  rw [liliuAdmissibleResidues, mem_image] at hc
  obtain ⟨q, hq, rfl⟩ := hc
  have hm_pos : 0 < m := by omega
  have hr_pos : 0 < r := by omega
  have h_mod_lt : q % m < m := Nat.mod_lt q hm_pos
  have h_mod_pos : 1 ≤ q % m :=
    (liliuShearContractedFiber_lower_pinch_10_9 hr_pos hq).2.2 m hm2 hmr
  rw [liliuNonZeroResidues, mem_filter, mem_range]
  exact ⟨h_mod_lt, h_mod_pos⟩

/-!
## Section 3: Master 27-Module Capstone Welding `D19 N`, Shifted Strides & Admissible Fibers
-/

/-- **Master Theorem 3.1 (`master_27module_D19_shifted_window_and_admissible_fiber_capstone`):**
    Complete 27-Module Capstone uniting `Goldbach.one_plus_one_nine_count` (`D19 N`),
    the shifted-window fiber bounds (`(N / r - (r + 2)) / 2 + 1` and `((N / r) / 65 - (r + 2) / 65) + 1`),
    the `Finset.biUnion` decomposition over `liliuAdmissibleResidues N r m`, and the
    Factorial Lighthouse next-prime generator (`hasNextPrimeConnection_unconditional`). -/
theorem master_27module_D19_shifted_window_and_admissible_fiber_capstone :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (∀ r m : ℕ,
        liliuShearContractedFiber N r =
          (liliuAdmissibleResidues N r m).biUnion (liliuResidueSlice N r m)) ∧
      (∀ r : ℕ, r % 2 = 1 →
        (liliuShearContractedFiber N r).card ≤ (N / r - (r + 2)) / 2 + 1 ∧
        ∀ c : ℕ, (liliuResidueSlice N r 65 c).card ≤ ((N / r) / 65 - (r + 2) / 65) + 1) ∧
      (fiveupPinchedQRSubfilter 9 10 N).card ≤
        1 + ((pinchedOddPrimes919 N).biUnion (liliuShearContractedFiberPairs N)).card ∧
      ((((1 + ((pinchedOddPrimes919 N).biUnion (liliuShearContractedFiberPairs N)).card : ℕ) : ℝ) ≤
          liuMainTerm0004 N) →
        ∃ p q p_next' : ℕ,
          Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next' ∧ IsPrimeNat p_next') := by
  obtain ⟨K, hK4, hCap⟩ := master_25module_D19_pinched_stride_goldbach_capstone
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven
  have hM := hCap N hNK hEven
  refine ⟨hM.1, fun r m => liliuFiber_eq_biUnion_admissible_slices N r m, ?_,
          hM.2.2.2.2.1, hM.2.2.2.2.2⟩
  intro r hr_odd
  refine ⟨liliuShearContractedFiber_card_le_shifted_half_window hr_odd, ?_⟩
  intro c
  exact liliuResidueSlice_card_le_shifted_quotient_diff (by omega : 0 < 65) c

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.div_le_div_right_liliu
#print axioms WuPaper.ESZerosBridge.liliuResidueSlice_card_le_shifted_quotient_diff
#print axioms WuPaper.ESZerosBridge.liliuShiftedResidueSlice_card_le_window_div
#print axioms WuPaper.ESZerosBridge.liliuShearContractedFiber_card_le_shifted_half_window
#print axioms WuPaper.ESZerosBridge.liliuFiber_eq_biUnion_admissible_slices
#print axioms WuPaper.ESZerosBridge.liliuAdmissibleResidues_subset_nonZero
#print axioms WuPaper.ESZerosBridge.master_27module_D19_shifted_window_and_admissible_fiber_capstone
