import WR2Step205WR2BilateralOMCLaneExclusionAndGeneralFloorStride

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step207WR2Mod130CompositeStrideAndBilateralOMCCardBound.lean — Branch-Free CRT-130 Absorber & Bilateral OMC `m - 2` Bound

1. **Constructive `m - 1` and `m - 2` Cardinality Bounds on `bilateralOMCResidues N r m`
   (`bilateralOMCResidues_card_le_sub_one`, `bilateralOMCResidues_card_le_sub_two_of_collision`):**
   Uses explicit `expandAvoidLane_of_lt` and `expandAvoidLane_of_not_lt` reductions to prove
   `(bilateralOMCResidues N r m).card ≤ m - 1` and, when a target collision lane `1 ≤ c₀ < m`
   exists, `(bilateralOMCResidues N r m).card ≤ m - 2`.
2. **Branch-Free Parity-CRT Absorber (`crtOddLift130 c := c + 65 * (1 - c % 2)`):**
   Eliminates `if-then-else` branching so `omega` directly certifies `q % 130 = crtOddLift130 c`,
   cutting every Mod-65 fiber slice stride in half to `(((N - 2) / r) / 130 - L / 130) + 1`.
3. **Explicit Connection to Kernel Shear & Triple-QR Absorbers (`wr2FloorSubfiber_shear_and_triple_qr_locks`):**
   Connects every `q ∈ wr2FloorSubfiber N r L` directly to the division-free 5UP Reciprocal
   Shear congruence (`∀ m, ((r + q) * r) % m = (r * r + r * q) % m`), the Mod-63/64/65
   Triple-QR half-chord absorber equations, and the `r ^ 5000 ≤ q ^ 4469` lower pinch.
-/

/-!
## Section 1: Constructive `m - 1` and `m - 2` Cardinality Bounds on `bilateralOMCResidues`
-/

/-- Shift map `k ↦ k + 1` mapping `range (m - 1)` onto `{1, ..., m - 1}`. -/
def shiftSuccNat (k : ℕ) : ℕ :=
  k + 1

/-- Target-avoiding expansion map mapping `range (m - 2)` onto `{1, ..., m - 1} \ {c₀}`. -/
def expandAvoidLane (c₀ j : ℕ) : ℕ :=
  if j + 1 < c₀ then j + 1 else j + 2

theorem expandAvoidLane_of_lt {c₀ j : ℕ} (h : j + 1 < c₀) :
    expandAvoidLane c₀ j = j + 1 := by
  unfold expandAvoidLane
  rw [if_pos h]

theorem expandAvoidLane_of_not_lt {c₀ j : ℕ} (h : ¬ (j + 1 < c₀)) :
    expandAvoidLane c₀ j = j + 2 := by
  unfold expandAvoidLane
  rw [if_neg h]

/-- Pure linear inclusion: every `c` with `1 ≤ c < m` belongs to `(range (m - 1)).image shiftSuccNat`. -/
theorem mem_image_shiftSuccNat_of_pos_lt {m c : ℕ} (hc_pos : 1 ≤ c) (hc_lt : c < m) :
    c ∈ (range (m - 1)).image shiftSuccNat := by
  rw [mem_image]
  refine ⟨c - 1, ?_, ?_⟩
  · rw [mem_range]; omega
  · unfold shiftSuccNat; omega

/-- Pure linear inclusion: every `c` with `1 ≤ c < m` and `c ≠ c₀` (for `1 ≤ c₀ < m`)
    belongs to `(range (m - 2)).image (expandAvoidLane c₀)`. -/
theorem mem_image_expandAvoidLane_of_ne
    {m c₀ c : ℕ} (hc0_pos : 1 ≤ c₀) (hc0_lt : c₀ < m)
    (hc_pos : 1 ≤ c) (hc_lt : c < m) (hc_ne : c ≠ c₀) :
    c ∈ (range (m - 2)).image (expandAvoidLane c₀) := by
  rw [mem_image]
  if h_lt : c < c₀ then
    have h_cond : (c - 1) + 1 < c₀ := by omega
    refine ⟨c - 1, ?_, ?_⟩
    · rw [mem_range]; omega
    · rw [expandAvoidLane_of_lt h_cond]; omega
  else
    have h_not_cond : ¬ ((c - 2) + 1 < c₀) := by omega
    refine ⟨c - 2, ?_, ?_⟩
    · rw [mem_range]; omega
    · rw [expandAvoidLane_of_not_lt h_not_cond]; omega

/-- **Theorem 1.1 (`bilateralOMCResidues_card_le_sub_one`):**
    For every modulus `m : ℕ`, `(nonZeroResidues m).card ≤ m - 1` and
    `(bilateralOMCResidues N r m).card ≤ m - 1`. -/
theorem bilateralOMCResidues_card_le_sub_one (N r m : ℕ) :
    (nonZeroResidues m).card ≤ m - 1 ∧
    (bilateralOMCResidues N r m).card ≤ m - 1 := by
  have h_sub_nz : nonZeroResidues m ⊆ (range (m - 1)).image shiftSuccNat := by
    intro c hc
    rw [nonZeroResidues, mem_filter, mem_range] at hc
    exact mem_image_shiftSuccNat_of_pos_lt hc.2 hc.1
  have h_nz_le : (nonZeroResidues m).card ≤ m - 1 := by
    have h1 := Nat.le_trans (card_le_card h_sub_nz) card_image_le
    rw [card_range] at h1
    exact h1
  have h_sub_bil : bilateralOMCResidues N r m ⊆ nonZeroResidues m := by
    intro c hc
    rw [bilateralOMCResidues, mem_filter, mem_range] at hc
    rw [nonZeroResidues, mem_filter, mem_range]
    exact ⟨hc.1, hc.2.1⟩
  exact ⟨h_nz_le, Nat.le_trans (card_le_card h_sub_bil) h_nz_le⟩

/-- **Theorem 1.2 (`bilateralOMCResidues_card_le_sub_two_of_collision`):**
    Whenever there exists a non-zero target collision lane `c₀` (`1 ≤ c₀ < m` with
    `(r * c₀) % m = N % m`), `(bilateralOMCResidues N r m).card ≤ m - 2`, and for
    `2 ≤ m ≤ r`, `(admissibleFiberResidues (wr2TargetSievedFiber N r m) m).card ≤ m - 2`. -/
theorem bilateralOMCResidues_card_le_sub_two_of_collision
    {N r m c₀ : ℕ} (hm2 : 2 ≤ m) (hmr : m ≤ r)
    (hc0_pos : 1 ≤ c₀) (hc0_lt : c₀ < m) (h_coll : (r * c₀) % m = N % m) :
    (bilateralOMCResidues N r m).card ≤ m - 2 ∧
    (admissibleFiberResidues (wr2TargetSievedFiber N r m) m).card ≤ m - 2 := by
  have h_sub : bilateralOMCResidues N r m ⊆ (range (m - 2)).image (expandAvoidLane c₀) := by
    intro c hc
    rw [bilateralOMCResidues, mem_filter, mem_range] at hc
    obtain ⟨hc_lt, hc_pos, hc_ne_N⟩ := hc
    have hc_ne_c0 : c ≠ c₀ := by
      intro h_eq
      rw [h_eq] at hc_ne_N
      exact hc_ne_N h_coll
    exact mem_image_expandAvoidLane_of_ne hc0_pos hc0_lt hc_pos hc_lt hc_ne_c0
  have h_bil_le : (bilateralOMCResidues N r m).card ≤ m - 2 := by
    have h1 := Nat.le_trans (card_le_card h_sub) card_image_le
    rw [card_range] at h1
    exact h1
  have h_adm_sub := targetSievedFiber_admissible_subset_bilateralOMCResidues (N := N) hm2 hmr
  exact ⟨h_bil_le, Nat.le_trans (card_le_card h_adm_sub) h_bil_le⟩

/-!
## Section 2: Branch-Free Parity-CRT Absorber (`crtOddLift130`) & Mod-130 Stride Contraction
-/

/-- Branch-free Parity-CRT absorber lifting Mod-2 (`q % 2 = 1`) and Mod-65 (`q % 65 = c`)
    to Mod-130 (`2 * 65 = 130`): `c + 65 * (1 - c % 2)`. -/
def crtOddLift130 (c : ℕ) : ℕ :=
  c + 65 * (1 - c % 2)

/-- Pure native Presburger CRT proof: if `c < 65`, `q % 2 = 1`, and `q % 65 = c`,
    then `q % 130 = crtOddLift130 c` and `crtOddLift130 c < 130`. -/
theorem crt_mod2_mod65_to_mod130
    {q c : ℕ} (hc : c < 65) (hq2 : q % 2 = 1) (hq65 : q % 65 = c) :
    q % 130 = crtOddLift130 c ∧ crtOddLift130 c < 130 := by
  unfold crtOddLift130
  omega

/-- Every `q ∈ wr2FloorSubfiber N r L` is odd (`q % 2 = 1`). -/
theorem wr2FloorSubfiber_mem_odd {N r L q : ℕ} (hq : q ∈ wr2FloorSubfiber N r L) :
    q % 2 = 1 := by
  rw [wr2FloorSubfiber, mem_filter] at hq
  have hq_hyp := (wr2ShearContractedFiber_to_hyperbolic_and_sum hq.1).1
  rw [hyperbolicPrimeFiber, mem_filter] at hq_hyp
  exact hq_hyp.2.2.1

/-- Explicit connection of every `q ∈ wr2FloorSubfiber N r L` to the 5UP Reciprocal Shear
    congruence (`∀ m, ((r + q) * r) % m = (r * r + r * q) % m`), the Mod-63/64/65
    Triple-QR half-chord absorber equations, and the `r ^ 5000 ≤ q ^ 4469` lower pinch. -/
theorem wr2FloorSubfiber_shear_and_triple_qr_locks
    {N r L q : ℕ} (hr_pos : 0 < r) (hr_odd : r % 2 = 1)
    (hq : q ∈ wr2FloorSubfiber N r L) :
    r ^ 5000 ≤ q ^ 4469 ∧
    r ^ 9469 ≤ (N - 2) ^ 4469 ∧
    (∀ m : ℕ, ((r + q) * r) % m = (r * r + r * q) % m) ∧
    (((q + r) / 2) ^ 2) % 63 = (r * q + ((q - r) / 2) ^ 2) % 63 ∧
    (((q + r) / 2) ^ 2) % 64 = (r * q + ((q - r) / 2) ^ 2) % 64 ∧
    (((q + r) / 2) ^ 2) % 65 = (r * q + ((q - r) / 2) ^ 2) % 65 := by
  rw [wr2FloorSubfiber, mem_filter] at hq
  have h_lp := (wr2ShearContractedFiber_lower_pinch_and_bilateral_omc hr_pos hq.1).1
  have hq_hyp := (wr2ShearContractedFiber_to_hyperbolic_and_sum hq.1).1
  have h_abs := hyperbolicPrimeFiber_pinch_cutoff_and_shear hq_hyp
  have h_qr := h_abs.2.2.2.2 hr_odd
  exact ⟨h_lp, h_abs.2.1, h_abs.2.2.2.1, h_qr.1, h_qr.2.1, h_qr.2.2⟩

/-- Every Mod-65 slice `residueClassSlice (wr2FloorSubfiber N r L) 65 c` (with `c < 65`)
    is contained in the Mod-130 slice `residueClassSlice (wr2FloorSubfiber N r L) 130 (crtOddLift130 c)`. -/
theorem wr2FloorSubfiber_mod65_slice_subset_mod130_slice
    {N r L c : ℕ} (hc : c < 65) :
    residueClassSlice (wr2FloorSubfiber N r L) 65 c ⊆
      residueClassSlice (wr2FloorSubfiber N r L) 130 (crtOddLift130 c) := by
  intro q hq
  rw [residueClassSlice, mem_filter] at hq ⊢
  have hq_odd : q % 2 = 1 := wr2FloorSubfiber_mem_odd hq.1
  exact ⟨hq.1, (crt_mod2_mod65_to_mod130 hc hq_odd hq.2).1⟩

/-- **Theorem 2.1 (`wr2FloorSubfiber_mod65_slice_card_le_mod130_stride`):**
    Composite Mod-130 Quotient-Stride Contraction on `WR2`:
    For every floor `L : ℕ` and every Mod-65 residue class `c < 65`,
    `(residueClassSlice (wr2FloorSubfiber N r L) 65 c).card ≤ (((N - 2) / r) / 130 - L / 130) + 1`. -/
theorem wr2FloorSubfiber_mod65_slice_card_le_mod130_stride
    {N r L c : ℕ} (hc : c < 65) :
    (residueClassSlice (wr2FloorSubfiber N r L) 65 c).card ≤
      (((N - 2) / r) / 130 - L / 130) + 1 := by
  have h_sub := wr2FloorSubfiber_mod65_slice_subset_mod130_slice (N := N) (r := r) (L := L) hc
  have h_130 :=
    wr2FloorSubfiber_slice_card_le_shifted_quotient_diff
      (N := N) (r := r) (L := L) (by omega : 0 < 130) (crtOddLift130 c)
  exact Nat.le_trans (card_le_card h_sub) h_130

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.bilateralOMCResidues_card_le_sub_one
#print axioms WuPaper.ESZerosBridge.bilateralOMCResidues_card_le_sub_two_of_collision
#print axioms WuPaper.ESZerosBridge.crt_mod2_mod65_to_mod130
#print axioms WuPaper.ESZerosBridge.wr2FloorSubfiber_shear_and_triple_qr_locks
#print axioms WuPaper.ESZerosBridge.wr2FloorSubfiber_mod65_slice_card_le_mod130_stride
