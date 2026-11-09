import WR2Step206LiLiu3PrimeTightBilateralOMCFiberCapstone

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step208LiLiuMod130CompositeStrideAndOMCCardCapstone.lean — Branch-Free Mod-130 Stride & Bilateral OMC `m - 2` Capstone for `D19 N`

Welds the Branch-Free Parity-CRT 130 Absorber (`liliuCrtOddLift130 c := c + 65 * (1 - c % 2)`),
the Bilateral OMC `m - 1` / `m - 2` Cardinality Bounds, and the 5UP Reciprocal Shear +
Triple-QR Absorber Locks directly into the `Goldbach.All` (`D19 N`) 3-Prime Tight Fiber stack.
-/

/-!
## Section 1: Constructive `m - 1` and `m - 2` Bounds on `liliuBilateralOMCResidues`
-/

def liliuShiftSuccNat (k : ℕ) : ℕ :=
  k + 1

def liliuExpandAvoidLane (c₀ j : ℕ) : ℕ :=
  if j + 1 < c₀ then j + 1 else j + 2

theorem liliuExpandAvoidLane_of_lt {c₀ j : ℕ} (h : j + 1 < c₀) :
    liliuExpandAvoidLane c₀ j = j + 1 := by
  unfold liliuExpandAvoidLane
  rw [if_pos h]

theorem liliuExpandAvoidLane_of_not_lt {c₀ j : ℕ} (h : ¬ (j + 1 < c₀)) :
    liliuExpandAvoidLane c₀ j = j + 2 := by
  unfold liliuExpandAvoidLane
  rw [if_neg h]

theorem mem_image_liliuShiftSuccNat_of_pos_lt {m c : ℕ} (hc_pos : 1 ≤ c) (hc_lt : c < m) :
    c ∈ (range (m - 1)).image liliuShiftSuccNat := by
  rw [mem_image]
  refine ⟨c - 1, ?_, ?_⟩
  · rw [mem_range]; omega
  · unfold liliuShiftSuccNat; omega

theorem mem_image_liliuExpandAvoidLane_of_ne
    {m c₀ c : ℕ} (hc0_pos : 1 ≤ c₀) (hc0_lt : c₀ < m)
    (hc_pos : 1 ≤ c) (hc_lt : c < m) (hc_ne : c ≠ c₀) :
    c ∈ (range (m - 2)).image (liliuExpandAvoidLane c₀) := by
  rw [mem_image]
  if h_lt : c < c₀ then
    have h_cond : (c - 1) + 1 < c₀ := by omega
    refine ⟨c - 1, ?_, ?_⟩
    · rw [mem_range]; omega
    · rw [liliuExpandAvoidLane_of_lt h_cond]; omega
  else
    have h_not_cond : ¬ ((c - 2) + 1 < c₀) := by omega
    refine ⟨c - 2, ?_, ?_⟩
    · rw [mem_range]; omega
    · rw [liliuExpandAvoidLane_of_not_lt h_not_cond]; omega

/-- **Theorem 1.1 (`liliuBilateralOMCResidues_card_le_sub_one`):**
    For every modulus `m : ℕ`, `(liliuBilateralOMCResidues N r m).card ≤ m - 1`. -/
theorem liliuBilateralOMCResidues_card_le_sub_one (N r m : ℕ) :
    (liliuBilateralOMCResidues N r m).card ≤ m - 1 := by
  have h_sub : liliuBilateralOMCResidues N r m ⊆ (range (m - 1)).image liliuShiftSuccNat := by
    intro c hc
    rw [liliuBilateralOMCResidues, mem_filter, mem_range] at hc
    exact mem_image_liliuShiftSuccNat_of_pos_lt hc.2.1 hc.1
  have h1 := Nat.le_trans (card_le_card h_sub) card_image_le
  rw [card_range] at h1
  exact h1

/-- **Theorem 1.2 (`liliuBilateralOMCResidues_card_le_sub_two_of_collision`):**
    Whenever `1 ≤ c₀ < m` satisfies `(r * c₀) % m = N % m`,
    `(liliuBilateralOMCResidues N r m).card ≤ m - 2`, and for `2 ≤ m ≤ r`,
    `((liliuTargetSieved3PrimeFiber N r m).image (fun q => q % m)).card ≤ m - 2`. -/
theorem liliuBilateralOMCResidues_card_le_sub_two_of_collision
    {N r m c₀ : ℕ} (hm2 : 2 ≤ m) (hmr : m ≤ r)
    (hc0_pos : 1 ≤ c₀) (hc0_lt : c₀ < m) (h_coll : (r * c₀) % m = N % m) :
    (liliuBilateralOMCResidues N r m).card ≤ m - 2 ∧
    ((liliuTargetSieved3PrimeFiber N r m).image (fun q : ℕ => q % m)).card ≤ m - 2 := by
  have h_sub :
      liliuBilateralOMCResidues N r m ⊆ (range (m - 2)).image (liliuExpandAvoidLane c₀) := by
    intro c hc
    rw [liliuBilateralOMCResidues, mem_filter, mem_range] at hc
    obtain ⟨hc_lt, hc_pos, hc_ne_N⟩ := hc
    have hc_ne_c0 : c ≠ c₀ := by
      intro h_eq
      rw [h_eq] at hc_ne_N
      exact hc_ne_N h_coll
    exact mem_image_liliuExpandAvoidLane_of_ne hc0_pos hc0_lt hc_pos hc_lt hc_ne_c0
  have h_bil_le : (liliuBilateralOMCResidues N r m).card ≤ m - 2 := by
    have h1 := Nat.le_trans (card_le_card h_sub) card_image_le
    rw [card_range] at h1
    exact h1
  have h_adm_sub := liliuTargetSieved_admissible_subset_bilateralOMC (N := N) hm2 hmr
  exact ⟨h_bil_le, Nat.le_trans (card_le_card h_adm_sub) h_bil_le⟩

/-!
## Section 2: Branch-Free Parity-CRT Absorber (`liliuCrtOddLift130`) & Mod-130 Stride
-/

/-- Branch-free Parity-CRT absorber lifting Mod-2 (`q % 2 = 1`) and Mod-65 (`q % 65 = c`)
    to Mod-130 (`2 * 65 = 130`): `c + 65 * (1 - c % 2)`. -/
def liliuCrtOddLift130 (c : ℕ) : ℕ :=
  c + 65 * (1 - c % 2)

theorem crt_mod2_mod65_to_mod130_liliu
    {q c : ℕ} (hc : c < 65) (hq2 : q % 2 = 1) (hq65 : q % 65 = c) :
    q % 130 = liliuCrtOddLift130 c ∧ liliuCrtOddLift130 c < 130 := by
  unfold liliuCrtOddLift130
  omega

/-- Every `q ∈ liliuFloorSubfiber N r L` is odd (`q % 2 = 1`). -/
theorem liliuFloorSubfiber_mem_odd {N r L q : ℕ} (hq : q ∈ liliuFloorSubfiber N r L) :
    q % 2 = 1 := by
  rw [liliuFloorSubfiber, mem_filter] at hq
  have hq_hyp := (liliuTight3PrimeFiber_mem_props hq.1).2.1
  rw [liliuHyperbolicPrimeFiber, mem_filter] at hq_hyp
  exact hq_hyp.2.2.1

/-- Explicit connection of every `q ∈ liliuFloorSubfiber N r L` to the `10/9` lower pinch,
    the `9/19` upper pinch, the division-free 5UP Reciprocal Shear congruence, and the
    Mod-63/64/65 Triple-QR absorber equations. -/
theorem liliuFloorSubfiber_shear_and_triple_qr_locks
    {N r L q : ℕ} (hr_pos : 0 < r) (hr_odd : r % 2 = 1)
    (hq : q ∈ liliuFloorSubfiber N r L) :
    r ^ 10 ≤ q ^ 9 ∧
    r ^ 19 ≤ N ^ 9 ∧
    (∀ m : ℕ, ((r + q) * r) % m = (r * r + r * q) % m) ∧
    (((q + r) / 2) ^ 2) % 63 = (r * q + ((q - r) / 2) ^ 2) % 63 ∧
    (((q + r) / 2) ^ 2) % 64 = (r * q + ((q - r) / 2) ^ 2) % 64 ∧
    (((q + r) / 2) ^ 2) % 65 = (r * q + ((q - r) / 2) ^ 2) % 65 := by
  rw [liliuFloorSubfiber, mem_filter] at hq
  have h_props := liliuTight3PrimeFiber_mem_props hq.1
  have h_lp := liliuShearContractedFiber_lower_pinch_10_9 hr_pos h_props.1
  have h_abs := liliuHyperbolicPrimeFiber_919_pinch_and_shear h_props.2.1
  have h_qr := h_abs.2.2.2 hr_odd
  exact ⟨h_lp.1, h_lp.2.1, h_abs.2.2.1, h_qr.1, h_qr.2.1, h_qr.2.2⟩

/-- Every Mod-65 slice `liliuFloorResidueSlice N r L 65 c` (`c < 65`) is contained in the
    Mod-130 slice `liliuFloorResidueSlice N r L 130 (liliuCrtOddLift130 c)`. -/
theorem liliuFloorResidueSlice_mod65_subset_mod130
    {N r L c : ℕ} (hc : c < 65) :
    liliuFloorResidueSlice N r L 65 c ⊆
      liliuFloorResidueSlice N r L 130 (liliuCrtOddLift130 c) := by
  intro q hq
  rw [liliuFloorResidueSlice, mem_filter] at hq ⊢
  have hq_odd : q % 2 = 1 := liliuFloorSubfiber_mem_odd hq.1
  exact ⟨hq.1, (crt_mod2_mod65_to_mod130_liliu hc hq_odd hq.2).1⟩

/-- **Theorem 2.1 (`liliuFloorResidueSlice_mod65_card_le_mod130_stride`):**
    For every certified floor `L : ℕ` and Mod-65 residue class `c < 65`,
    `(liliuFloorResidueSlice N r L 65 c).card ≤ ((N / r) / 130 - L / 130) + 1`. -/
theorem liliuFloorResidueSlice_mod65_card_le_mod130_stride
    {N r L c : ℕ} (hc : c < 65) :
    (liliuFloorResidueSlice N r L 65 c).card ≤ ((N / r) / 130 - L / 130) + 1 := by
  have h_sub := liliuFloorResidueSlice_mod65_subset_mod130 (N := N) (r := r) (L := L) hc
  have h_130 :=
    liliuFloorResidueSlice_card_le_shifted_quotient_diff
      (N := N) (r := r) (L := L) (by omega : 0 < 130) (liliuCrtOddLift130 c)
  exact Nat.le_trans (card_le_card h_sub) h_130

/-- **Master 31-Module Capstone (`master_31module_D19_mod130_stride_and_bilateral_omc_capstone`):**
    Complete 31-Module Capstone uniting `Goldbach.one_plus_one_nine_count` (`liuMainTerm0004 N < (D19 N : ℝ)`),
    the 3-Prime Tight `9/19` Hyperbolic Fibers (`liliuTight3PrimeFiberPairs N`),
    the `m - 1` and `m - 2` Bilateral OMC Residue Cardinality Bounds,
    the Mod-130 CRT Composite Quotient-Stride Bound (`((N / r) / 130 - L / 130) + 1`),
    and the Factorial Lighthouse Next-Prime Generator (`hasNextPrimeConnection_unconditional`). -/
theorem master_31module_D19_mod130_stride_and_bilateral_omc_capstone :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (∀ r m : ℕ, 2 ≤ m → m ≤ r →
        ((liliuTargetSieved3PrimeFiber N r m).image (fun q : ℕ => q % m)).card ≤ m - 1) ∧
      (∀ r m c₀ : ℕ, 2 ≤ m → m ≤ r → 1 ≤ c₀ → c₀ < m → (r * c₀) % m = N % m →
        ((liliuTargetSieved3PrimeFiber N r m).image (fun q : ℕ => q % m)).card ≤ m - 2) ∧
      (∀ r L c : ℕ, c < 65 →
        (liliuFloorResidueSlice N r L 65 c).card ≤ ((N / r) / 130 - L / 130) + 1) ∧
      (fiveupPinchedQRSubfilter 9 10 N).card ≤
        1 + ((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).card ∧
      ((((1 + ((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).card : ℕ) : ℝ) ≤
          liuMainTerm0004 N) →
        ∃ p q p_next' : ℕ,
          Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next' ∧ IsPrimeNat p_next') := by
  obtain ⟨K, hK4, hCap⟩ := master_29module_D19_tight_3prime_bilateral_omc_capstone
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven
  have hM := hCap N hNK hEven
  refine ⟨hM.1, ?_, ?_, ?_, hM.2.2.2.1, hM.2.2.2.2⟩
  · intro r m hm2 hmr
    have h_sub := liliuTargetSieved_admissible_subset_bilateralOMC (N := N) hm2 hmr
    exact Nat.le_trans (card_le_card h_sub) (liliuBilateralOMCResidues_card_le_sub_one N r m)
  · intro r m c₀ hm2 hmr hc0_pos hc0_lt h_coll
    exact (liliuBilateralOMCResidues_card_le_sub_two_of_collision hm2 hmr hc0_pos hc0_lt h_coll).2
  · intro r L c hc
    exact liliuFloorResidueSlice_mod65_card_le_mod130_stride hc

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.liliuBilateralOMCResidues_card_le_sub_one
#print axioms WuPaper.ESZerosBridge.liliuBilateralOMCResidues_card_le_sub_two_of_collision
#print axioms WuPaper.ESZerosBridge.crt_mod2_mod65_to_mod130_liliu
#print axioms WuPaper.ESZerosBridge.liliuFloorSubfiber_shear_and_triple_qr_locks
#print axioms WuPaper.ESZerosBridge.liliuFloorResidueSlice_mod65_card_le_mod130_stride
#print axioms WuPaper.ESZerosBridge.master_31module_D19_mod130_stride_and_bilateral_omc_capstone
