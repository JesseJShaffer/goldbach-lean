import WR2Step213WR2UniversalPVenAndMod63CRTProductBound

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step215WR2RSCOrthogonalMultiplexorAnd8190FiberBound.lean — 5-Channel RSC Orthogonal Frequency Multiplexor, Alternate Histories & Global Fiber Product Bound

1. **5-Channel RSC Orthogonal Frequency Multiplexor (`rscMultiplex8190`, `rscMultiplex8190_roundtrip_id`):**
   Decomposes `8190 = 2 * 9 * 5 * 7 * 13` into the four Radical (`R`) prime channels
   `{2, 5, 7, 13}` and the Square-Shell (`S²`) Threeven channel `9 = 3²` using the
   orthogonal frequency carriers `(4095, 910, 3276, 1170, 6930)` satisfying
   `4095 + 910 + 3276 + 1170 + 6930 = 2 * 8190 + 1`.
2. **Disjoint Alternate-History Partition (`struck5ChannelHistoryDomain`, `unstruck5ChannelHistoryDomain`,
   `wr2Fiber_struck5ChannelHistory_card_eq_zero`):**
   Partitions any `Finset ℕ` into its struck `p`-ven alternate histories and its single
   unstruck pure-radical history, proving that for all `r ≥ 13`, all 31 struck histories
   collapse to `card = 0` on `wr2ShearContractedFiber N r`.
3. **Mod-8190 Active Lane Bound (`1728` and `990` Lanes) & Global Per-Fiber Product Contraction
   (`targetSieved13_mod8190_admissible_card_bounds`,
   `wr2FloorSubfiber_card_le_admissible_mul_stride`):**
   Proves that for all `r ≥ 13`, the active Mod-8190 lanes of `wr2TargetSievedFiber N r 13`
   satisfy `card ≤ 1728` (`48 * 36`) and `card ≤ 990` (`33 * 30`) under target collisions,
   and bounds the total cardinality of `wr2FloorSubfiber N r L` by
   `(admissibleFiberResidues (wr2FloorSubfiber N r L) m).card * ((((N - 2) / r) / m - L / m) + 1)`.
-/

/-!
## Section 1: 5-Channel RSC (`R(S²)`) Orthogonal Frequency Multiplexor on Mod-8190
-/

/-- Branch-free 5-channel RSC Orthogonal Frequency Multiplexor reconstructing `q % 8190`
    from Radical channels `(q % 2, q % 5, q % 7, q % 13)` and Square-Shell channel `q % 9`:
    uses orthogonal carriers `E₂ = 4095, E₉ = 910, E₅ = 3276, E₇ = 1170, E₁₃ = 6930`. -/
def rscMultiplex8190 (a2 a9 a5 a7 a13 : ℕ) : ℕ :=
  (4095 * a2 + 910 * a9 + 3276 * a5 + 1170 * a7 + 6930 * a13) % 8190

/-- **Theorem 1.1 (`rscMultiplex8190_roundtrip_id`):**
    Exact Partition of Unity (`4095 + 910 + 3276 + 1170 + 6930 = 2 * 8190 + 1`) and
    lossless 5-channel RSC reconstruction for every `q : ℕ`. -/
theorem rscMultiplex8190_roundtrip_id (q : ℕ) :
    4095 + 910 + 3276 + 1170 + 6930 = 2 * 8190 + 1 ∧
    rscMultiplex8190 (q % 2) (q % 9) (q % 5) (q % 7) (q % 13) = q % 8190 ∧
    (q % 8190) % 130 = q % 130 ∧
    (q % 8190) % 65 = q % 65 ∧
    (q % 8190) % 63 = q % 63 := by
  unfold rscMultiplex8190
  omega

/-!
## Section 2: Alternate-History Disjoint Partition & Collapse of Struck Histories
-/

/-- The union of all 31 struck `p`-ven alternate histories across channels `{2, 3, 5, 7, 13}`:
    elements divisible by at least one `p ∈ {2, 3, 5, 7, 13}`. -/
def struck5ChannelHistoryDomain (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun q : ℕ =>
    q % 2 = 0 ∨ q % 3 = 0 ∨ q % 5 = 0 ∨ q % 7 = 0 ∨ q % 13 = 0)

/-- The single unstruck pure-radical history across `{2, 3, 5, 7, 13}`:
    elements surviving all five `p`-ven waves (`1 ≤ q % p` for all `p ∈ {2, 3, 5, 7, 13}`). -/
def unstruck5ChannelHistoryDomain (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun q : ℕ =>
    1 ≤ q % 2 ∧ 1 ≤ q % 3 ∧ 1 ≤ q % 5 ∧ 1 ≤ q % 7 ∧ 1 ≤ q % 13)

theorem disjoint_struck_unstruck_5ChannelHistory (S : Finset ℕ) :
    Disjoint (struck5ChannelHistoryDomain S) (unstruck5ChannelHistoryDomain S) := by
  rw [Finset.disjoint_left]
  intro q hst hun
  rw [struck5ChannelHistoryDomain, mem_filter] at hst
  rw [unstruck5ChannelHistoryDomain, mem_filter] at hun
  omega

theorem eq_struck_union_unstruck_5ChannelHistory (S : Finset ℕ) :
    S = struck5ChannelHistoryDomain S ∪ unstruck5ChannelHistoryDomain S := by
  ext q
  rw [mem_union, struck5ChannelHistoryDomain, unstruck5ChannelHistoryDomain,
      mem_filter, mem_filter]
  constructor
  · intro hq
    if h_st : q % 2 = 0 ∨ q % 3 = 0 ∨ q % 5 = 0 ∨ q % 7 = 0 ∨ q % 13 = 0 then
      exact Or.inl ⟨hq, h_st⟩
    else
      exact Or.inr ⟨hq, by omega⟩
  · intro hor
    cases hor with
    | inl h1 => exact h1.1
    | inr h2 => exact h2.1

/-- **Theorem 2.1 (`wr2Fiber_struck5ChannelHistory_card_eq_zero`):**
    For every `r ≥ 13`, all 31 struck alternate histories vanish identically on
    `wr2ShearContractedFiber N r` (`card = 0`), leaving 100% of the fiber in
    `unstruck5ChannelHistoryDomain`. -/
theorem wr2Fiber_struck5ChannelHistory_card_eq_zero
    {N r : ℕ} (hr13 : 13 ≤ r) :
    (struck5ChannelHistoryDomain (wr2ShearContractedFiber N r)).card = 0 ∧
    (wr2ShearContractedFiber N r).card =
      (unstruck5ChannelHistoryDomain (wr2ShearContractedFiber N r)).card := by
  have h_st_zero :
      (struck5ChannelHistoryDomain (wr2ShearContractedFiber N r)).card = 0 := by
    match Nat.eq_zero_or_pos
        (struck5ChannelHistoryDomain (wr2ShearContractedFiber N r)).card with
    | Or.inl h0 => exact h0
    | Or.inr hpos =>
      obtain ⟨q, hq⟩ := card_pos.mp hpos
      rw [struck5ChannelHistoryDomain, mem_filter] at hq
      have hr_pos : 0 < r := by omega
      have h_omc := (wr2ShearContractedFiber_lower_pinch_and_bilateral_omc hr_pos hq.1).2.1
      have h2 := h_omc 2 (by omega) (by omega)
      have h3 := h_omc 3 (by omega) (by omega)
      have h5 := h_omc 5 (by omega) (by omega)
      have h7 := h_omc 7 (by omega) (by omega)
      have h13 := h_omc 13 (by omega) hr13
      omega
  have h_part :
      (wr2ShearContractedFiber N r).card =
        (struck5ChannelHistoryDomain (wr2ShearContractedFiber N r)).card +
        (unstruck5ChannelHistoryDomain (wr2ShearContractedFiber N r)).card := by
    conv_lhs => rw [eq_struck_union_unstruck_5ChannelHistory (wr2ShearContractedFiber N r)]
    exact card_union_of_disjoint
      (disjoint_struck_unstruck_5ChannelHistory (wr2ShearContractedFiber N r))
  omega

/-!
## Section 3: Mod-8190 Active Lane Contraction (`1728` and `990` Lanes) & Global Fiber Product Bound
-/

/-- Branch-free CRT map from `(c65, c63)` to `Mod 8190` via `crtOddLift130` and `crtReconstruct8190From130And63`. -/
def crtPair65And63To8190 (pair : ℕ × ℕ) : ℕ :=
  crtReconstruct8190From130And63 (crtOddLift130 pair.1) pair.2

/-- Inclusion `wr2TargetSievedFiber N r 13 ⊆ wr2TargetSievedFiber N r 7`. -/
theorem wr2TargetSievedFiber_13_subset_7 (N r : ℕ) :
    wr2TargetSievedFiber N r 13 ⊆ wr2TargetSievedFiber N r 7 := by
  intro q hq
  rw [wr2TargetSievedFiber, mem_filter] at hq ⊢
  exact ⟨hq.1, by omega⟩

/-- **Theorem 3.1 (`targetSieved13_mod8190_admissible_subset_image`):**
    For every `r ≥ 13`, the active Mod-8190 lanes of `wr2TargetSievedFiber N r 13` are
    contained in the image under `crtPair65And63To8190` of the product of its active
    Mod-65 and Mod-63 lane sets. -/
theorem targetSieved13_mod8190_admissible_subset_image (N r : ℕ) :
    admissibleFiberResidues (wr2TargetSievedFiber N r 13) 8190 ⊆
      (admissibleFiberResidues (wr2TargetSievedFiber N r 13) 65 ×ˢ
       admissibleFiberResidues (wr2TargetSievedFiber N r 7) 63).image
        crtPair65And63To8190 := by
  intro c hc
  rw [admissibleFiberResidues, mem_image] at hc
  obtain ⟨q, hq13, rfl⟩ := hc
  have hq7 : q ∈ wr2TargetSievedFiber N r 7 := wr2TargetSievedFiber_13_subset_7 N r hq13
  have hq_fiber : q ∈ wr2ShearContractedFiber N r := by
    rw [wr2TargetSievedFiber, mem_filter] at hq13
    exact hq13.1
  have hq_hyp := (wr2ShearContractedFiber_to_hyperbolic_and_sum hq_fiber).1
  have hq_odd : q % 2 = 1 := by
    rw [hyperbolicPrimeFiber, mem_filter] at hq_hyp
    exact hq_hyp.2.2.1
  have hc65 : q % 65 < 65 := Nat.mod_lt q (by omega : 0 < 65)
  have hc63 : q % 63 < 63 := Nat.mod_lt q (by omega : 0 < 63)
  have h130 := crt_mod2_mod65_to_mod130 hc65 hq_odd rfl
  have h8190 := crt_mod130_mod63_to_mod8190 h130.2 hc63 h130.1 rfl
  rw [mem_image]
  refine ⟨(q % 65, q % 63), ?_, ?_⟩
  · rw [mem_product, admissibleFiberResidues, admissibleFiberResidues, mem_image, mem_image]
    exact ⟨⟨q, hq13, rfl⟩, ⟨q, hq7, rfl⟩⟩
  · unfold crtPair65And63To8190
    dsimp only
    exact h8190.2.2.1.symm

/-- **Theorem 3.2 (`targetSieved13_mod8190_admissible_card_bounds`):**
    For every `r ≥ 13`, the active Mod-8190 lanes of `wr2TargetSievedFiber N r 13` satisfy
    `card ≤ 1728` (`48 * 36`) unconditionally and `card ≤ 990` (`33 * 30`) whenever
    non-zero Mod-5, Mod-7, and Mod-13 target collision lanes exist. -/
theorem targetSieved13_mod8190_admissible_card_bounds
    {N r : ℕ} (hr13 : 13 ≤ r) :
    (admissibleFiberResidues (wr2TargetSievedFiber N r 13) 8190).card ≤ 1728 ∧
    (∀ c₅ c₇ c₁₃ : ℕ,
      1 ≤ c₅ → c₅ < 5 → (r * c₅) % 5 = N % 5 →
      1 ≤ c₇ → c₇ < 7 → (r * c₇) % 7 = N % 7 →
      1 ≤ c₁₃ → c₁₃ < 13 → (r * c₁₃) % 13 = N % 13 →
      (admissibleFiberResidues (wr2TargetSievedFiber N r 13) 8190).card ≤ 990) := by
  have h_sub := targetSieved13_mod8190_admissible_subset_image N r
  have h_prod_le :
      (admissibleFiberResidues (wr2TargetSievedFiber N r 13) 8190).card ≤
        (admissibleFiberResidues (wr2TargetSievedFiber N r 13) 65).card *
        (admissibleFiberResidues (wr2TargetSievedFiber N r 7) 63).card := by
    have h1 := Nat.le_trans (card_le_card h_sub) card_image_le
    rw [card_product] at h1
    exact h1
  have hr7 : 7 ≤ r := by omega
  have h65_bounds := targetSieved13_mod65_admissible_card_bounds (N := N) hr13
  have h63_bounds := targetSieved7_mod63_admissible_card_bounds (N := N) hr7
  have h65_le48 : (admissibleFiberResidues (wr2TargetSievedFiber N r 13) 65).card ≤ 48 :=
    h65_bounds.2.2.2.1
  have h63_le36 : (admissibleFiberResidues (wr2TargetSievedFiber N r 7) 63).card ≤ 36 :=
    h63_bounds.2.1
  have h_mul1728 := Nat.mul_le_mul h65_le48 h63_le36
  refine ⟨by omega, ?_⟩
  intro c₅ c₇ c₁₃ hc5_pos hc5_lt h_c5 hc7_pos hc7_lt h_c7 hc13_pos hc13_lt h_c13
  have h65_le33 := h65_bounds.2.2.2.2.2 c₅ c₁₃ hc5_pos hc5_lt h_c5 hc13_pos hc13_lt h_c13
  have h63_le30 := h63_bounds.2.2.2 c₇ hc7_pos hc7_lt h_c7
  have h_mul990 := Nat.mul_le_mul h65_le33 h63_le30
  omega

/-- 2D reconstruction map `(c, j) ↦ m * (L_div + j) + c` recovering every fiber element `q`
    from its active residue lane `c = q % m` and its shifted quotient `j = q / m - L / m`. -/
def reconstructFromResidueAndQuotientPair (m L_div : ℕ) (pair : ℕ × ℕ) : ℕ :=
  m * (L_div + pair.2) + pair.1

/-- **Theorem 3.3 (`wr2FloorSubfiber_card_le_admissible_mul_stride`):**
    Constructive Global Per-Fiber Product Bound: for ANY floor `L : ℕ` and ANY modulus `m > 0`
    (including `m = 65`, `130`, and `8190`),
    `(wr2FloorSubfiber N r L).card ≤ (admissibleFiberResidues (wr2FloorSubfiber N r L) m).card * ((((N - 2) / r) / m - L / m) + 1)`. -/
theorem wr2FloorSubfiber_card_le_admissible_mul_stride
    {N r L m : ℕ} (hm_pos : 0 < m) :
    (wr2FloorSubfiber N r L).card ≤
      (admissibleFiberResidues (wr2FloorSubfiber N r L) m).card *
        ((((N - 2) / r) / m - L / m) + 1) := by
  have h_sub :
      wr2FloorSubfiber N r L ⊆
        (admissibleFiberResidues (wr2FloorSubfiber N r L) m ×ˢ
         range ((((N - 2) / r) / m - L / m) + 1)).image
          (reconstructFromResidueAndQuotientPair m (L / m)) := by
    intro q hq
    have hq_copy := hq
    rw [wr2FloorSubfiber, mem_filter] at hq_copy
    have h_q_le : q ≤ (N - 2) / r :=
      (wr2ShearContractedFiber_to_hyperbolic_and_sum hq_copy.1).2.1
    have h_q_div_ge : L / m ≤ q / m := div_le_div_right_native hm_pos hq_copy.2
    have h_q_div_le : q / m ≤ ((N - 2) / r) / m := div_le_div_right_native hm_pos h_q_le
    have h_div_mod : m * (q / m) + q % m = q := Nat.div_add_mod q m
    have h_add_sub : L / m + (q / m - L / m) = q / m := by omega
    rw [mem_image]
    refine ⟨(q % m, q / m - L / m), ?_, ?_⟩
    · rw [mem_product, admissibleFiberResidues, mem_image, mem_range]
      exact ⟨⟨q, hq, rfl⟩, by omega⟩
    · unfold reconstructFromResidueAndQuotientPair
      dsimp only
      rw [h_add_sub]
      omega
  have h1 := Nat.le_trans (card_le_card h_sub) card_image_le
  rw [card_product, card_range] at h1
  exact h1

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.rscMultiplex8190_roundtrip_id
#print axioms WuPaper.ESZerosBridge.wr2Fiber_struck5ChannelHistory_card_eq_zero
#print axioms WuPaper.ESZerosBridge.targetSieved13_mod8190_admissible_card_bounds
#print axioms WuPaper.ESZerosBridge.wr2FloorSubfiber_card_le_admissible_mul_stride
