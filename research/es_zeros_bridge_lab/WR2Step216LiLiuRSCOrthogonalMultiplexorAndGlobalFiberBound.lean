import WR2Step214LiLiuUniversalPVenAndMod8190MasterCapstone

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step216LiLiuRSCOrthogonalMultiplexorAndGlobalFiberBound.lean — 5-Channel RSC Orthogonal Frequency Multiplexor & Global Fiber Product Capstone for `D19 N`

Welds the 5-Channel RSC Orthogonal Frequency Multiplexor (`liliuRscMultiplex8190`),
the Alternate-History Struck-Domain Collapse (`liliuStruck5ChannelHistoryDomain`),
the Mod-8190 Active Lane Contraction (`1728` and `990` lanes out of `8190`),
and the Constructive Global Per-Fiber Product Contraction
(`(liliuFloorSubfiber N r L).card ≤ (active lanes) * (((N / r) / m - L / m) + 1)`)
into the 39-Module `Goldbach.All` (`D19 N`) Master Capstone.
-/

/-!
## Section 1: 5-Channel RSC (`R(S²)`) Orthogonal Frequency Multiplexor & Alternate Histories
-/

/-- Branch-free 5-channel RSC Orthogonal Frequency Multiplexor modulo `8190 = 2 * 9 * 5 * 7 * 13`. -/
def liliuRscMultiplex8190 (a2 a9 a5 a7 a13 : ℕ) : ℕ :=
  (4095 * a2 + 910 * a9 + 3276 * a5 + 1170 * a7 + 6930 * a13) % 8190

theorem liliuRscMultiplex8190_roundtrip_id (q : ℕ) :
    4095 + 910 + 3276 + 1170 + 6930 = 2 * 8190 + 1 ∧
    liliuRscMultiplex8190 (q % 2) (q % 9) (q % 5) (q % 7) (q % 13) = q % 8190 := by
  unfold liliuRscMultiplex8190
  omega

/-- Union of all 31 struck `p`-ven alternate histories across `{2, 3, 5, 7, 13}`. -/
def liliuStruck5ChannelHistoryDomain (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun q : ℕ =>
    q % 2 = 0 ∨ q % 3 = 0 ∨ q % 5 = 0 ∨ q % 7 = 0 ∨ q % 13 = 0)

/-- The single unstruck pure-radical history across `{2, 3, 5, 7, 13}`. -/
def liliuUnstruck5ChannelHistoryDomain (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun q : ℕ =>
    1 ≤ q % 2 ∧ 1 ≤ q % 3 ∧ 1 ≤ q % 5 ∧ 1 ≤ q % 7 ∧ 1 ≤ q % 13)

theorem disjoint_liliuStruck_unstruck_5ChannelHistory (S : Finset ℕ) :
    Disjoint (liliuStruck5ChannelHistoryDomain S) (liliuUnstruck5ChannelHistoryDomain S) := by
  rw [Finset.disjoint_left]
  intro q hst hun
  rw [liliuStruck5ChannelHistoryDomain, mem_filter] at hst
  rw [liliuUnstruck5ChannelHistoryDomain, mem_filter] at hun
  omega

theorem eq_liliuStruck_union_unstruck_5ChannelHistory (S : Finset ℕ) :
    S = liliuStruck5ChannelHistoryDomain S ∪ liliuUnstruck5ChannelHistoryDomain S := by
  ext q
  rw [mem_union, liliuStruck5ChannelHistoryDomain, liliuUnstruck5ChannelHistoryDomain,
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

/-- **Theorem 1.1 (`liliuFiber_struck5ChannelHistory_card_eq_zero`):**
    For every `r ≥ 13`, all 31 struck alternate histories vanish identically on
    `liliuShearContractedFiber N r`. -/
theorem liliuFiber_struck5ChannelHistory_card_eq_zero
    {N r : ℕ} (hr13 : 13 ≤ r) :
    (liliuStruck5ChannelHistoryDomain (liliuShearContractedFiber N r)).card = 0 ∧
    (liliuShearContractedFiber N r).card =
      (liliuUnstruck5ChannelHistoryDomain (liliuShearContractedFiber N r)).card := by
  have h_st_zero :
      (liliuStruck5ChannelHistoryDomain (liliuShearContractedFiber N r)).card = 0 := by
    match Nat.eq_zero_or_pos
        (liliuStruck5ChannelHistoryDomain (liliuShearContractedFiber N r)).card with
    | Or.inl h0 => exact h0
    | Or.inr hpos =>
      obtain ⟨q, hq⟩ := card_pos.mp hpos
      rw [liliuStruck5ChannelHistoryDomain, mem_filter] at hq
      have hr_pos : 0 < r := by omega
      have h_omc := (liliuShearContractedFiber_lower_pinch_10_9 hr_pos hq.1).2.2
      have h2 := h_omc 2 (by omega) (by omega)
      have h3 := h_omc 3 (by omega) (by omega)
      have h5 := h_omc 5 (by omega) (by omega)
      have h7 := h_omc 7 (by omega) (by omega)
      have h13 := h_omc 13 (by omega) hr13
      omega
  have h_part :
      (liliuShearContractedFiber N r).card =
        (liliuStruck5ChannelHistoryDomain (liliuShearContractedFiber N r)).card +
        (liliuUnstruck5ChannelHistoryDomain (liliuShearContractedFiber N r)).card := by
    conv_lhs => rw [eq_liliuStruck_union_unstruck_5ChannelHistory (liliuShearContractedFiber N r)]
    exact card_union_of_disjoint
      (disjoint_liliuStruck_unstruck_5ChannelHistory (liliuShearContractedFiber N r))
  omega

/-!
## Section 2: Mod-8190 Active Lane Contraction (`1728` and `990` Lanes) & Global Fiber Product Bound
-/

def liliuCrtPair65And63To8190 (pair : ℕ × ℕ) : ℕ :=
  liliuCrtReconstruct8190From130And63 (liliuCrtOddLift130 pair.1) pair.2

theorem liliuTargetSieved3PrimeFiber_13_subset_7 (N r : ℕ) :
    liliuTargetSieved3PrimeFiber N r 13 ⊆ liliuTargetSieved3PrimeFiber N r 7 := by
  intro q hq
  rw [liliuTargetSieved3PrimeFiber, mem_filter] at hq ⊢
  exact ⟨hq.1, by omega⟩

theorem liliuTargetSieved13_mod8190_subset_image (N r : ℕ) :
    (liliuTargetSieved3PrimeFiber N r 13).image (fun q : ℕ => q % 8190) ⊆
      ((liliuTargetSieved3PrimeFiber N r 13).image (fun q : ℕ => q % 65) ×ˢ
       (liliuTargetSieved3PrimeFiber N r 7).image (fun q : ℕ => q % 63)).image
        liliuCrtPair65And63To8190 := by
  intro c hc
  rw [mem_image] at hc
  obtain ⟨q, hq13, rfl⟩ := hc
  have hq7 : q ∈ liliuTargetSieved3PrimeFiber N r 7 :=
    liliuTargetSieved3PrimeFiber_13_subset_7 N r hq13
  have hq_tight : q ∈ liliuTight3PrimeFiber N r := by
    rw [liliuTargetSieved3PrimeFiber, mem_filter] at hq13
    exact hq13.1
  have hq_hyp := (liliuTight3PrimeFiber_mem_props hq_tight).2.1
  have hq_odd : q % 2 = 1 := by
    rw [liliuHyperbolicPrimeFiber, mem_filter] at hq_hyp
    exact hq_hyp.2.2.1
  have hc65 : q % 65 < 65 := Nat.mod_lt q (by omega : 0 < 65)
  have hc63 : q % 63 < 63 := Nat.mod_lt q (by omega : 0 < 63)
  have h130 := crt_mod2_mod65_to_mod130_liliu hc65 hq_odd rfl
  have h8190 := crt_mod130_mod63_to_mod8190_liliu h130.2 hc63 h130.1 rfl
  rw [mem_image]
  refine ⟨(q % 65, q % 63), ?_, ?_⟩
  · rw [mem_product, mem_image, mem_image]
    exact ⟨⟨q, hq13, rfl⟩, ⟨q, hq7, rfl⟩⟩
  · unfold liliuCrtPair65And63To8190
    dsimp only
    exact h8190.2.2.1.symm

/-- **Theorem 2.1 (`liliuTargetSieved13_mod8190_card_bounds`):**
    For every `r ≥ 13`, the active Mod-8190 lanes of `liliuTargetSieved3PrimeFiber N r 13`
    satisfy `card ≤ 1728` (`48 * 36`) unconditionally and `card ≤ 990` (`33 * 30`) under
    Mod-5, Mod-7, and Mod-13 target collisions. -/
theorem liliuTargetSieved13_mod8190_card_bounds
    {N r : ℕ} (hr13 : 13 ≤ r) :
    ((liliuTargetSieved3PrimeFiber N r 13).image (fun q : ℕ => q % 8190)).card ≤ 1728 ∧
    (∀ c₅ c₇ c₁₃ : ℕ,
      1 ≤ c₅ → c₅ < 5 → (r * c₅) % 5 = N % 5 →
      1 ≤ c₇ → c₇ < 7 → (r * c₇) % 7 = N % 7 →
      1 ≤ c₁₃ → c₁₃ < 13 → (r * c₁₃) % 13 = N % 13 →
      ((liliuTargetSieved3PrimeFiber N r 13).image (fun q : ℕ => q % 8190)).card ≤ 990) := by
  have h_sub := liliuTargetSieved13_mod8190_subset_image N r
  have h_prod_le :
      ((liliuTargetSieved3PrimeFiber N r 13).image (fun q : ℕ => q % 8190)).card ≤
        ((liliuTargetSieved3PrimeFiber N r 13).image (fun q : ℕ => q % 65)).card *
        ((liliuTargetSieved3PrimeFiber N r 7).image (fun q : ℕ => q % 63)).card := by
    have h1 := Nat.le_trans (card_le_card h_sub) card_image_le
    rw [card_product] at h1
    exact h1
  have hr7 : 7 ≤ r := by omega
  have h65_bounds := liliuTargetSieved13_mod65_card_bounds (N := N) hr13
  have h63_bounds := liliuTargetSieved7_mod63_card_bounds (N := N) hr7
  have h65_le48 := h65_bounds.2.2.2.1
  have h63_le36 := h63_bounds.2.1
  have h_mul1728 := Nat.mul_le_mul h65_le48 h63_le36
  refine ⟨by omega, ?_⟩
  intro c₅ c₇ c₁₃ hc5_pos hc5_lt h_c5 hc7_pos hc7_lt h_c7 hc13_pos hc13_lt h_c13
  have h65_le33 := h65_bounds.2.2.2.2.2 c₅ c₁₃ hc5_pos hc5_lt h_c5 hc13_pos hc13_lt h_c13
  have h63_le30 := h63_bounds.2.2.2 c₇ hc7_pos hc7_lt h_c7
  have h_mul990 := Nat.mul_le_mul h65_le33 h63_le30
  omega

/-- 2D reconstruction map `(c, j) ↦ m * (L_div + j) + c`. -/
def liliuReconstructResidueAndQuotientPair (m L_div : ℕ) (pair : ℕ × ℕ) : ℕ :=
  m * (L_div + pair.2) + pair.1

/-- **Theorem 2.2 (`liliuFloorSubfiber_card_le_admissible_mul_stride`):**
    Constructive Global Per-Fiber Product Bound on `D19 N`:
    For ANY certified floor `L : ℕ` and ANY modulus `m > 0` (including `m = 65`, `130`, and `8190`),
    `(liliuFloorSubfiber N r L).card ≤ ((liliuFloorSubfiber N r L).image (fun q => q % m)).card * (((N / r) / m - L / m) + 1)`. -/
theorem liliuFloorSubfiber_card_le_admissible_mul_stride
    {N r L m : ℕ} (hm_pos : 0 < m) :
    (liliuFloorSubfiber N r L).card ≤
      ((liliuFloorSubfiber N r L).image (fun q : ℕ => q % m)).card *
        (((N / r) / m - L / m) + 1) := by
  have h_sub :
      liliuFloorSubfiber N r L ⊆
        ((liliuFloorSubfiber N r L).image (fun q : ℕ => q % m) ×ˢ
         range (((N / r) / m - L / m) + 1)).image
          (liliuReconstructResidueAndQuotientPair m (L / m)) := by
    intro q hq
    have hq_copy := hq
    rw [liliuFloorSubfiber, mem_filter] at hq_copy
    have h_q_le : q ≤ N / r := (liliuTight3PrimeFiber_mem_props hq_copy.1).2.2.1
    have h_q_div_ge : L / m ≤ q / m := div_le_div_right_liliu hm_pos hq_copy.2
    have h_q_div_le : q / m ≤ (N / r) / m := div_le_div_right_liliu hm_pos h_q_le
    have h_div_mod : m * (q / m) + q % m = q := Nat.div_add_mod q m
    have h_add_sub : L / m + (q / m - L / m) = q / m := by omega
    rw [mem_image]
    refine ⟨(q % m, q / m - L / m), ?_, ?_⟩
    · rw [mem_product, mem_image, mem_range]
      exact ⟨⟨q, hq, rfl⟩, by omega⟩
    · unfold liliuReconstructResidueAndQuotientPair
      dsimp only
      rw [h_add_sub]
      omega
  have h1 := Nat.le_trans (card_le_card h_sub) card_image_le
  rw [card_product, card_range] at h1
  exact h1

/-- **Master 39-Module Capstone (`master_39module_D19_rsc_multiplexor_and_global_fiber_product_capstone`):**
    Complete 39-Module Capstone uniting `Goldbach.one_plus_one_nine_count` (`liuMainTerm0004 N < (D19 N : ℝ)`),
    the 5-Channel RSC Orthogonal Frequency Multiplexor (`liliuRscMultiplex8190_roundtrip_id`),
    the Collapse of all 31 Struck Alternate Histories (`liliuFiber_struck5ChannelHistory_card_eq_zero`),
    the Mod-8190 Active Lane Bound (`1728` and `990` lanes out of `8190`),
    the Constructive Global Per-Fiber Product Contraction (`liliuFloorSubfiber_card_le_admissible_mul_stride`),
    and the Factorial Lighthouse Next-Prime Generator (`hasNextPrimeConnection_unconditional`). -/
theorem master_39module_D19_rsc_multiplexor_and_global_fiber_product_capstone :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (∀ q : ℕ,
        liliuRscMultiplex8190 (q % 2) (q % 9) (q % 5) (q % 7) (q % 13) = q % 8190) ∧
      (∀ r : ℕ, 13 ≤ r →
        (liliuStruck5ChannelHistoryDomain (liliuShearContractedFiber N r)).card = 0 ∧
        ((liliuTargetSieved3PrimeFiber N r 13).image (fun q : ℕ => q % 8190)).card ≤ 1728) ∧
      (∀ r L m : ℕ, 0 < m →
        (liliuFloorSubfiber N r L).card ≤
          ((liliuFloorSubfiber N r L).image (fun q : ℕ => q % m)).card *
            (((N / r) / m - L / m) + 1)) ∧
      (fiveupPinchedQRSubfilter 9 10 N).card ≤
        1 + ((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).card ∧
      ((((1 + ((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).card : ℕ) : ℝ) ≤
          liuMainTerm0004 N) →
        ∃ p q p_next' : ℕ,
          Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next' ∧ IsPrimeNat p_next') := by
  obtain ⟨K, hK4, hCap37⟩ := master_37module_D19_universal_pVen_and_mod8190_capstone
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven
  have hM := hCap37 N hNK hEven
  refine ⟨hM.1,
          fun q => (liliuRscMultiplex8190_roundtrip_id q).2,
          ?_,
          fun r L m hm => liliuFloorSubfiber_card_le_admissible_mul_stride hm,
          hM.2.2.2.2.2.2.1,
          hM.2.2.2.2.2.2.2⟩
  intro r hr13
  exact ⟨(liliuFiber_struck5ChannelHistory_card_eq_zero hr13).1,
         (liliuTargetSieved13_mod8190_card_bounds hr13).1⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.liliuRscMultiplex8190_roundtrip_id
#print axioms WuPaper.ESZerosBridge.liliuFiber_struck5ChannelHistory_card_eq_zero
#print axioms WuPaper.ESZerosBridge.liliuTargetSieved13_mod8190_card_bounds
#print axioms WuPaper.ESZerosBridge.liliuFloorSubfiber_card_le_admissible_mul_stride
#print axioms WuPaper.ESZerosBridge.master_39module_D19_rsc_multiplexor_and_global_fiber_product_capstone
