import WR2Step208LiLiuMod130CompositeStrideAndOMCCardCapstone

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step210LiLiuMod65CRTProductBilateralOMCAndQRAbsorberCapstone.lean — Disjoint `p`-ven Domains & Mod-65 CRT Product Contraction (`48` & `33` Lanes) for `D19 N`

Welds the Disjoint `p`-ven Domain Partition (`liliuPVenDomain`, `liliuNonPVenDomain`),
the Branch-Free Mod-65 Orthogonal Idempotent Absorber (`liliuCrtReconstruct65From5And13`),
and the Simultaneous Mod-5 × Mod-13 Bilateral OMC Product Contraction (`48` and `33` lanes)
into the `Goldbach.All` (`D19 N`) Capstone.
-/

/-!
## Section 1: Disjoint `p`-ven Domains on `liliuShearContractedFiber`
-/

/-- The `p`-ven domain of `S`: elements divisible by `p` (`q % p = 0`). -/
def liliuPVenDomain (S : Finset ℕ) (p : ℕ) : Finset ℕ :=
  S.filter (fun q : ℕ => q % p = 0)

/-- The non-`p`-ven domain of `S`: elements with positive remainder `1 ≤ q % p`. -/
def liliuNonPVenDomain (S : Finset ℕ) (p : ℕ) : Finset ℕ :=
  S.filter (fun q : ℕ => 1 ≤ q % p)

theorem disjoint_liliuPVen_nonPVen (S : Finset ℕ) (p : ℕ) :
    Disjoint (liliuPVenDomain S p) (liliuNonPVenDomain S p) := by
  rw [Finset.disjoint_left]
  intro q hpv hnpv
  rw [liliuPVenDomain, mem_filter] at hpv
  rw [liliuNonPVenDomain, mem_filter] at hnpv
  have h0 : q % p = 0 := hpv.2
  have h1 : 1 ≤ q % p := hnpv.2
  omega

theorem eq_liliuPVen_union_nonPVen (S : Finset ℕ) (p : ℕ) :
    S = liliuPVenDomain S p ∪ liliuNonPVenDomain S p := by
  ext q
  rw [mem_union, liliuPVenDomain, liliuNonPVenDomain, mem_filter, mem_filter]
  constructor
  · intro hq
    if h0 : q % p = 0 then
      exact Or.inl ⟨hq, h0⟩
    else
      exact Or.inr ⟨hq, by omega⟩
  · intro hor
    cases hor with
    | inl hpv => exact hpv.1
    | inr hnpv => exact hnpv.1

theorem card_eq_liliuPVen_add_nonPVen (S : Finset ℕ) (p : ℕ) :
    S.card = (liliuPVenDomain S p).card + (liliuNonPVenDomain S p).card := by
  conv_lhs => rw [eq_liliuPVen_union_nonPVen S p]
  exact card_union_of_disjoint (disjoint_liliuPVen_nonPVen S p)

/-- For every `p` with `2 ≤ p ≤ r`, `(liliuPVenDomain (liliuShearContractedFiber N r) p).card = 0`. -/
theorem liliuFiber_pVenDomain_card_eq_zero
    {N r p : ℕ} (hp2 : 2 ≤ p) (hpr : p ≤ r) :
    (liliuPVenDomain (liliuShearContractedFiber N r) p).card = 0 ∧
    (liliuShearContractedFiber N r).card =
      (liliuNonPVenDomain (liliuShearContractedFiber N r) p).card := by
  have h_eq_slice :
      liliuPVenDomain (liliuShearContractedFiber N r) p = liliuResidueSlice N r p 0 := rfl
  have h_zero : (liliuPVenDomain (liliuShearContractedFiber N r) p).card = 0 := by
    rw [h_eq_slice]
    exact (liliuShearContractedFiber_stride_bounds N r).2.2 p hp2 hpr
  have h_part := card_eq_liliuPVen_add_nonPVen (liliuShearContractedFiber N r) p
  omega

/-!
## Section 2: Branch-Free Mod-65 CRT Orthogonal Idempotent Absorber (`26, 40`)
-/

/-- Branch-free CRT reconstruction absorber from `Mod 5 × Mod 13` to `Mod 65`:
    `(26 * pair.1 + 40 * pair.2) % 65`. -/
def liliuCrtReconstruct65From5And13 (pair : ℕ × ℕ) : ℕ :=
  (26 * pair.1 + 40 * pair.2) % 65

theorem liliuCrtReconstruct65_mod5_mod13_id (q c : ℕ) (hc : c < 65) :
    liliuCrtReconstruct65From5And13 (c % 5, c % 13) = c ∧
    (q % 65) % 5 = q % 5 ∧
    (q % 65) % 13 = q % 13 := by
  unfold liliuCrtReconstruct65From5And13
  dsimp only
  omega

theorem liliuTargetSieved3PrimeFiber_13_subset_5 (N r : ℕ) :
    liliuTargetSieved3PrimeFiber N r 13 ⊆ liliuTargetSieved3PrimeFiber N r 5 := by
  intro q hq
  rw [liliuTargetSieved3PrimeFiber, mem_filter] at hq ⊢
  exact ⟨hq.1, by omega⟩

/-- **Theorem 2.1 (`liliuTargetSieved13_mod65_subset_image_crt5_13`):**
    For every `r ≥ 13`, the active Mod-65 residue classes of `liliuTargetSieved3PrimeFiber N r 13`
    are contained in the image under `liliuCrtReconstruct65From5And13` of
    `liliuBilateralOMCResidues N r 5 ×ˢ liliuBilateralOMCResidues N r 13`. -/
theorem liliuTargetSieved13_mod65_subset_image_crt5_13
    {N r : ℕ} (hr13 : 13 ≤ r) :
    (liliuTargetSieved3PrimeFiber N r 13).image (fun q : ℕ => q % 65) ⊆
      (liliuBilateralOMCResidues N r 5 ×ˢ liliuBilateralOMCResidues N r 13).image
        liliuCrtReconstruct65From5And13 := by
  intro c hc
  rw [mem_image] at hc
  obtain ⟨q, hq13, rfl⟩ := hc
  have hq5 : q ∈ liliuTargetSieved3PrimeFiber N r 5 :=
    liliuTargetSieved3PrimeFiber_13_subset_5 N r hq13
  have hr5 : 5 ≤ r := by omega
  have h_sub5 := liliuTargetSieved_admissible_subset_bilateralOMC (N := N) (by omega : 2 ≤ 5) hr5
  have h_sub13 := liliuTargetSieved_admissible_subset_bilateralOMC (N := N) (by omega : 2 ≤ 13) hr13
  have h_mem5 : q % 5 ∈ liliuBilateralOMCResidues N r 5 := by
    apply h_sub5
    rw [mem_image]
    exact ⟨q, hq5, rfl⟩
  have h_mem13 : q % 13 ∈ liliuBilateralOMCResidues N r 13 := by
    apply h_sub13
    rw [mem_image]
    exact ⟨q, hq13, rfl⟩
  have h_c_lt : q % 65 < 65 := Nat.mod_lt q (by omega : 0 < 65)
  have h_crt := liliuCrtReconstruct65_mod5_mod13_id q (q % 65) h_c_lt
  rw [mem_image]
  refine ⟨(q % 5, q % 13), ?_, ?_⟩
  · rw [mem_product]
    exact ⟨h_mem5, h_mem13⟩
  · rw [← h_crt.2.1, ← h_crt.2.2]
    exact h_crt.1

/-- **Theorem 2.2 (`liliuTargetSieved13_mod65_card_bounds`):**
    For every `r ≥ 13`, the Fivens (`p = 5`) and Thirteenvens (`p = 13`) `pVenDomain` sets
    vanish on `liliuShearContractedFiber N r`, and the active Mod-65 lanes of
    `liliuTargetSieved3PrimeFiber N r 13` satisfy `card ≤ 48` unconditionally and
    `card ≤ 33` whenever Mod-5 and Mod-13 non-zero target collision lanes exist. -/
theorem liliuTargetSieved13_mod65_card_bounds
    {N r : ℕ} (hr13 : 13 ≤ r) :
    (liliuPVenDomain (liliuShearContractedFiber N r) 5).card = 0 ∧
    (liliuPVenDomain (liliuShearContractedFiber N r) 13).card = 0 ∧
    ((liliuTargetSieved3PrimeFiber N r 13).image (fun q : ℕ => q % 65)).card ≤
      (liliuBilateralOMCResidues N r 5).card * (liliuBilateralOMCResidues N r 13).card ∧
    ((liliuTargetSieved3PrimeFiber N r 13).image (fun q : ℕ => q % 65)).card ≤ 48 ∧
    ((5 - 1) / 2 < 5 - 2 ∧ (13 + 1) / 2 < 13 - 2) ∧
    (∀ c₅ c₁₃ : ℕ,
      1 ≤ c₅ → c₅ < 5 → (r * c₅) % 5 = N % 5 →
      1 ≤ c₁₃ → c₁₃ < 13 → (r * c₁₃) % 13 = N % 13 →
      ((liliuTargetSieved3PrimeFiber N r 13).image (fun q : ℕ => q % 65)).card ≤ 33) := by
  have h_fiven0 : (liliuPVenDomain (liliuShearContractedFiber N r) 5).card = 0 :=
    (liliuFiber_pVenDomain_card_eq_zero (by omega : 2 ≤ 5) (by omega : 5 ≤ r)).1
  have h_thirteenven0 : (liliuPVenDomain (liliuShearContractedFiber N r) 13).card = 0 :=
    (liliuFiber_pVenDomain_card_eq_zero (by omega : 2 ≤ 13) hr13).1
  have h_sub := liliuTargetSieved13_mod65_subset_image_crt5_13 (N := N) hr13
  have h_prod_le :
      ((liliuTargetSieved3PrimeFiber N r 13).image (fun q : ℕ => q % 65)).card ≤
        (liliuBilateralOMCResidues N r 5).card * (liliuBilateralOMCResidues N r 13).card := by
    have h1 := Nat.le_trans (card_le_card h_sub) card_image_le
    rw [card_product] at h1
    exact h1
  have h5_le4 : (liliuBilateralOMCResidues N r 5).card ≤ 4 :=
    liliuBilateralOMCResidues_card_le_sub_one N r 5
  have h13_le12 : (liliuBilateralOMCResidues N r 13).card ≤ 12 :=
    liliuBilateralOMCResidues_card_le_sub_one N r 13
  have h_mul48 :
      (liliuBilateralOMCResidues N r 5).card * (liliuBilateralOMCResidues N r 13).card ≤ 4 * 12 :=
    Nat.mul_le_mul h5_le4 h13_le12
  have h_inv5 :=
    fiveup_reciprocal_involution_base_m5 (m := 5) (by omega : 5 ≤ 5) (by omega : 5 % 2 = 1)
  have h_inv13 :=
    fiveup_reciprocal_involution_lane_halving (m := 13) (by omega : 7 ≤ 13) (by omega : 13 % 2 = 1)
  refine ⟨h_fiven0, h_thirteenven0, h_prod_le, by omega, ⟨h_inv5.2.1, h_inv13.2.1⟩, ?_⟩
  intro c₅ c₁₃ hc5_pos hc5_lt h_coll5 hc13_pos hc13_lt h_coll13
  have h5_le3 : (liliuBilateralOMCResidues N r 5).card ≤ 3 :=
    (liliuBilateralOMCResidues_card_le_sub_two_of_collision
      (by omega : 2 ≤ 5) (by omega : 5 ≤ r) hc5_pos hc5_lt h_coll5).1
  have h13_le11 : (liliuBilateralOMCResidues N r 13).card ≤ 11 :=
    (liliuBilateralOMCResidues_card_le_sub_two_of_collision
      (by omega : 2 ≤ 13) hr13 hc13_pos hc13_lt h_coll13).1
  have h_mul33 :
      (liliuBilateralOMCResidues N r 5).card * (liliuBilateralOMCResidues N r 13).card ≤ 3 * 11 :=
    Nat.mul_le_mul h5_le3 h13_le11
  omega

/-- **Master 33-Module Capstone (`master_33module_D19_mod65_crt_absorber_and_mod130_stride_capstone`):**
    Complete 33-Module Capstone uniting `Goldbach.one_plus_one_nine_count` (`liuMainTerm0004 N < (D19 N : ℝ)`),
    the Disjoint `p`-ven Domain Vanishing Theorems, the 3-Prime Tight `9/19` Hyperbolic Fibers,
    the Mod-65 Orthogonal Idempotent CRT Absorber (`48`-lane and `33`-lane contractions),
    and the Branch-Free Mod-130 Parity-CRT Stride Bound (`((N / r) / 130 - L / 130) + 1`). -/
theorem master_33module_D19_mod65_crt_absorber_and_mod130_stride_capstone :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (∀ r : ℕ, 13 ≤ r →
        (liliuPVenDomain (liliuShearContractedFiber N r) 5).card = 0 ∧
        (liliuPVenDomain (liliuShearContractedFiber N r) 13).card = 0 ∧
        ((liliuTargetSieved3PrimeFiber N r 13).image (fun q : ℕ => q % 65)).card ≤ 48 ∧
        ∀ c₅ c₁₃ : ℕ,
          1 ≤ c₅ → c₅ < 5 → (r * c₅) % 5 = N % 5 →
          1 ≤ c₁₃ → c₁₃ < 13 → (r * c₁₃) % 13 = N % 13 →
          ((liliuTargetSieved3PrimeFiber N r 13).image (fun q : ℕ => q % 65)).card ≤ 33) ∧
      (∀ r L c : ℕ, c < 65 →
        (liliuFloorResidueSlice N r L 65 c).card ≤ ((N / r) / 130 - L / 130) + 1) ∧
      (fiveupPinchedQRSubfilter 9 10 N).card ≤
        1 + ((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).card ∧
      ((((1 + ((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).card : ℕ) : ℝ) ≤
          liuMainTerm0004 N) →
        ∃ p q p_next' : ℕ,
          Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next' ∧ IsPrimeNat p_next') := by
  obtain ⟨K, hK4, hCap⟩ := master_31module_D19_mod130_stride_and_bilateral_omc_capstone
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven
  have hM := hCap N hNK hEven
  refine ⟨hM.1, ?_, hM.2.2.2.1, hM.2.2.2.2.1, hM.2.2.2.2.2⟩
  intro r hr13
  have h_b := liliuTargetSieved13_mod65_card_bounds (N := N) hr13
  exact ⟨h_b.1, h_b.2.1, h_b.2.2.2.1, h_b.2.2.2.2.2⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.liliuFiber_pVenDomain_card_eq_zero
#print axioms WuPaper.ESZerosBridge.liliuCrtReconstruct65_mod5_mod13_id
#print axioms WuPaper.ESZerosBridge.liliuTargetSieved13_mod65_subset_image_crt5_13
#print axioms WuPaper.ESZerosBridge.liliuTargetSieved13_mod65_card_bounds
#print axioms WuPaper.ESZerosBridge.master_33module_D19_mod65_crt_absorber_and_mod130_stride_capstone
