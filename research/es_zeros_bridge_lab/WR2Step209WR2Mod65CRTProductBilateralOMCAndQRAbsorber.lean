import WR2Step207WR2Mod130CompositeStrideAndBilateralOMCCardBound

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step209WR2Mod65CRTProductBilateralOMCAndQRAbsorber.lean — Disjoint `p`-ven Domains & Mod-65 CRT Orthogonal Idempotent Absorber

1. **Disjoint `p`-ven Domain Decomposition (`pVenDomain`, `nonPVenDomain`,
   `disjoint_pVen_nonPVen`, `card_eq_pVen_add_nonPVen`, `wr2Fiber_pVenDomain_card_eq_zero`):**
   Explicitly partitions any finite set `S : Finset ℕ` into its `p`-ven multiples
   (`q % p = 0`: Evens for `p = 2`, Threevens for `p = 3`, Fivens for `p = 5`, Sevens for `p = 7`,
   Thirteenvens for `p = 13`) and its `nonPVenDomain` (`1 ≤ q % p`), proving that on
   `wr2ShearContractedFiber N r`, the `p`-ven domain vanishes identically for all `2 ≤ p ≤ r`.
2. **Branch-Free Mod-65 Orthogonal Idempotent Reconstruction (`crtReconstruct65_mod5_mod13_id`):**
   Uses the orthogonal idempotents `(26, 40)` (`26 * a + 40 * b % 65`) to reconstruct
   Mod-65 lanes from Fivens (`Mod 5`) and Thirteenvens (`Mod 13`) survivor lanes.
3. **Explicit `48`-Lane and `33`-Lane Contraction Bounds (`targetSieved13_mod65_admissible_card_bounds`):**
   Connects both `fiveup_reciprocal_involution_base_m5` (`m = 5`) and
   `fiveup_reciprocal_involution_lane_halving` (`m = 13`) and proves the `48`-lane and
   `33`-lane (`3 * 11`) bilateral OMC product bounds on Mod-65.
-/

/-!
## Section 1: Disjoint `p`-ven Domains (Evens, Threevens, Fivens, Sevens, Thirteenvens)
-/

/-- The `p`-ven domain of `S`: elements divisible by `p` (`q % p = 0`, e.g., Evens for `p = 2`,
    Threevens for `p = 3`, Fivens for `p = 5`, Sevens for `p = 7`, Thirteenvens for `p = 13`). -/
def pVenDomain (S : Finset ℕ) (p : ℕ) : Finset ℕ :=
  S.filter (fun q : ℕ => q % p = 0)

/-- The non-`p`-ven domain of `S`: elements with positive remainder `1 ≤ q % p`. -/
def nonPVenDomain (S : Finset ℕ) (p : ℕ) : Finset ℕ :=
  S.filter (fun q : ℕ => 1 ≤ q % p)

/-- Strict disjointness of `pVenDomain S p` and `nonPVenDomain S p`. -/
theorem disjoint_pVen_nonPVen (S : Finset ℕ) (p : ℕ) :
    Disjoint (pVenDomain S p) (nonPVenDomain S p) := by
  rw [Finset.disjoint_left]
  intro q hpv hnpv
  rw [pVenDomain, mem_filter] at hpv
  rw [nonPVenDomain, mem_filter] at hnpv
  have h0 : q % p = 0 := hpv.2
  have h1 : 1 ≤ q % p := hnpv.2
  omega

/-- Exact set union partitioning `S` into its `p`-ven and non-`p`-ven domains. -/
theorem eq_pVen_union_nonPVen (S : Finset ℕ) (p : ℕ) :
    S = pVenDomain S p ∪ nonPVenDomain S p := by
  ext q
  rw [mem_union, pVenDomain, nonPVenDomain, mem_filter, mem_filter]
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

/-- **Theorem 1.1 (`card_eq_pVen_add_nonPVen`):**
    Exact additive cardinality partition across the `p`-ven and non-`p`-ven domains. -/
theorem card_eq_pVen_add_nonPVen (S : Finset ℕ) (p : ℕ) :
    S.card = (pVenDomain S p).card + (nonPVenDomain S p).card := by
  conv_lhs => rw [eq_pVen_union_nonPVen S p]
  exact card_union_of_disjoint (disjoint_pVen_nonPVen S p)

/-- **Theorem 1.2 (`wr2Fiber_pVenDomain_card_eq_zero`):**
    For every `p` with `2 ≤ p ≤ r` (covering Evens `2`, Threevens `3`, Fivens `5`, Sevens `7`,
    Elevenvens `11`, Thirteenvens `13`), the `p`-ven domain on `wr2ShearContractedFiber N r`
    vanishes identically (`card = 0`), so the entire fiber lies in `nonPVenDomain`. -/
theorem wr2Fiber_pVenDomain_card_eq_zero
    {N r p : ℕ} (hp2 : 2 ≤ p) (hpr : p ≤ r) :
    (pVenDomain (wr2ShearContractedFiber N r) p).card = 0 ∧
    (wr2ShearContractedFiber N r).card =
      (nonPVenDomain (wr2ShearContractedFiber N r) p).card := by
  have h_eq_slice :
      pVenDomain (wr2ShearContractedFiber N r) p =
        residueClassSlice (wr2ShearContractedFiber N r) p 0 := rfl
  have h_zero : (pVenDomain (wr2ShearContractedFiber N r) p).card = 0 := by
    rw [h_eq_slice]
    exact wr2ShearContractedFiber_zero_slice_eq_zero hp2 hpr
  have h_part := card_eq_pVen_add_nonPVen (wr2ShearContractedFiber N r) p
  omega

/-!
## Section 2: Branch-Free Mod-65 CRT Orthogonal Idempotent Absorber (`26, 40`)
-/

/-- Branch-free CRT reconstruction absorber from Fivens (`Mod 5`) and Thirteenvens (`Mod 13`)
    to `Mod 65`: uses orthogonal idempotents `26 ≡ 1 (mod 5), 0 (mod 13)` and `40 ≡ 0 (mod 5), 1 (mod 13)`. -/
def crtReconstruct65From5And13 (pair : ℕ × ℕ) : ℕ :=
  (26 * pair.1 + 40 * pair.2) % 65

/-- Pure native Presburger proof of the Mod-65 CRT round-trip identity and sub-modulus projections. -/
theorem crtReconstruct65_mod5_mod13_id (q c : ℕ) (hc : c < 65) :
    crtReconstruct65From5And13 (c % 5, c % 13) = c ∧
    (q % 65) % 5 = q % 5 ∧
    (q % 65) % 13 = q % 13 := by
  unfold crtReconstruct65From5And13
  dsimp only
  omega

/-- Target-sieved inclusion: `wr2TargetSievedFiber N r 13 ⊆ wr2TargetSievedFiber N r 5`. -/
theorem wr2TargetSievedFiber_13_subset_5 (N r : ℕ) :
    wr2TargetSievedFiber N r 13 ⊆ wr2TargetSievedFiber N r 5 := by
  intro q hq
  rw [wr2TargetSievedFiber, mem_filter] at hq ⊢
  exact ⟨hq.1, by omega⟩

/-- **Theorem 2.1 (`targetSieved13_mod65_admissible_subset_image_crt5_13`):**
    For every `r ≥ 13`, the active Mod-65 residue classes of `wr2TargetSievedFiber N r 13`
    are contained in the image under `crtReconstruct65From5And13` of
    `bilateralOMCResidues N r 5 ×ˢ bilateralOMCResidues N r 13`. -/
theorem targetSieved13_mod65_admissible_subset_image_crt5_13
    {N r : ℕ} (hr13 : 13 ≤ r) :
    admissibleFiberResidues (wr2TargetSievedFiber N r 13) 65 ⊆
      (bilateralOMCResidues N r 5 ×ˢ bilateralOMCResidues N r 13).image
        crtReconstruct65From5And13 := by
  intro c hc
  rw [admissibleFiberResidues, mem_image] at hc
  obtain ⟨q, hq13, rfl⟩ := hc
  have hq5 : q ∈ wr2TargetSievedFiber N r 5 := wr2TargetSievedFiber_13_subset_5 N r hq13
  have hr5 : 5 ≤ r := by omega
  have h_sub5 := targetSievedFiber_admissible_subset_bilateralOMCResidues (N := N) (by omega : 2 ≤ 5) hr5
  have h_sub13 := targetSievedFiber_admissible_subset_bilateralOMCResidues (N := N) (by omega : 2 ≤ 13) hr13
  have h_mem5 : q % 5 ∈ bilateralOMCResidues N r 5 := by
    apply h_sub5
    rw [admissibleFiberResidues, mem_image]
    exact ⟨q, hq5, rfl⟩
  have h_mem13 : q % 13 ∈ bilateralOMCResidues N r 13 := by
    apply h_sub13
    rw [admissibleFiberResidues, mem_image]
    exact ⟨q, hq13, rfl⟩
  have h_c_lt : q % 65 < 65 := Nat.mod_lt q (by omega : 0 < 65)
  have h_crt := crtReconstruct65_mod5_mod13_id q (q % 65) h_c_lt
  rw [mem_image]
  refine ⟨(q % 5, q % 13), ?_, ?_⟩
  · rw [mem_product]
    exact ⟨h_mem5, h_mem13⟩
  · rw [← h_crt.2.1, ← h_crt.2.2]
    exact h_crt.1

/-- **Theorem 2.2 (`targetSieved13_mod65_admissible_card_bounds`):**
    For every `r ≥ 13`:
    1. Both Fivens (`p = 5`) and Thirteenvens (`p = 13`) `pVenDomain` sets vanish on the fiber,
    2. `(admissibleFiberResidues (wr2TargetSievedFiber N r 13) 65).card ≤ 48` (`4 * 12`),
    3. Both `fiveup_reciprocal_involution_base_m5` (`m = 5`) and
       `fiveup_reciprocal_involution_lane_halving` (`m = 13`) hold explicitly, and
    4. When non-zero Mod-5 and Mod-13 target collision lanes `c₅, c₁₃` exist,
       `(admissibleFiberResidues (wr2TargetSievedFiber N r 13) 65).card ≤ 33` (`3 * 11`). -/
theorem targetSieved13_mod65_admissible_card_bounds
    {N r : ℕ} (hr13 : 13 ≤ r) :
    (pVenDomain (wr2ShearContractedFiber N r) 5).card = 0 ∧
    (pVenDomain (wr2ShearContractedFiber N r) 13).card = 0 ∧
    (admissibleFiberResidues (wr2TargetSievedFiber N r 13) 65).card ≤
      (bilateralOMCResidues N r 5).card * (bilateralOMCResidues N r 13).card ∧
    (admissibleFiberResidues (wr2TargetSievedFiber N r 13) 65).card ≤ 48 ∧
    ((5 - 1) / 2 < 5 - 2 ∧ (13 + 1) / 2 < 13 - 2) ∧
    (∀ c₅ c₁₃ : ℕ,
      1 ≤ c₅ → c₅ < 5 → (r * c₅) % 5 = N % 5 →
      1 ≤ c₁₃ → c₁₃ < 13 → (r * c₁₃) % 13 = N % 13 →
      (admissibleFiberResidues (wr2TargetSievedFiber N r 13) 65).card ≤ 33) := by
  have h_fiven0 : (pVenDomain (wr2ShearContractedFiber N r) 5).card = 0 :=
    (wr2Fiber_pVenDomain_card_eq_zero (by omega : 2 ≤ 5) (by omega : 5 ≤ r)).1
  have h_thirteenven0 : (pVenDomain (wr2ShearContractedFiber N r) 13).card = 0 :=
    (wr2Fiber_pVenDomain_card_eq_zero (by omega : 2 ≤ 13) hr13).1
  have h_sub := targetSieved13_mod65_admissible_subset_image_crt5_13 (N := N) hr13
  have h_prod_le :
      (admissibleFiberResidues (wr2TargetSievedFiber N r 13) 65).card ≤
        (bilateralOMCResidues N r 5).card * (bilateralOMCResidues N r 13).card := by
    have h1 := Nat.le_trans (card_le_card h_sub) card_image_le
    rw [card_product] at h1
    exact h1
  have h5_le4 : (bilateralOMCResidues N r 5).card ≤ 4 :=
    (bilateralOMCResidues_card_le_sub_one N r 5).2
  have h13_le12 : (bilateralOMCResidues N r 13).card ≤ 12 :=
    (bilateralOMCResidues_card_le_sub_one N r 13).2
  have h_mul48 :
      (bilateralOMCResidues N r 5).card * (bilateralOMCResidues N r 13).card ≤ 4 * 12 :=
    Nat.mul_le_mul h5_le4 h13_le12
  have h_inv5 :=
    fiveup_reciprocal_involution_base_m5 (m := 5) (by omega : 5 ≤ 5) (by omega : 5 % 2 = 1)
  have h_inv13 :=
    fiveup_reciprocal_involution_lane_halving (m := 13) (by omega : 7 ≤ 13) (by omega : 13 % 2 = 1)
  refine ⟨h_fiven0, h_thirteenven0, h_prod_le, by omega, ⟨h_inv5.2.1, h_inv13.2.1⟩, ?_⟩
  intro c₅ c₁₃ hc5_pos hc5_lt h_coll5 hc13_pos hc13_lt h_coll13
  have h5_le3 : (bilateralOMCResidues N r 5).card ≤ 3 :=
    (bilateralOMCResidues_card_le_sub_two_of_collision
      (by omega : 2 ≤ 5) (by omega : 5 ≤ r) hc5_pos hc5_lt h_coll5).1
  have h13_le11 : (bilateralOMCResidues N r 13).card ≤ 11 :=
    (bilateralOMCResidues_card_le_sub_two_of_collision
      (by omega : 2 ≤ 13) hr13 hc13_pos hc13_lt h_coll13).1
  have h_mul33 :
      (bilateralOMCResidues N r 5).card * (bilateralOMCResidues N r 13).card ≤ 3 * 11 :=
    Nat.mul_le_mul h5_le3 h13_le11
  omega

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.card_eq_pVen_add_nonPVen
#print axioms WuPaper.ESZerosBridge.wr2Fiber_pVenDomain_card_eq_zero
#print axioms WuPaper.ESZerosBridge.crtReconstruct65_mod5_mod13_id
#print axioms WuPaper.ESZerosBridge.targetSieved13_mod65_admissible_subset_image_crt5_13
#print axioms WuPaper.ESZerosBridge.targetSieved13_mod65_admissible_card_bounds
