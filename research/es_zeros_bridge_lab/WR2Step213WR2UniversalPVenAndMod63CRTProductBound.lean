import WR2Step211WR2Mod8190TripleQRAbsorberAndFiberSumBound

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step213WR2UniversalPVenAndMod63CRTProductBound.lean — Disjoint Bilateral `p`-ven Domains & Mod-63 (`9 × 7`) CRT Absorber

1. **Disjoint Bilateral `p`-ven Partition (`targetPVenCollisionDomain`, `bilateralNonPVenDomain`,
   `wr2TargetSievedFiber_bilateral_pVen_vanish`):**
   Partitions `nonPVenDomain S p` into `targetPVenCollisionDomain S N r p`
   (`(r * (q % p)) % p = N % p`) and `bilateralNonPVenDomain S N r p`
   (`(r * (q % p)) % p ≠ N % p`), proving that for EVERY `p` with `2 ≤ p ≤ r`, both
   `pVenDomain` and `targetPVenCollisionDomain` vanish identically on `wr2TargetSievedFiber N r p`.
2. **Branch-Free Mod-63 (`9 × 7`) Orthogonal Idempotent Absorber (`crtReconstruct63From9And7`):**
   Uses the orthogonal idempotents `e₉ = 28` (`28 % 9 = 1, 28 % 7 = 0`) and `e₇ = 36`
   (`36 % 9 = 0, 36 % 7 = 1`) together with Threeven divisibility inheritance (`3 ∣ 9`) and
   Sevenven (`Mod 7`) bilateral OMC to prove that for all `r ≥ 7`:
   - `(admissibleFiberResidues (wr2TargetSievedFiber N r 7) 63).card ≤ 36` (`6 * 6`), and
   - Under a Mod-7 target collision lane `1 ≤ c₇ < 7`, `card ≤ 30` (`6 * 5`).
-/

/-!
## Section 1: Disjoint Bilateral `p`-ven Domains (`targetPVenCollisionDomain` & `bilateralNonPVenDomain`)
-/

/-- The target-side `p`-ven collision domain: elements of `nonPVenDomain S p` whose residue
    `q % p` collides with the target congruence `(r * (q % p)) % p = N % p`. -/
def targetPVenCollisionDomain (S : Finset ℕ) (N r p : ℕ) : Finset ℕ :=
  S.filter (fun q : ℕ => 1 ≤ q % p ∧ (r * (q % p)) % p = N % p)

/-- The bilateral non-`p`-ven survivor domain: elements of `S` surviving both factor-side
    and target-side `p`-ven sieving (`1 ≤ q % p ∧ (r * (q % p)) % p ≠ N % p`). -/
def bilateralNonPVenDomain (S : Finset ℕ) (N r p : ℕ) : Finset ℕ :=
  S.filter (fun q : ℕ => 1 ≤ q % p ∧ (r * (q % p)) % p ≠ N % p)

/-- Strict disjointness of `targetPVenCollisionDomain` and `bilateralNonPVenDomain`. -/
theorem disjoint_targetPVenCollision_bilateralNonPVen (S : Finset ℕ) (N r p : ℕ) :
    Disjoint (targetPVenCollisionDomain S N r p) (bilateralNonPVenDomain S N r p) := by
  rw [Finset.disjoint_left]
  intro q hcoll hbil
  rw [targetPVenCollisionDomain, mem_filter] at hcoll
  rw [bilateralNonPVenDomain, mem_filter] at hbil
  exact hbil.2.2 hcoll.2.2

/-- Exact set union decomposing `nonPVenDomain S p` into `targetPVenCollisionDomain` and
    `bilateralNonPVenDomain`. -/
theorem nonPVenDomain_eq_collision_union_bilateral (S : Finset ℕ) (N r p : ℕ) :
    nonPVenDomain S p =
      targetPVenCollisionDomain S N r p ∪ bilateralNonPVenDomain S N r p := by
  ext q
  rw [mem_union, nonPVenDomain, targetPVenCollisionDomain, bilateralNonPVenDomain,
      mem_filter, mem_filter, mem_filter]
  constructor
  · intro hq
    if h_eq : (r * (q % p)) % p = N % p then
      exact Or.inl ⟨hq.1, hq.2, h_eq⟩
    else
      exact Or.inr ⟨hq.1, hq.2, h_eq⟩
  · intro hor
    cases hor with
    | inl hc => exact ⟨hc.1, hc.2.1⟩
    | inr hb => exact ⟨hb.1, hb.2.1⟩

/-- **Theorem 1.1 (`wr2TargetSievedFiber_bilateral_pVen_vanish`):**
    Universal Bilateral `p`-ven Law: for EVERY integer `p` with `2 ≤ p ≤ r`, on
    `wr2TargetSievedFiber N r p` (`p < N - r * q`), both `pVenDomain` and
    `targetPVenCollisionDomain` vanish identically (`card = 0`), so
    `wr2TargetSievedFiber N r p = bilateralNonPVenDomain (wr2TargetSievedFiber N r p) N r p`. -/
theorem wr2TargetSievedFiber_bilateral_pVen_vanish
    {N r p : ℕ} (hp2 : 2 ≤ p) (hpr : p ≤ r) :
    (pVenDomain (wr2TargetSievedFiber N r p) p).card = 0 ∧
    (targetPVenCollisionDomain (wr2TargetSievedFiber N r p) N r p).card = 0 ∧
    (wr2TargetSievedFiber N r p).card =
      (bilateralNonPVenDomain (wr2TargetSievedFiber N r p) N r p).card := by
  have h_sub_fiber : wr2TargetSievedFiber N r p ⊆ wr2ShearContractedFiber N r :=
    filter_subset _ _
  have h_pv_sub :
      pVenDomain (wr2TargetSievedFiber N r p) p ⊆
        pVenDomain (wr2ShearContractedFiber N r) p := by
    intro q hq
    rw [pVenDomain, mem_filter] at hq ⊢
    exact ⟨h_sub_fiber hq.1, hq.2⟩
  have h_pv_zero_main := (wr2Fiber_pVenDomain_card_eq_zero (N := N) hp2 hpr).1
  have h_pv_le : (pVenDomain (wr2TargetSievedFiber N r p) p).card ≤ 0 := by
    rw [← h_pv_zero_main]
    exact card_le_card h_pv_sub
  have h_coll_zero :
      (targetPVenCollisionDomain (wr2TargetSievedFiber N r p) N r p).card = 0 := by
    match Nat.eq_zero_or_pos
        (targetPVenCollisionDomain (wr2TargetSievedFiber N r p) N r p).card with
    | Or.inl h0 => exact h0
    | Or.inr hpos =>
      obtain ⟨q, hq⟩ := card_pos.mp hpos
      rw [targetPVenCollisionDomain, mem_filter] at hq
      have h_mem_adm : q % p ∈ admissibleFiberResidues (wr2TargetSievedFiber N r p) p := by
        rw [admissibleFiberResidues, mem_image]
        exact ⟨q, hq.1, rfl⟩
      have h_mem_bil :=
        targetSievedFiber_admissible_subset_bilateralOMCResidues (N := N) hp2 hpr h_mem_adm
      rw [bilateralOMCResidues, mem_filter] at h_mem_bil
      exact False.elim (h_mem_bil.2.2 hq.2.2)
  have h_part1 := card_eq_pVen_add_nonPVen (wr2TargetSievedFiber N r p) p
  have h_part2 :
      (nonPVenDomain (wr2TargetSievedFiber N r p) p).card =
        (targetPVenCollisionDomain (wr2TargetSievedFiber N r p) N r p).card +
        (bilateralNonPVenDomain (wr2TargetSievedFiber N r p) N r p).card := by
    conv_lhs => rw [nonPVenDomain_eq_collision_union_bilateral (wr2TargetSievedFiber N r p) N r p]
    exact card_union_of_disjoint
      (disjoint_targetPVenCollision_bilateralNonPVen (wr2TargetSievedFiber N r p) N r p)
  omega

/-!
## Section 2: Branch-Free Mod-63 (`9 × 7`) Orthogonal Idempotent Absorber (`28, 36`)
-/

/-- Branch-free CRT reconstruction absorber from `Mod 9 × Mod 7` to `Mod 63`:
    uses orthogonal idempotents `28 ≡ 1 (mod 9), 0 (mod 7)` and `36 ≡ 0 (mod 9), 1 (mod 7)`. -/
def crtReconstruct63From9And7 (pair : ℕ × ℕ) : ℕ :=
  (28 * pair.1 + 36 * pair.2) % 63

/-- Pure native Presburger proof of the Mod-63 CRT round-trip identity and sub-modulus projections. -/
theorem crtReconstruct63_mod9_mod7_id (q c : ℕ) (hc : c < 63) :
    c < 63 ∧
    crtReconstruct63From9And7 (c % 9, c % 7) = c ∧
    (q % 63) % 9 = q % 9 ∧
    (q % 63) % 7 = q % 7 := by
  refine ⟨hc, ?_⟩
  unfold crtReconstruct63From9And7
  dsimp only
  omega

/-- The `6` non-Threeven residue classes modulo `9`: `{a ∈ range 9 | 1 ≤ a % 3}` (`{1, 2, 4, 5, 7, 8}`). -/
def nonThreevenMod9Residues : Finset ℕ :=
  (range 9).filter (fun a : ℕ => 1 ≤ a % 3)

/-- Branch-free expansion map from `range 6` onto `nonThreevenMod9Residues = {1, 2, 4, 5, 7, 8}`:
    `k ↦ k + 1 + k / 2`. -/
def expandNonThreevenMod9 (k : ℕ) : ℕ :=
  k + 1 + k / 2

theorem nonThreevenMod9Residues_card_le_six :
    nonThreevenMod9Residues.card ≤ 6 := by
  have h_sub : nonThreevenMod9Residues ⊆ (range 6).image expandNonThreevenMod9 := by
    intro a ha
    rw [nonThreevenMod9Residues, mem_filter, mem_range] at ha
    rw [mem_image]
    refine ⟨a - 1 - a / 3, ?_, ?_⟩
    · rw [mem_range]; omega
    · unfold expandNonThreevenMod9; omega
  have h1 := Nat.le_trans (card_le_card h_sub) card_image_le
  rw [card_range] at h1
  exact h1

/-- **Theorem 2.1 (`targetSieved7_mod63_admissible_subset_image_crt9_7`):**
    For every `r ≥ 7`, the active Mod-63 residue classes of `wr2TargetSievedFiber N r 7`
    are contained in the image under `crtReconstruct63From9And7` of
    `nonThreevenMod9Residues ×ˢ bilateralOMCResidues N r 7`. -/
theorem targetSieved7_mod63_admissible_subset_image_crt9_7
    {N r : ℕ} (hr7 : 7 ≤ r) :
    admissibleFiberResidues (wr2TargetSievedFiber N r 7) 63 ⊆
      (nonThreevenMod9Residues ×ˢ bilateralOMCResidues N r 7).image
        crtReconstruct63From9And7 := by
  intro c hc
  rw [admissibleFiberResidues, mem_image] at hc
  obtain ⟨q, hq7, rfl⟩ := hc
  have hq_fiber : q ∈ wr2ShearContractedFiber N r := by
    rw [wr2TargetSievedFiber, mem_filter] at hq7
    exact hq7.1
  have hr_pos : 0 < r := by omega
  have hq_mod3_pos : 1 ≤ q % 3 :=
    (wr2ShearContractedFiber_lower_pinch_and_bilateral_omc hr_pos hq_fiber).2.1
      3 (by omega : 2 ≤ 3) (by omega : 3 ≤ r)
  have h_mem9 : q % 9 ∈ nonThreevenMod9Residues := by
    rw [nonThreevenMod9Residues, mem_filter, mem_range]
    exact ⟨Nat.mod_lt q (by omega : 0 < 9), by omega⟩
  have h_sub7 := targetSievedFiber_admissible_subset_bilateralOMCResidues (N := N) (by omega : 2 ≤ 7) hr7
  have h_mem7 : q % 7 ∈ bilateralOMCResidues N r 7 := by
    apply h_sub7
    rw [admissibleFiberResidues, mem_image]
    exact ⟨q, hq7, rfl⟩
  have h_c_lt : q % 63 < 63 := Nat.mod_lt q (by omega : 0 < 63)
  have h_crt := crtReconstruct63_mod9_mod7_id q (q % 63) h_c_lt
  rw [mem_image]
  refine ⟨(q % 9, q % 7), ?_, ?_⟩
  · rw [mem_product]
    exact ⟨h_mem9, h_mem7⟩
  · rw [← h_crt.2.2.1, ← h_crt.2.2.2]
    exact h_crt.2.1

/-- **Theorem 2.2 (`targetSieved7_mod63_admissible_card_bounds`):**
    For every `r ≥ 7`:
    1. `(admissibleFiberResidues (wr2TargetSievedFiber N r 7) 63).card ≤ 36` (`6 * 6`),
    2. `fiveup_reciprocal_involution_lane_halving` holds on `m = 7` (`(7 + 1) / 2 < 7 - 2`), and
    3. Whenever a non-zero Mod-7 target collision lane `1 ≤ c₇ < 7` exists,
       `(admissibleFiberResidues (wr2TargetSievedFiber N r 7) 63).card ≤ 30` (`6 * 5`). -/
theorem targetSieved7_mod63_admissible_card_bounds
    {N r : ℕ} (hr7 : 7 ≤ r) :
    (admissibleFiberResidues (wr2TargetSievedFiber N r 7) 63).card ≤
      nonThreevenMod9Residues.card * (bilateralOMCResidues N r 7).card ∧
    (admissibleFiberResidues (wr2TargetSievedFiber N r 7) 63).card ≤ 36 ∧
    (7 + 1) / 2 < 7 - 2 ∧
    (∀ c₇ : ℕ, 1 ≤ c₇ → c₇ < 7 → (r * c₇) % 7 = N % 7 →
      (admissibleFiberResidues (wr2TargetSievedFiber N r 7) 63).card ≤ 30) := by
  have h_sub := targetSieved7_mod63_admissible_subset_image_crt9_7 (N := N) hr7
  have h_prod_le :
      (admissibleFiberResidues (wr2TargetSievedFiber N r 7) 63).card ≤
        nonThreevenMod9Residues.card * (bilateralOMCResidues N r 7).card := by
    have h1 := Nat.le_trans (card_le_card h_sub) card_image_le
    rw [card_product] at h1
    exact h1
  have h9_le6 : nonThreevenMod9Residues.card ≤ 6 := nonThreevenMod9Residues_card_le_six
  have h7_le6 : (bilateralOMCResidues N r 7).card ≤ 6 :=
    (bilateralOMCResidues_card_le_sub_one N r 7).2
  have h_mul36 :
      nonThreevenMod9Residues.card * (bilateralOMCResidues N r 7).card ≤ 6 * 6 :=
    Nat.mul_le_mul h9_le6 h7_le6
  have h_inv7 :=
    fiveup_reciprocal_involution_lane_halving (m := 7) (by omega : 7 ≤ 7) (by omega : 7 % 2 = 1)
  refine ⟨h_prod_le, by omega, h_inv7.2.1, ?_⟩
  intro c₇ hc7_pos hc7_lt h_coll7
  have h7_le5 : (bilateralOMCResidues N r 7).card ≤ 5 :=
    (bilateralOMCResidues_card_le_sub_two_of_collision
      (by omega : 2 ≤ 7) hr7 hc7_pos hc7_lt h_coll7).1
  have h_mul30 :
      nonThreevenMod9Residues.card * (bilateralOMCResidues N r 7).card ≤ 6 * 5 :=
    Nat.mul_le_mul h9_le6 h7_le5
  omega

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.wr2TargetSievedFiber_bilateral_pVen_vanish
#print axioms WuPaper.ESZerosBridge.crtReconstruct63_mod9_mod7_id
#print axioms WuPaper.ESZerosBridge.nonThreevenMod9Residues_card_le_six
#print axioms WuPaper.ESZerosBridge.targetSieved7_mod63_admissible_subset_image_crt9_7
#print axioms WuPaper.ESZerosBridge.targetSieved7_mod63_admissible_card_bounds
