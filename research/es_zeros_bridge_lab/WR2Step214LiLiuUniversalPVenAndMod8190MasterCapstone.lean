import WR2Step212LiLiuMod8190TripleQRAbsorberAndD19Capstone

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step214LiLiuUniversalPVenAndMod8190MasterCapstone.lean — Universal Bilateral `p`-ven Law, Mod-63 (`36`/`30` Lanes) & Master 37-Module `D19 N` Capstone

Welds the Disjoint Bilateral `p`-ven Domain Law (`liliuTargetPVenCollisionDomain`,
`liliuBilateralNonPVenDomain`), the Branch-Free Mod-63 (`28, 36`) CRT Orthogonal Idempotent
Absorber (`36`-lane and `30`-lane bounds), the Mod-65 (`48`-lane and `33`-lane bounds),
and the Mod-8190 (`((N / r) / 8190 - L / 8190) + 1`) Triple-QR Stride into the
37-Module `Goldbach.All` (`D19 N`) Master Capstone.
-/

/-!
## Section 1: Disjoint Bilateral `p`-ven Domains on `liliuTargetSieved3PrimeFiber`
-/

/-- The target-side `p`-ven collision domain on `S`. -/
def liliuTargetPVenCollisionDomain (S : Finset ℕ) (N r p : ℕ) : Finset ℕ :=
  S.filter (fun q : ℕ => 1 ≤ q % p ∧ (r * (q % p)) % p = N % p)

/-- The bilateral non-`p`-ven survivor domain on `S`. -/
def liliuBilateralNonPVenDomain (S : Finset ℕ) (N r p : ℕ) : Finset ℕ :=
  S.filter (fun q : ℕ => 1 ≤ q % p ∧ (r * (q % p)) % p ≠ N % p)

theorem disjoint_liliuTargetPVenCollision_bilateralNonPVen (S : Finset ℕ) (N r p : ℕ) :
    Disjoint (liliuTargetPVenCollisionDomain S N r p) (liliuBilateralNonPVenDomain S N r p) := by
  rw [Finset.disjoint_left]
  intro q hcoll hbil
  rw [liliuTargetPVenCollisionDomain, mem_filter] at hcoll
  rw [liliuBilateralNonPVenDomain, mem_filter] at hbil
  exact hbil.2.2 hcoll.2.2

theorem liliuNonPVenDomain_eq_collision_union_bilateral (S : Finset ℕ) (N r p : ℕ) :
    liliuNonPVenDomain S p =
      liliuTargetPVenCollisionDomain S N r p ∪ liliuBilateralNonPVenDomain S N r p := by
  ext q
  rw [mem_union, liliuNonPVenDomain, liliuTargetPVenCollisionDomain, liliuBilateralNonPVenDomain,
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

/-- **Theorem 1.1 (`liliuTargetSieved3PrimeFiber_bilateral_pVen_vanish`):**
    Universal Bilateral `p`-ven Law on `D19 N`: for EVERY integer `p` with `2 ≤ p ≤ r`,
    on `liliuTargetSieved3PrimeFiber N r p`, both `liliuPVenDomain` and
    `liliuTargetPVenCollisionDomain` have cardinality `0`. -/
theorem liliuTargetSieved3PrimeFiber_bilateral_pVen_vanish
    {N r p : ℕ} (hp2 : 2 ≤ p) (hpr : p ≤ r) :
    (liliuPVenDomain (liliuTargetSieved3PrimeFiber N r p) p).card = 0 ∧
    (liliuTargetPVenCollisionDomain (liliuTargetSieved3PrimeFiber N r p) N r p).card = 0 ∧
    (liliuTargetSieved3PrimeFiber N r p).card =
      (liliuBilateralNonPVenDomain (liliuTargetSieved3PrimeFiber N r p) N r p).card := by
  have h_pv_sub :
      liliuPVenDomain (liliuTargetSieved3PrimeFiber N r p) p ⊆
        liliuPVenDomain (liliuShearContractedFiber N r) p := by
    intro q hq
    rw [liliuPVenDomain, mem_filter, liliuTargetSieved3PrimeFiber, mem_filter] at hq
    rw [liliuPVenDomain, mem_filter]
    exact ⟨(liliuTight3PrimeFiber_mem_props hq.1.1).1, hq.2⟩
  have h_pv_zero_main := (liliuFiber_pVenDomain_card_eq_zero (N := N) hp2 hpr).1
  have h_pv_le : (liliuPVenDomain (liliuTargetSieved3PrimeFiber N r p) p).card ≤ 0 := by
    rw [← h_pv_zero_main]
    exact card_le_card h_pv_sub
  have h_coll_zero :
      (liliuTargetPVenCollisionDomain (liliuTargetSieved3PrimeFiber N r p) N r p).card = 0 := by
    match Nat.eq_zero_or_pos
        (liliuTargetPVenCollisionDomain (liliuTargetSieved3PrimeFiber N r p) N r p).card with
    | Or.inl h0 => exact h0
    | Or.inr hpos =>
      obtain ⟨q, hq⟩ := card_pos.mp hpos
      rw [liliuTargetPVenCollisionDomain, mem_filter] at hq
      have h_mem_adm :
          q % p ∈ (liliuTargetSieved3PrimeFiber N r p).image (fun x : ℕ => x % p) := by
        rw [mem_image]
        exact ⟨q, hq.1, rfl⟩
      have h_mem_bil :=
        liliuTargetSieved_admissible_subset_bilateralOMC (N := N) hp2 hpr h_mem_adm
      rw [liliuBilateralOMCResidues, mem_filter] at h_mem_bil
      exact False.elim (h_mem_bil.2.2 hq.2.2)
  have h_part1 := card_eq_liliuPVen_add_nonPVen (liliuTargetSieved3PrimeFiber N r p) p
  have h_part2 :
      (liliuNonPVenDomain (liliuTargetSieved3PrimeFiber N r p) p).card =
        (liliuTargetPVenCollisionDomain (liliuTargetSieved3PrimeFiber N r p) N r p).card +
        (liliuBilateralNonPVenDomain (liliuTargetSieved3PrimeFiber N r p) N r p).card := by
    conv_lhs =>
      rw [liliuNonPVenDomain_eq_collision_union_bilateral (liliuTargetSieved3PrimeFiber N r p) N r p]
    exact card_union_of_disjoint
      (disjoint_liliuTargetPVenCollision_bilateralNonPVen (liliuTargetSieved3PrimeFiber N r p) N r p)
  omega

/-!
## Section 2: Branch-Free Mod-63 (`9 × 7`) Orthogonal Idempotent Absorber (`28, 36`)
-/

/-- Branch-free CRT reconstruction absorber from `Mod 9 × Mod 7` to `Mod 63`:
    `(28 * pair.1 + 36 * pair.2) % 63`. -/
def liliuCrtReconstruct63From9And7 (pair : ℕ × ℕ) : ℕ :=
  (28 * pair.1 + 36 * pair.2) % 63

theorem liliuCrtReconstruct63_mod9_mod7_id (q c : ℕ) (hc : c < 63) :
    c < 63 ∧
    liliuCrtReconstruct63From9And7 (c % 9, c % 7) = c ∧
    (q % 63) % 9 = q % 9 ∧
    (q % 63) % 7 = q % 7 := by
  refine ⟨hc, ?_⟩
  unfold liliuCrtReconstruct63From9And7
  dsimp only
  omega

/-- The `6` non-Threeven residue classes modulo `9`: `{1, 2, 4, 5, 7, 8}`. -/
def liliuNonThreevenMod9Residues : Finset ℕ :=
  (range 9).filter (fun a : ℕ => 1 ≤ a % 3)

def liliuExpandNonThreevenMod9 (k : ℕ) : ℕ :=
  k + 1 + k / 2

theorem liliuNonThreevenMod9Residues_card_le_six :
    liliuNonThreevenMod9Residues.card ≤ 6 := by
  have h_sub : liliuNonThreevenMod9Residues ⊆ (range 6).image liliuExpandNonThreevenMod9 := by
    intro a ha
    rw [liliuNonThreevenMod9Residues, mem_filter, mem_range] at ha
    rw [mem_image]
    refine ⟨a - 1 - a / 3, ?_, ?_⟩
    · rw [mem_range]; omega
    · unfold liliuExpandNonThreevenMod9; omega
  have h1 := Nat.le_trans (card_le_card h_sub) card_image_le
  rw [card_range] at h1
  exact h1

/-- **Theorem 2.1 (`liliuTargetSieved7_mod63_subset_image_crt9_7`):**
    For every `r ≥ 7`, the active Mod-63 residue classes of `liliuTargetSieved3PrimeFiber N r 7`
    are contained in the image under `liliuCrtReconstruct63From9And7` of
    `liliuNonThreevenMod9Residues ×ˢ liliuBilateralOMCResidues N r 7`. -/
theorem liliuTargetSieved7_mod63_subset_image_crt9_7
    {N r : ℕ} (hr7 : 7 ≤ r) :
    (liliuTargetSieved3PrimeFiber N r 7).image (fun q : ℕ => q % 63) ⊆
      (liliuNonThreevenMod9Residues ×ˢ liliuBilateralOMCResidues N r 7).image
        liliuCrtReconstruct63From9And7 := by
  intro c hc
  rw [mem_image] at hc
  obtain ⟨q, hq7, rfl⟩ := hc
  rw [liliuTargetSieved3PrimeFiber, mem_filter] at hq7
  have hq_shear := (liliuTight3PrimeFiber_mem_props hq7.1).1
  have hr_pos : 0 < r := by omega
  have hq_mod3_pos : 1 ≤ q % 3 :=
    (liliuShearContractedFiber_lower_pinch_10_9 hr_pos hq_shear).2.2
      3 (by omega : 2 ≤ 3) (by omega : 3 ≤ r)
  have h_mem9 : q % 9 ∈ liliuNonThreevenMod9Residues := by
    rw [liliuNonThreevenMod9Residues, mem_filter, mem_range]
    exact ⟨Nat.mod_lt q (by omega : 0 < 9), by omega⟩
  have h_sub7 := liliuTargetSieved_admissible_subset_bilateralOMC (N := N) (by omega : 2 ≤ 7) hr7
  have h_mem7 : q % 7 ∈ liliuBilateralOMCResidues N r 7 := by
    apply h_sub7
    rw [mem_image]
    exact ⟨q, by rw [liliuTargetSieved3PrimeFiber, mem_filter]; exact hq7, rfl⟩
  have h_c_lt : q % 63 < 63 := Nat.mod_lt q (by omega : 0 < 63)
  have h_crt := liliuCrtReconstruct63_mod9_mod7_id q (q % 63) h_c_lt
  rw [mem_image]
  refine ⟨(q % 9, q % 7), ?_, ?_⟩
  · rw [mem_product]
    exact ⟨h_mem9, h_mem7⟩
  · rw [← h_crt.2.2.1, ← h_crt.2.2.2]
    exact h_crt.2.1

/-- **Theorem 2.2 (`liliuTargetSieved7_mod63_card_bounds`):**
    For every `r ≥ 7`, the active Mod-63 lanes of `liliuTargetSieved3PrimeFiber N r 7`
    satisfy `card ≤ 36` (`6 * 6`) unconditionally and `card ≤ 30` (`6 * 5`) whenever a
    non-zero Mod-7 target collision lane `1 ≤ c₇ < 7` exists. -/
theorem liliuTargetSieved7_mod63_card_bounds
    {N r : ℕ} (hr7 : 7 ≤ r) :
    ((liliuTargetSieved3PrimeFiber N r 7).image (fun q : ℕ => q % 63)).card ≤
      liliuNonThreevenMod9Residues.card * (liliuBilateralOMCResidues N r 7).card ∧
    ((liliuTargetSieved3PrimeFiber N r 7).image (fun q : ℕ => q % 63)).card ≤ 36 ∧
    (7 + 1) / 2 < 7 - 2 ∧
    (∀ c₇ : ℕ, 1 ≤ c₇ → c₇ < 7 → (r * c₇) % 7 = N % 7 →
      ((liliuTargetSieved3PrimeFiber N r 7).image (fun q : ℕ => q % 63)).card ≤ 30) := by
  have h_sub := liliuTargetSieved7_mod63_subset_image_crt9_7 (N := N) hr7
  have h_prod_le :
      ((liliuTargetSieved3PrimeFiber N r 7).image (fun q : ℕ => q % 63)).card ≤
        liliuNonThreevenMod9Residues.card * (liliuBilateralOMCResidues N r 7).card := by
    have h1 := Nat.le_trans (card_le_card h_sub) card_image_le
    rw [card_product] at h1
    exact h1
  have h9_le6 : liliuNonThreevenMod9Residues.card ≤ 6 := liliuNonThreevenMod9Residues_card_le_six
  have h7_le6 : (liliuBilateralOMCResidues N r 7).card ≤ 6 :=
    liliuBilateralOMCResidues_card_le_sub_one N r 7
  have h_mul36 :
      liliuNonThreevenMod9Residues.card * (liliuBilateralOMCResidues N r 7).card ≤ 6 * 6 :=
    Nat.mul_le_mul h9_le6 h7_le6
  have h_inv7 :=
    fiveup_reciprocal_involution_lane_halving (m := 7) (by omega : 7 ≤ 7) (by omega : 7 % 2 = 1)
  refine ⟨h_prod_le, by omega, h_inv7.2.1, ?_⟩
  intro c₇ hc7_pos hc7_lt h_coll7
  have h7_le5 : (liliuBilateralOMCResidues N r 7).card ≤ 5 :=
    (liliuBilateralOMCResidues_card_le_sub_two_of_collision
      (by omega : 2 ≤ 7) hr7 hc7_pos hc7_lt h_coll7).1
  have h_mul30 :
      liliuNonThreevenMod9Residues.card * (liliuBilateralOMCResidues N r 7).card ≤ 6 * 5 :=
    Nat.mul_le_mul h9_le6 h7_le5
  omega

/-- **Master 37-Module Capstone (`master_37module_D19_universal_pVen_and_mod8190_capstone`):**
    Complete 37-Module Capstone uniting `Goldbach.one_plus_one_nine_count` (`liuMainTerm0004 N < (D19 N : ℝ)`),
    Universal Bilateral `p`-ven Vanishing (`∀ p, 2 ≤ p → p ≤ r`),
    Universal `p`-ven Divisibility Inheritance (`∀ p m, 2 ≤ p → p ≤ r → p ∣ m`),
    the Mod-63 (`36`/`30` lane) and Mod-65 (`48`/`33` lane) CRT Product Bounds,
    the Mod-8190 (`((N / r) / 8190 - L / 8190) + 1`) Triple-QR Quotient Stride,
    and the Factorial Lighthouse Next-Prime Generator (`hasNextPrimeConnection_unconditional`). -/
theorem master_37module_D19_universal_pVen_and_mod8190_capstone :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (∀ r p : ℕ, 2 ≤ p → p ≤ r →
        (liliuPVenDomain (liliuTargetSieved3PrimeFiber N r p) p).card = 0 ∧
        (liliuTargetPVenCollisionDomain (liliuTargetSieved3PrimeFiber N r p) N r p).card = 0) ∧
      (∀ r p m : ℕ, 2 ≤ p → p ≤ r → p ∣ m →
        (liliuPVenDomain (liliuShearContractedFiber N r) m).card = 0) ∧
      (∀ r : ℕ, 7 ≤ r →
        ((liliuTargetSieved3PrimeFiber N r 7).image (fun q : ℕ => q % 63)).card ≤ 36) ∧
      (∀ r : ℕ, 13 ≤ r →
        ((liliuTargetSieved3PrimeFiber N r 13).image (fun q : ℕ => q % 65)).card ≤ 48) ∧
      (∀ r L c65 c63 : ℕ, c65 < 65 → c63 < 63 →
        (liliuJointMod65Mod63Slice N r L c65 c63).card ≤ ((N / r) / 8190 - L / 8190) + 1) ∧
      (fiveupPinchedQRSubfilter 9 10 N).card ≤
        1 + ((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).card ∧
      ((((1 + ((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).card : ℕ) : ℝ) ≤
          liuMainTerm0004 N) →
        ∃ p q p_next' : ℕ,
          Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next' ∧ IsPrimeNat p_next') := by
  obtain ⟨K, hK4, hCap35⟩ := master_35module_D19_pVen_and_mod8190_triple_qr_capstone
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven
  have hM := hCap35 N hNK hEven
  refine ⟨hM.1, ?_, hM.2.1, ?_, ?_, hM.2.2.1, hM.2.2.2.1, hM.2.2.2.2⟩
  · intro r p hp2 hpr
    have h_bil := liliuTargetSieved3PrimeFiber_bilateral_pVen_vanish (N := N) hp2 hpr
    exact ⟨h_bil.1, h_bil.2.1⟩
  · intro r hr7
    exact (liliuTargetSieved7_mod63_card_bounds (N := N) hr7).2.1
  · intro r hr13
    exact (liliuTargetSieved13_mod65_card_bounds (N := N) hr13).2.2.2.1

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.liliuTargetSieved3PrimeFiber_bilateral_pVen_vanish
#print axioms WuPaper.ESZerosBridge.liliuCrtReconstruct63_mod9_mod7_id
#print axioms WuPaper.ESZerosBridge.liliuNonThreevenMod9Residues_card_le_six
#print axioms WuPaper.ESZerosBridge.liliuTargetSieved7_mod63_subset_image_crt9_7
#print axioms WuPaper.ESZerosBridge.liliuTargetSieved7_mod63_card_bounds
#print axioms WuPaper.ESZerosBridge.master_37module_D19_universal_pVen_and_mod8190_capstone
