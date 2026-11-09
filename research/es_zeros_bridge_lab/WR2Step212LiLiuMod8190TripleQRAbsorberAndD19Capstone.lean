import WR2Step210LiLiuMod65CRTProductBilateralOMCAndQRAbsorberCapstone

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step212LiLiuMod8190TripleQRAbsorberAndD19Capstone.lean — Universal `p`-ven Divisibility Inheritance & Mod-8190 (`130 × 63`) Absorber for `D19 N`

Unites Universal `p`-ven Divisibility Inheritance (`p ∣ m → liliuPVenDomain S m ⊆ liliuPVenDomain S p`),
the Branch-Free Mod-8190 (`6111, 2080`) Orthogonal Idempotent Absorber, and the Mod-8190
Quotient-Stride Contraction (`((N / r) / 8190 - L / 8190) + 1`) with `Goldbach.one_plus_one_nine_count`.
-/

/-!
## Section 1: Universal `p`-ven Divisibility Inheritance on `liliuShearContractedFiber`
-/

theorem mod_eq_zero_of_dvd_of_mod_eq_zero_liliu
    {p m q : ℕ} (hp_pos : 0 < p) (h_dvd : p ∣ m) (hq_mod : q % m = 0) :
    q % p = 0 := by
  obtain ⟨k, hk⟩ := h_dvd
  have h_qm : m * (q / m) + q % m = q := Nat.div_add_mod q m
  have h_qp : p * (q / p) + q % p = q := Nat.div_add_mod q p
  have h_rem_lt : q % p < p := Nat.mod_lt q hp_pos
  have h_q_eq : q = p * (k * (q / m)) := by
    calc q
      _ = m * (q / m) := by omega
      _ = (p * k) * (q / m) := by rw [hk]
      _ = p * (k * (q / m)) := Nat.mul_assoc p k (q / m)
  have h_mul_eq : p * (q / p) + q % p = p * (k * (q / m)) := by omega
  exact eq_zero_of_mul_add_eq_mul_of_lt_liliu h_rem_lt h_mul_eq

/-- **Theorem 1.1 (`liliuPVenDomain_subset_of_dvd`):**
    Universal `p`-ven Divisibility Inheritance: whenever `0 < p` and `p ∣ m`,
    `liliuPVenDomain S m ⊆ liliuPVenDomain S p` and `liliuNonPVenDomain S p ⊆ liliuNonPVenDomain S m`. -/
theorem liliuPVenDomain_subset_of_dvd
    (S : Finset ℕ) {p m : ℕ} (hp_pos : 0 < p) (h_dvd : p ∣ m) :
    liliuPVenDomain S m ⊆ liliuPVenDomain S p ∧
    liliuNonPVenDomain S p ⊆ liliuNonPVenDomain S m := by
  constructor
  · intro q hq
    rw [liliuPVenDomain, mem_filter] at hq ⊢
    exact ⟨hq.1, mod_eq_zero_of_dvd_of_mod_eq_zero_liliu hp_pos h_dvd hq.2⟩
  · intro q hq
    rw [liliuNonPVenDomain, mem_filter] at hq ⊢
    refine ⟨hq.1, ?_⟩
    if hm0 : q % m = 0 then
      have hp0 := mod_eq_zero_of_dvd_of_mod_eq_zero_liliu hp_pos h_dvd hm0
      omega
    else
      omega

/-- **Theorem 1.2 (`liliuFiber_pVenDomain_multiple_card_eq_zero`):**
    For ANY `p` with `2 ≤ p ≤ r` and ANY multiple `m` (`p ∣ m`, even when `m ≫ r`),
    `(liliuPVenDomain (liliuShearContractedFiber N r) m).card = 0` and
    `(liliuShearContractedFiber N r).card = (liliuNonPVenDomain (liliuShearContractedFiber N r) m).card`. -/
theorem liliuFiber_pVenDomain_multiple_card_eq_zero
    {N r p m : ℕ} (hp2 : 2 ≤ p) (hpr : p ≤ r) (h_dvd : p ∣ m) :
    (liliuPVenDomain (liliuShearContractedFiber N r) m).card = 0 ∧
    (liliuShearContractedFiber N r).card =
      (liliuNonPVenDomain (liliuShearContractedFiber N r) m).card := by
  have hp_pos : 0 < p := by omega
  have h_sub := (liliuPVenDomain_subset_of_dvd (liliuShearContractedFiber N r) hp_pos h_dvd).1
  have h_p_zero := (liliuFiber_pVenDomain_card_eq_zero (N := N) hp2 hpr).1
  have h_m_le : (liliuPVenDomain (liliuShearContractedFiber N r) m).card ≤ 0 := by
    rw [← h_p_zero]
    exact card_le_card h_sub
  have h_part := card_eq_liliuPVen_add_nonPVen (liliuShearContractedFiber N r) m
  omega

/-!
## Section 2: Branch-Free Mod-8190 (`130 × 63`) Triple-QR CRT Absorber
-/

/-- Branch-free CRT orthogonal idempotent absorber combining Mod-130 (`2 * 65`) and Mod-63 (`7 * 9`)
    into Mod-8190 (`130 * 63 = 8190`): `(6111 * c130 + 2080 * c63) % 8190`. -/
def liliuCrtReconstruct8190From130And63 (c130 c63 : ℕ) : ℕ :=
  (6111 * c130 + 2080 * c63) % 8190

theorem crt_mod130_mod63_to_mod8190_liliu
    {q c130 c63 : ℕ} (hc130 : c130 < 130) (hc63 : c63 < 63)
    (hq130 : q % 130 = c130) (hq63 : q % 63 = c63) :
    c130 < 130 ∧
    c63 < 63 ∧
    q % 8190 = liliuCrtReconstruct8190From130And63 c130 c63 ∧
    (liliuCrtReconstruct8190From130And63 c130 c63) % 130 = c130 ∧
    (liliuCrtReconstruct8190From130And63 c130 c63) % 63 = c63 ∧
    liliuCrtReconstruct8190From130And63 c130 c63 < 8190 := by
  refine ⟨hc130, hc63, ?_⟩
  unfold liliuCrtReconstruct8190From130And63
  omega

/-- The joint `(Mod 65, Mod 63)` Triple-QR residue slice of `liliuFloorSubfiber N r L`. -/
def liliuJointMod65Mod63Slice (N r L c65 c63 : ℕ) : Finset ℕ :=
  (liliuFloorSubfiber N r L).filter (fun q : ℕ => q % 65 = c65 ∧ q % 63 = c63)

theorem liliuJointMod65Mod63Slice_subset_mod8190
    {N r L c65 c63 : ℕ} (hc65 : c65 < 65) (hc63 : c63 < 63) :
    liliuJointMod65Mod63Slice N r L c65 c63 ⊆
      liliuFloorResidueSlice N r L 8190
        (liliuCrtReconstruct8190From130And63 (liliuCrtOddLift130 c65) c63) := by
  intro q hq
  rw [liliuJointMod65Mod63Slice, mem_filter] at hq
  rw [liliuFloorResidueSlice, mem_filter]
  have hq_odd : q % 2 = 1 := liliuFloorSubfiber_mem_odd hq.1
  have h130 := crt_mod2_mod65_to_mod130_liliu hc65 hq_odd hq.2.1
  have h8190 := crt_mod130_mod63_to_mod8190_liliu h130.2 hc63 h130.1 hq.2.2
  exact ⟨hq.1, h8190.2.2.1⟩

/-- **Theorem 2.1 (`liliuJointMod65Mod63Slice_card_le_mod8190_stride`):**
    Mod-8190 Triple-QR Quotient-Stride Contraction on `D19 N`:
    For every floor `L : ℕ`, `c65 < 65`, and `c63 < 63`,
    `(liliuJointMod65Mod63Slice N r L c65 c63).card ≤ ((N / r) / 8190 - L / 8190) + 1`. -/
theorem liliuJointMod65Mod63Slice_card_le_mod8190_stride
    {N r L c65 c63 : ℕ} (hc65 : c65 < 65) (hc63 : c63 < 63) :
    (liliuJointMod65Mod63Slice N r L c65 c63).card ≤
      ((N / r) / 8190 - L / 8190) + 1 := by
  have h_sub := liliuJointMod65Mod63Slice_subset_mod8190 (N := N) (r := r) (L := L) hc65 hc63
  have h_8190 :=
    liliuFloorResidueSlice_card_le_shifted_quotient_diff
      (N := N) (r := r) (L := L) (by omega : 0 < 8190)
      (liliuCrtReconstruct8190From130And63 (liliuCrtOddLift130 c65) c63)
  exact Nat.le_trans (card_le_card h_sub) h_8190

/-- **Master 35-Module Capstone (`master_35module_D19_pVen_and_mod8190_triple_qr_capstone`):**
    Unites `Goldbach.one_plus_one_nine_count` (`liuMainTerm0004 N < (D19 N : ℝ)`),
    Universal `p`-ven Divisibility Inheritance (`∀ p m, 2 ≤ p → p ≤ r → p ∣ m → card = 0`),
    the Mod-65 (`48`/`33` lane) and Mod-8190 (`((N / r) / 8190 - L / 8190) + 1`) CRT Absorbers,
    and the Factorial Lighthouse Next-Prime Generator. -/
theorem master_35module_D19_pVen_and_mod8190_triple_qr_capstone :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (∀ r p m : ℕ, 2 ≤ p → p ≤ r → p ∣ m →
        (liliuPVenDomain (liliuShearContractedFiber N r) m).card = 0) ∧
      (∀ r L c65 c63 : ℕ, c65 < 65 → c63 < 63 →
        (liliuJointMod65Mod63Slice N r L c65 c63).card ≤ ((N / r) / 8190 - L / 8190) + 1) ∧
      (fiveupPinchedQRSubfilter 9 10 N).card ≤
        1 + ((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).card ∧
      ((((1 + ((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).card : ℕ) : ℝ) ≤
          liuMainTerm0004 N) →
        ∃ p q p_next' : ℕ,
          Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next' ∧ IsPrimeNat p_next') := by
  obtain ⟨K, hK4, hCap⟩ := master_33module_D19_mod65_crt_absorber_and_mod130_stride_capstone
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven
  have hM := hCap N hNK hEven
  refine ⟨hM.1, ?_, ?_, hM.2.2.2.1, hM.2.2.2.2⟩
  · intro r p m hp2 hpr hdvd
    exact (liliuFiber_pVenDomain_multiple_card_eq_zero hp2 hpr hdvd).1
  · intro r L c65 c63 hc65 hc63
    exact liliuJointMod65Mod63Slice_card_le_mod8190_stride hc65 hc63

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.liliuPVenDomain_subset_of_dvd
#print axioms WuPaper.ESZerosBridge.liliuFiber_pVenDomain_multiple_card_eq_zero
#print axioms WuPaper.ESZerosBridge.crt_mod130_mod63_to_mod8190_liliu
#print axioms WuPaper.ESZerosBridge.liliuJointMod65Mod63Slice_card_le_mod8190_stride
#print axioms WuPaper.ESZerosBridge.master_35module_D19_pVen_and_mod8190_triple_qr_capstone
