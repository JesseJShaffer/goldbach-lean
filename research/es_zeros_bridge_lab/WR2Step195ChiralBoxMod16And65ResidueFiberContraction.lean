import WR2Step194WaveSegmentSquareOnsetElimination

set_option exponentiation.threshold 10000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step195ChiralBoxMod16And65ResidueFiberContraction.lean — Roadmap Step 2: Chiral Box Partition & Mod-16/65 Signature Contraction

1. **Exact Wave-Horizon Partition of `wr2TightChiralHalfChordBox N`
   (`wr2TightChiralHalfChordBox_card_eq_lowPrime_add_waveSieved`):**
   Splits `wr2TightChiralHalfChordBox N` at any primorial sieve prime `p_next` into the
   disjoint union of `lowPrimeTightChiralBox p_next N` (`A_h - D_h < p_next`) and
   `waveSievedTightChiralBox p_next N` (`p_next ≤ A_h - D_h`).
2. **Exact Collapse of the Global Chiral Box Below `(p_next + 1) ^ 2`
   (`wr2TightChiralHalfChordBox_card_eq_lowPrime_of_le_succ_sq`,
   `wr2CutlineSemiprimePrimes_card_le_one_add_lowPrime_of_le_succ_sq`):**
   Combines the disjoint partition with `waveSievedPos_and_Neg_card_eq_zero_of_le_succ_sq`
   (`WR2Step194`) to prove that for all even `N ≤ (p_next + 1) ^ 2`, the wave-sieved tail
   vanishes and `(wr2CutlineSemiprimePrimes N).card ≤ 1 + (lowPrimeTightChiralBox p_next N).card`.
3. **Singleton Contraction of the Mod-16 × Mod-4 Chiral Discriminant Signature
   (`wr2Pos_and_Neg_image_signature_card_le_one`):**
   Maps `wr2PosTightChiralBox N` and `wr2NegTightChiralBox N` via
   `chiralMod16Mod4SignatureMap (A_h, D_h) = (((2 * D_h) ^ 2) % 16, (A_h ^ 2 - D_h ^ 2) % 4)`
   and proves via `wr2_pos_neg_tight_box_triple_qr_and_mod16_lock` (`WR2Step191`) that their
   images are locked inside the singletons `{(0, 1)}` and `{(4, 3)}` (`card ≤ 1`).
-/

/-!
## Section 1: Disjoint Wave-Horizon Partition of `wr2TightChiralHalfChordBox N`
-/

/-- The low-prime boundary subset of `wr2TightChiralHalfChordBox N` where the smaller
    prime factor `r = A_h - D_h` lies strictly below the sieve horizon `p_next`. -/
def lowPrimeTightChiralBox (p_next N : ℕ) : Finset (ℕ × ℕ) :=
  (wr2TightChiralHalfChordBox N).filter (fun pair : ℕ × ℕ => pair.1 - pair.2 < p_next)

/-- Strict disjointness of `lowPrimeTightChiralBox p_next N` and `waveSievedTightChiralBox p_next N`. -/
theorem disjoint_lowPrime_waveSieved_tightChiralBox (p_next N : ℕ) :
    Disjoint (lowPrimeTightChiralBox p_next N) (waveSievedTightChiralBox p_next N) := by
  rw [Finset.disjoint_left]
  intro pair hlow hwave
  rw [lowPrimeTightChiralBox, mem_filter] at hlow
  rw [waveSievedTightChiralBox, mem_filter] at hwave
  have h1 : pair.1 - pair.2 < p_next := hlow.2
  have h2 : p_next ≤ pair.1 - pair.2 := hwave.2
  omega

/-- Exact union identity partitioning `wr2TightChiralHalfChordBox N` at `p_next`. -/
theorem wr2TightChiralHalfChordBox_eq_lowPrime_union_waveSieved (p_next N : ℕ) :
    wr2TightChiralHalfChordBox N =
      lowPrimeTightChiralBox p_next N ∪ waveSievedTightChiralBox p_next N := by
  ext pair
  rw [mem_union, lowPrimeTightChiralBox, waveSievedTightChiralBox, mem_filter, mem_filter]
  constructor
  · intro hmem
    match Nat.lt_or_ge (pair.1 - pair.2) p_next with
    | Or.inl hlt => exact Or.inl ⟨hmem, hlt⟩
    | Or.inr hge => exact Or.inr ⟨hmem, hge⟩
  · intro hor
    cases hor with
    | inl hlow => exact hlow.1
    | inr hwave => exact hwave.1

/-- **Theorem 1.1 (`wr2TightChiralHalfChordBox_card_eq_lowPrime_add_waveSieved`):**
    Exact additive decomposition of `wr2TightChiralHalfChordBox N` across any sieve horizon `p_next`. -/
theorem wr2TightChiralHalfChordBox_card_eq_lowPrime_add_waveSieved (p_next N : ℕ) :
    (wr2TightChiralHalfChordBox N).card =
      (lowPrimeTightChiralBox p_next N).card + (waveSievedTightChiralBox p_next N).card := by
  rw [wr2TightChiralHalfChordBox_eq_lowPrime_union_waveSieved p_next N]
  exact card_union_of_disjoint (disjoint_lowPrime_waveSieved_tightChiralBox p_next N)

/-- **Theorem 1.2 (`wr2TightChiralHalfChordBox_card_eq_lowPrime_of_le_succ_sq`):**
    For every target `N ≤ (p_next + 1) ^ 2`, the wave-sieved component vanishes and
    `(wr2TightChiralHalfChordBox N).card = (lowPrimeTightChiralBox p_next N).card`. -/
theorem wr2TightChiralHalfChordBox_card_eq_lowPrime_of_le_succ_sq
    {p_next N : ℕ} (hN_le : N ≤ (p_next + 1) ^ 2) :
    (wr2TightChiralHalfChordBox N).card = (lowPrimeTightChiralBox p_next N).card := by
  have h_part := wr2TightChiralHalfChordBox_card_eq_lowPrime_add_waveSieved p_next N
  have h_zero := (waveSievedPos_and_Neg_card_eq_zero_of_le_succ_sq hN_le).1
  omega

/-- **Theorem 1.3 (`wr2CutlineSemiprimePrimes_card_le_one_add_lowPrime_of_le_succ_sq`):**
    For every even target `N ≤ (p_next + 1) ^ 2`,
    `(wr2CutlineSemiprimePrimes N).card ≤ 1 + (lowPrimeTightChiralBox p_next N).card`. -/
theorem wr2CutlineSemiprimePrimes_card_le_one_add_lowPrime_of_le_succ_sq
    {p_next N : ℕ} (hEven : N % 2 = 0) (hN_le : N ≤ (p_next + 1) ^ 2) :
    (wr2CutlineSemiprimePrimes N).card ≤ 1 + (lowPrimeTightChiralBox p_next N).card := by
  have h_disj := wr2CutlineSemiprimePrimes_card_le_disjoint_tight_chiral_boxes hEven
  rw [← wr2TightChiralHalfChordBox_card_eq_pos_add_neg N] at h_disj
  rw [wr2TightChiralHalfChordBox_card_eq_lowPrime_of_le_succ_sq hN_le] at h_disj
  exact h_disj

/-!
## Section 2: Singleton Contraction of the Mod-16 × Mod-4 Chiral Discriminant Signature
-/

/-- The Mod-16 Full-Discriminant and Mod-4 Chiral Product signature map on half-chord pairs:
    `pair = (A_h, D_h) ↦ (((2 * D_h) ^ 2) % 16, (A_h ^ 2 - D_h ^ 2) % 4)`. -/
def chiralMod16Mod4SignatureMap (pair : ℕ × ℕ) : ℕ × ℕ :=
  (((2 * pair.2) ^ 2) % 16, (pair.1 ^ 2 - pair.2 ^ 2) % 4)

/-- Every witness in `wr2PosTightChiralBox N` maps to the single signature `(0, 1)` out of `64`. -/
theorem wr2PosTightChiralBox_image_signature_subset_singleton (N : ℕ) :
    (wr2PosTightChiralBox N).image chiralMod16Mod4SignatureMap ⊆ ({(0, 1)} : Finset (ℕ × ℕ)) := by
  intro sig hsig
  rw [mem_image] at hsig
  obtain ⟨pair, hmem, rfl⟩ := hsig
  have h_lock := (wr2_pos_neg_tight_box_triple_qr_and_mod16_lock N pair).1 hmem
  rw [mem_singleton]
  unfold chiralMod16Mod4SignatureMap
  rw [h_lock.2.1, h_lock.1]

/-- Every witness in `wr2NegTightChiralBox N` maps to the single signature `(4, 3)` out of `64`. -/
theorem wr2NegTightChiralBox_image_signature_subset_singleton (N : ℕ) :
    (wr2NegTightChiralBox N).image chiralMod16Mod4SignatureMap ⊆ ({(4, 3)} : Finset (ℕ × ℕ)) := by
  intro sig hsig
  rw [mem_image] at hsig
  obtain ⟨pair, hmem, rfl⟩ := hsig
  have h_lock := (wr2_pos_neg_tight_box_triple_qr_and_mod16_lock N pair).2 hmem
  rw [mem_singleton]
  unfold chiralMod16Mod4SignatureMap
  rw [h_lock.2.1, h_lock.1]

/-- **Theorem 2.1 (`wr2Pos_and_Neg_image_signature_card_le_one`):**
    The Mod-16 × Mod-4 signature images of `wr2PosTightChiralBox N` and `wr2NegTightChiralBox N`
    each have cardinality at most `1` (a `1 / 16` contraction on each chiral branch). -/
theorem wr2Pos_and_Neg_image_signature_card_le_one (N : ℕ) :
    ((wr2PosTightChiralBox N).image chiralMod16Mod4SignatureMap).card ≤ 1 ∧
    ((wr2NegTightChiralBox N).image chiralMod16Mod4SignatureMap).card ≤ 1 := by
  have h_pos := card_le_card (wr2PosTightChiralBox_image_signature_subset_singleton N)
  have h_neg := card_le_card (wr2NegTightChiralBox_image_signature_subset_singleton N)
  rw [card_singleton] at h_pos h_neg
  exact ⟨h_pos, h_neg⟩

/-- **Master Theorem 3.1 (`wr2_wave_horizon_and_chiral_signature_master_bridge`):**
    Unites `WR2ClassicalCertificate` (`one8938`), the expanding primorial wave-horizon
    decomposition (`lowPrimeTightChiralBox`), the Mod-16 × Mod-4 singleton signature
    contraction, and the Factorial Lighthouse next-prime generator:
    For every primorial anchor `p_n`, there exists a prime `p_next > p_n` such that for
    all even `N ≥ T` with `N ≤ (p_next + 1) ^ 2`, whenever
    `1 + (lowPrimeTightChiralBox p_next N).card < (wr2RepresentedPrimes N).card`,
    Binary Goldbach `N = p + q` holds unconditionally with `p < p_next'`. -/
theorem wr2_wave_horizon_and_chiral_signature_master_bridge (p_n : ℕ) :
    ∃ p_next T : ℕ,
      p_n < p_next ∧
      Nat.Prime p_next ∧
      IsPrimeNat p_next ∧
      512 ≤ T ∧
      ∀ N : ℕ, T ≤ N → N ≤ (p_next + 1) ^ 2 → Even N →
        0 < (wr2RepresentedPrimes N).card ∧
        ((wr2PosTightChiralBox N).image chiralMod16Mod4SignatureMap).card ≤ 1 ∧
        ((wr2NegTightChiralBox N).image chiralMod16Mod4SignatureMap).card ≤ 1 ∧
        (wr2CutlineSemiprimePrimes N).card ≤ 1 + (lowPrimeTightChiralBox p_next N).card ∧
        (1 + (lowPrimeTightChiralBox p_next N).card < (wr2RepresentedPrimes N).card →
          ∃ p q p_next' : ℕ,
            Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧
            p < p_next' ∧ Nat.Prime p_next' ∧ IsPrimeNat p_next') := by
  obtain ⟨p_next, h_pn_lt, hp_nat, hp_isp⟩ := hasNextPrimeMathlib_unconditional p_n
  obtain ⟨_, T, hT512, hMaster⟩ := wr2_one8938_unconditional_master_goldbach_bridge
  refine ⟨p_next, T, h_pn_lt, hp_nat, hp_isp, hT512, ?_⟩
  intro N hNT hN_le hEven
  have hM := hMaster N hNT hEven
  rcases hEven with ⟨k, hk⟩
  have hMod2 : N % 2 = 0 := by omega
  have h_low_le := wr2CutlineSemiprimePrimes_card_le_one_add_lowPrime_of_le_succ_sq hMod2 hN_le
  have h_sig := wr2Pos_and_Neg_image_signature_card_le_one N
  refine ⟨hM.1, h_sig.1, h_sig.2, h_low_le, ?_⟩
  intro hLowLt
  have hCutLt : (wr2CutlineSemiprimePrimes N).card < (wr2RepresentedPrimes N).card :=
    Nat.lt_of_le_of_lt h_low_le hLowLt
  obtain ⟨p, q, p_next', hp, hq, hN_eq, hp_lt, hp_next_isp⟩ := hM.2.2 hCutLt
  exact ⟨p, q, p_next', hp, hq, hN_eq, hp_lt, isPrimeNat_to_natPrime hp_next_isp, hp_next_isp⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.wr2TightChiralHalfChordBox_card_eq_lowPrime_of_le_succ_sq
#print axioms WuPaper.ESZerosBridge.wr2CutlineSemiprimePrimes_card_le_one_add_lowPrime_of_le_succ_sq
#print axioms WuPaper.ESZerosBridge.wr2Pos_and_Neg_image_signature_card_le_one
#print axioms WuPaper.ESZerosBridge.wr2_wave_horizon_and_chiral_signature_master_bridge
