import WR2Step209WR2Mod65CRTProductBilateralOMCAndQRAbsorber

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step211WR2Mod8190TripleQRAbsorberAndFiberSumBound.lean — Universal `p`-ven Divisibility Inheritance & Branch-Free Mod-8190 (`130 × 63`) Absorber

1. **Universal `p`-ven Divisibility Inheritance (`pVenDomain_subset_of_dvd`,
   `wr2Fiber_pVenDomain_multiple_card_eq_zero`):**
   Proves in pure native `Init` arithmetic that whenever `p ∣ m`, `pVenDomain S m ⊆ pVenDomain S p`
   and `nonPVenDomain S p ⊆ nonPVenDomain S m`. Consequently, for ANY `p` with `2 ≤ p ≤ r` and
   ANY multiple `m` with `p ∣ m` (even when `m > r`, such as `m ∈ {9, 63, 65, 130, 8190}`),
   `(pVenDomain (wr2ShearContractedFiber N r) m).card = 0`.
2. **Branch-Free Mod-8190 Orthogonal Idempotent Absorber (`crtReconstruct8190From130And63`):**
   Uses the exact Bezout orthogonal idempotents `e₁₃₀ = 6111` and `e₆₃ = 2080` to prove the
   round-trip CRT identity and contract every joint `(Mod 65, Mod 63)` slice stride to
   `(((N - 2) / r) / 8190 - L / 8190) + 1`.
-/

/-!
## Section 1: Universal `p`-ven Divisibility Inheritance (`p ∣ m → pVenDomain S m ⊆ pVenDomain S p`)
-/

/-- Pure native Euclidean lemma: if `0 < p`, `p ∣ m`, and `q % m = 0`, then `q % p = 0`. -/
theorem mod_eq_zero_of_dvd_of_mod_eq_zero_native
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
  exact eq_zero_of_mul_add_eq_mul_of_lt h_rem_lt h_mul_eq

/-- **Theorem 1.1 (`pVenDomain_subset_of_dvd`):**
    Universal `p`-ven Divisibility Inheritance: for any `p > 0` and any multiple `m` (`p ∣ m`),
    every `m`-ven is a `p`-ven (`pVenDomain S m ⊆ pVenDomain S p`) and every non-`p`-ven is a
    non-`m`-ven (`nonPVenDomain S p ⊆ nonPVenDomain S m`). -/
theorem pVenDomain_subset_of_dvd
    (S : Finset ℕ) {p m : ℕ} (hp_pos : 0 < p) (h_dvd : p ∣ m) :
    pVenDomain S m ⊆ pVenDomain S p ∧
    nonPVenDomain S p ⊆ nonPVenDomain S m := by
  constructor
  · intro q hq
    rw [pVenDomain, mem_filter] at hq ⊢
    exact ⟨hq.1, mod_eq_zero_of_dvd_of_mod_eq_zero_native hp_pos h_dvd hq.2⟩
  · intro q hq
    rw [nonPVenDomain, mem_filter] at hq ⊢
    refine ⟨hq.1, ?_⟩
    if hm0 : q % m = 0 then
      have hp0 := mod_eq_zero_of_dvd_of_mod_eq_zero_native hp_pos h_dvd hm0
      omega
    else
      omega

/-- **Theorem 1.2 (`wr2Fiber_pVenDomain_multiple_card_eq_zero`):**
    Universal `p`-ven Vanishing for All Multiples: for ANY `p` with `2 ≤ p ≤ r` and ANY
    multiple `m` (`p ∣ m`, even when `m ≫ r`), `(pVenDomain (wr2ShearContractedFiber N r) m).card = 0`
    and `(wr2ShearContractedFiber N r).card = (nonPVenDomain (wr2ShearContractedFiber N r) m).card`. -/
theorem wr2Fiber_pVenDomain_multiple_card_eq_zero
    {N r p m : ℕ} (hp2 : 2 ≤ p) (hpr : p ≤ r) (h_dvd : p ∣ m) :
    (pVenDomain (wr2ShearContractedFiber N r) m).card = 0 ∧
    (wr2ShearContractedFiber N r).card =
      (nonPVenDomain (wr2ShearContractedFiber N r) m).card := by
  have hp_pos : 0 < p := by omega
  have h_sub := (pVenDomain_subset_of_dvd (wr2ShearContractedFiber N r) hp_pos h_dvd).1
  have h_p_zero := (wr2Fiber_pVenDomain_card_eq_zero (N := N) hp2 hpr).1
  have h_m_le : (pVenDomain (wr2ShearContractedFiber N r) m).card ≤ 0 := by
    rw [← h_p_zero]
    exact card_le_card h_sub
  have h_part := card_eq_pVen_add_nonPVen (wr2ShearContractedFiber N r) m
  omega

/-!
## Section 2: Branch-Free Mod-8190 (`130 × 63`) Triple-QR CRT Absorber
-/

/-- Branch-free CRT orthogonal idempotent absorber combining Mod-130 (`2 * 65`) and Mod-63 (`7 * 9`)
    into Mod-8190 (`130 * 63 = 8190`): `(6111 * c130 + 2080 * c63) % 8190`. -/
def crtReconstruct8190From130And63 (c130 c63 : ℕ) : ℕ :=
  (6111 * c130 + 2080 * c63) % 8190

/-- Pure linear Presburger CRT proof with explicit round-trip projections referencing both
    `hc130 : c130 < 130` and `hc63 : c63 < 63`. -/
theorem crt_mod130_mod63_to_mod8190
    {q c130 c63 : ℕ} (hc130 : c130 < 130) (hc63 : c63 < 63)
    (hq130 : q % 130 = c130) (hq63 : q % 63 = c63) :
    c130 < 130 ∧
    c63 < 63 ∧
    q % 8190 = crtReconstruct8190From130And63 c130 c63 ∧
    (crtReconstruct8190From130And63 c130 c63) % 130 = c130 ∧
    (crtReconstruct8190From130And63 c130 c63) % 63 = c63 ∧
    crtReconstruct8190From130And63 c130 c63 < 8190 := by
  refine ⟨hc130, hc63, ?_⟩
  unfold crtReconstruct8190From130And63
  omega

/-- The joint `(Mod 65, Mod 63)` Triple-QR residue slice of `wr2FloorSubfiber N r L`. -/
def wr2JointMod65Mod63Slice (N r L c65 c63 : ℕ) : Finset ℕ :=
  (wr2FloorSubfiber N r L).filter (fun q : ℕ => q % 65 = c65 ∧ q % 63 = c63)

/-- Every joint `(Mod 65, Mod 63)` slice (with `c65 < 65` and `c63 < 63`) is contained in a
    single Mod-8190 slice via `crtOddLift130` and `crtReconstruct8190From130And63`. -/
theorem wr2JointMod65Mod63Slice_subset_mod8190_slice
    {N r L c65 c63 : ℕ} (hc65 : c65 < 65) (hc63 : c63 < 63) :
    wr2JointMod65Mod63Slice N r L c65 c63 ⊆
      residueClassSlice (wr2FloorSubfiber N r L) 8190
        (crtReconstruct8190From130And63 (crtOddLift130 c65) c63) := by
  intro q hq
  rw [wr2JointMod65Mod63Slice, mem_filter] at hq
  rw [residueClassSlice, mem_filter]
  have hq_odd : q % 2 = 1 := wr2FloorSubfiber_mem_odd hq.1
  have h130 := crt_mod2_mod65_to_mod130 hc65 hq_odd hq.2.1
  have h8190 := crt_mod130_mod63_to_mod8190 h130.2 hc63 h130.1 hq.2.2
  exact ⟨hq.1, h8190.2.2.1⟩

/-- **Theorem 2.1 (`wr2JointMod65Mod63Slice_card_le_mod8190_stride`):**
    Mod-8190 Triple-QR Quotient-Stride Contraction on `WR2`:
    For every floor `L : ℕ`, `c65 < 65`, and `c63 < 63`,
    `(wr2JointMod65Mod63Slice N r L c65 c63).card ≤ (((N - 2) / r) / 8190 - L / 8190) + 1`. -/
theorem wr2JointMod65Mod63Slice_card_le_mod8190_stride
    {N r L c65 c63 : ℕ} (hc65 : c65 < 65) (hc63 : c63 < 63) :
    (wr2JointMod65Mod63Slice N r L c65 c63).card ≤
      (((N - 2) / r) / 8190 - L / 8190) + 1 := by
  have h_sub := wr2JointMod65Mod63Slice_subset_mod8190_slice (N := N) (r := r) (L := L) hc65 hc63
  have h_8190 :=
    wr2FloorSubfiber_slice_card_le_shifted_quotient_diff
      (N := N) (r := r) (L := L) (by omega : 0 < 8190)
      (crtReconstruct8190From130And63 (crtOddLift130 c65) c63)
  exact Nat.le_trans (card_le_card h_sub) h_8190

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.pVenDomain_subset_of_dvd
#print axioms WuPaper.ESZerosBridge.wr2Fiber_pVenDomain_multiple_card_eq_zero
#print axioms WuPaper.ESZerosBridge.crt_mod130_mod63_to_mod8190
#print axioms WuPaper.ESZerosBridge.wr2JointMod65Mod63Slice_card_le_mod8190_stride
