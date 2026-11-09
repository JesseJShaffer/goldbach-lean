import WR2Step225PureCosetOuterConeSubTwoQBlockAndZeroSumCollapse

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step227WR2SubTwoQSingleHitAnd2Pn1FirstSemiprimeFilter.lean — `Step208` Exact-Species `2 · P_{n+1}` First-Semiprime Filter & Sub-`2r` Single-Hit Closure (`WR2` Track 1)

Completes the `Step208` combinatorics on Track 1 (`WR2`):

1. **Section 1 — Exact-Species `2 · P_{n+1}` First-Semiprime Filter (`Step208` §3):**
   - `composite_below_two_mul_Pn1_has_proper_prime_factor_lt_Pn1`: proves with ZERO `→` guards
     on `Pn1` that every composite integer `2 ≤ x < 2 * Pn1` (`¬ IsPrimeNat x`) has a proper
     divisor `d` satisfying `2 ≤ d ∧ d < Pn1 ∧ d < x ∧ d ∣ x`.
   - `rough_below_two_mul_Pn1_isPrimeNat`: proves that every integer `2 ≤ x < 2 * Pn1` that is
     `Pn1`-rough (`∀ d, 2 ≤ d → d < Pn1 → 1 ≤ x % d`) is unconditionally prime (`IsPrimeNat x ∧ Nat.Prime x`).
   - `pn1RoughCompositeTail_eq_empty_below_two_mul_Pn1`: proves that the `Pn1`-rough composite
     tail vanishes identically (`card = 0`) on any set bounded below `2 * Pn1`.
2. **Section 2 — Unconditional Sub-`2r` Single-Hit Closure on Residue Slices (`Step208` §1–§2):**
   - Proves that on any odd-element residue slice `residueClassSlice S r c` (`q % 2 = 1 ∧ q % r = c`
     with `r % 2 = 1`), each Quotient Wave Shear block `subTwoQBlock (residueClassSlice S r c) r k`
     has cardinality at most `1`, so `(residueClassSlice S r c).card ≤ (subTwoQBlockIndices (residueClassSlice S r c) r).card`.
-/

/-!
## Section 1: Exact-Species `2 · P_{n+1}` First-Semiprime Filter (`Step208` §3)
-/

/-- **Theorem 1.1 (`composite_below_two_mul_Pn1_has_proper_prime_factor_lt_Pn1`):**
    Exact-Species `2 · P_{n+1}` First-Semiprime Filter (`Step208` §3):
    Every composite integer `x` with `2 ≤ x < 2 * Pn1` (`¬ IsPrimeNat x`) has a proper divisor
    `d` satisfying `2 ≤ d ∧ d < Pn1 ∧ d < x ∧ d ∣ x` (and `x % d = 0`). -/
theorem composite_below_two_mul_Pn1_has_proper_prime_factor_lt_Pn1
    {x Pn1 : ℕ} (hx2 : 2 ≤ x) (hx_lt : x < 2 * Pn1) (h_comp : ¬ IsPrimeNat x) :
    ∃ d : ℕ, 2 ≤ d ∧ d < Pn1 ∧ d < x ∧ d ∣ x ∧ x % d = 0 := by
  cases Classical.em (∃ d : ℕ, 2 ≤ d ∧ d < Pn1 ∧ d < x ∧ d ∣ x ∧ x % d = 0) with
  | inl h_exists => exact h_exists
  | inr h_none =>
    have h_isp : IsPrimeNat x := by
      refine ⟨hx2, ?_⟩
      intro d hd_dvd
      obtain ⟨k, hk⟩ := hd_dvd
      if hd0 : d = 0 then
        rw [hd0, Nat.zero_mul] at hk
        omega
      else if hd1 : d = 1 then
        exact Or.inl hd1
      else if hdx : d = x then
        exact Or.inr hdx
      else
        have hd_pos : 0 < d := by omega
        have hd2 : 2 ≤ d := by omega
        have hk_ne0 : k ≠ 0 := by
          intro hk0
          rw [hk0, Nat.mul_zero] at hk
          omega
        have hk_ne1 : k ≠ 1 := by
          intro hk1
          rw [hk1, Nat.mul_one] at hk
          omega
        have hk2 : 2 ≤ k := by omega
        have hd_dvd_x : d ∣ x := ⟨k, hk⟩
        have h_d2_le : d * 2 ≤ x := by
          rw [hk]
          exact Nat.mul_le_mul_left d hk2
        have hd_lt_x : d < x := by omega
        have hd_mod0 : x % d = 0 := (mod_eq_zero_and_mul_div_of_dvd_native hd_pos hd_dvd_x).1
        match Nat.lt_or_ge d Pn1 with
        | Or.inl hd_lt_Pn1 =>
          exact False.elim (h_none ⟨d, hd2, hd_lt_Pn1, hd_lt_x, hd_dvd_x, hd_mod0⟩)
        | Or.inr hd_ge_Pn1 =>
          have h_2Pn1_le : 2 * Pn1 ≤ x := by
            calc 2 * Pn1
              _ = Pn1 * 2 := Nat.mul_comm 2 Pn1
              _ ≤ d * k := Nat.mul_le_mul hd_ge_Pn1 hk2
              _ = x := hk.symm
          exact False.elim (Nat.lt_irrefl x (Nat.lt_of_lt_of_le hx_lt h_2Pn1_le))
    exact False.elim (h_comp h_isp)

/-- **Theorem 1.2 (`rough_below_two_mul_Pn1_isPrimeNat`):**
    Unconditional `2 · P_{n+1}` Primality Filter (`Step208` §3):
    Every integer `2 ≤ x < 2 * Pn1` that has no divisor `2 ≤ d < Pn1` (`1 ≤ x % d`)
    is unconditionally prime (`IsPrimeNat x ∧ Nat.Prime x`)! -/
theorem rough_below_two_mul_Pn1_isPrimeNat
    {x Pn1 : ℕ} (hx2 : 2 ≤ x) (hx_lt : x < 2 * Pn1)
    (h_rough : ∀ d : ℕ, 2 ≤ d → d < Pn1 → 1 ≤ x % d) :
    IsPrimeNat x ∧ Nat.Prime x := by
  cases Classical.em (IsPrimeNat x) with
  | inl h_isp => exact ⟨h_isp, isPrimeNat_to_natPrime h_isp⟩
  | inr h_comp =>
    obtain ⟨d, hd2, hd_lt_Pn1, _, _, hd_mod0⟩ :=
      composite_below_two_mul_Pn1_has_proper_prime_factor_lt_Pn1 hx2 hx_lt h_comp
    have h_pos := h_rough d hd2 hd_lt_Pn1
    omega

/-- The `Pn1`-rough composite tail on any finite set `S : Finset ℕ`. -/
def pn1RoughCompositeTail (S : Finset ℕ) (Pn1 : ℕ) : Finset ℕ :=
  S.filter (fun x : ℕ =>
    2 ≤ x ∧
    (∀ d ∈ range Pn1, 2 ≤ d → 1 ≤ x % d) ∧
    ¬ IsPrimeNat x)

/-- **Theorem 1.3 (`pn1RoughCompositeTail_eq_empty_below_two_mul_Pn1`):**
    Whenever every `x ∈ S` satisfies `x < 2 * Pn1`, the `Pn1`-rough composite tail
    `pn1RoughCompositeTail S Pn1` has cardinality `0` (`= 0`) with zero `→` guards on `Pn1`! -/
theorem pn1RoughCompositeTail_eq_empty_below_two_mul_Pn1
    {S : Finset ℕ} {Pn1 : ℕ} (h_bound : ∀ x ∈ S, x < 2 * Pn1) :
    (pn1RoughCompositeTail S Pn1).card = 0 := by
  match Nat.eq_zero_or_pos (pn1RoughCompositeTail S Pn1).card with
  | Or.inl h0 => exact h0
  | Or.inr hpos =>
    obtain ⟨x, hx⟩ := card_pos.mp hpos
    rw [pn1RoughCompositeTail, mem_filter] at hx
    obtain ⟨hx_S, hx2, h_rough, h_not_p⟩ := hx
    have hx_lt : x < 2 * Pn1 := h_bound x hx_S
    have h_isp := (rough_below_two_mul_Pn1_isPrimeNat hx2 hx_lt
      (fun d hd2 hd_lt => h_rough d (mem_range.mpr hd_lt) hd2)).1
    exact False.elim (h_not_p h_isp)

/-!
## Section 2: Unconditional Sub-`2r` Single-Hit Closure on Odd Residue Slices (`Step208` §1–§2)
-/

/-- Pure native uniqueness inside a sub-`2r` Quotient Wave Shear block:
    if `r % 2 = 1`, `a0 ≤ b0`, `b0 - a0 < 2 * max r 1`, `a0 % 2 = 1`, `b0 % 2 = 1`,
    and `a0 % r = b0 % r`, then `a0 = b0`. -/
theorem eq_of_sub_lt_two_max_of_odd_of_mod_eq
    {r a0 b0 : ℕ} (hr_odd : r % 2 = 1) (h_le : a0 ≤ b0)
    (h_diam : b0 - a0 < 2 * max r 1)
    (ha_odd : a0 % 2 = 1) (hb_odd : b0 % 2 = 1)
    (h_mod_r : a0 % r = b0 % r) :
    a0 = b0 := by
  have hr_pos : 0 < r := by omega
  have h_max_eq : max r 1 = r := by omega
  rw [h_max_eq] at h_diam
  have ha_div : r * (a0 / r) + a0 % r = a0 := Nat.div_add_mod a0 r
  have hb_div : r * (b0 / r) + b0 % r = b0 := Nat.div_add_mod b0 r
  rw [← h_mod_r] at hb_div
  have h_q_le : a0 / r ≤ b0 / r := div_le_div_right_native hr_pos h_le
  match Nat.lt_or_ge (a0 / r) (b0 / r) with
  | Or.inr h_q_ge =>
    have h_q_eq : a0 / r = b0 / r := Nat.le_antisymm h_q_le h_q_ge
    rw [h_q_eq] at ha_div
    omega
  | Or.inl _ =>
    match Nat.lt_or_ge (a0 / r + 1) (b0 / r) with
    | Or.inl h_q_gt1 =>
      have h_step2 : a0 / r + 2 ≤ b0 / r := h_q_gt1
      have h_mul2 : r * (a0 / r + 2) ≤ r * (b0 / r) := Nat.mul_le_mul_left r h_step2
      rw [Nat.left_distrib r (a0 / r) 2, Nat.mul_comm r 2] at h_mul2
      omega
    | Or.inr _ =>
      have h_q_eq1 : b0 / r = a0 / r + 1 := by omega
      rw [h_q_eq1, Nat.left_distrib r (a0 / r) 1, Nat.mul_one] at hb_div
      omega

/-- General Sub-`2r` Single-Hit theorem for any odd-element `Finset ℕ` (`∀ q ∈ S, q % 2 = 1`). -/
theorem oddSet_slice_subTwoQBlock_card_le_one
    {S : Finset ℕ} {r c : ℕ} (hS_odd : ∀ q ∈ S, q % 2 = 1) (hr_odd : r % 2 = 1) (k : ℕ) :
    (subTwoQBlock (residueClassSlice S r c) r k).card ≤ 1 ∧
    (residueClassSlice S r c).card ≤
      (subTwoQBlockIndices (residueClassSlice S r c) r).card := by
  have h_part := subTwoQBlock_unconditional_partition_and_diameter (residueClassSlice S r c) r
  have h_blk_le1 : ∀ j : ℕ, (subTwoQBlock (residueClassSlice S r c) r j).card ≤ 1 := by
    intro j
    rw [Finset.card_le_one]
    intro a0 ha0 b0 hb0
    have h_diam_fn := h_part.2.2.2 j
    have ha_slice : a0 ∈ residueClassSlice S r c := by
      rw [subTwoQBlock, mem_filter] at ha0
      exact ha0.1
    have hb_slice : b0 ∈ residueClassSlice S r c := by
      rw [subTwoQBlock, mem_filter] at hb0
      exact hb0.1
    rw [residueClassSlice, mem_filter] at ha_slice hb_slice
    have ha_odd : a0 % 2 = 1 := hS_odd a0 ha_slice.1
    have hb_odd : b0 % 2 = 1 := hS_odd b0 hb_slice.1
    have h_mod_eq : a0 % r = b0 % r := by rw [ha_slice.2, hb_slice.2]
    match Nat.lt_or_ge a0 b0 with
    | Or.inl hlt =>
      have hle : a0 ≤ b0 := Nat.le_of_lt hlt
      exact eq_of_sub_lt_two_max_of_odd_of_mod_eq hr_odd hle
        (h_diam_fn a0 b0 ha0 hb0 hle) ha_odd hb_odd h_mod_eq
    | Or.inr hge =>
      exact (eq_of_sub_lt_two_max_of_odd_of_mod_eq hr_odd hge
        (h_diam_fn b0 a0 hb0 ha0 hge) hb_odd ha_odd h_mod_eq.symm).symm
  refine ⟨h_blk_le1 k, ?_⟩
  rw [h_part.2.2.1]
  have h_sum_le :
      ∑ j ∈ subTwoQBlockIndices (residueClassSlice S r c) r,
          (subTwoQBlock (residueClassSlice S r c) r j).card ≤
        ∑ _j ∈ subTwoQBlockIndices (residueClassSlice S r c) r, 1 := by
    apply sum_le_sum
    intro j _
    exact h_blk_le1 j
  rw [sum_const, smul_eq_mul, Nat.mul_one] at h_sum_le
  exact h_sum_le

/-- **Theorem 2.1 (`wr2FloorSubfiber_slice_subTwoQBlock_card_le_one`):**
    Unconditional Sub-`2r` Single-Hit Closure (`Step208` §2) on `wr2FloorSubfiber N r L`. -/
theorem wr2FloorSubfiber_slice_subTwoQBlock_card_le_one
    {N r L c : ℕ} (hr_odd : r % 2 = 1) (k : ℕ) :
    (subTwoQBlock (residueClassSlice (wr2FloorSubfiber N r L) r c) r k).card ≤ 1 ∧
    (residueClassSlice (wr2FloorSubfiber N r L) r c).card ≤
      (subTwoQBlockIndices (residueClassSlice (wr2FloorSubfiber N r L) r c) r).card :=
  oddSet_slice_subTwoQBlock_card_le_one (fun _ hq => wr2FloorSubfiber_mem_odd hq) hr_odd k

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.composite_below_two_mul_Pn1_has_proper_prime_factor_lt_Pn1
#print axioms WuPaper.ESZerosBridge.rough_below_two_mul_Pn1_isPrimeNat
#print axioms WuPaper.ESZerosBridge.pn1RoughCompositeTail_eq_empty_below_two_mul_Pn1
#print axioms WuPaper.ESZerosBridge.wr2FloorSubfiber_slice_subTwoQBlock_card_le_one
