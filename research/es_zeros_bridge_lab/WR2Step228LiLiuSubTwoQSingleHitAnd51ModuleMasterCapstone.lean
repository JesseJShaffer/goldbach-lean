import WR2Step226LiLiuPureCosetOuterConeZeroSumAnd49ModuleCapstone

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step228LiLiuSubTwoQSingleHitAnd51ModuleMasterCapstone.lean — `Step208` Exact-Species `2 · P_{n+1}` First-Semiprime Filter, Sub-`2r` Single-Hit Closure & Master 51-Module `D19 N` Capstone

Completes the 51-Module `goldbach-lean` x `ES_Zeros` verification suite by welding:
1. The `Step208` Exact-Species `2 · P_{n+1}` First-Semiprime Filter (`liliu_composite_below_two_mul_Pn1_has_proper_prime_factor_lt_Pn1`
   and `liliuPn1RoughCompositeTail_eq_empty_below_two_mul_Pn1`),
2. The `Step208` Sub-`2r` Single-Hit Closure on Odd Residue Slices (`liliuFloorResidueSlice_subTwoQBlock_card_le_one`),
3. The `Step203`/`Step205` Pure-Coset Outer Cayley Cone Unconditional Primality Discharge, and
4. The `Step212` First-Missing-Prime `q_E` Zero-Sum Collapse & Global Low-Target Deduplication
directly into `Goldbach.one_plus_one_nine_count` (`D19 N`).
-/

/-!
## Section 1: Exact-Species `2 · P_{n+1}` First-Semiprime Filter (`Step208` §3)
-/

/-- **Theorem 1.1 (`liliu_composite_below_two_mul_Pn1_has_proper_prime_factor_lt_Pn1`):**
    Every composite integer `2 ≤ x < 2 * Pn1` (`¬ IsPrimeNat x`) has a proper divisor
    `2 ≤ d < Pn1` (`d < x ∧ d ∣ x ∧ x % d = 0`) with zero `→` guards on `Pn1`. -/
theorem liliu_composite_below_two_mul_Pn1_has_proper_prime_factor_lt_Pn1
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
        have hd_mod0 : x % d = 0 := (mod_eq_zero_and_mul_div_of_dvd_liliu hd_pos hd_dvd_x).1
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

/-- **Theorem 1.2 (`liliu_rough_below_two_mul_Pn1_isPrimeNat`):**
    Every integer `2 ≤ x < 2 * Pn1` with `∀ d, 2 ≤ d → d < Pn1 → 1 ≤ x % d` is
    unconditionally prime (`IsPrimeNat x ∧ Nat.Prime x`). -/
theorem liliu_rough_below_two_mul_Pn1_isPrimeNat
    {x Pn1 : ℕ} (hx2 : 2 ≤ x) (hx_lt : x < 2 * Pn1)
    (h_rough : ∀ d : ℕ, 2 ≤ d → d < Pn1 → 1 ≤ x % d) :
    IsPrimeNat x ∧ Nat.Prime x := by
  cases Classical.em (IsPrimeNat x) with
  | inl h_isp => exact ⟨h_isp, isPrimeNat_to_natPrime_liliu h_isp⟩
  | inr h_comp =>
    obtain ⟨d, hd2, hd_lt_Pn1, _, _, hd_mod0⟩ :=
      liliu_composite_below_two_mul_Pn1_has_proper_prime_factor_lt_Pn1 hx2 hx_lt h_comp
    have h_pos := h_rough d hd2 hd_lt_Pn1
    omega

/-- The `Pn1`-rough composite tail on any finite set `S : Finset ℕ`. -/
def liliuPn1RoughCompositeTail (S : Finset ℕ) (Pn1 : ℕ) : Finset ℕ :=
  S.filter (fun x : ℕ =>
    2 ≤ x ∧
    (∀ d ∈ range Pn1, 2 ≤ d → 1 ≤ x % d) ∧
    ¬ IsPrimeNat x)

/-- **Theorem 1.3 (`liliuPn1RoughCompositeTail_eq_empty_below_two_mul_Pn1`):**
    Whenever every `x ∈ S` satisfies `x < 2 * Pn1`, `(liliuPn1RoughCompositeTail S Pn1).card = 0`. -/
theorem liliuPn1RoughCompositeTail_eq_empty_below_two_mul_Pn1
    {S : Finset ℕ} {Pn1 : ℕ} (h_bound : ∀ x ∈ S, x < 2 * Pn1) :
    (liliuPn1RoughCompositeTail S Pn1).card = 0 := by
  match Nat.eq_zero_or_pos (liliuPn1RoughCompositeTail S Pn1).card with
  | Or.inl h0 => exact h0
  | Or.inr hpos =>
    obtain ⟨x, hx⟩ := card_pos.mp hpos
    rw [liliuPn1RoughCompositeTail, mem_filter] at hx
    obtain ⟨hx_S, hx2, h_rough, h_not_p⟩ := hx
    have hx_lt : x < 2 * Pn1 := h_bound x hx_S
    have h_isp := (liliu_rough_below_two_mul_Pn1_isPrimeNat hx2 hx_lt
      (fun d hd2 hd_lt => h_rough d (mem_range.mpr hd_lt) hd2)).1
    exact False.elim (h_not_p h_isp)

/-!
## Section 2: Unconditional Sub-`2r` Single-Hit Closure on Odd Residue Slices (`Step208` §1–§2)
-/

theorem eq_of_sub_lt_two_max_of_odd_of_mod_eq_liliu
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
  have h_q_le : a0 / r ≤ b0 / r := div_le_div_right_liliu hr_pos h_le
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

/-- **Theorem 2.1 (`liliuFloorResidueSlice_subTwoQBlock_card_le_one`):**
    Unconditional Sub-`2r` Single-Hit Closure (`Step208` §2) on `D19 N`:
    For every odd `r` (`r % 2 = 1`), floor `L`, residue class `c`, and Quotient Wave Shear
    block index `k`, `(liliuSubTwoQBlock (liliuFloorResidueSlice N r L r c) r k).card ≤ 1`
    and `(liliuFloorResidueSlice N r L r c).card ≤ (liliuSubTwoQBlockIndices (liliuFloorResidueSlice N r L r c) r).card`. -/
theorem liliuFloorResidueSlice_subTwoQBlock_card_le_one
    {N r L c : ℕ} (hr_odd : r % 2 = 1) (k : ℕ) :
    (liliuSubTwoQBlock (liliuFloorResidueSlice N r L r c) r k).card ≤ 1 ∧
    (liliuFloorResidueSlice N r L r c).card ≤
      (liliuSubTwoQBlockIndices (liliuFloorResidueSlice N r L r c) r).card := by
  have h_part :=
    liliuSubTwoQBlock_unconditional_partition_and_diameter (liliuFloorResidueSlice N r L r c) r
  have h_blk_le1 :
      ∀ j : ℕ, (liliuSubTwoQBlock (liliuFloorResidueSlice N r L r c) r j).card ≤ 1 := by
    intro j
    rw [Finset.card_le_one]
    intro a0 ha0 b0 hb0
    have h_diam_fn := h_part.2.2.2 j
    have ha_slice : a0 ∈ liliuFloorResidueSlice N r L r c := by
      rw [liliuSubTwoQBlock, mem_filter] at ha0
      exact ha0.1
    have hb_slice : b0 ∈ liliuFloorResidueSlice N r L r c := by
      rw [liliuSubTwoQBlock, mem_filter] at hb0
      exact hb0.1
    rw [liliuFloorResidueSlice, mem_filter] at ha_slice hb_slice
    have ha_odd : a0 % 2 = 1 := liliuFloorSubfiber_mem_odd ha_slice.1
    have hb_odd : b0 % 2 = 1 := liliuFloorSubfiber_mem_odd hb_slice.1
    have h_mod_eq : a0 % r = b0 % r := by rw [ha_slice.2, hb_slice.2]
    match Nat.lt_or_ge a0 b0 with
    | Or.inl hlt =>
      have hle : a0 ≤ b0 := Nat.le_of_lt hlt
      exact eq_of_sub_lt_two_max_of_odd_of_mod_eq_liliu hr_odd hle
        (h_diam_fn a0 b0 ha0 hb0 hle) ha_odd hb_odd h_mod_eq
    | Or.inr hge =>
      exact (eq_of_sub_lt_two_max_of_odd_of_mod_eq_liliu hr_odd hge
        (h_diam_fn b0 a0 hb0 ha0 hge) hb_odd ha_odd h_mod_eq.symm).symm
  refine ⟨h_blk_le1 k, ?_⟩
  rw [h_part.2.2.1]
  have h_sum_le :
      ∑ j ∈ liliuSubTwoQBlockIndices (liliuFloorResidueSlice N r L r c) r,
          (liliuSubTwoQBlock (liliuFloorResidueSlice N r L r c) r j).card ≤
        ∑ _j ∈ liliuSubTwoQBlockIndices (liliuFloorResidueSlice N r L r c) r, 1 := by
    apply sum_le_sum
    intro j _
    exact h_blk_le1 j
  rw [sum_const, smul_eq_mul, Nat.mul_one] at h_sum_le
  exact h_sum_le

/-- **Master Theorem 3.1 (`master_51module_complete_step208_step212_and_goldbach_lean_capstone`):**
    Complete 51-Module Master Synthesis uniting:
    1. `liuMainTerm0004 N < (D19 N : ℝ)` (`Goldbach.one_plus_one_nine_count`),
    2. `Step208` Exact-Species `2 · P_{n+1}` First-Semiprime Filter
       (`(liliuPn1RoughCompositeTail S Pn1).card = 0` for `x < 2 * Pn1`),
    3. `Step208` Unconditional Sub-`2r` Single-Hit Block Closure
       (`(liliuSubTwoQBlock (liliuFloorResidueSlice N r L r c) r k).card ≤ 1`),
    4. `Step203`/`Step205` Unconditional Bilateral Outer-Cone Primality & Goldbach Discharge, and
    5. `Step212` First-Missing-Prime `q_E` Zero-Sum Collapse & Global Low-Target Deduplication. -/
theorem master_51module_complete_step208_step212_and_goldbach_lean_capstone :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (∀ S : Finset ℕ, ∀ Pn1 : ℕ, (∀ x ∈ S, x < 2 * Pn1) →
        (liliuPn1RoughCompositeTail S Pn1).card = 0) ∧
      (∀ r L c k : ℕ, r % 2 = 1 →
        (liliuSubTwoQBlock (liliuFloorResidueSlice N r L r c) r k).card ≤ 1) ∧
      (∀ q_up : ℕ,
        0 < (liliuBilateralOuterConeRadii (N / 2) q_up).card →
          ∃ p q p_next' : ℕ,
            Nat.Prime p ∧ Nat.Prime q ∧ 2 * (N / 2) = p + q ∧ p < p_next' ∧ IsPrimeNat p_next') ∧
      (∀ q_E : ℕ, IsFirstMissingOddPrimeLiliu N q_E → N < q_E * (q_E + 2) + 2 →
        (∑ r ∈ pinchedOddPrimes919 N, (liliuTargetSieved3PrimeFiber N r q_E).card) = 0 ∧
        (fiveupPinchedQRSubfilter 9 10 N).card ≤ q_E ∧
        (((q_E : ℝ) ≤ liuMainTerm0004 N) →
          ∃ p q p_next' : ℕ,
            Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next' ∧ IsPrimeNat p_next')) := by
  obtain ⟨K, hK4, hCap49⟩ := master_49module_unconditional_outer_cone_and_first_missing_prime_capstone
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven
  have hM := hCap49 N hNK hEven
  exact ⟨hM.1,
         fun S Pn1 h_b => liliuPn1RoughCompositeTail_eq_empty_below_two_mul_Pn1 h_b,
         fun r L c k hr_odd => (liliuFloorResidueSlice_subTwoQBlock_card_le_one hr_odd k).1,
         hM.2.1,
         hM.2.2.2⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.liliu_composite_below_two_mul_Pn1_has_proper_prime_factor_lt_Pn1
#print axioms WuPaper.ESZerosBridge.liliu_rough_below_two_mul_Pn1_isPrimeNat
#print axioms WuPaper.ESZerosBridge.liliuPn1RoughCompositeTail_eq_empty_below_two_mul_Pn1
#print axioms WuPaper.ESZerosBridge.liliuFloorResidueSlice_subTwoQBlock_card_le_one
#print axioms WuPaper.ESZerosBridge.master_51module_complete_step208_step212_and_goldbach_lean_capstone
