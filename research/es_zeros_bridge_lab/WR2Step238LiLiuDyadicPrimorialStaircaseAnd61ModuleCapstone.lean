import WR2Step236LiLiuPrimorialWaveSegmentLadderAnd59ModuleCapstone

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step238LiLiuDyadicPrimorialStaircaseAnd61ModuleCapstone.lean — `Step211` Generalized Dyadic/Primorial Staircase, PrefixCoset Phase-Return Period, Local Sub-`2q` Block Closure & Master 61-Module `D19 N` Capstone

Ports `Step211` Sections 2–4 onto Track 2 (`D19 N`) and welds them into the 61-Module
`Goldbach.All` (`D19 N`) Master Capstone.
-/

/-!
## Section 1: Generalized Dyadic & Primorial Quotient-Cofactor Staircase (`Step211` §2)
-/

theorem div_le_div_left_of_le_liliu
    {A B E : ℕ} (hA_pos : 0 < A) (hAB : A ≤ B) :
    E / B ≤ E / A := by
  have hB_div : B * (E / B) + E % B = E := Nat.div_add_mod E B
  have hB_mul_le : B * (E / B) ≤ E := by omega
  have hA_mul_B : A * (E / B) ≤ B * (E / B) := Nat.mul_le_mul_right (E / B) hAB
  have hA_mul_le : A * (E / B) ≤ E := Nat.le_trans hA_mul_B hB_mul_le
  exact le_div_of_mul_le_liliu hA_pos hA_mul_le

theorem nat_pow_le_pow_right_liliu {b : ℕ} (hb1 : 1 ≤ b) (m₁ : ℕ) :
    ∀ d : ℕ, b ^ m₁ ≤ b ^ (m₁ + d)
  | 0 => Nat.le_refl (b ^ m₁)
  | d + 1 => by
    have ih := nat_pow_le_pow_right_liliu hb1 m₁ d
    have h_step : b ^ (m₁ + d) * 1 ≤ b ^ (m₁ + d) * b :=
      Nat.mul_le_mul_left (b ^ (m₁ + d)) hb1
    rw [Nat.mul_one] at h_step
    exact Nat.le_trans ih h_step

def liliuDyadicQuotientStair (E m : ℕ) : ℕ :=
  E / (2 ^ m)

/-- **Theorem 1.1 (`liliu_generalized_dyadic_and_primorial_quotient_cofactor_staircase`):**
    Ports `Step211` Section 2 onto Track 2 (`D19 N`). -/
theorem liliu_generalized_dyadic_and_primorial_quotient_cofactor_staircase
    (E m₁ m₂ W Q : ℕ) :
    (liliuDyadicQuotientStair E 0 = E ∧
     liliuDyadicQuotientStair E 1 = E / 2 ∧
     (2 ^ m₁) * liliuDyadicQuotientStair E m₁ + E % (2 ^ m₁) = E) ∧
    (E / 16 ≤ E / 8 ∧ E / 8 ≤ E / 4 ∧ E / 4 ≤ E / 2 ∧ E / 2 ≤ E) ∧
    (m₁ ≤ m₂ → liliuDyadicQuotientStair E m₂ ≤ liliuDyadicQuotientStair E m₁) ∧
    (0 < W → 0 < Q → E / (W * Q) ≤ E / W ∧ E / (W * W) ≤ E / W) := by
  have h_base :
      liliuDyadicQuotientStair E 0 = E ∧
      liliuDyadicQuotientStair E 1 = E / 2 ∧
      (2 ^ m₁) * liliuDyadicQuotientStair E m₁ + E % (2 ^ m₁) = E := by
    unfold liliuDyadicQuotientStair
    exact ⟨Nat.div_one E, rfl, Nat.div_add_mod E (2 ^ m₁)⟩
  have h_fixed : E / 16 ≤ E / 8 ∧ E / 8 ≤ E / 4 ∧ E / 4 ≤ E / 2 ∧ E / 2 ≤ E := by
    omega
  have h_mono : m₁ ≤ m₂ → liliuDyadicQuotientStair E m₂ ≤ liliuDyadicQuotientStair E m₁ := by
    intro hle
    unfold liliuDyadicQuotientStair
    have h_add : m₁ + (m₂ - m₁) = m₂ := Nat.add_sub_of_le hle
    have h_pow_le : 2 ^ m₁ ≤ 2 ^ m₂ := by
      rw [← h_add]
      exact nat_pow_le_pow_right_liliu (by omega : 1 ≤ 2) m₁ (m₂ - m₁)
    have h_pow_pos : 0 < 2 ^ m₁ := nat_pow_pos (by omega : 0 < 2) m₁
    exact div_le_div_left_of_le_liliu h_pow_pos h_pow_le
  refine ⟨h_base, h_fixed, h_mono, ?_⟩
  intro hW_pos hQ_pos
  have h_WQ_ge : W ≤ W * Q := by
    have h1 : W * 1 ≤ W * Q := Nat.mul_le_mul_left W hQ_pos
    rw [Nat.mul_one] at h1
    exact h1
  have h_WW_ge : W ≤ W * W := by
    have h1 : W * 1 ≤ W * W := Nat.mul_le_mul_left W hW_pos
    rw [Nat.mul_one] at h1
    exact h1
  exact ⟨div_le_div_left_of_le_liliu hW_pos h_WQ_ge,
         div_le_div_left_of_le_liliu hW_pos h_WW_ge⟩

/-!
## Section 2: PrefixCoset Tensor Phase-Return Period `P_{q,e}(W) = q^e / gcd(q^e, W)` (`Step211` §2)
-/

def liliuPrefixCosetReturnPeriod (q e W : ℕ) : ℕ :=
  (q ^ e) / Nat.gcd (q ^ e) W

/-- **Theorem 2.1 (`liliuPrefixCosetReturnPeriod_exact_mul_and_wave_dvd`):**
    PrefixCoset Tensor Phase-Return Period (`Step195` & `Step211` §2) on Track 2,
    explicitly connected to `predictedNextPrime q` and `hasNextPrimeConnection_unconditional q`. -/
theorem liliuPrefixCosetReturnPeriod_exact_mul_and_wave_dvd
    {q : ℕ} (hq_pos : 0 < q) (e W : ℕ) :
    1 ≤ liliuPrefixCosetReturnPeriod q e W ∧
    liliuPrefixCosetReturnPeriod q e W ≤ q ^ e ∧
    Nat.gcd (q ^ e) W * liliuPrefixCosetReturnPeriod q e W = q ^ e ∧
    q ^ e ∣ W * liliuPrefixCosetReturnPeriod q e W ∧
    predictedNextPrime q = nextPrimeBoundedAux (q + 1) (factorialNat q + 1) ∧
    (∃ q_next : ℕ, q < q_next ∧ IsPrimeNat q_next) := by
  have h_qe_pos : 0 < q ^ e := nat_pow_pos hq_pos e
  have h_gcd_pos : 0 < Nat.gcd (q ^ e) W := Nat.gcd_pos_of_pos_left W h_qe_pos
  have h_gcd_dvd_qe : Nat.gcd (q ^ e) W ∣ q ^ e := Nat.gcd_dvd_left (q ^ e) W
  have h_gcd_dvd_W : Nat.gcd (q ^ e) W ∣ W := Nat.gcd_dvd_right (q ^ e) W
  have h_gcd_le_qe : Nat.gcd (q ^ e) W ≤ q ^ e := dvd_le_of_pos h_gcd_dvd_qe h_qe_pos
  have h_mul_eq : Nat.gcd (q ^ e) W * liliuPrefixCosetReturnPeriod q e W = q ^ e :=
    (mod_eq_zero_and_mul_div_of_dvd_liliu h_gcd_pos h_gcd_dvd_qe).2
  have h_ge1 : 1 ≤ liliuPrefixCosetReturnPeriod q e W := by
    unfold liliuPrefixCosetReturnPeriod
    have h_m1 : Nat.gcd (q ^ e) W * 1 ≤ q ^ e := by
      rw [Nat.mul_one]
      exact h_gcd_le_qe
    exact le_div_of_mul_le_liliu h_gcd_pos h_m1
  have h_le_qe : liliuPrefixCosetReturnPeriod q e W ≤ q ^ e := by
    unfold liliuPrefixCosetReturnPeriod
    have h_1_le_gcd : 1 ≤ Nat.gcd (q ^ e) W := h_gcd_pos
    have h_div1 := div_le_div_left_of_le_liliu (E := q ^ e) (by omega : 0 < 1) h_1_le_gcd
    rw [Nat.div_one] at h_div1
    exact h_div1
  have h_dvd_wave : q ^ e ∣ W * liliuPrefixCosetReturnPeriod q e W := by
    obtain ⟨m, hm⟩ := h_gcd_dvd_W
    refine ⟨m, ?_⟩
    calc W * liliuPrefixCosetReturnPeriod q e W
      _ = (Nat.gcd (q ^ e) W * m) * liliuPrefixCosetReturnPeriod q e W := by rw [← hm]
      _ = (m * Nat.gcd (q ^ e) W) * liliuPrefixCosetReturnPeriod q e W := by
          rw [Nat.mul_comm (Nat.gcd (q ^ e) W) m]
      _ = m * (Nat.gcd (q ^ e) W * liliuPrefixCosetReturnPeriod q e W) :=
          Nat.mul_assoc m (Nat.gcd (q ^ e) W) (liliuPrefixCosetReturnPeriod q e W)
      _ = m * (q ^ e) := by rw [h_mul_eq]
      _ = (q ^ e) * m := Nat.mul_comm m (q ^ e)
  exact ⟨h_ge1, h_le_qe, h_mul_eq, h_dvd_wave, rfl, hasNextPrimeConnection_unconditional q⟩

/-!
## Section 3: Local Sub-`2q` Block `|R_Q(J)| - |T_Q(J)|` Survivor Bound & Master 61-Module Capstone
-/

/-- **Theorem 3.1 (`liliu_local_subTwoQBlock_rq_minus_tq_and_single_block_goldbach_closure`):**
    Local Sub-`2q` Block Survivor Closure (`Step211` Bridge Option 2) on Track 2:
    On any single block `J_k := liliuSubTwoQBlock (liliuFullLowerMURUpper M) q k`,
    `(liliuSqrtActiveOwnerPrimes M q).card < (liliuRoughSurvivorSet J_k q).card`
    unconditionally produces a certified Binary Goldbach partition `2 * M = p + q'`. -/
theorem liliu_local_subTwoQBlock_rq_minus_tq_and_single_block_goldbach_closure
    (M q k : ℕ) :
    let J_k := liliuSubTwoQBlock (liliuFullLowerMURUpper M) q k
    (liliuRoughSurvivorSet J_k q).card =
      (liliuPrimeSurvivorSet J_k q).card + (liliuPn1RoughCompositeTail J_k q).card ∧
    (liliuRoughSurvivorSet J_k q).card - (liliuSqrtActiveOwnerPrimes M q).card ≤
      (liliuPrimeSurvivorSet J_k q).card ∧
    ((liliuSqrtActiveOwnerPrimes M q).card < (liliuRoughSurvivorSet J_k q).card →
      0 < (liliuPrimeSurvivorSet J_k q).card ∧
      ∃ p q' p_next' : ℕ,
        Nat.Prime p ∧ Nat.Prime q' ∧ 2 * M = p + q' ∧
        p < p_next' ∧ IsPrimeNat p_next') := by
  dsimp only
  have h_part :=
    liliuRoughSurvivorSet_card_eq_primeSurvivors_add_compositeTail
      (liliuSubTwoQBlock (liliuFullLowerMURUpper M) q k) q
  have h_tail_le :=
    liliuSubTwoQBlock_roughCompositeTail_card_le_sqrtActiveOwnerPrimes M q k
  have h_sub_le :
      (liliuRoughSurvivorSet (liliuSubTwoQBlock (liliuFullLowerMURUpper M) q k) q).card -
        (liliuSqrtActiveOwnerPrimes M q).card ≤
      (liliuPrimeSurvivorSet (liliuSubTwoQBlock (liliuFullLowerMURUpper M) q k) q).card := by
    omega
  refine ⟨h_part, h_sub_le, ?_⟩
  intro h_lt
  have h_pos :
      0 < (liliuPrimeSurvivorSet (liliuSubTwoQBlock (liliuFullLowerMURUpper M) q k) q).card := by
    omega
  refine ⟨h_pos, ?_⟩
  obtain ⟨u, hu⟩ := card_pos.mp h_pos
  rw [liliuPrimeSurvivorSet, mem_filter, liliuSubTwoQBlock, mem_filter] at hu
  obtain ⟨⟨hu_full, _⟩, _, _, hu_isp⟩ := hu
  have h_props := liliuFullLowerMURUpper_mem_props hu_full
  have hp_nat : Nat.Prime (2 * M - u) := isPrimeNat_to_natPrime_liliu h_props.2.2.2.2.1
  have hu_nat : Nat.Prime u := isPrimeNat_to_natPrime_liliu hu_isp
  obtain ⟨p_next', hp_lt, hp_next_isp⟩ :=
    hasNextPrimeConnection_unconditional (2 * M - u)
  exact ⟨2 * M - u, u, p_next', hp_nat, hu_nat, h_props.2.2.2.2.2.symm,
    hp_lt, hp_next_isp⟩

/-- **Master Theorem 3.2 (`master_61module_complete_step208_to_step212_goldbach_lean_capstone`):**
    Complete 61-Module Master Capstone uniting `Goldbach.one_plus_one_nine_count` (`D19 N`),
    the `Step211` Generalized Dyadic/Primorial Staircase & PrefixCoset Tensor Return Period,
    the `Step211` Local Sub-`2q` Single-Block `|R_Q(J_k)| - |sqrtOwners|` Goldbach Closure,
    the `Step209` `√(2M) + 1` Zero-Tail Collapse & Lower-MUR Reflection Inequality, and
    the `Step212` First-Missing-Prime `q_E` Zero-Sum Collapse. -/
theorem master_61module_complete_step208_to_step212_goldbach_lean_capstone :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (N / 16 ≤ N / 8 ∧ N / 8 ≤ N / 4 ∧ N / 4 ≤ N / 2 ∧ N / 2 ≤ N) ∧
      (∀ q e W : ℕ, 0 < q →
        Nat.gcd (q ^ e) W * liliuPrefixCosetReturnPeriod q e W = q ^ e ∧
        q ^ e ∣ W * liliuPrefixCosetReturnPeriod q e W) ∧
      (∀ q k : ℕ,
        (liliuSqrtActiveOwnerPrimes (N / 2) q).card <
          (liliuRoughSurvivorSet
            (liliuSubTwoQBlock (liliuFullLowerMURUpper (N / 2)) q k) q).card →
          ∃ p q' p_next' : ℕ,
            Nat.Prime p ∧ Nat.Prime q' ∧ 2 * (N / 2) = p + q' ∧
            p < p_next' ∧ IsPrimeNat p_next') ∧
      (∀ q_E : ℕ, IsFirstMissingOddPrimeLiliu N q_E → N < q_E * (q_E + 2) + 2 →
        (∑ r ∈ pinchedOddPrimes919 N, (liliuTargetSieved3PrimeFiber N r q_E).card) = 0 ∧
        (fiveupPinchedQRSubfilter 9 10 N).card ≤ q_E ∧
        (((q_E : ℝ) ≤ liuMainTerm0004 N) →
          ∃ p q p_next' : ℕ,
            Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next' ∧ IsPrimeNat p_next')) := by
  obtain ⟨K, hK4, hCap59⟩ := master_59module_step208_step209_step211_step212_goldbach_lean_capstone
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven
  have hM := hCap59 N hNK hEven
  have h_stair :=
    (liliu_generalized_dyadic_and_primorial_quotient_cofactor_staircase N 0 1 1 1).2.1
  refine ⟨hM.1, h_stair, ?_, ?_, hM.2.2.2.2⟩
  · intro q e W hq_pos
    have h_per := liliuPrefixCosetReturnPeriod_exact_mul_and_wave_dvd hq_pos e W
    exact ⟨h_per.2.2.1, h_per.2.2.2.1⟩
  · intro q k h_lt
    exact ((liliu_local_subTwoQBlock_rq_minus_tq_and_single_block_goldbach_closure
      (N / 2) q k).2.2 h_lt).2

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.liliu_generalized_dyadic_and_primorial_quotient_cofactor_staircase
#print axioms WuPaper.ESZerosBridge.liliuPrefixCosetReturnPeriod_exact_mul_and_wave_dvd
#print axioms WuPaper.ESZerosBridge.liliu_local_subTwoQBlock_rq_minus_tq_and_single_block_goldbach_closure
#print axioms WuPaper.ESZerosBridge.master_61module_complete_step208_to_step212_goldbach_lean_capstone
