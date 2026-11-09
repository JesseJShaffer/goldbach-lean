import WR2Step244LiLiuRescuedLowerMURSurvivorAnd67ModuleCapstone

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step246LiLiuUpperHalfIntervalAnd69ModuleMasterCapstone.lean — Signature-Operator Quotient-One Non-Divisibility, Upper-Half Interval `√(2M) + 1` Separation & Master 69-Module `D19 N` Capstone

Ports the `Step209` Section 3b upper-half interval non-divisibility and strict pincer
theorems onto Track 2 (`D19 N`) via `quotient_one_triangle_zero_free_dead_zone` (`WR2Step224`)
and `liliu_sig_mul_operator_sound` (`WR2Step242`), welding the complete 69-module suite into the
`Goldbach.All` Master Capstone.
-/

theorem isPrimeNat_three_liliu : IsPrimeNat 3 := by
  refine ⟨by omega, ?_⟩
  intro d hd
  have hd_le : d ≤ 3 := dvd_le_of_pos hd (by omega : 0 < 3)
  obtain ⟨k, hk⟩ := hd
  if hd0 : d = 0 then
    rw [hd0, Nat.zero_mul] at hk
    omega
  else if hd1 : d = 1 then
    exact Or.inl hd1
  else if hd2 : d = 2 then
    rw [hd2] at hk
    omega
  else
    exact Or.inr (by omega)

theorem exists_prime_aboveSqrt_nondividing_M4_liliu :
    ∃ p : ℕ, IsPrimeNat p ∧ p % 2 = 1 ∧ p < 4 ∧ 2 * 4 < p * p ∧ (2 * 4) % p ≠ 0 :=
  ⟨3, isPrimeNat_three_liliu, by omega, by omega, by omega, by omega⟩

/-- **Lemma 1.1 (`two_mul_rem_mod_pos_of_odd_liliu`):**
    For any odd modulus `p` (`p % 2 = 1`) and `1 ≤ R < p`, `1 ≤ (2 * R) % p`. -/
theorem two_mul_rem_mod_pos_of_odd_liliu
    {p R : ℕ} (hp_odd : p % 2 = 1) (hR_pos : 1 ≤ R) (hR_lt : R < p) :
    1 ≤ (2 * R) % p := by
  have h_2R_ne_p : 2 * R ≠ p := by
    intro h_eq
    have hp_div2 : 2 * (p / 2) + p % 2 = p := Nat.div_add_mod p 2
    omega
  match Nat.lt_or_ge (2 * R) p with
  | Or.inl h_lt =>
    have h_mod_eq : (2 * R) % p = 2 * R := Nat.mod_eq_of_lt h_lt
    rw [h_mod_eq]
    omega
  | Or.inr h_ge =>
    have h_gt : p < 2 * R := by omega
    have h_lt_2p : 2 * R < 2 * p :=
      Nat.mul_lt_mul_of_pos_left hR_lt (by omega : 0 < 2)
    exact (quotient_one_triangle_zero_free_dead_zone h_gt h_lt_2p).2.1

/-- **Theorem 1.2 (`liliu_odd_in_upper_half_interval_nondividing_two_mul_M`):**
    Signature-Operator Quotient-One Non-Divisibility Law on Track 2:
    Combines `quotient_one_triangle_zero_free_dead_zone` (`WR2Step224`) with
    `liliu_sig_mul_operator_sound` (`WR2Step242`) to prove for EVERY odd integer `p`
    in `p < M` and `M < 2 * p`:
    `1 ≤ M % p`, `¬ (p ∣ M)`, `(2 * M) % p = (liliuSigMulOperator 2 p 1 (M % p)).2`,
    `1 ≤ (2 * M) % p`, and `(2 * M) % p ≠ 0`. -/
theorem liliu_odd_in_upper_half_interval_nondividing_two_mul_M
    {M p : ℕ} (hp_odd : p % 2 = 1) (hp_lt_M : p < M) (hM_lt_2p : M < 2 * p) :
    1 ≤ M % p ∧
    ¬ (p ∣ M) ∧
    (2 * M) % p = (liliuSigMulOperator 2 p 1 (M % p)).2 ∧
    1 ≤ (2 * M) % p ∧
    (2 * M) % p ≠ 0 := by
  have h_q1 := quotient_one_triangle_zero_free_dead_zone hp_lt_M hM_lt_2p
  have hR_pos : 1 ≤ M % p := h_q1.2.1
  have hR_lt : M % p < p := h_q1.2.2.1
  have h_sum : p + M % p = M := h_q1.2.2.2.1
  have h_ndvd : ¬ (p ∣ M) := h_q1.2.2.2.2
  have hM_decomp : M = p * 1 + M % p := by
    rw [Nat.mul_one]
    exact h_sum.symm
  have h_sig := (liliu_sig_mul_operator_sound (a := 2) hM_decomp).2
  have h_sig_eval : (liliuSigMulOperator 2 p 1 (M % p)).2 = (2 * (M % p)) % p := rfl
  have h_2R_pos : 1 ≤ (2 * (M % p)) % p :=
    two_mul_rem_mod_pos_of_odd_liliu hp_odd hR_pos hR_lt
  have h_2M_pos : 1 ≤ (2 * M) % p := by
    rw [h_sig, h_sig_eval]
    exact h_2R_pos
  have h_2M_ne0 : (2 * M) % p ≠ 0 := by
    intro h0
    exact false_of_one_le_of_eq_zero_liliu h_2M_pos h0
  exact ⟨hR_pos, h_ndvd, h_sig, h_2M_pos, h_2M_ne0⟩

theorem sqrt_add_one_le_of_lt_sq_liliu {M p : ℕ} (h_lt : 2 * M < p * p) :
    Nat.sqrt (2 * M) + 1 ≤ p := by
  match Nat.lt_or_ge p (Nat.sqrt (2 * M) + 1) with
  | Or.inr hge => exact hge
  | Or.inl hlt =>
    have hp_le : p ≤ Nat.sqrt (2 * M) := by omega
    have h_p2_le : p * p ≤ Nat.sqrt (2 * M) * Nat.sqrt (2 * M) :=
      Nat.mul_le_mul hp_le hp_le
    have h_sqrt_le : Nat.sqrt (2 * M) * Nat.sqrt (2 * M) ≤ 2 * M :=
      Nat.sqrt_le (2 * M)
    have h_p2_2M : p * p ≤ 2 * M := Nat.le_trans h_p2_le h_sqrt_le
    exact False.elim (Nat.lt_irrefl (2 * M) (Nat.lt_of_lt_of_le h_lt h_p2_2M))

/-- **Theorem 2.1 (`liliu_upper_half_interval_prime_satisfies_step209_aboveSqrt_conditions`):**
    Ports the core arithmetic of `exists_prime_in_aboveSqrt_nondividing_two_mul_M` (`Step209` §3b)
    onto Track 2 (`D19 N`). -/
theorem liliu_upper_half_interval_prime_satisfies_step209_aboveSqrt_conditions
    {M p : ℕ} (hM6 : 6 ≤ M) (hp : IsPrimeNat p)
    (h_gt_half : M / 2 < p) (h_le_two_half : p ≤ 2 * (M / 2)) :
    p % 2 = 1 ∧
    p < M ∧
    2 * M < p * p ∧
    Nat.sqrt (2 * M) + 1 ≤ p ∧
    1 ≤ (2 * M) % p ∧
    (2 * M) % p ≠ 0 := by
  have h_M_div2 : 2 * (M / 2) + M % 2 = M := Nat.div_add_mod M 2
  have h_M_mod2 : M % 2 < 2 := Nat.mod_lt M (by omega : 0 < 2)
  have hh3 : 3 ≤ M / 2 := by omega
  have hp_ge4 : 4 ≤ p := by omega
  have hp_odd : p % 2 = 1 := by
    rcases isPrimeNat_eq_two_or_odd_liliu hp with hp2 | hp_o
    · omega
    · exact hp_o
  have hp_div2 : 2 * (p / 2) + p % 2 = p := Nat.div_add_mod p 2
  have hp_lt_2half : p < 2 * (M / 2) := by omega
  have hp_lt_M : p < M := by omega
  have hM_lt_2p : M < 2 * p := by omega
  have h_3h_le_h2 : 3 * (M / 2) ≤ (M / 2) * (M / 2) :=
    Nat.mul_le_mul_right (M / 2) hh3
  have h_exp1 :
      (M / 2 + 1) * (M / 2 + 1) = (M / 2 + 1) * (M / 2) + (M / 2 + 1) * 1 :=
    Nat.left_distrib (M / 2 + 1) (M / 2) 1
  have h_exp2 :
      (M / 2 + 1) * (M / 2) = (M / 2) * (M / 2) + 1 * (M / 2) :=
    Nat.right_distrib (M / 2) 1 (M / 2)
  have h_2M_lt_h1_sq : 2 * M < (M / 2 + 1) * (M / 2 + 1) := by omega
  have h_h1_le_p : M / 2 + 1 ≤ p := by omega
  have h_h1_sq_le_p2 : (M / 2 + 1) * (M / 2 + 1) ≤ p * p :=
    Nat.mul_le_mul h_h1_le_p h_h1_le_p
  have h_2M_lt_p2 : 2 * M < p * p := Nat.lt_of_lt_of_le h_2M_lt_h1_sq h_h1_sq_le_p2
  have h_sqrt_le_p : Nat.sqrt (2 * M) + 1 ≤ p :=
    sqrt_add_one_le_of_lt_sq_liliu h_2M_lt_p2
  have h_nondiv :=
    liliu_odd_in_upper_half_interval_nondividing_two_mul_M hp_odd hp_lt_M hM_lt_2p
  exact ⟨hp_odd, hp_lt_M, h_2M_lt_p2, h_sqrt_le_p, h_nondiv.2.2.2.1, h_nondiv.2.2.2.2⟩

/-- **Theorem 2.2 (`bertrand_upper_half_prime_discharges_step209_strict_pincer_liliu`):**
    Complete `Step209` Section 3b Strict Pincer Discharge on Track 2 (`D19 N`),
    connected directly to `liliu_local_subTwoQBlock_rq_minus_tq_and_single_block_goldbach_closure` (`WR2Step238`). -/
theorem bertrand_upper_half_prime_discharges_step209_strict_pincer_liliu
    {M q k : ℕ}
    (hM4 : 4 ≤ M) (hM_ne5 : M ≠ 5)
    (h_bertrand : 6 ≤ M → ∃ p : ℕ, IsPrimeNat p ∧ M / 2 < p ∧ p ≤ 2 * (M / 2))
    (h_fmp : ∀ p0 : ℕ, IsPrimeNat p0 → p0 % 2 = 1 → p0 < max q 3 → (2 * M) % p0 = 0) :
    1 ≤ (liliuAboveSqrtLowerMURPrimesCutoff M q).card ∧
    (liliuSqrtActiveOwnerPrimes M (max q 3)).card <
      (liliuRoughSurvivorSet (liliuFullLowerMURUpper M) (max q 3)).card ∧
    (liliuPn1RoughCompositeTail
      (liliuSubTwoQBlock (liliuFullLowerMURUpper M) (max q 3) k) (max q 3)).card <
      (liliuRoughSurvivorSet (liliuFullLowerMURUpper M) (max q 3)).card ∧
    ((liliuRoughSurvivorSet (liliuFullLowerMURUpper M) (max q 3)).card ≤
        (liliuRoughSurvivorSet
          (liliuSubTwoQBlock (liliuFullLowerMURUpper M) (max q 3) k) (max q 3)).card →
      ∃ p q' p_next' : ℕ,
        Nat.Prime p ∧ Nat.Prime q' ∧ 2 * M = p + q' ∧
        p < p_next' ∧ IsPrimeNat p_next') := by
  have h_ex :
      ∃ p : ℕ, IsPrimeNat p ∧ p % 2 = 1 ∧ p < M ∧ 2 * M < p * p ∧ (2 * M) % p ≠ 0 := by
    if hM_eq4 : M = 4 then
      subst hM_eq4
      exact exists_prime_aboveSqrt_nondividing_M4_liliu
    else
      have hM6 : 6 ≤ M := by omega
      obtain ⟨p, hp_isp, h_gt, h_le⟩ := h_bertrand hM6
      have h_props :=
        liliu_upper_half_interval_prime_satisfies_step209_aboveSqrt_conditions
          hM6 hp_isp h_gt h_le
      exact ⟨p, hp_isp, h_props.1, h_props.2.1, h_props.2.2.1, h_props.2.2.2.2.2⟩
  have h_strict :=
    (unconditional_strict_sqrt_owner_lt_rescued_lower_mur_survivors_liliu M q k h_fmp).2.2 h_ex
  refine ⟨h_strict.1, h_strict.2.1, h_strict.2.2, ?_⟩
  intro h_blk_full
  have h_lt_blk :
      (liliuSqrtActiveOwnerPrimes M (max q 3)).card <
        (liliuRoughSurvivorSet
          (liliuSubTwoQBlock (liliuFullLowerMURUpper M) (max q 3) k) (max q 3)).card :=
    Nat.lt_of_lt_of_le h_strict.2.1 h_blk_full
  exact ((liliu_local_subTwoQBlock_rq_minus_tq_and_single_block_goldbach_closure
    M (max q 3) k).2.2 h_lt_blk).2

/-- **Master Theorem 3.1 (`master_69module_complete_es_zeros_and_goldbach_lean_capstone`):**
    Complete 69-Module Master Capstone uniting `Goldbach.one_plus_one_nine_count` (`D19 N`),
    the Signature-Operator Quotient-One Non-Divisibility Law (`liliu_odd_in_upper_half_interval_nondividing_two_mul_M`),
    the `Step209` Section 3b Strict Pincer (`bertrand_upper_half_prime_discharges_step209_strict_pincer_liliu`),
    the `Step217` Factorial Wavelength Shift & Unconditional `r ∣ N` Singleton Fiber Bound,
    the `Step215` & `Step216` OMC Reflection & Difference-of-Squares Shell Packing,
    the `Step211` Local Sub-`2q` Single-Block Goldbach Closure, and
    the `Step212` First-Missing-Prime `q_E` Zero-Sum Collapse. -/
theorem master_69module_complete_es_zeros_and_goldbach_lean_capstone :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (∀ p : ℕ, p % 2 = 1 → p < N / 2 → N / 2 < 2 * p →
        1 ≤ (N / 2) % p ∧
        (2 * (N / 2)) % p = (liliuSigMulOperator 2 p 1 ((N / 2) % p)).2 ∧
        1 ≤ (2 * (N / 2)) % p) ∧
      (∀ q k : ℕ,
        (∀ p0 : ℕ, IsPrimeNat p0 → p0 % 2 = 1 → p0 < max q 3 → (2 * (N / 2)) % p0 = 0) →
        (liliuPn1RoughCompositeTail
          (liliuSubTwoQBlock (liliuFullLowerMURUpper (N / 2)) (max q 3) k) (max q 3)).card +
          (liliuAboveSqrtLowerMURPrimesCutoff (N / 2) q).card ≤
          (liliuRoughSurvivorSet (liliuFullLowerMURUpper (N / 2)) (max q 3)).card) ∧
      (∀ r m_sieve : ℕ, IsPrimeNat r → N % r = 0 →
        (liliuTight3PrimeFiber N r).card ≤ 1 ∧
        (liliuTargetSieved3PrimeFiber N r m_sieve).card ≤ 1) ∧
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
  obtain ⟨K, hK4, hCap67⟩ := master_67module_complete_step208_to_step217_rescued_survivor_capstone
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven
  have hM := hCap67 N hNK hEven
  refine ⟨hM.1, ?_, hM.2.1, hM.2.2.1, hM.2.2.2.1, hM.2.2.2.2⟩
  intro p hp_odd hp_lt h_lt_2p
  have h_nd := liliu_odd_in_upper_half_interval_nondividing_two_mul_M hp_odd hp_lt h_lt_2p
  exact ⟨h_nd.1, h_nd.2.2.1, h_nd.2.2.2.1⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.isPrimeNat_three_liliu
#print axioms WuPaper.ESZerosBridge.exists_prime_aboveSqrt_nondividing_M4_liliu
#print axioms WuPaper.ESZerosBridge.two_mul_rem_mod_pos_of_odd_liliu
#print axioms WuPaper.ESZerosBridge.liliu_odd_in_upper_half_interval_nondividing_two_mul_M
#print axioms WuPaper.ESZerosBridge.liliu_upper_half_interval_prime_satisfies_step209_aboveSqrt_conditions
#print axioms WuPaper.ESZerosBridge.bertrand_upper_half_prime_discharges_step209_strict_pincer_liliu
#print axioms WuPaper.ESZerosBridge.master_69module_complete_es_zeros_and_goldbach_lean_capstone
