import WR2Step240LiLiuOMCReflectionShellPackingAnd63ModuleCapstone

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step242LiLiuPreArgonStep217And65ModuleMasterCapstone.lean — Unconditional `r ∣ N` Singleton Fiber Bound, `Step217` Signature Operator, Factorial Wavelength Shift, Cube-Cutoff Tail Depth & Master 65-Module `D19 N` Capstone

Ports `Step217` and the unconditional `r ∣ N` singleton fiber theorem onto Track 2 (`D19 N`)
and welds the complete 65-module suite into the `Goldbach.All` Master Capstone.
-/

/-!
## Section 1: Unconditional `r ∣ N` Singleton Fiber Collapse on `D19 N` (No `r < p` Required)
-/

/-- **Theorem 1.1 (`liliuTight3PrimeFiber_card_le_one_of_dvd_target`):**
    For EVERY prime `r` dividing `N` (`IsPrimeNat r`, `N % r = 0`) and every `m_sieve : ℕ`
    (with zero `r < p` or `r ≤ m_sieve` hypothesis):
    1. `(liliuTight3PrimeFiber N r).card ≤ 1`, and
    2. `(liliuTargetSieved3PrimeFiber N r m_sieve).card ≤ 1`. -/
theorem liliuTight3PrimeFiber_card_le_one_of_dvd_target
    {N r : ℕ} (hr : IsPrimeNat r) (hN_mod : N % r = 0) (m_sieve : ℕ) :
    (liliuTight3PrimeFiber N r).card ≤ 1 ∧
    (liliuTargetSieved3PrimeFiber N r m_sieve).card ≤ 1 := by
  have h_tight_le1 : (liliuTight3PrimeFiber N r).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro q₁ hq₁ q₂ hq₂
    have h1 := (tight_fiber_dvd_target_forces_p_eq_r_and_q_eq_liliu hr hN_mod hq₁).2.1
    have h2 := (tight_fiber_dvd_target_forces_p_eq_r_and_q_eq_liliu hr hN_mod hq₂).2.1
    rw [h1, h2]
  have h_sub : liliuTargetSieved3PrimeFiber N r m_sieve ⊆ liliuTight3PrimeFiber N r :=
    filter_subset _ _
  have h_ts_le1 : (liliuTargetSieved3PrimeFiber N r m_sieve).card ≤ 1 :=
    Nat.le_trans (card_le_card h_sub) h_tight_le1
  exact ⟨h_tight_le1, h_ts_le1⟩

/-!
## Section 2: `Step217` Signature Multiplication Operator & Factorial Wavelength Shift on Track 2
-/

def liliuSigMulOperator (a d Q R : ℕ) : ℕ × ℕ :=
  (a * Q + (a * R) / d, (a * R) % d)

/-- **Theorem 2.1 (`liliu_sig_mul_operator_sound`):**
    Ports `Step217` Theorem 2.1 onto Track 2 (`D19 N`). -/
theorem liliu_sig_mul_operator_sound
    {a d Q R n : ℕ} (hn : n = d * Q + R) :
    a * n = d * (liliuSigMulOperator a d Q R).1 + (liliuSigMulOperator a d Q R).2 ∧
    (a * n) % d = (liliuSigMulOperator a d Q R).2 := by
  unfold liliuSigMulOperator
  dsimp only
  have h_div_mod : d * ((a * R) / d) + (a * R) % d = a * R := Nat.div_add_mod (a * R) d
  have h_expand : a * n = d * (a * Q) + a * R := by
    calc a * n
      _ = a * (d * Q + R) := by rw [hn]
      _ = a * (d * Q) + a * R := Nat.left_distrib a (d * Q) R
      _ = (a * d) * Q + a * R := by rw [← Nat.mul_assoc a d Q]
      _ = (d * a) * Q + a * R := by rw [Nat.mul_comm a d]
      _ = d * (a * Q) + a * R := by rw [Nat.mul_assoc d a Q]
  have h_dist : d * (a * Q + (a * R) / d) = d * (a * Q) + d * ((a * R) / d) :=
    Nat.left_distrib d (a * Q) ((a * R) / d)
  have h_eq : a * n = d * (a * Q + (a * R) / d) + (a * R) % d := by omega
  have h_mod : (a * n) % d = (a * R) % d := by
    rw [h_expand]
    exact mul_add_mod_self_left_liliu d (a * Q) (a * R)
  exact ⟨h_eq, h_mod⟩

/-- **Theorem 2.2 (`liliu_factorial_wavelength_affine_shift`):**
    Ports `Step217` Theorem 2.2 onto Track 2 (`D19 N`). -/
theorem liliu_factorial_wavelength_affine_shift
    {W d : ℕ} (hd_pos : 0 < d) (h_dvd : d ∣ W) (k t : ℕ) :
    (k * W + t) / d = k * (W / d) + t / d ∧
    (k * W + t) % d = t % d := by
  have hW_eq : d * (W / d) = W := (mod_eq_zero_and_mul_div_of_dvd_liliu hd_pos h_dvd).2
  have hkW_eq : k * W = d * (k * (W / d)) := by
    calc k * W
      _ = k * (d * (W / d)) := by rw [hW_eq]
      _ = (k * d) * (W / d) := (Nat.mul_assoc k d (W / d)).symm
      _ = (d * k) * (W / d) := by rw [Nat.mul_comm k d]
      _ = d * (k * (W / d)) := Nat.mul_assoc d k (W / d)
  have h_mod : (k * W + t) % d = t % d := by
    rw [hkW_eq]
    exact mul_add_mod_self_left_liliu d (k * (W / d)) t
  have h_lhs_div : d * ((k * W + t) / d) + (k * W + t) % d = k * W + t :=
    Nat.div_add_mod (k * W + t) d
  have ht_div : d * (t / d) + t % d = t := Nat.div_add_mod t d
  have h_dist : d * (k * (W / d) + t / d) = d * (k * (W / d)) + d * (t / d) :=
    Nat.left_distrib d (k * (W / d)) (t / d)
  have h_mul_eq : d * ((k * W + t) / d) = d * (k * (W / d) + t / d) := by omega
  have h_le1 : (k * W + t) / d ≤ k * (W / d) + t / d :=
    le_of_mul_le_mul_left_pos_liliu hd_pos (Nat.le_of_eq h_mul_eq)
  have h_le2 : k * (W / d) + t / d ≤ (k * W + t) / d :=
    le_of_mul_le_mul_left_pos_liliu hd_pos (Nat.le_of_eq h_mul_eq.symm)
  exact ⟨Nat.le_antisymm h_le1 h_le2, h_mod⟩

theorem liliu_factorialNat_wavelength_affine_shift
    {n d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ n) (k t : ℕ) :
    (k * factorialNat n + t) / d = k * (factorialNat n / d) + t / d ∧
    (k * factorialNat n + t) % d = t % d := by
  have hd_pos : 0 < d := by omega
  have h_dvd : d ∣ factorialNat n := dvd_factorialNat n d hd1 hdn
  exact liliu_factorial_wavelength_affine_shift hd_pos h_dvd k t

/-!
## Section 3: `Step217` Cube-Cutoff Tail Depth, Singular Series & Master 65-Module Capstone
-/

/-- **Theorem 3.1 (`liliu_cube_cutoff_tail_depth_three_factors`):**
    Ports `Step217` Section 3 (Cube-Cutoff Tail Depth) onto Track 2. -/
theorem liliu_cube_cutoff_tail_depth_three_factors
    {N q₁ q₂ q₃ x : ℕ}
    (hq1 : N + 1 ≤ q₁) (hq2 : N + 1 ≤ q₂) (hq3 : N + 1 ≤ q₃)
    (hx_lt : x < (N + 1) ^ 3) :
    x < q₁ * q₂ * q₃ ∧ (0 < x → ¬ (q₁ * q₂ * q₃ ∣ x)) := by
  have h_cube_eq : (N + 1) ^ 3 = (N + 1) * (N + 1) * (N + 1) := by
    show (1 * (N + 1)) * (N + 1) * (N + 1) = (N + 1) * (N + 1) * (N + 1)
    rw [Nat.one_mul]
  have h_12 : (N + 1) * (N + 1) ≤ q₁ * q₂ := Nat.mul_le_mul hq1 hq2
  have h_123 : (N + 1) * (N + 1) * (N + 1) ≤ q₁ * q₂ * q₃ := Nat.mul_le_mul h_12 hq3
  rw [← h_cube_eq] at h_123
  have h_lt_prod : x < q₁ * q₂ * q₃ := Nat.lt_of_lt_of_le hx_lt h_123
  refine ⟨h_lt_prod, ?_⟩
  intro hx_pos h_dvd
  have h_le : q₁ * q₂ * q₃ ≤ x := dvd_le_of_pos h_dvd hx_pos
  exact Nat.lt_irrefl x (Nat.lt_of_lt_of_le h_lt_prod h_le)

theorem add_two_mul_self_add_one_eq_add_one_sq_liliu (m : ℕ) :
    (m + 2) * m + 1 = (m + 1) * (m + 1) := by
  have h1 : (m + 2) * m = m * m + 2 * m := Nat.right_distrib m 2 m
  have h2 : (m + 1) * (m + 1) = (m + 1) * m + (m + 1) * 1 :=
    Nat.left_distrib (m + 1) m 1
  have h3 : (m + 1) * m = m * m + 1 * m := Nat.right_distrib m 1 m
  omega

/-- **Theorem 3.2 (`liliu_local_ray_singular_series_and_65G_reduction`):**
    Ports `Step217` Section 1 & Section 3 (`p * (p - 2) + 1 = (p - 1) ^ 2` and
    `5 * D ≤ C → 65 * G ≤ C → 13 * (2 * G + D) ≤ 3 * C`). -/
theorem liliu_local_ray_singular_series_and_65G_reduction
    {p G D C : ℕ} (hp2 : 2 ≤ p) (hD : 5 * D ≤ C) (hG : 65 * G ≤ C) :
    p * (p - 2) + 1 = (p - 1) ^ 2 ∧
    13 * (2 * G + D) ≤ 3 * C := by
  have hp_eq : p = (p - 2) + 2 := by omega
  have hp1_eq : p - 1 = (p - 2) + 1 := by omega
  have h_sq_id : p * (p - 2) + 1 = (p - 1) ^ 2 := by
    calc p * (p - 2) + 1
      _ = ((p - 2) + 2) * (p - 2) + 1 :=
          congrArg (fun x => x * (p - 2) + 1) hp_eq
      _ = ((p - 2) + 1) * ((p - 2) + 1) :=
          add_two_mul_self_add_one_eq_add_one_sq_liliu (p - 2)
      _ = (p - 1) * (p - 1) :=
          congrArg (fun x => x * x) hp1_eq.symm
      _ = (p - 1) ^ 2 := (nat_sq_eq_mul (p - 1)).symm
  exact ⟨h_sq_id, by omega⟩

/-- **Master Theorem 3.3 (`master_65module_complete_step208_to_step217_goldbach_lean_capstone`):**
    Complete 65-Module Master Capstone uniting `Goldbach.one_plus_one_nine_count` (`D19 N`),
    the Unconditional `r ∣ N` Singleton Fiber Bound (`(liliuTight3PrimeFiber N r).card ≤ 1`),
    `Step217` Factorial Wavelength Affine Shift & Cube-Cutoff Tail Depth,
    `Step215` & `Step216` OMC Reflection & Difference-of-Squares Shell Packing,
    `Step211` Local Sub-`2q` Single-Block Goldbach Closure, and
    `Step212` First-Missing-Prime `q_E` Zero-Sum Collapse. -/
theorem master_65module_complete_step208_to_step217_goldbach_lean_capstone :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (∀ r m_sieve : ℕ, IsPrimeNat r → N % r = 0 →
        (liliuTight3PrimeFiber N r).card ≤ 1 ∧
        (liliuTargetSieved3PrimeFiber N r m_sieve).card ≤ 1) ∧
      (∀ n d k t : ℕ, 1 ≤ d → d ≤ n →
        (k * factorialNat n + t) / d = k * (factorialNat n / d) + t / d ∧
        (k * factorialNat n + t) % d = t % d) ∧
      (∀ q₁ q₂ q₃ x : ℕ,
        N + 1 ≤ q₁ → N + 1 ≤ q₂ → N + 1 ≤ q₃ → x < (N + 1) ^ 3 →
        x < q₁ * q₂ * q₃) ∧
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
  obtain ⟨K, hK4, hCap63⟩ := master_63module_complete_es_zeros_and_goldbach_lean_capstone
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven
  have hM := hCap63 N hNK hEven
  refine ⟨hM.1,
          fun r m_sieve hr hmod => liliuTight3PrimeFiber_card_le_one_of_dvd_target hr hmod m_sieve,
          fun n d k t hd1 hdn => liliu_factorialNat_wavelength_affine_shift hd1 hdn k t,
          fun q₁ q₂ q₃ x hq1 hq2 hq3 hx =>
            (liliu_cube_cutoff_tail_depth_three_factors hq1 hq2 hq3 hx).1,
          hM.2.2.2.1,
          hM.2.2.2.2⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.liliuTight3PrimeFiber_card_le_one_of_dvd_target
#print axioms WuPaper.ESZerosBridge.liliu_sig_mul_operator_sound
#print axioms WuPaper.ESZerosBridge.liliu_factorial_wavelength_affine_shift
#print axioms WuPaper.ESZerosBridge.liliu_factorialNat_wavelength_affine_shift
#print axioms WuPaper.ESZerosBridge.liliu_cube_cutoff_tail_depth_three_factors
#print axioms WuPaper.ESZerosBridge.liliu_local_ray_singular_series_and_65G_reduction
#print axioms WuPaper.ESZerosBridge.master_65module_complete_step208_to_step217_goldbach_lean_capstone
