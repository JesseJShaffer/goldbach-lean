import WR2Step239WR2OMCReflectionAndDifferenceOfSquaresShellBridge

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step241WR2PreArgonStep217SignatureOperatorAndDivisorFiberSingleton.lean — Unconditional `r ∣ N` Singleton Fiber Bound, `Step217` Signature Multiplication Operator, Factorial Wavelength Shift & Cube-Cutoff Tail Depth (`WR2` Track 1)

1. **Section 1 — Unconditional `r ∣ N` Singleton Fiber Collapse (No `r < p` Required):**
   - `wr2ShearContractedFiber_card_le_one_of_dvd_target`: proves via
     `tight_fiber_dvd_target_forces_p_eq_r_and_q_eq` (`WR2Step223`) that for EVERY prime `r`
     dividing `N` (`N % r = 0`), every `q` in the fiber equals `(N - r) / r`, so
     `(wr2ShearContractedFiber N r).card ≤ 1` and `(wr2TargetSievedFiber N r m_sieve).card ≤ 1`
     unconditionally for all `r` and `m_sieve` (without assuming `r < p` or `r ≤ m_sieve`).
2. **Section 2 — `Step217` Signature Multiplication Operator & Factorial Wavelength Affine Shift:**
   - `sigMulOperator a d Q R` & `sig_mul_operator_sound_native`: proves
     `n = d * Q + R → a * n = d * (sigMulOperator a d Q R).1 + (sigMulOperator a d Q R).2`
     and `(a * n) % d = (a * R) % d`.
   - `factorial_wavelength_affine_shift_native`: proves for `0 < d` and `d ∣ W` (and
     specifically for `W = factorialNat n` with `1 ≤ d ≤ n`) that
     `(k * W + t) / d = k * (W / d) + t / d` and `(k * W + t) % d = t % d`.
3. **Section 3 — `Step217` Cube-Cutoff Tail Depth, Local-Ray Singular Series & `65G ≤ C` Reduction:**
   - `cube_cutoff_tail_depth_three_factors_native`: proves that if `N + 1 ≤ q₁, q₂, q₃` and
     `0 < x < (N + 1) ^ 3`, then `x < q₁ * q₂ * q₃` and `¬ (q₁ * q₂ * q₃ ∣ x)`.
   - `local_ray_singular_series_sq_identity_native`: proves `p * (p - 2) + 1 = (p - 1) ^ 2` for `2 ≤ p`.
   - `sixty_five_generator_threshold_reduction_native`: proves `5 * D ≤ C → 65 * G ≤ C → 13 * (2 * G + D) ≤ 3 * C`.
-/

/-!
## Section 1: Unconditional `r ∣ N` Singleton Fiber Collapse (Eliminating `r < p`)
-/

/-- **Theorem 1.1 (`wr2ShearContractedFiber_card_le_one_of_dvd_target`):**
    For EVERY prime `r` dividing `N` (`IsPrimeNat r`, `N % r = 0`) and every `m_sieve : ℕ`
    (with zero `r < p` or `r ≤ m_sieve` hypothesis):
    1. `(wr2ShearContractedFiber N r).card ≤ 1`, and
    2. `(wr2TargetSievedFiber N r m_sieve).card ≤ 1`. -/
theorem wr2ShearContractedFiber_card_le_one_of_dvd_target
    {N r : ℕ} (hr : IsPrimeNat r) (hN_mod : N % r = 0) (m_sieve : ℕ) :
    (wr2ShearContractedFiber N r).card ≤ 1 ∧
    (wr2TargetSievedFiber N r m_sieve).card ≤ 1 := by
  have h_shear_le1 : (wr2ShearContractedFiber N r).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro q₁ hq₁ q₂ hq₂
    have h1 := (tight_fiber_dvd_target_forces_p_eq_r_and_q_eq hr hN_mod hq₁).2.1
    have h2 := (tight_fiber_dvd_target_forces_p_eq_r_and_q_eq hr hN_mod hq₂).2.1
    rw [h1, h2]
  have h_sub : wr2TargetSievedFiber N r m_sieve ⊆ wr2ShearContractedFiber N r :=
    filter_subset _ _
  have h_ts_le1 : (wr2TargetSievedFiber N r m_sieve).card ≤ 1 :=
    Nat.le_trans (card_le_card h_sub) h_shear_le1
  exact ⟨h_shear_le1, h_ts_le1⟩

/-!
## Section 2: `Step217` Signature Multiplication Operator & Factorial Wavelength Affine Shift
-/

/-- The 5UP modular signature multiplication operator `M_{a,d}(Q, R)` (`Step217` §2). -/
def sigMulOperator (a d Q R : ℕ) : ℕ × ℕ :=
  (a * Q + (a * R) / d, (a * R) % d)

/-- **Theorem 2.1 (`sig_mul_operator_sound_native`):**
    Ports `Step217` Theorem 2.1 in pure `Init` arithmetic:
    If `n = d * Q + R`, then `a * n = d * (sigMulOperator a d Q R).1 + (sigMulOperator a d Q R).2`
    and `(a * n) % d = (a * R) % d`. -/
theorem sig_mul_operator_sound_native
    {a d Q R n : ℕ} (hn : n = d * Q + R) :
    a * n = d * (sigMulOperator a d Q R).1 + (sigMulOperator a d Q R).2 ∧
    (a * n) % d = (sigMulOperator a d Q R).2 := by
  unfold sigMulOperator
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
    exact mul_add_mod_self_left_native d (a * Q) (a * R)
  exact ⟨h_eq, h_mod⟩

/-- **Theorem 2.2 (`factorial_wavelength_affine_shift_native`):**
    Ports `Step217` Theorem 2.2 (`factorial_wavelength_affine_shift`) in pure `Init` arithmetic:
    For any wavelength `W` divisible by `d > 0` (`d ∣ W`), advancing by `k` wavelengths shifts
    the OMC quotient coordinate by `k * (W / d)` and preserves the OMC remainder `t % d` identically:
    `(k * W + t) / d = k * (W / d) + t / d` and `(k * W + t) % d = t % d`. -/
theorem factorial_wavelength_affine_shift_native
    {W d : ℕ} (hd_pos : 0 < d) (h_dvd : d ∣ W) (k t : ℕ) :
    (k * W + t) / d = k * (W / d) + t / d ∧
    (k * W + t) % d = t % d := by
  have hW_eq : d * (W / d) = W := (mod_eq_zero_and_mul_div_of_dvd_native hd_pos h_dvd).2
  have hkW_eq : k * W = d * (k * (W / d)) := by
    calc k * W
      _ = k * (d * (W / d)) := by rw [hW_eq]
      _ = (k * d) * (W / d) := (Nat.mul_assoc k d (W / d)).symm
      _ = (d * k) * (W / d) := by rw [Nat.mul_comm k d]
      _ = d * (k * (W / d)) := Nat.mul_assoc d k (W / d)
  have h_mod : (k * W + t) % d = t % d := by
    rw [hkW_eq]
    exact mul_add_mod_self_left_native d (k * (W / d)) t
  have h_lhs_div : d * ((k * W + t) / d) + (k * W + t) % d = k * W + t :=
    Nat.div_add_mod (k * W + t) d
  have ht_div : d * (t / d) + t % d = t := Nat.div_add_mod t d
  have h_dist : d * (k * (W / d) + t / d) = d * (k * (W / d)) + d * (t / d) :=
    Nat.left_distrib d (k * (W / d)) (t / d)
  have h_mul_eq : d * ((k * W + t) / d) = d * (k * (W / d) + t / d) := by omega
  have h_le1 : (k * W + t) / d ≤ k * (W / d) + t / d :=
    le_of_mul_le_mul_left_pos_wr2 hd_pos (Nat.le_of_eq h_mul_eq)
  have h_le2 : k * (W / d) + t / d ≤ (k * W + t) / d :=
    le_of_mul_le_mul_left_pos_wr2 hd_pos (Nat.le_of_eq h_mul_eq.symm)
  exact ⟨Nat.le_antisymm h_le1 h_le2, h_mod⟩

/-- Specialization of `factorial_wavelength_affine_shift_native` to the Factorial Lighthouse
    `W = factorialNat n` (`WR2ESZerosGoldbachBridge`) for every `1 ≤ d ≤ n`. -/
theorem factorialNat_wavelength_affine_shift
    {n d : ℕ} (hd1 : 1 ≤ d) (hdn : d ≤ n) (k t : ℕ) :
    (k * factorialNat n + t) / d = k * (factorialNat n / d) + t / d ∧
    (k * factorialNat n + t) % d = t % d := by
  have hd_pos : 0 < d := by omega
  have h_dvd : d ∣ factorialNat n := dvd_factorialNat n d hd1 hdn
  exact factorial_wavelength_affine_shift_native hd_pos h_dvd k t

/-!
## Section 3: `Step217` Cube-Cutoff Tail Depth, Local-Ray Singular Series & `65G ≤ C` Reduction
-/

/-- **Theorem 3.1 (`cube_cutoff_tail_depth_three_factors_native`):**
    Ports `Step217` Section 3 (Scope-Corrected Cube-Cutoff Tail Depth):
    If `N + 1 ≤ q₁`, `N + 1 ≤ q₂`, `N + 1 ≤ q₃`, and `x < (N + 1) ^ 3`, then
    `x < q₁ * q₂ * q₃`, and if `0 < x`, then `¬ (q₁ * q₂ * q₃ ∣ x)`. -/
theorem cube_cutoff_tail_depth_three_factors_native
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

/-- Pure distributive helper `(m + 2) * m + 1 = (m + 1) * (m + 1)`. -/
theorem add_two_mul_self_add_one_eq_add_one_sq (m : ℕ) :
    (m + 2) * m + 1 = (m + 1) * (m + 1) := by
  have h1 : (m + 2) * m = m * m + 2 * m := Nat.right_distrib m 2 m
  have h2 : (m + 1) * (m + 1) = (m + 1) * m + (m + 1) * 1 :=
    Nat.left_distrib (m + 1) m 1
  have h3 : (m + 1) * m = m * m + 1 * m := Nat.right_distrib m 1 m
  omega

/-- **Theorem 3.2 (`local_ray_singular_series_sq_identity_native`):**
    Ports `Step217` Section 3: for every `p ≥ 2`, `p * (p - 2) + 1 = (p - 1) ^ 2`. -/
theorem local_ray_singular_series_sq_identity_native {p : ℕ} (hp2 : 2 ≤ p) :
    p * (p - 2) + 1 = (p - 1) ^ 2 := by
  have hp_eq : p = (p - 2) + 2 := by omega
  have hp1_eq : p - 1 = (p - 2) + 1 := by omega
  calc p * (p - 2) + 1
    _ = ((p - 2) + 2) * (p - 2) + 1 :=
        congrArg (fun x => x * (p - 2) + 1) hp_eq
    _ = ((p - 2) + 1) * ((p - 2) + 1) :=
        add_two_mul_self_add_one_eq_add_one_sq (p - 2)
    _ = (p - 1) * (p - 1) :=
        congrArg (fun x => x * x) hp1_eq.symm
    _ = (p - 1) ^ 2 := (nat_sq_eq_mul (p - 1)).symm

/-- **Theorem 3.3 (`sixty_five_generator_threshold_reduction_native`):**
    Ports `Step217` Theorem 1.3 (`sixty_five_generator_threshold_reduction`) and
    the subtraction-free stagewise recurrence:
    1. If `5 * D ≤ C` and `65 * G ≤ C`, then `13 * (2 * G + D) ≤ 3 * C`, and
    2. If `S_after + H = S_before`, then `p * S_after + p * H = (p - ν) * S_before + ν * S_before`
       for all `ν ≤ p`. -/
theorem sixty_five_generator_threshold_reduction_native
    {G D C p ν S_before S_after H : ℕ}
    (hD : 5 * D ≤ C) (hG : 65 * G ≤ C)
    (h_rec : S_after + H = S_before) (hν : ν ≤ p) :
    13 * (2 * G + D) ≤ 3 * C ∧
    p * S_after + p * H = (p - ν) * S_before + ν * S_before := by
  have h_lhs : p * S_after + p * H = p * S_before := by
    rw [← Nat.left_distrib p S_after H, h_rec]
  have h_rhs : (p - ν) * S_before + ν * S_before = p * S_before := by
    rw [← Nat.right_distrib (p - ν) ν S_before, Nat.sub_add_cancel hν]
  exact ⟨by omega, by rw [h_lhs, h_rhs]⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.wr2ShearContractedFiber_card_le_one_of_dvd_target
#print axioms WuPaper.ESZerosBridge.sig_mul_operator_sound_native
#print axioms WuPaper.ESZerosBridge.factorial_wavelength_affine_shift_native
#print axioms WuPaper.ESZerosBridge.factorialNat_wavelength_affine_shift
#print axioms WuPaper.ESZerosBridge.cube_cutoff_tail_depth_three_factors_native
#print axioms WuPaper.ESZerosBridge.local_ray_singular_series_sq_identity_native
#print axioms WuPaper.ESZerosBridge.sixty_five_generator_threshold_reduction_native
