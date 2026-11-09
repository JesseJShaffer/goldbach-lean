import WR2Step237WR2DyadicPrimorialStaircaseAndLocalSubTwoQCombClosure

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step239WR2OMCReflectionAndDifferenceOfSquaresShellBridge.lean — `Step215` Bilateral OMC Reflection Target-Divisor Shield & `Step216` Difference-of-Squares Shell Packing (`WR2` Track 1)

Unites the Pre-Argon / FiberSpace structural bridges (`Step215` and `Step216`) with our
Target-Divisor Shield (`WR2Step223`) and `fullLowerMURUpper` (`WR2Step229`–`WR2Step237`):

1. **Section 1 — Bilateral OMC Reflection Target-Divisor Shield (`Step215` + `WR2Step223`):**
   - `omc_bilateral_reflection_target_divisor_shield`: proves using
     `mod_eq_zero_of_add_eq_of_mod_eq_zero_native` (`WR2Step223`) that for any `R ≤ M` and
     any modulus `p` dividing `2 * M` (`(2 * M) % p = 0`),
     `(M + R) % p = 0 ↔ (M - R) % p = 0` and `1 ≤ (M - R) % p ↔ 1 ≤ (M + R) % p`.
   - `fullLowerMURUpper_shielded_from_target_prime_divisors`: proves that for every
     `u ∈ fullLowerMURUpper M` and every prime `p` dividing `2 * M` with `p < 2 * M - u`,
     `1 ≤ u % p` (`u` is automatically non-`p`-ven and coprime to `p`).
2. **Section 2 — Difference-of-Squares Shell Packing (`Step216`):**
   - `mur_difference_of_squares_shell_identity`: proves in pure native distributive arithmetic
     for all `R ≤ M` that `(M - R) * (M + R) + R * R = M * M` and `(M - R) * (M + R) + R ^ 2 = M ^ 2`.
-/

/-!
## Section 1: Bilateral OMC Reflection Target-Divisor Shield (`Step215` + `WR2Step223`)
-/

/-- **Theorem 1.1 (`omc_bilateral_reflection_target_divisor_shield`):**
    Bilateral OMC Reflection Symmetry (`Step215`) connected to `mod_eq_zero_of_add_eq_of_mod_eq_zero_native`
    (`WR2Step223`): for any `R ≤ M` and any modulus `p` with `(2 * M) % p = 0`,
    1. `(M + R) % p = 0 → (M - R) % p = 0 ∧ p ∣ (M - R)`,
    2. `(M - R) % p = 0 → (M + R) % p = 0 ∧ p ∣ (M + R)`, and
    3. `1 ≤ (M - R) % p ↔ 1 ≤ (M + R) % p`. -/
theorem omc_bilateral_reflection_target_divisor_shield
    {M R p : ℕ} (hR : R ≤ M) (h2M_mod : (2 * M) % p = 0) :
    ((M + R) % p = 0 → (M - R) % p = 0 ∧ p ∣ (M - R)) ∧
    ((M - R) % p = 0 → (M + R) % p = 0 ∧ p ∣ (M + R)) ∧
    (1 ≤ (M - R) % p ↔ 1 ≤ (M + R) % p) := by
  have h_sum_2M : (M + R) + (M - R) = 2 * M := by omega
  have h_fwd : (M + R) % p = 0 → (M - R) % p = 0 ∧ p ∣ (M - R) := by
    intro h_up0
    have h_up_div : p * ((M + R) / p) + (M + R) % p = M + R := Nat.div_add_mod (M + R) p
    have h_eq : p * ((M + R) / p) + (M - R) = 2 * M := by omega
    exact mod_eq_zero_of_add_eq_of_mod_eq_zero_native h_eq h2M_mod
  have h_bwd : (M - R) % p = 0 → (M + R) % p = 0 ∧ p ∣ (M + R) := by
    intro h_low0
    have h_low_div : p * ((M - R) / p) + (M - R) % p = M - R := Nat.div_add_mod (M - R) p
    have h_eq : p * ((M - R) / p) + (M + R) = 2 * M := by omega
    exact mod_eq_zero_of_add_eq_of_mod_eq_zero_native h_eq h2M_mod
  refine ⟨h_fwd, h_bwd, ?_⟩
  constructor
  · intro h_low_pos
    if h_up0 : (M + R) % p = 0 then
      have h_low0 := (h_fwd h_up0).1
      omega
    else
      omega
  · intro h_up_pos
    if h_low0 : (M - R) % p = 0 then
      have h_up0 := (h_bwd h_low0).1
      omega
    else
      omega

/-- **Theorem 1.2 (`fullLowerMURUpper_shielded_from_target_prime_divisors`):**
    Every upper-MUR candidate `u ∈ fullLowerMURUpper M` is automatically shielded from
    every prime divisor `p` of `2 * M` (`IsPrimeNat p`, `(2 * M) % p = 0`) that is distinct
    from its lower-prime partner `2 * M - u`:
    `1 ≤ u % p`, `u ∈ nonPVenDomain (fullLowerMURUpper M) p`, and `predictedNextPrime p = nextPrimeBoundedAux (p + 1) (factorialNat p + 1)`. -/
theorem fullLowerMURUpper_shielded_from_target_prime_divisors
    {M u p : ℕ} (hu : u ∈ fullLowerMURUpper M)
    (hp : IsPrimeNat p) (h2M_mod : (2 * M) % p = 0) (hne : p ≠ 2 * M - u) :
    1 ≤ u % p ∧
    u ∈ nonPVenDomain (fullLowerMURUpper M) p ∧
    predictedNextPrime p = nextPrimeBoundedAux (p + 1) (factorialNat p + 1) ∧
    (∃ p_next : ℕ, p < p_next ∧ IsPrimeNat p_next) := by
  have hu_copy := hu
  rw [fullLowerMURUpper, mem_image] at hu_copy
  obtain ⟨R, hR_mem, rfl⟩ := hu_copy
  rw [fullLowerMURPrimeRadii, mem_filter, mem_range] at hR_mem
  obtain ⟨hR_lt, _, _, hMR_isp⟩ := hR_mem
  have hR_le : R ≤ M := by omega
  have h_sub_eq : 2 * M - (M + R) = M - R := by omega
  rw [h_sub_eq] at hne
  have h_ref := omc_bilateral_reflection_target_divisor_shield hR_le h2M_mod
  have h_up_pos : 1 ≤ (M + R) % p := by
    if h_up0 : (M + R) % p = 0 then
      have h_dvd_low : p ∣ (M - R) := (h_ref.1 h_up0).2
      have h_eq : M - R = p := prime_eq_of_dvd_of_isPrimeNat hp hMR_isp h_dvd_low
      exact False.elim (hne h_eq.symm)
    else
      omega
  refine ⟨h_up_pos, ?_, rfl, hasNextPrimeConnection_unconditional p⟩
  rw [nonPVenDomain, mem_filter]
  exact ⟨hu, h_up_pos⟩

/-!
## Section 2: Difference-of-Squares Shell Packing (`Step216`)
-/

/-- **Theorem 2.1 (`mur_difference_of_squares_shell_identity`):**
    Pure native subtraction-safe Difference-of-Squares Shell Packing identity (`Step216`):
    For all `R ≤ M`, `(M - R) * (M + R) + R * R = M * M` and `(M - R) * (M + R) + R ^ 2 = M ^ 2`. -/
theorem mur_difference_of_squares_shell_identity {M R : ℕ} (hR : R ≤ M) :
    (M - R) * (M + R) + R * R = M * M ∧
    (M - R) * (M + R) + R ^ 2 = M ^ 2 := by
  have h_add : (M - R) + R = M := Nat.sub_add_cancel hR
  have h1 : M * M = ((M - R) + R) * M := by rw [h_add]
  have h2 : ((M - R) + R) * M = (M - R) * M + R * M :=
    Nat.right_distrib (M - R) R M
  have h3 : (M - R) * (M + R) = (M - R) * M + (M - R) * R :=
    Nat.left_distrib (M - R) M R
  have h4 : R * M = ((M - R) + R) * R := by
    rw [h_add, Nat.mul_comm R M]
  have h5 : ((M - R) + R) * R = (M - R) * R + R * R :=
    Nat.right_distrib (M - R) R R
  have h_mul_eq : (M - R) * (M + R) + R * R = M * M := by omega
  refine ⟨h_mul_eq, ?_⟩
  rw [nat_sq_eq_mul R, nat_sq_eq_mul M]
  exact h_mul_eq

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.omc_bilateral_reflection_target_divisor_shield
#print axioms WuPaper.ESZerosBridge.fullLowerMURUpper_shielded_from_target_prime_divisors
#print axioms WuPaper.ESZerosBridge.mur_difference_of_squares_shell_identity
