import WR2Step238LiLiuDyadicPrimorialStaircaseAnd61ModuleCapstone

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step240LiLiuOMCReflectionShellPackingAnd63ModuleCapstone.lean — `Step215` Bilateral OMC Reflection Target-Divisor Shield, `Step216` Difference-of-Squares Shell Packing & Master 63-Module `D19 N` Capstone

Ports `Step215` (OMC Reflection Symmetry & Target-Divisor Shield on `liliuFullLowerMURUpper`)
and `Step216` (Difference-of-Squares Shell Packing `(M - R) * (M + R) + R^2 = M^2`) onto
Track 2 (`D19 N`) and welds the complete 63-module suite into the `Goldbach.All` Master Capstone.
-/

/-!
## Section 1: Bilateral OMC Reflection Target-Divisor Shield (`Step215` + `WR2Step224`)
-/

/-- **Theorem 1.1 (`liliu_omc_bilateral_reflection_target_divisor_shield`):**
    Bilateral OMC Reflection Symmetry (`Step215`) connected to `mod_eq_zero_of_add_eq_of_mod_eq_zero_liliu`
    (`WR2Step224`). -/
theorem liliu_omc_bilateral_reflection_target_divisor_shield
    {M R p : ℕ} (hR : R ≤ M) (h2M_mod : (2 * M) % p = 0) :
    ((M + R) % p = 0 → (M - R) % p = 0 ∧ p ∣ (M - R)) ∧
    ((M - R) % p = 0 → (M + R) % p = 0 ∧ p ∣ (M + R)) ∧
    (1 ≤ (M - R) % p ↔ 1 ≤ (M + R) % p) := by
  have h_sum_2M : (M + R) + (M - R) = 2 * M := by omega
  have h_fwd : (M + R) % p = 0 → (M - R) % p = 0 ∧ p ∣ (M - R) := by
    intro h_up0
    have h_up_div : p * ((M + R) / p) + (M + R) % p = M + R := Nat.div_add_mod (M + R) p
    have h_eq : p * ((M + R) / p) + (M - R) = 2 * M := by omega
    exact mod_eq_zero_of_add_eq_of_mod_eq_zero_liliu h_eq h2M_mod
  have h_bwd : (M - R) % p = 0 → (M + R) % p = 0 ∧ p ∣ (M + R) := by
    intro h_low0
    have h_low_div : p * ((M - R) / p) + (M - R) % p = M - R := Nat.div_add_mod (M - R) p
    have h_eq : p * ((M - R) / p) + (M + R) = 2 * M := by omega
    exact mod_eq_zero_of_add_eq_of_mod_eq_zero_liliu h_eq h2M_mod
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

/-- **Theorem 1.2 (`liliuFullLowerMURUpper_shielded_from_target_prime_divisors`):**
    Every upper-MUR candidate `u ∈ liliuFullLowerMURUpper M` is automatically shielded from
    every prime divisor `p` of `2 * M` (`IsPrimeNat p`, `(2 * M) % p = 0`) distinct from `2 * M - u`. -/
theorem liliuFullLowerMURUpper_shielded_from_target_prime_divisors
    {M u p : ℕ} (hu : u ∈ liliuFullLowerMURUpper M)
    (hp : IsPrimeNat p) (h2M_mod : (2 * M) % p = 0) (hne : p ≠ 2 * M - u) :
    1 ≤ u % p ∧
    u ∈ liliuNonPVenDomain (liliuFullLowerMURUpper M) p ∧
    predictedNextPrime p = nextPrimeBoundedAux (p + 1) (factorialNat p + 1) ∧
    (∃ p_next : ℕ, p < p_next ∧ IsPrimeNat p_next) := by
  have hu_copy := hu
  rw [liliuFullLowerMURUpper, mem_image] at hu_copy
  obtain ⟨R, hR_mem, rfl⟩ := hu_copy
  rw [liliuFullLowerMURPrimeRadii, mem_filter, mem_range] at hR_mem
  obtain ⟨hR_lt, _, _, hMR_isp⟩ := hR_mem
  have hR_le : R ≤ M := by omega
  have h_sub_eq : 2 * M - (M + R) = M - R := by omega
  rw [h_sub_eq] at hne
  have h_ref := liliu_omc_bilateral_reflection_target_divisor_shield hR_le h2M_mod
  have h_up_pos : 1 ≤ (M + R) % p := by
    if h_up0 : (M + R) % p = 0 then
      have h_dvd_low : p ∣ (M - R) := (h_ref.1 h_up0).2
      have h_eq : M - R = p := prime_eq_of_dvd_of_isPrimeNat_liliu hp hMR_isp h_dvd_low
      exact False.elim (hne h_eq.symm)
    else
      omega
  refine ⟨h_up_pos, ?_, rfl, hasNextPrimeConnection_unconditional p⟩
  rw [liliuNonPVenDomain, mem_filter]
  exact ⟨hu, h_up_pos⟩

/-!
## Section 2: Difference-of-Squares Shell Packing (`Step216`) & Master 63-Module Capstone
-/

/-- **Theorem 2.1 (`liliu_mur_difference_of_squares_shell_identity`):**
    Pure native Difference-of-Squares Shell Packing identity (`Step216`):
    For all `R ≤ M`, `(M - R) * (M + R) + R * R = M * M` and `(M - R) * (M + R) + R ^ 2 = M ^ 2`. -/
theorem liliu_mur_difference_of_squares_shell_identity {M R : ℕ} (hR : R ≤ M) :
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

/-- **Master Theorem 2.2 (`master_63module_complete_es_zeros_and_goldbach_lean_capstone`):**
    Complete 63-Module Master Capstone uniting `Goldbach.one_plus_one_nine_count` (`D19 N`),
    the `Step215` Bilateral OMC Reflection Target-Divisor Shield on `liliuFullLowerMURUpper`,
    the `Step216` Difference-of-Squares Shell Packing identity,
    the `Step211` Dyadic/Primorial Staircase, PrefixCoset Return Period & Single-Block Closure,
    the `Step209` `√(2M) + 1` Zero-Tail Collapse, and
    the `Step212` First-Missing-Prime `q_E` Zero-Sum Collapse. -/
theorem master_63module_complete_es_zeros_and_goldbach_lean_capstone :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (∀ R : ℕ, R ≤ N / 2 →
        ((N / 2 - R) * (N / 2 + R) + R ^ 2 = (N / 2) ^ 2)) ∧
      (∀ u ∈ liliuFullLowerMURUpper (N / 2), ∀ p : ℕ,
        IsPrimeNat p → (2 * (N / 2)) % p = 0 → p ≠ 2 * (N / 2) - u →
        1 ≤ u % p ∧ u ∈ liliuNonPVenDomain (liliuFullLowerMURUpper (N / 2)) p) ∧
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
  obtain ⟨K, hK4, hCap61⟩ := master_61module_complete_step208_to_step212_goldbach_lean_capstone
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven
  have hM := hCap61 N hNK hEven
  refine ⟨hM.1, ?_, ?_, hM.2.2.2.1, hM.2.2.2.2⟩
  · intro R hR
    exact (liliu_mur_difference_of_squares_shell_identity hR).2
  · intro u hu p hp h2M_mod hne
    have h_sh := liliuFullLowerMURUpper_shielded_from_target_prime_divisors hu hp h2M_mod hne
    exact ⟨h_sh.1, h_sh.2.1⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.liliu_omc_bilateral_reflection_target_divisor_shield
#print axioms WuPaper.ESZerosBridge.liliuFullLowerMURUpper_shielded_from_target_prime_divisors
#print axioms WuPaper.ESZerosBridge.liliu_mur_difference_of_squares_shell_identity
#print axioms WuPaper.ESZerosBridge.master_63module_complete_es_zeros_and_goldbach_lean_capstone
