import WR2Step249WR2NativeFirstMissingPrimeExistenceAndUnconditionalMURShield

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step251WR2FiberSpaceConcreteKbCarrierWeld.lean — `FiberSpace` Track A `concreteKb` Carrier (`Step24` & `Step207`) Non-Self-Obstruction & Rescued-Survivor Weld (`WR2` Track 1)
-/

def concreteKbRadii (M : ℕ) : Finset ℕ :=
  (range (M - 2)).filter (fun R : ℕ =>
    1 ≤ R ∧
    1 ≤ (M - R) % 2 ∧
    IsPrimeNat (M - R) ∧
    1 ≤ M % (M - R))

def concreteKbUpper (M : ℕ) : Finset ℕ :=
  (concreteKbRadii M).image (fun R : ℕ => M + R)

theorem concreteKbUpper_subset_fullLowerMURUpper_and_non_self_obstructing (M : ℕ) :
    concreteKbRadii M ⊆ fullLowerMURPrimeRadii M ∧
    concreteKbUpper M ⊆ fullLowerMURUpper M ∧
    (concreteKbUpper M).card ≤ (fullLowerMURUpper M).card ∧
    (∀ u ∈ concreteKbUpper M,
      let p := 2 * M - u
      IsPrimeNat p ∧ 1 ≤ M % p ∧ 1 ≤ (2 * M) % p ∧ 1 ≤ u % p) := by
  have h_rad_sub : concreteKbRadii M ⊆ fullLowerMURPrimeRadii M := by
    intro R hR
    rw [concreteKbRadii, mem_filter] at hR
    rw [fullLowerMURPrimeRadii, mem_filter]
    exact ⟨hR.1, hR.2.1, hR.2.2.1, hR.2.2.2.1⟩
  have h_up_sub : concreteKbUpper M ⊆ fullLowerMURUpper M := by
    intro u hu
    rw [concreteKbUpper, mem_image] at hu
    obtain ⟨R, hR, rfl⟩ := hu
    rw [fullLowerMURUpper, mem_image]
    exact ⟨R, h_rad_sub hR, rfl⟩
  have h_card_le : (concreteKbUpper M).card ≤ (fullLowerMURUpper M).card :=
    card_le_card h_up_sub
  refine ⟨h_rad_sub, h_up_sub, h_card_le, ?_⟩
  intro u hu
  dsimp only
  rw [concreteKbUpper, mem_image] at hu
  obtain ⟨R, hR, rfl⟩ := hu
  rw [concreteKbRadii, mem_filter, mem_range] at hR
  obtain ⟨hR_lt, hR1, hMR_npv2, hMR_isp, hM_npv⟩ := hR
  have h_sub_eq : 2 * M - (M + R) = M - R := by omega
  rw [h_sub_eq]
  set p := M - R
  have hp_two : 2 ≤ p := hMR_isp.1
  have hp_pos : 0 < p := by omega
  have hp_mod2_lt : p % 2 < 2 := Nat.mod_lt p (by omega : 0 < 2)
  have hp_odd : p % 2 = 1 := by omega
  have hM_mod_lt : M % p < p := Nat.mod_lt M hp_pos
  have hM_div : M = p * (M / p) + M % p := (Nat.div_add_mod M p).symm
  have h_sig := (sig_mul_operator_sound_native (a := 2) hM_div).2
  have h_sig_eval : (sigMulOperator 2 p (M / p) (M % p)).2 = (2 * (M % p)) % p := rfl
  have h_2rem_pos : 1 ≤ (2 * (M % p)) % p :=
    two_mul_rem_mod_pos_of_odd hp_odd hM_npv hM_mod_lt
  have h_2M_pos : 1 ≤ (2 * M) % p := by
    rw [h_sig, h_sig_eval]
    exact h_2rem_pos
  have h_2M_decomp : p * 1 + (M + R) = 2 * M := by omega
  have h_mod_eq : (2 * M) % p = (M + R) % p := by
    rw [← h_2M_decomp]
    exact mul_add_mod_self_left_native p 1 (M + R)
  have h_u_pos : 1 ≤ (M + R) % p := by
    rw [← h_mod_eq]
    exact h_2M_pos
  exact ⟨hMR_isp, hM_npv, h_2M_pos, h_u_pos⟩

theorem mirror_mem_concreteKbUpper_of_nondividing_two_mul_M
    {M p : ℕ} (hp_isp : IsPrimeNat p) (hp_odd : p % 2 = 1)
    (hp_lt_M : p < M) (h2M_npv : 1 ≤ (2 * M) % p) :
    1 ≤ M % p ∧ mirrorUpperFromLowerPrime M p ∈ concreteKbUpper M := by
  have hp2 : 2 ≤ p := hp_isp.1
  have hp3 : 3 ≤ p := by omega
  have hp_pos : 0 < p := by omega
  have hM_dvd_2M : M ∣ 2 * M := ⟨2, Nat.mul_comm 2 M⟩
  have hM_npv : 1 ≤ M % p :=
    (nonPVen_divisor_inheritance_native hp_pos hM_dvd_2M h2M_npv).1
  refine ⟨hM_npv, ?_⟩
  rw [concreteKbUpper, mem_image]
  refine ⟨M - p, ?_, ?_⟩
  · rw [concreteKbRadii, mem_filter, mem_range]
    have h_sub : M - (M - p) = p := by omega
    rw [h_sub]
    exact ⟨by omega, by omega, by omega, hp_isp, hM_npv⟩
  · unfold mirrorUpperFromLowerPrime
    omega

theorem roughSurvivorSet_concreteKbUpper_subset_fullLowerMURUpper (M q : ℕ) :
    roughSurvivorSet (concreteKbUpper M) q ⊆
      roughSurvivorSet (fullLowerMURUpper M) q ∧
    primeSurvivorSet (concreteKbUpper M) q ⊆
      primeSurvivorSet (fullLowerMURUpper M) q ∧
    (roughSurvivorSet (concreteKbUpper M) q).card ≤
      (roughSurvivorSet (fullLowerMURUpper M) q).card := by
  have h_kb_sub := (concreteKbUpper_subset_fullLowerMURUpper_and_non_self_obstructing M).2.1
  have h_rough_sub :
      roughSurvivorSet (concreteKbUpper M) q ⊆
        roughSurvivorSet (fullLowerMURUpper M) q := by
    intro u hu
    rw [roughSurvivorSet, mem_filter] at hu ⊢
    exact ⟨h_kb_sub hu.1, hu.2⟩
  have h_prime_sub :
      primeSurvivorSet (concreteKbUpper M) q ⊆
        primeSurvivorSet (fullLowerMURUpper M) q := by
    intro u hu
    rw [primeSurvivorSet, mem_filter] at hu ⊢
    exact ⟨h_kb_sub hu.1, hu.2⟩
  exact ⟨h_rough_sub, h_prime_sub, card_le_card h_rough_sub⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.concreteKbUpper_subset_fullLowerMURUpper_and_non_self_obstructing
#print axioms WuPaper.ESZerosBridge.mirror_mem_concreteKbUpper_of_nondividing_two_mul_M
#print axioms WuPaper.ESZerosBridge.roughSurvivorSet_concreteKbUpper_subset_fullLowerMURUpper
