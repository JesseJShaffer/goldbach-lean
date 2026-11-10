import WR2Step261WR2R6MultiBlockSpeciesPlacementAndCofactorQuota

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step263WR2CompleteR1R2R3R4R8StructuralClosure.lean — Complete Structural Closure of R1, R2, R3, R4 & R8 (`WR2` Track 1)
-/

/-!
## Section 1 (R1): Prime-Only Screening Equals All-Divisor Screening on `concreteKbRadii M`
-/

def primeScreenedConcreteKbRadii (M : ℕ) : Finset ℕ :=
  (concreteKbRadii M).filter (fun R : ℕ =>
    2 ≤ M + R ∧
    ∀ p ∈ range (sqrtMidpointCutoff M), IsPrimeNat p → 1 ≤ (M + R) % p)

theorem primeScreenedConcreteKbRadii_eq_screenedConcreteKbRadii (M : ℕ) :
    primeScreenedConcreteKbRadii M = screenedConcreteKbRadii M ∧
    (primeScreenedConcreteKbRadii M).card = (screenedConcreteKbRadii M).card := by
  have h_eq : primeScreenedConcreteKbRadii M = screenedConcreteKbRadii M := by
    ext R
    rw [primeScreenedConcreteKbRadii, screenedConcreteKbRadii, mem_filter, mem_filter]
    constructor
    · rintro ⟨hR_kb, hMR2, h_primes⟩
      refine ⟨hR_kb, hMR2, ?_⟩
      intro d hd_range hd2
      rw [mem_range] at hd_range
      obtain ⟨p0, hp0_isp, hp0_dvd_d⟩ :=
        exists_prime_divisor_aux d d hd2 (Nat.le_refl d)
      have hd_pos : 0 < d := by omega
      have hp0_pos : 0 < p0 := isPrimeNat_pos hp0_isp
      have hp0_le_d : p0 ≤ d := dvd_le_of_pos hp0_dvd_d hd_pos
      have hp0_lt : p0 < sqrtMidpointCutoff M := Nat.lt_of_le_of_lt hp0_le_d hd_range
      have h_npv_p0 : 1 ≤ (M + R) % p0 :=
        h_primes p0 (mem_range.mpr hp0_lt) hp0_isp
      if h_mod_d0 : (M + R) % d = 0 then
        have hd_dvd : d ∣ (M + R) := by
          have h_div : d * ((M + R) / d) + (M + R) % d = M + R :=
            Nat.div_add_mod (M + R) d
          exact ⟨(M + R) / d, by omega⟩
        have hp0_dvd : p0 ∣ (M + R) := Nat.dvd_trans hp0_dvd_d hd_dvd
        have h_mod_p0_0 : (M + R) % p0 = 0 :=
          (mod_eq_zero_and_mul_div_of_dvd_native hp0_pos hp0_dvd).1
        omega
      else
        omega
    · rintro ⟨hR_kb, hMR2, h_all⟩
      refine ⟨hR_kb, hMR2, ?_⟩
      intro p hp_range hp_isp
      exact h_all p hp_range hp_isp.1
  exact ⟨h_eq, by rw [h_eq]⟩

/-!
## Section 2 (R1 & R3): Dropped Source Rows Are 100% Composite & Exact Prime-Survivor Equality
-/

def droppedTargetDividingSourceRows (M : ℕ) : Finset ℕ :=
  (fullLowerMURUpper M).filter (fun u : ℕ => u ∉ concreteKbUpper M)

theorem dropped_source_rows_are_composite_and_primeSurvivorSet_eq (M q : ℕ) :
    (∀ u ∈ fullLowerMURUpper M, u ∉ concreteKbUpper M →
      M % (2 * M - u) = 0 ∧ u % (2 * M - u) = 0 ∧ ¬ IsPrimeNat u) ∧
    primeSurvivorSet (concreteKbUpper M) q =
      primeSurvivorSet (fullLowerMURUpper M) q ∧
    (primeSurvivorSet (concreteKbUpper M) q).card =
      (primeSurvivorSet (fullLowerMURUpper M) q).card ∧
    (fullLowerMURUpper M).card =
      (concreteKbUpper M).card + (droppedTargetDividingSourceRows M).card := by
  have h_dropped_comp :
      ∀ u ∈ fullLowerMURUpper M, u ∉ concreteKbUpper M →
        M % (2 * M - u) = 0 ∧ u % (2 * M - u) = 0 ∧ ¬ IsPrimeNat u := by
    intro u hu_full hu_not_kb
    have hu_copy := hu_full
    rw [fullLowerMURUpper, mem_image] at hu_copy
    obtain ⟨R, hR_full, rfl⟩ := hu_copy
    rw [fullLowerMURPrimeRadii, mem_filter, mem_range] at hR_full
    obtain ⟨hR_lt, hR1, hMR_npv2, hMR_isp⟩ := hR_full
    have h_sub_eq : 2 * M - (M + R) = M - R := by omega
    rw [h_sub_eq]
    set p := M - R
    have hp2 : 2 ≤ p := hMR_isp.1
    have hp_pos : 0 < p := by omega
    have hM_mod0 : M % p = 0 := by
      if h_pos : 1 ≤ M % p then
        have h_in_kb : M + R ∈ concreteKbUpper M := by
          rw [concreteKbUpper, mem_image]
          refine ⟨R, ?_, rfl⟩
          rw [concreteKbRadii, mem_filter, mem_range]
          exact ⟨hR_lt, hR1, hMR_npv2, hMR_isp, h_pos⟩
        exact False.elim (hu_not_kb h_in_kb)
      else
        omega
    have hM_div : p * (M / p) + M % p = M := Nat.div_add_mod M p
    rw [hM_mod0, Nat.add_zero] at hM_div
    have h_2M_eq : p * (2 * (M / p)) = 2 * M := by
      calc p * (2 * (M / p))
        _ = (p * 2) * (M / p) := (Nat.mul_assoc p 2 (M / p)).symm
        _ = (2 * p) * (M / p) := by rw [Nat.mul_comm p 2]
        _ = 2 * (p * (M / p)) := Nat.mul_assoc 2 p (M / p)
        _ = 2 * M := by rw [hM_div]
    have h_sum_2M : p * 1 + (M + R) = 2 * M := by omega
    have h_u_mod0 : (M + R) % p = 0 := by
      have h_2M_mod0 : (2 * M) % p = 0 := by
        have h_dvd_2M : p ∣ 2 * M := ⟨2 * (M / p), h_2M_eq.symm⟩
        exact (mod_eq_zero_and_mul_div_of_dvd_native hp_pos h_dvd_2M).1
      exact (mod_eq_zero_of_add_eq_of_mod_eq_zero_native h_sum_2M h_2M_mod0).1
    have h_not_prime : ¬ IsPrimeNat (M + R) := by
      intro hu_isp
      have hp_dvd_u : p ∣ (M + R) := by
        have h_u_div : p * ((M + R) / p) + (M + R) % p = M + R :=
          Nat.div_add_mod (M + R) p
        exact ⟨(M + R) / p, by omega⟩
      have h_eq_pu : M + R = p := prime_eq_of_dvd_of_isPrimeNat hMR_isp hu_isp hp_dvd_u
      omega
    exact ⟨hM_mod0, h_u_mod0, h_not_prime⟩
  have h_prime_eq :
      primeSurvivorSet (concreteKbUpper M) q =
        primeSurvivorSet (fullLowerMURUpper M) q := by
    ext u
    rw [primeSurvivorSet, primeSurvivorSet, mem_filter, mem_filter]
    constructor
    · rintro ⟨hu_kb, hu_rest⟩
      have hu_full :=
        (concreteKbUpper_subset_fullLowerMURUpper_and_non_self_obstructing M).2.1 hu_kb
      exact ⟨hu_full, hu_rest⟩
    · rintro ⟨hu_full, hu2, hu_rough, hu_isp⟩
      refine ⟨?_, hu2, hu_rough, hu_isp⟩
      cases Classical.em (u ∈ concreteKbUpper M) with
      | inl h_in => exact h_in
      | inr h_nin =>
        have h_comp := (h_dropped_comp u hu_full h_nin).2.2
        exact False.elim (h_comp hu_isp)
  have h_kb_sub :=
    (concreteKbUpper_subset_fullLowerMURUpper_and_non_self_obstructing M).2.1
  have h_disj_drop :
      Disjoint (concreteKbUpper M) (droppedTargetDividingSourceRows M) := by
    apply Finset.disjoint_left.mpr
    intro u hu_kb hu_drop
    rw [droppedTargetDividingSourceRows, mem_filter] at hu_drop
    exact hu_drop.2 hu_kb
  have h_union_drop :
      fullLowerMURUpper M =
        concreteKbUpper M ∪ droppedTargetDividingSourceRows M := by
    ext u
    simp only [mem_union, droppedTargetDividingSourceRows, mem_filter]
    constructor
    · intro hu_full
      cases Classical.em (u ∈ concreteKbUpper M) with
      | inl h_in => exact Or.inl h_in
      | inr h_nin => exact Or.inr ⟨hu_full, h_nin⟩
    · intro hor
      cases hor with
      | inl h_in => exact h_kb_sub h_in
      | inr h_dr => exact h_dr.1
  have h_card_drop :
      (fullLowerMURUpper M).card =
        (concreteKbUpper M).card + (droppedTargetDividingSourceRows M).card := by
    conv_lhs => rw [h_union_drop]
    exact card_union_of_disjoint h_disj_drop
  exact ⟨h_dropped_comp, h_prime_eq, by rw [h_prime_eq], h_card_drop⟩

/-!
## Section 3 (R2): Inverse 2D Factor-Pair Catalog Bijection (`concreteHbc ↔ K_comp`)
-/

def concreteHbcPairCatalog (M : ℕ) : Finset (ℕ × ℕ) :=
  (pn1RoughCompositeTail (concreteKbUpper M) (sqrtMidpointCutoff M)).image
    (fun u : ℕ => (u.minFac, u / u.minFac))

theorem concreteHbc_bijection_with_screenedConcreteKb_composites
    {M : ℕ} (hM1 : 1 ≤ M) :
    (∀ pair ∈ concreteHbcPairCatalog M,
      IsPrimeNat pair.1 ∧
      IsPrimeNat pair.2 ∧
      sqrtMidpointCutoff M ≤ pair.1 ∧
      pair.1 ≤ pair.2 ∧
      pair.1 * pair.2 ∈ pn1RoughCompositeTail (concreteKbUpper M) (sqrtMidpointCutoff M)) ∧
    (concreteHbcPairCatalog M).image (fun pair : ℕ × ℕ => pair.1 * pair.2) =
      pn1RoughCompositeTail (concreteKbUpper M) (sqrtMidpointCutoff M) ∧
    (concreteHbcPairCatalog M).card =
      (pn1RoughCompositeTail (concreteKbUpper M) (sqrtMidpointCutoff M)).card ∧
    (concreteHbcPairCatalog M).card =
      (sq1TailSet (concreteKbUpper M) (sqrtMidpointCutoff M)).card +
        (p2TailSet (concreteKbUpper M) (sqrtMidpointCutoff M)).card := by
  have h_bal := screenedConcreteKbUpper_exact_sq1_p2_balance hM1
  have h_h3_zero :
      (higherSpeciesTailSet (concreteKbUpper M) (sqrtMidpointCutoff M)).card = 0 := h_bal.1
  have h_factor_props :
      ∀ u ∈ pn1RoughCompositeTail (concreteKbUpper M) (sqrtMidpointCutoff M),
        IsPrimeNat u.minFac ∧
        IsPrimeNat (u / u.minFac) ∧
        sqrtMidpointCutoff M ≤ u.minFac ∧
        u.minFac ≤ u / u.minFac ∧
        u.minFac * (u / u.minFac) = u := by
    intro u hu
    have hu_copy := hu
    rw [pn1RoughCompositeTail, mem_filter] at hu_copy
    obtain ⟨_, hu2, hu_rough, hu_comp⟩ := hu_copy
    have h_mf := minFac_mul_self_le_of_not_isPrimeNat hu2 hu_comp
    have hp1_isp : IsPrimeNat u.minFac := h_mf.1
    have hp1_two : 2 ≤ u.minFac := hp1_isp.1
    have hp1_pos : 0 < u.minFac := by omega
    have h_mul_eq : u.minFac * (u / u.minFac) = u :=
      (mod_eq_zero_and_mul_div_of_dvd_native hp1_pos (Nat.minFac_dvd u)).2
    have hqb_le : sqrtMidpointCutoff M ≤ u.minFac := by
      match Nat.lt_or_ge u.minFac (sqrtMidpointCutoff M) with
      | Or.inr hge => exact hge
      | Or.inl hlt =>
        have h_pos := hu_rough u.minFac (mem_range.mpr hlt) hp1_two
        have h_m0 := h_mf.2.1
        omega
    have h_sq_le : u.minFac * u.minFac ≤ u.minFac * (u / u.minFac) := by
      rw [h_mul_eq]
      exact h_mf.2.2.2
    have hp1_le_q2 : u.minFac ≤ u / u.minFac :=
      le_of_mul_le_mul_left_pos_wr2 hp1_pos h_sq_le
    have hq2_isp : IsPrimeNat (u / u.minFac) := by
      if h_sq : u.minFac * u.minFac = u then
        have h_eq_mul : u.minFac * (u / u.minFac) = u.minFac * u.minFac := by
          rw [h_mul_eq, h_sq]
        have h_le1 : u / u.minFac ≤ u.minFac :=
          le_of_mul_le_mul_left_pos_wr2 hp1_pos (Nat.le_of_eq h_eq_mul)
        have h_eq_q2 : u / u.minFac = u.minFac := Nat.le_antisymm h_le1 hp1_le_q2
        rw [h_eq_q2]
        exact hp1_isp
      else
        cases Classical.em (IsPrimeNat (u / u.minFac)) with
        | inl hp => exact hp
        | inr hnp =>
          have hu_h3 : u ∈ higherSpeciesTailSet (concreteKbUpper M) (sqrtMidpointCutoff M) := by
            rw [higherSpeciesTailSet, mem_filter, nonSqTailSet, mem_filter]
            exact ⟨⟨hu, h_sq⟩, hnp⟩
          have h_pos_h3 :
              0 < (higherSpeciesTailSet (concreteKbUpper M) (sqrtMidpointCutoff M)).card :=
            card_pos.mpr ⟨u, hu_h3⟩
          omega
    exact ⟨hp1_isp, hq2_isp, hqb_le, hp1_le_q2, h_mul_eq⟩
  have h_pair_props :
      ∀ pair ∈ concreteHbcPairCatalog M,
        IsPrimeNat pair.1 ∧
        IsPrimeNat pair.2 ∧
        sqrtMidpointCutoff M ≤ pair.1 ∧
        pair.1 ≤ pair.2 ∧
        pair.1 * pair.2 ∈ pn1RoughCompositeTail (concreteKbUpper M) (sqrtMidpointCutoff M) := by
    intro pair hpair
    rw [concreteHbcPairCatalog, mem_image] at hpair
    obtain ⟨u, hu, rfl⟩ := hpair
    have hp := h_factor_props u hu
    dsimp only
    rw [hp.2.2.2.2]
    exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hu⟩
  have h_inv_img :
      (concreteHbcPairCatalog M).image (fun pair : ℕ × ℕ => pair.1 * pair.2) =
        pn1RoughCompositeTail (concreteKbUpper M) (sqrtMidpointCutoff M) := by
    ext u
    rw [mem_image]
    constructor
    · rintro ⟨pair, hpair, rfl⟩
      exact (h_pair_props pair hpair).2.2.2.2
    · intro hu
      refine ⟨(u.minFac, u / u.minFac), ?_, (h_factor_props u hu).2.2.2.2⟩
      rw [concreteHbcPairCatalog, mem_image]
      exact ⟨u, hu, rfl⟩
  have h_inj :
      Set.InjOn (fun u : ℕ => (u.minFac, u / u.minFac))
        (↑(pn1RoughCompositeTail (concreteKbUpper M) (sqrtMidpointCutoff M)) : Set ℕ) := by
    intro a ha b hb h_eq
    rw [mem_coe] at ha hb
    dsimp only at h_eq
    have h1 : a.minFac = b.minFac := congrArg Prod.fst h_eq
    have h2 : a / a.minFac = b / b.minFac := congrArg Prod.snd h_eq
    have ha_mul := (h_factor_props a ha).2.2.2.2
    have hb_mul := (h_factor_props b hb).2.2.2.2
    calc a
      _ = a.minFac * (a / a.minFac) := ha_mul.symm
      _ = b.minFac * (a / a.minFac) := congrArg (fun x => x * (a / a.minFac)) h1
      _ = b.minFac * (b / b.minFac) := congrArg (fun x => b.minFac * x) h2
      _ = b := hb_mul
  have h_card_eq :
      (concreteHbcPairCatalog M).card =
        (pn1RoughCompositeTail (concreteKbUpper M) (sqrtMidpointCutoff M)).card :=
    Finset.card_image_of_injOn h_inj
  exact ⟨h_pair_props, h_inv_img, h_card_eq, by rw [h_card_eq, h_bal.2.1]⟩

/-!
## Section 4 (R8): `Step218` Fixed-Point vs. Strictly Progressing Return Dichotomy
-/

theorem step218_fixed_point_iff_q0_eq_S_and_progressing_dichotomy
    {M p S A H q0 : ℕ}
    (hp_le : p ≤ 2 * M) (h_gap : 2 * M - p = A * S)
    (hA1 : 1 ≤ A) (hH_le : H ≤ 2 * M) (h_trans : p + S = H + q0) :
    2 * M - H = (A - 1) * S + q0 ∧
    (H = p ↔ q0 = S) ∧
    (q0 < S → p < H ∧ 2 * M - H < 2 * M - p) := by
  have h_ret := (step218_m1_translation_return_identity hp_le h_gap hA1 hH_le h_trans).2
  exact ⟨h_ret, by omega, fun h_lt => by omega⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.primeScreenedConcreteKbRadii_eq_screenedConcreteKbRadii
#print axioms WuPaper.ESZerosBridge.dropped_source_rows_are_composite_and_primeSurvivorSet_eq
#print axioms WuPaper.ESZerosBridge.concreteHbc_bijection_with_screenedConcreteKb_composites
#print axioms WuPaper.ESZerosBridge.step218_fixed_point_iff_q0_eq_S_and_progressing_dichotomy
