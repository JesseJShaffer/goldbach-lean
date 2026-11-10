import WR2Step256LiLiuScreenedConcreteKbExponentSeparationAnd79ModuleCapstone

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step258LiLiuStep220StrikeEqOwnerRouteBAnd81ModuleCapstone.lean — R5, R7, R8, R9 & R10 Implementation on Track 2 (`D19 N`)
-/

def liliuLpfOwnerFiber (S : Finset ℕ) (q r : ℕ) : Finset ℕ :=
  (liliuPn1RoughCompositeTail S q).filter (fun u : ℕ => u.minFac = r)

def liliuSubCubicStrikeFiber (S : Finset ℕ) (q r : ℕ) : Finset ℕ :=
  (liliuPn1RoughCompositeTail S q).filter (fun u : ℕ => r * r ≤ u ∧ u % r = 0)

theorem liliuSubCubicStrikeFiber_eq_lpfOwnerFiber
    {S : Finset ℕ} {q r : ℕ} (hr : IsPrimeNat r) (h_cube : ∀ u ∈ S, u < q ^ 3) :
    liliuSubCubicStrikeFiber S q r = liliuLpfOwnerFiber S q r ∧
    (liliuSubCubicStrikeFiber S q r).card = (liliuLpfOwnerFiber S q r).card := by
  have h_eq : liliuSubCubicStrikeFiber S q r = liliuLpfOwnerFiber S q r := by
    ext u
    rw [liliuSubCubicStrikeFiber, liliuLpfOwnerFiber, mem_filter, mem_filter]
    constructor
    · rintro ⟨hu_tail, hr_sq, hr_mod0⟩
      refine ⟨hu_tail, ?_⟩
      rw [liliuPn1RoughCompositeTail, mem_filter] at hu_tail
      obtain ⟨hu_S, hu2, hu_rough, hu_comp⟩ := hu_tail
      have hu_lt_cube : u < q ^ 3 := h_cube u hu_S
      have hr_two : 2 ≤ r := hr.1
      have hr_pos : 0 < r := by omega
      have hr_prime : Nat.Prime r := isPrimeNat_to_natPrime_liliu hr
      have hr_dvd_u : r ∣ u := by
        have h_div : r * (u / r) + u % r = u := Nat.div_add_mod u r
        exact ⟨u / r, by omega⟩
      have h_mf_le_r : u.minFac ≤ r :=
        Nat.minFac_le_of_dvd hr_prime.two_le hr_dvd_u
      have h_mf_props := minFac_mul_self_le_of_not_isPrimeNat_liliu hu2 hu_comp
      have h_mf_isp : IsPrimeNat u.minFac := h_mf_props.1
      have h_mf_two : 2 ≤ u.minFac := h_mf_isp.1
      have hq_le_mf : q ≤ u.minFac := by
        match Nat.lt_or_ge u.minFac q with
        | Or.inr hge => exact hge
        | Or.inl hlt =>
          have h_pos := hu_rough u.minFac (mem_range.mpr hlt) h_mf_two
          have h_m0 := h_mf_props.2.1
          omega
      have hq_le_r : q ≤ r := Nat.le_trans hq_le_mf h_mf_le_r
      set m := u / r
      have h_rm_eq : r * m = u :=
        (mod_eq_zero_and_mul_div_of_dvd_liliu hr_pos hr_dvd_u).2
      have hr_sq_le_rm : r * r ≤ r * m := by
        rw [h_rm_eq]
        exact hr_sq
      have hr_le_m : r ≤ m := le_of_mul_le_mul_left_pos_liliu hr_pos hr_sq_le_rm
      have hm2 : 2 ≤ m := Nat.le_trans hr_two hr_le_m
      have hm_dvd_u : m ∣ u := ⟨r, by rw [Nat.mul_comm m r]; exact h_rm_eq.symm⟩
      have hm_isp : IsPrimeNat m := by
        cases Classical.em (IsPrimeNat m) with
        | inl h_p => exact h_p
        | inr h_m_comp =>
          have h_mmf := minFac_mul_self_le_of_not_isPrimeNat_liliu hm2 h_m_comp
          have h_mmf_prime : Nat.Prime m.minFac := isPrimeNat_to_natPrime_liliu h_mmf.1
          have h_mmf_dvd_u : m.minFac ∣ u :=
            Nat.dvd_trans (Nat.minFac_dvd m) hm_dvd_u
          have h_mf_le_mmf : u.minFac ≤ m.minFac :=
            Nat.minFac_le_of_dvd h_mmf_prime.two_le h_mmf_dvd_u
          have hq_le_mmf : q ≤ m.minFac := Nat.le_trans hq_le_mf h_mf_le_mmf
          have hq2_le_mmf2 : q * q ≤ m.minFac * m.minFac :=
            Nat.mul_le_mul hq_le_mmf hq_le_mmf
          have hq2_le_m : q * q ≤ m := Nat.le_trans hq2_le_mmf2 h_mmf.2.2.2
          have hq3_le_rm : q * (q * q) ≤ r * m := Nat.mul_le_mul hq_le_r hq2_le_m
          have h_cube_eq : q ^ 3 = q * (q * q) := by
            show (1 * q) * q * q = q * (q * q)
            rw [Nat.one_mul, Nat.mul_assoc q q q]
          rw [h_rm_eq, ← h_cube_eq] at hq3_le_rm
          exact False.elim (Nat.lt_irrefl u (Nat.lt_of_lt_of_le hu_lt_cube hq3_le_rm))
      have h_mf_prime : Nat.Prime u.minFac := isPrimeNat_to_natPrime_liliu h_mf_isp
      have h_mf_dvd_rm : u.minFac ∣ r * m := by
        rw [h_rm_eq]
        exact Nat.minFac_dvd u
      rcases h_mf_prime.dvd_mul.mp h_mf_dvd_rm with h_dvd_r | h_dvd_m
      · exact (prime_eq_of_dvd_of_isPrimeNat_liliu h_mf_isp hr h_dvd_r).symm
      · have h_eq_m : m = u.minFac :=
          prime_eq_of_dvd_of_isPrimeNat_liliu h_mf_isp hm_isp h_dvd_m
        omega
    · rintro ⟨hu_tail, rfl⟩
      refine ⟨hu_tail, ?_⟩
      rw [liliuPn1RoughCompositeTail, mem_filter] at hu_tail
      have h_mf := minFac_mul_self_le_of_not_isPrimeNat_liliu hu_tail.2.1 hu_tail.2.2.2
      exact ⟨h_mf.2.2.2, h_mf.2.1⟩
  exact ⟨h_eq, by rw [h_eq]⟩

def liliuSourceAboveFactorBranch (M q : ℕ) : Finset ℕ :=
  (liliuPn1RoughCompositeTail (liliuFullLowerMURUpper M) q).filter
    (fun u : ℕ => u.minFac < 2 * M - u)

def liliuSourceBelowFactorBranch (M q : ℕ) : Finset ℕ :=
  (liliuPn1RoughCompositeTail (liliuFullLowerMURUpper M) q).filter
    (fun u : ℕ => 2 * M - u ≤ u.minFac)

theorem liliu_step220_source_factor_ordering_dichotomy (M q : ℕ) :
    Disjoint (liliuSourceAboveFactorBranch M q) (liliuSourceBelowFactorBranch M q) ∧
    (liliuPn1RoughCompositeTail (liliuFullLowerMURUpper M) q).card =
      (liliuSourceAboveFactorBranch M q).card + (liliuSourceBelowFactorBranch M q).card ∧
    (∀ u ∈ liliuSourceAboveFactorBranch M q, 1 ≤ (2 * M) % u.minFac) ∧
    (∀ u ∈ liliuSourceBelowFactorBranch M q,
      (2 * M - u) * (2 * M - u) + (2 * M - u) ≤ 2 * M) := by
  have h_disj : Disjoint (liliuSourceAboveFactorBranch M q) (liliuSourceBelowFactorBranch M q) := by
    apply Finset.disjoint_left.mpr
    intro u h1 h2
    rw [liliuSourceAboveFactorBranch, mem_filter] at h1
    rw [liliuSourceBelowFactorBranch, mem_filter] at h2
    have hlt : u.minFac < 2 * M - u := h1.2
    have hle : 2 * M - u ≤ u.minFac := h2.2
    omega
  have h_union :
      liliuPn1RoughCompositeTail (liliuFullLowerMURUpper M) q =
        liliuSourceAboveFactorBranch M q ∪ liliuSourceBelowFactorBranch M q := by
    ext u
    simp only [mem_union, liliuSourceAboveFactorBranch, liliuSourceBelowFactorBranch, mem_filter]
    constructor
    · intro hu
      match Nat.lt_or_ge u.minFac (2 * M - u) with
      | Or.inl hlt => exact Or.inl ⟨hu, hlt⟩
      | Or.inr hge => exact Or.inr ⟨hu, hge⟩
    · intro hor
      cases hor with
      | inl h1 => exact h1.1
      | inr h2 => exact h2.1
  have h_card :
      (liliuPn1RoughCompositeTail (liliuFullLowerMURUpper M) q).card =
        (liliuSourceAboveFactorBranch M q).card + (liliuSourceBelowFactorBranch M q).card := by
    conv_lhs => rw [h_union]
    exact card_union_of_disjoint h_disj
  have h_above : ∀ u ∈ liliuSourceAboveFactorBranch M q, 1 ≤ (2 * M) % u.minFac := by
    intro u hu
    rw [liliuSourceAboveFactorBranch, mem_filter, liliuPn1RoughCompositeTail, mem_filter] at hu
    obtain ⟨⟨hu_full, hu2, _, hu_comp⟩, h_mf_lt_p⟩ := hu
    have h_mf := minFac_mul_self_le_of_not_isPrimeNat_liliu hu2 hu_comp
    have h_mf_isp : IsPrimeNat u.minFac := h_mf.1
    if h2M_mod0 : (2 * M) % u.minFac = 0 then
      have h_ne : u.minFac ≠ 2 * M - u := by omega
      have h_sh :=
        (liliuFullLowerMURUpper_shielded_from_target_prime_divisors
          hu_full h_mf_isp h2M_mod0 h_ne).1
      omega
    else
      omega
  have h_below :
      ∀ u ∈ liliuSourceBelowFactorBranch M q,
        (2 * M - u) * (2 * M - u) + (2 * M - u) ≤ 2 * M := by
    intro u hu
    rw [liliuSourceBelowFactorBranch, mem_filter, liliuPn1RoughCompositeTail, mem_filter] at hu
    obtain ⟨⟨hu_full, hu2, _, hu_comp⟩, hp_le_mf⟩ := hu
    have hu_props := liliuFullLowerMURUpper_mem_props hu_full
    have h_sum_2M : (2 * M - u) + u = 2 * M := hu_props.2.2.2.2.2
    have h_mf_sq_le_u : u.minFac * u.minFac ≤ u :=
      (minFac_mul_self_le_of_not_isPrimeNat_liliu hu2 hu_comp).2.2.2
    have hp_sq_le_mf_sq : (2 * M - u) * (2 * M - u) ≤ u.minFac * u.minFac :=
      Nat.mul_le_mul hp_le_mf hp_le_mf
    have hp_sq_le_u : (2 * M - u) * (2 * M - u) ≤ u :=
      Nat.le_trans hp_sq_le_mf_sq h_mf_sq_le_u
    omega
  exact ⟨h_disj, h_card, h_above, h_below⟩

theorem liliu_step218_m1_translation_return_identity
    {M p S A H q0 : ℕ}
    (hp_le : p ≤ 2 * M) (h_gap : 2 * M - p = A * S)
    (hA1 : 1 ≤ A) (hH_le : H ≤ 2 * M) (h_trans : p + S = H + q0) :
    (∀ p₁ p₂ : ℕ, p₁ + S = p₂ + S → p₁ = p₂) ∧
    2 * M - H = (A - 1) * S + q0 := by
  have h_inj : ∀ p₁ p₂ : ℕ, p₁ + S = p₂ + S → p₁ = p₂ := by
    intro p₁ p₂ h_eq
    omega
  have h_AS_split : (A - 1) * S + S = A * S := by
    have h1 : (A - 1) * S + 1 * S = ((A - 1) + 1) * S :=
      (Nat.right_distrib (A - 1) 1 S).symm
    have h2 : (A - 1) + 1 = A := Nat.sub_add_cancel hA1
    rw [Nat.one_mul, h2] at h1
    exact h1
  exact ⟨h_inj, by omega⟩

theorem liliu_routeB_additive_neutral_credit_pincer
    {K P S1 S2 H3 H1 H2 R1 R2 Q1 Q2 C1 C2 L : ℕ}
    (h_part : K = P + S1 + S2 + H3)
    (h_neutral : H3 = 0)
    (h_s1 : S1 + R1 ≤ H1)
    (h_s2 : S2 + R2 ≤ H2)
    (hQ1 : H1 ≤ Q1)
    (hQ2 : H2 ≤ Q2)
    (hC1 : C1 ≤ R1)
    (hC2 : C2 ≤ R2)
    (hL : L ≤ K)
    (h_star : Q1 + Q2 + 1 ≤ L + C1 + C2) :
    1 ≤ P ∧ 0 < P := by
  omega

/-- **Theorem 3.1 (`routeB_species_credit_inequality_to_binary_goldbach_liliu` — R9 & R10):**
    The Complete R9 / R10 Route B Partition-Credit Receiver on Track 2 (`D19 N`). -/
theorem routeB_species_credit_inequality_to_binary_goldbach_liliu
    {M : ℕ} (hM1 : 1 ≤ M)
    {H_SQ1 H_P2 : Finset ℕ}
    (h_cov_sq1 : liliuSq1TailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M) ⊆ H_SQ1)
    (h_cov_p2 : liliuP2TailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M) ⊆ H_P2) :
    (liliuSq1TailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M)).card +
      (liliuRejectedByLowerComposite M H_SQ1).card ≤ H_SQ1.card ∧
    (liliuP2TailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M)).card +
      (liliuRejectedByLowerComposite M H_P2).card ≤ H_P2.card ∧
    (∀ Q_SQ1 Q_P2 C_SQ1 C_P2 L : ℕ,
      H_SQ1.card ≤ Q_SQ1 →
      H_P2.card ≤ Q_P2 →
      C_SQ1 ≤ (liliuRejectedByLowerComposite M H_SQ1).card →
      C_P2 ≤ (liliuRejectedByLowerComposite M H_P2).card →
      L ≤ (liliuScreenedConcreteKbRadii M).card →
      Q_SQ1 + Q_P2 + 1 ≤ L + C_SQ1 + C_P2 →
      1 ≤ (liliuPrimeSurvivorSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M)).card ∧
      ∃ p q' p_next' : ℕ,
        Nat.Prime p ∧ Nat.Prime q' ∧ p < q' ∧ 2 * M = p + q' ∧
        p < p_next' ∧ IsPrimeNat p_next') := by
  have h_kb_sub := (liliuConcreteKbUpper_subset_fullLowerMURUpper_and_non_self_obstructing M).2.1
  have h_sq1_ret :
      liliuSq1TailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M) ⊆
        liliuRetainedByLowerPrime M H_SQ1 := by
    intro u hu
    have hu_in_H : u ∈ H_SQ1 := h_cov_sq1 hu
    rw [liliuSq1TailSet, mem_filter, liliuPn1RoughCompositeTail, mem_filter] at hu
    have hu_full := h_kb_sub hu.1.1
    have h_low_isp := (liliuFullLowerMURUpper_mem_props hu_full).2.2.2.2.1
    rw [liliuRetainedByLowerPrime, mem_filter]
    exact ⟨hu_in_H, h_low_isp⟩
  have h_p2_ret :
      liliuP2TailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M) ⊆
        liliuRetainedByLowerPrime M H_P2 := by
    intro u hu
    have hu_in_H : u ∈ H_P2 := h_cov_p2 hu
    rw [liliuP2TailSet, mem_filter, liliuNonSqTailSet, mem_filter,
        liliuPn1RoughCompositeTail, mem_filter] at hu
    have hu_full := h_kb_sub hu.1.1.1
    have h_low_isp := (liliuFullLowerMURUpper_mem_props hu_full).2.2.2.2.1
    rw [liliuRetainedByLowerPrime, mem_filter]
    exact ⟨hu_in_H, h_low_isp⟩
  have h_sq1_le_ret :
      (liliuSq1TailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M)).card ≤
        (liliuRetainedByLowerPrime M H_SQ1).card :=
    card_le_card h_sq1_ret
  have h_p2_le_ret :
      (liliuP2TailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M)).card ≤
        (liliuRetainedByLowerPrime M H_P2).card :=
    card_le_card h_p2_ret
  have h_bal_sq1 := (liliu_routeB_retained_rejected_catalog_credit_balance M H_SQ1).2.2
  have h_bal_p2 := (liliu_routeB_retained_rejected_catalog_credit_balance M H_P2).2.2
  have h_ineq_sq1 :
      (liliuSq1TailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M)).card +
        (liliuRejectedByLowerComposite M H_SQ1).card ≤ H_SQ1.card := by omega
  have h_ineq_p2 :
      (liliuP2TailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M)).card +
        (liliuRejectedByLowerComposite M H_P2).card ≤ H_P2.card := by omega
  refine ⟨h_ineq_sq1, h_ineq_p2, ?_⟩
  intro Q_SQ1 Q_P2 C_SQ1 C_P2 L hQ1 hQ2 hC1 hC2 hL h_star
  have h_part4 :
      (liliuScreenedConcreteKbRadii M).card =
        (liliuPrimeSurvivorSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M)).card +
          (liliuSq1TailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M)).card +
          (liliuP2TailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M)).card +
          (liliuHigherSpeciesTailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M)).card := by
    rw [(liliuScreenedConcreteKb_image_and_card_eq M).2]
    exact (liliu_exact_species_three_way_composite_tail_partition
      (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M)).2
  have h_h3_zero :
      (liliuHigherSpeciesTailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M)).card = 0 :=
    (liliuScreenedConcreteKbUpper_exact_sq1_p2_balance hM1).1
  have h_pincer :=
    liliu_routeB_additive_neutral_credit_pincer
      h_part4 h_h3_zero h_ineq_sq1 h_ineq_p2 hQ1 hQ2 hC1 hC2 hL h_star
  refine ⟨h_pincer.1, ?_⟩
  obtain ⟨u, hu⟩ := card_pos.mp h_pincer.2
  rw [liliuPrimeSurvivorSet, mem_filter] at hu
  obtain ⟨hu_kb, _, _, hu_isp⟩ := hu
  have hu_full := h_kb_sub hu_kb
  have h_props := liliuFullLowerMURUpper_mem_props hu_full
  have hp_lt_u : 2 * M - u < u := by omega
  have hp_nat : Nat.Prime (2 * M - u) := isPrimeNat_to_natPrime_liliu h_props.2.2.2.2.1
  have hu_nat : Nat.Prime u := isPrimeNat_to_natPrime_liliu hu_isp
  obtain ⟨p_next', hp_lt, hp_next_isp⟩ :=
    hasNextPrimeConnection_unconditional (2 * M - u)
  exact ⟨2 * M - u, u, p_next', hp_nat, hu_nat, hp_lt_u, h_props.2.2.2.2.2.symm,
    hp_lt, hp_next_isp⟩

/-- **Master Theorem 3.2 (`master_81module_complete_r1_to_r10_architecture_capstone`):**
    Complete 81-Module Master Capstone uniting R1–R10 on Track 2 (`D19 N`). -/
theorem master_81module_complete_r1_to_r10_architecture_capstone :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (∀ r : ℕ, IsPrimeNat r →
        liliuSubCubicStrikeFiber
          (liliuConcreteKbUpper (N / 2)) (liliuSqrtMidpointCutoff (N / 2)) r =
        liliuLpfOwnerFiber
          (liliuConcreteKbUpper (N / 2)) (liliuSqrtMidpointCutoff (N / 2)) r) ∧
      (∀ q : ℕ,
        (liliuPn1RoughCompositeTail (liliuFullLowerMURUpper (N / 2)) q).card =
          (liliuSourceAboveFactorBranch (N / 2) q).card +
            (liliuSourceBelowFactorBranch (N / 2) q).card ∧
        (∀ u ∈ liliuSourceAboveFactorBranch (N / 2) q, 1 ≤ (2 * (N / 2)) % u.minFac) ∧
        (∀ u ∈ liliuSourceBelowFactorBranch (N / 2) q,
          (2 * (N / 2) - u) * (2 * (N / 2) - u) + (2 * (N / 2) - u) ≤ 2 * (N / 2))) ∧
      (∀ H_SQ1 H_P2 : Finset ℕ,
        liliuSq1TailSet (liliuConcreteKbUpper (N / 2)) (liliuSqrtMidpointCutoff (N / 2)) ⊆ H_SQ1 →
        liliuP2TailSet (liliuConcreteKbUpper (N / 2)) (liliuSqrtMidpointCutoff (N / 2)) ⊆ H_P2 →
        ∀ Q_SQ1 Q_P2 C_SQ1 C_P2 L : ℕ,
          H_SQ1.card ≤ Q_SQ1 →
          H_P2.card ≤ Q_P2 →
          C_SQ1 ≤ (liliuRejectedByLowerComposite (N / 2) H_SQ1).card →
          C_P2 ≤ (liliuRejectedByLowerComposite (N / 2) H_P2).card →
          L ≤ (liliuScreenedConcreteKbRadii (N / 2)).card →
          Q_SQ1 + Q_P2 + 1 ≤ L + C_SQ1 + C_P2 →
          ∃ p q' p_next' : ℕ,
            Nat.Prime p ∧ Nat.Prime q' ∧ p < q' ∧ 2 * (N / 2) = p + q' ∧
            p < p_next' ∧ IsPrimeNat p_next') := by
  obtain ⟨K, hK4, hCap79⟩ := master_79module_r1_to_r4_screened_concreteKb_and_goldbach_lean_capstone
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven
  have hM := hCap79 N hNK hEven
  have hN4 : 4 ≤ N := Nat.le_trans hK4 hNK
  have hM1 : 1 ≤ N / 2 := by omega
  have h_cube_kb :
      ∀ u ∈ liliuConcreteKbUpper (N / 2), u < (liliuSqrtMidpointCutoff (N / 2)) ^ 3 := by
    intro u hu
    have hu_full :=
      (liliuConcreteKbUpper_subset_fullLowerMURUpper_and_non_self_obstructing (N / 2)).2.1 hu
    have hu_lt_2M : u < 2 * (N / 2) := (liliuFullLowerMURUpper_mem_props hu_full).2.2.1
    have h_2M_lt := (liliu_two_mul_M_lt_sqrtMidpointCutoff_cube hM1).2
    exact Nat.lt_trans hu_lt_2M h_2M_lt
  refine ⟨hM.1,
          fun r hr => (liliuSubCubicStrikeFiber_eq_lpfOwnerFiber hr h_cube_kb).1,
          fun q => (liliu_step220_source_factor_ordering_dichotomy (N / 2) q).2,
          ?_⟩
  intro H_SQ1 H_P2 h_cov1 h_cov2 Q_SQ1 Q_P2 C_SQ1 C_P2 L hQ1 hQ2 hC1 hC2 hL h_star
  exact ((routeB_species_credit_inequality_to_binary_goldbach_liliu
    hM1 h_cov1 h_cov2).2.2 Q_SQ1 Q_P2 C_SQ1 C_P2 L hQ1 hQ2 hC1 hC2 hL h_star).2

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.liliuSubCubicStrikeFiber_eq_lpfOwnerFiber
#print axioms WuPaper.ESZerosBridge.liliu_step220_source_factor_ordering_dichotomy
#print axioms WuPaper.ESZerosBridge.liliu_step218_m1_translation_return_identity
#print axioms WuPaper.ESZerosBridge.liliu_routeB_additive_neutral_credit_pincer
#print axioms WuPaper.ESZerosBridge.routeB_species_credit_inequality_to_binary_goldbach_liliu
#print axioms WuPaper.ESZerosBridge.master_81module_complete_r1_to_r10_architecture_capstone
