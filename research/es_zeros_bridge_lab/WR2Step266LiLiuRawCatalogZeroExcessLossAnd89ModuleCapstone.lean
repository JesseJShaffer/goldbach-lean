import WR2Step264LiLiuCompleteR1ToR10StructuralAnd87ModuleCapstone

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step266LiLiuRawCatalogZeroExcessLossAnd89ModuleCapstone.lean — `v4` Review Implementation on Track 2 (`D19 N`): Concrete Raw `SQ-1` & `P-2` Catalogs (`e_σ = 0`), Canonical First-Strike Rejection Partition, `Step218` Varying-GPF Joint Translation Injectivity, Explicit Neutral/Absorber R9 Equivalence & Master 89-Module Capstone
-/

def liliuRawUpperInterval (M : ℕ) : Finset ℕ :=
  (range (2 * M)).filter (fun u : ℕ =>
    M + 1 ≤ u ∧
    u ≤ 2 * M - 3 ∧
    1 ≤ (2 * M - u) % 2 ∧
    1 ≤ M % (2 * M - u))

def liliuRawSq1Catalog (M : ℕ) : Finset ℕ :=
  liliuSq1TailSet (liliuRawUpperInterval M) (liliuSqrtMidpointCutoff M)

def liliuRawP2Catalog (M : ℕ) : Finset ℕ :=
  liliuP2TailSet (liliuRawUpperInterval M) (liliuSqrtMidpointCutoff M)

theorem liliu_retainedByLowerPrime_rawUpperInterval_eq_concreteKbUpper (M : ℕ) :
    liliuRetainedByLowerPrime M (liliuRawUpperInterval M) = liliuConcreteKbUpper M := by
  ext u
  rw [liliuRetainedByLowerPrime, mem_filter, liliuRawUpperInterval, mem_filter, mem_range]
  constructor
  · rintro ⟨⟨hu_lt, hu_ge, hu_le, hu_npv2, hu_cop⟩, hu_isp⟩
    rw [liliuConcreteKbUpper, mem_image]
    refine ⟨u - M, ?_, by omega⟩
    rw [liliuConcreteKbRadii, mem_filter, mem_range]
    have h_sub : M - (u - M) = 2 * M - u := by omega
    rw [h_sub]
    exact ⟨by omega, by omega, hu_npv2, hu_isp, hu_cop⟩
  · intro hu_kb
    rw [liliuConcreteKbUpper, mem_image] at hu_kb
    obtain ⟨R, hR, rfl⟩ := hu_kb
    rw [liliuConcreteKbRadii, mem_filter, mem_range] at hR
    obtain ⟨hR_lt, hR1, hMR_npv2, hMR_isp, hMR_cop⟩ := hR
    have h_sub : 2 * M - (M + R) = M - R := by omega
    rw [h_sub]
    exact ⟨⟨by omega, by omega, by omega, hMR_npv2, hMR_cop⟩, hMR_isp⟩

theorem liliu_rawSq1_and_rawP2_retained_eq_exact_tails_and_zero_excess_loss (M : ℕ) :
    liliuRetainedByLowerPrime M (liliuRawSq1Catalog M) =
      liliuSq1TailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M) ∧
    liliuRetainedByLowerPrime M (liliuRawP2Catalog M) =
      liliuP2TailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M) ∧
    liliuSq1TailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M) ⊆
      liliuRawSq1Catalog M ∧
    liliuP2TailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M) ⊆
      liliuRawP2Catalog M ∧
    (liliuRawSq1Catalog M).card =
      (liliuSq1TailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M)).card +
        (liliuRejectedByLowerComposite M (liliuRawSq1Catalog M)).card ∧
    (liliuRawP2Catalog M).card =
      (liliuP2TailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M)).card +
        (liliuRejectedByLowerComposite M (liliuRawP2Catalog M)).card := by
  have h_base := liliu_retainedByLowerPrime_rawUpperInterval_eq_concreteKbUpper M
  have h_sq1_eq :
      liliuRetainedByLowerPrime M (liliuRawSq1Catalog M) =
        liliuSq1TailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M) := by
    ext u
    rw [liliuRetainedByLowerPrime, mem_filter, liliuRawSq1Catalog,
        liliuSq1TailSet, liliuSq1TailSet, mem_filter, mem_filter,
        liliuPn1RoughCompositeTail, liliuPn1RoughCompositeTail, mem_filter, mem_filter,
        ← h_base, liliuRetainedByLowerPrime, mem_filter]
    constructor
    · rintro ⟨⟨⟨hu_raw, hu_rest⟩, hu_sq⟩, hu_isp⟩
      exact ⟨⟨⟨hu_raw, hu_isp⟩, hu_rest⟩, hu_sq⟩
    · rintro ⟨⟨⟨hu_raw, hu_isp⟩, hu_rest⟩, hu_sq⟩
      exact ⟨⟨⟨hu_raw, hu_rest⟩, hu_sq⟩, hu_isp⟩
  have h_p2_eq :
      liliuRetainedByLowerPrime M (liliuRawP2Catalog M) =
        liliuP2TailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M) := by
    ext u
    rw [liliuRetainedByLowerPrime, mem_filter, liliuRawP2Catalog,
        liliuP2TailSet, liliuP2TailSet, mem_filter, mem_filter,
        liliuNonSqTailSet, liliuNonSqTailSet, mem_filter, mem_filter,
        liliuPn1RoughCompositeTail, liliuPn1RoughCompositeTail, mem_filter, mem_filter,
        ← h_base, liliuRetainedByLowerPrime, mem_filter]
    constructor
    · rintro ⟨⟨⟨⟨hu_raw, hu_rest⟩, hu_nsq⟩, hu_p2⟩, hu_isp⟩
      exact ⟨⟨⟨⟨hu_raw, hu_isp⟩, hu_rest⟩, hu_nsq⟩, hu_p2⟩
    · rintro ⟨⟨⟨⟨hu_raw, hu_isp⟩, hu_rest⟩, hu_nsq⟩, hu_p2⟩
      exact ⟨⟨⟨⟨hu_raw, hu_rest⟩, hu_nsq⟩, hu_p2⟩, hu_isp⟩
  have h_cov1 :
      liliuSq1TailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M) ⊆
        liliuRawSq1Catalog M := by
    rw [← h_sq1_eq]
    exact filter_subset _ _
  have h_cov2 :
      liliuP2TailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M) ⊆
        liliuRawP2Catalog M := by
    rw [← h_p2_eq]
    exact filter_subset _ _
  have h_bal1 := (liliu_routeB_retained_rejected_catalog_credit_balance M (liliuRawSq1Catalog M)).2.2
  have h_bal2 := (liliu_routeB_retained_rejected_catalog_credit_balance M (liliuRawP2Catalog M)).2.2
  rw [h_sq1_eq] at h_bal1
  rw [h_p2_eq] at h_bal2
  exact ⟨h_sq1_eq, h_p2_eq, h_cov1, h_cov2, h_bal1, h_bal2⟩

def liliuRejectionByMinFacFiber (M : ℕ) (H : Finset ℕ) (s : ℕ) : Finset ℕ :=
  (liliuRejectedByLowerComposite M H).filter (fun u : ℕ => (2 * M - u).minFac = s)

def liliuActiveRejectionMinFacOwners (M : ℕ) (H : Finset ℕ) : Finset ℕ :=
  (liliuRejectedByLowerComposite M H).image (fun u : ℕ => (2 * M - u).minFac)

theorem liliuRejectionByMinFacFiber_disjoint_of_ne
    (M : ℕ) (H : Finset ℕ) {s₁ s₂ : ℕ} (hne : s₁ ≠ s₂) :
    Disjoint (liliuRejectionByMinFacFiber M H s₁) (liliuRejectionByMinFacFiber M H s₂) := by
  apply Finset.disjoint_left.mpr
  intro u hu1 hu2
  rw [liliuRejectionByMinFacFiber, mem_filter] at hu1 hu2
  have h1 : (2 * M - u).minFac = s₁ := hu1.2
  have h2 : (2 * M - u).minFac = s₂ := hu2.2
  omega

theorem liliu_rejectedByLowerComposite_eq_sum_rejectionByMinFacFiber (M : ℕ) (H : Finset ℕ) :
    liliuRejectedByLowerComposite M H =
      (liliuActiveRejectionMinFacOwners M H).biUnion (fun s : ℕ =>
        liliuRejectionByMinFacFiber M H s) ∧
    (liliuRejectedByLowerComposite M H).card =
      ∑ s ∈ liliuActiveRejectionMinFacOwners M H, (liliuRejectionByMinFacFiber M H s).card := by
  have h_bi :
      liliuRejectedByLowerComposite M H =
        (liliuActiveRejectionMinFacOwners M H).biUnion (fun s : ℕ =>
          liliuRejectionByMinFacFiber M H s) := by
    ext u
    rw [mem_biUnion]
    constructor
    · intro hu
      refine ⟨(2 * M - u).minFac, ?_, ?_⟩
      · rw [liliuActiveRejectionMinFacOwners, mem_image]
        exact ⟨u, hu, rfl⟩
      · rw [liliuRejectionByMinFacFiber, mem_filter]
        exact ⟨hu, rfl⟩
    · rintro ⟨s, _, hu_fib⟩
      rw [liliuRejectionByMinFacFiber, mem_filter] at hu_fib
      exact hu_fib.1
  have h_disj :
      (↑(liliuActiveRejectionMinFacOwners M H) : Set ℕ).PairwiseDisjoint
        (fun s : ℕ => liliuRejectionByMinFacFiber M H s) := by
    intro s₁ _ s₂ _ hne
    exact liliuRejectionByMinFacFiber_disjoint_of_ne M H hne
  have h_card :
      (liliuRejectedByLowerComposite M H).card =
        ∑ s ∈ liliuActiveRejectionMinFacOwners M H, (liliuRejectionByMinFacFiber M H s).card := by
    conv_lhs => rw [h_bi]
    exact card_biUnion h_disj
  exact ⟨h_bi, h_card⟩

theorem liliu_step218_varying_gpf_joint_translation_injective
    {M p1 p2 S1 S2 A1 A2 : ℕ}
    (hS1 : IsPrimeNat S1) (hS2 : IsPrimeNat S2)
    (hS1_sq : 2 * M < S1 * S1) (hS2_sq : 2 * M < S2 * S2)
    (hp1_le : p1 ≤ 2 * M) (hp2_le : p2 ≤ 2 * M)
    (hA1 : 2 ≤ A1) (hA2 : 2 ≤ A2)
    (h_gap1 : 2 * M - p1 = A1 * S1) (h_gap2 : 2 * M - p2 = A2 * S2)
    (h_trans_eq : p1 + S1 = p2 + S2) :
    (A1 - 1) * S1 = (A2 - 1) * S2 ∧
    S1 = S2 ∧
    p1 = p2 ∧
    A1 = A2 := by
  have hS1_two : 2 ≤ S1 := hS1.1
  have hS2_two : 2 ≤ S2 := hS2.1
  have hS1_pos : 0 < S1 := by omega
  have hS2_pos : 0 < S2 := by omega
  have h_split1 : (A1 - 1) * S1 + S1 = A1 * S1 := by
    have h1 : (A1 - 1) * S1 + 1 * S1 = ((A1 - 1) + 1) * S1 :=
      (Nat.right_distrib (A1 - 1) 1 S1).symm
    have h2 : (A1 - 1) + 1 = A1 := Nat.sub_add_cancel (by omega : 1 ≤ A1)
    rw [Nat.one_mul, h2] at h1
    exact h1
  have h_split2 : (A2 - 1) * S2 + S2 = A2 * S2 := by
    have h1 : (A2 - 1) * S2 + 1 * S2 = ((A2 - 1) + 1) * S2 :=
      (Nat.right_distrib (A2 - 1) 1 S2).symm
    have h2 : (A2 - 1) + 1 = A2 := Nat.sub_add_cancel (by omega : 1 ≤ A2)
    rw [Nat.one_mul, h2] at h1
    exact h1
  have h_prod_eq : (A1 - 1) * S1 = (A2 - 1) * S2 := by omega
  have hA1_lt_S1 : A1 < S1 := by
    match Nat.lt_or_ge A1 S1 with
    | Or.inl hlt => exact hlt
    | Or.inr hge =>
      have h_mul : S1 * S1 ≤ A1 * S1 := Nat.mul_le_mul_right S1 hge
      omega
  have hA2_lt_S2 : A2 < S2 := by
    match Nat.lt_or_ge A2 S2 with
    | Or.inl hlt => exact hlt
    | Or.inr hge =>
      have h_mul : S2 * S2 ≤ A2 * S2 := Nat.mul_le_mul_right S2 hge
      omega
  have hA1_sub1_pos : 0 < A1 - 1 := by omega
  have hA2_sub1_pos : 0 < A2 - 1 := by omega
  have hS_eq : S1 = S2 := by
    match Nat.lt_or_ge S1 S2 with
    | Or.inl h_lt12 =>
      have hS2_prime : Nat.Prime S2 := isPrimeNat_to_natPrime_liliu hS2
      have hS2_dvd : S2 ∣ (A1 - 1) * S1 := by
        refine ⟨A2 - 1, ?_⟩
        rw [Nat.mul_comm S2 (A2 - 1), h_prod_eq]
      rcases hS2_prime.dvd_mul.mp hS2_dvd with h_dvd_A1 | h_dvd_S1
      · have h_le : S2 ≤ A1 - 1 := dvd_le_of_pos h_dvd_A1 hA1_sub1_pos
        omega
      · have h_le : S2 ≤ S1 := dvd_le_of_pos h_dvd_S1 hS1_pos
        omega
    | Or.inr h_ge12 =>
      match Nat.lt_or_ge S2 S1 with
      | Or.inl h_lt21 =>
        have hS1_prime : Nat.Prime S1 := isPrimeNat_to_natPrime_liliu hS1
        have hS1_dvd : S1 ∣ (A2 - 1) * S2 := by
          refine ⟨A1 - 1, ?_⟩
          rw [Nat.mul_comm S1 (A1 - 1), ← h_prod_eq]
        rcases hS1_prime.dvd_mul.mp hS1_dvd with h_dvd_A2 | h_dvd_S2
        · have h_le : S1 ≤ A2 - 1 := dvd_le_of_pos h_dvd_A2 hA2_sub1_pos
          omega
        · have h_le : S1 ≤ S2 := dvd_le_of_pos h_dvd_S2 hS2_pos
          omega
      | Or.inr h_ge21 =>
        exact Nat.le_antisymm h_ge21 h_ge12
  have hp_eq : p1 = p2 := by omega
  have hA_mul_eq : S1 * A1 = S1 * A2 := by
    calc S1 * A1
      _ = A1 * S1 := Nat.mul_comm S1 A1
      _ = 2 * M - p1 := h_gap1.symm
      _ = 2 * M - p2 := by rw [hp_eq]
      _ = A2 * S2 := h_gap2
      _ = A2 * S1 := by rw [← hS_eq]
      _ = S1 * A2 := Nat.mul_comm A2 S1
  have hA_le1 : A1 ≤ A2 :=
    le_of_mul_le_mul_left_pos_liliu hS1_pos (Nat.le_of_eq hA_mul_eq)
  have hA_le2 : A2 ≤ A1 :=
    le_of_mul_le_mul_left_pos_liliu hS1_pos (Nat.le_of_eq hA_mul_eq.symm)
  exact ⟨h_prod_eq, hS_eq, hp_eq, Nat.le_antisymm hA_le1 hA_le2⟩

theorem liliu_zero_loss_neutral_absorber_routeB_realization
    {K P S1 S2 H3 Q1 Q2 C1 C2 L : ℕ}
    (h_part4 : K = P + S1 + S2 + H3)
    (h_h3_zero : H3 = 0)
    (h_raw1 : Q1 = S1 + C1)
    (h_raw2 : Q2 = S2 + C2)
    (h_L_eq : L = K) :
    0 * K = 0 ∧
    1 * P = P ∧
    K = P + S1 + S2 ∧
    L + C1 + C2 = P + (Q1 + Q2) ∧
    (1 ≤ P ↔ Q1 + Q2 + 1 ≤ L + C1 + C2) := by
  have h_zo := zero_absorber_and_one_neutral_pVen_laws_liliu (by omega : 2 ≤ 2) (P + S1 + S2)
  have h_add0 : (P + S1 + S2) + 0 = P + S1 + S2 := h_zo.2.1
  have hK_3 : K = P + S1 + S2 := by
    rw [h_h3_zero, h_add0] at h_part4
    exact h_part4
  refine ⟨Nat.zero_mul K, Nat.one_mul P, hK_3, by omega, by omega⟩

theorem routeB_producer_iff_screened_prime_survivor_pos_liliu
    {M : ℕ} (hM1 : 1 ≤ M) :
    (∃ (H_SQ1 H_P2 : Finset ℕ) (Q_SQ1 Q_P2 C_SQ1 C_P2 L : ℕ),
      liliuSq1TailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M) ⊆ H_SQ1 ∧
      liliuP2TailSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M) ⊆ H_P2 ∧
      H_SQ1.card ≤ Q_SQ1 ∧
      H_P2.card ≤ Q_P2 ∧
      C_SQ1 ≤ (liliuRejectedByLowerComposite M H_SQ1).card ∧
      C_P2 ≤ (liliuRejectedByLowerComposite M H_P2).card ∧
      L ≤ (liliuScreenedConcreteKbRadii M).card ∧
      Q_SQ1 + Q_P2 + 1 ≤ L + C_SQ1 + C_P2) ↔
    1 ≤ (liliuPrimeSurvivorSet (liliuConcreteKbUpper M) (liliuSqrtMidpointCutoff M)).card := by
  constructor
  · rintro ⟨H_SQ1, H_P2, Q_SQ1, Q_P2, C_SQ1, C_P2, L,
            h_cov1, h_cov2, hQ1, hQ2, hC1, hC2, hL, h_star⟩
    exact ((routeB_species_credit_inequality_to_binary_goldbach_liliu
      hM1 h_cov1 h_cov2).2.2 Q_SQ1 Q_P2 C_SQ1 C_P2 L hQ1 hQ2 hC1 hC2 hL h_star).1
  · intro h_pos
    have h_raw := liliu_rawSq1_and_rawP2_retained_eq_exact_tails_and_zero_excess_loss M
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
    have h_real :=
      liliu_zero_loss_neutral_absorber_routeB_realization
        h_part4 h_h3_zero h_raw.2.2.2.2.1 h_raw.2.2.2.2.2 rfl
    exact ⟨liliuRawSq1Catalog M,
           liliuRawP2Catalog M,
           (liliuRawSq1Catalog M).card,
           (liliuRawP2Catalog M).card,
           (liliuRejectedByLowerComposite M (liliuRawSq1Catalog M)).card,
           (liliuRejectedByLowerComposite M (liliuRawP2Catalog M)).card,
           (liliuScreenedConcreteKbRadii M).card,
           h_raw.2.2.1,
           h_raw.2.2.2.1,
           Nat.le_refl _,
           Nat.le_refl _,
           Nat.le_refl _,
           Nat.le_refl _,
           Nat.le_refl _,
           h_real.2.2.2.2.mp h_pos⟩

/-- **Master Theorem 3.2 (`master_89module_complete_v4_review_r1_to_r10_capstone`):**
    Complete 89-Module Master Capstone uniting `Goldbach.one_plus_one_nine_count` (`D19 N`)
    with the full `v4` Review & R1–R10 Closure Architecture. -/
theorem master_89module_complete_v4_review_r1_to_r10_capstone :
    (∀ N : ℕ, 4 ≤ N → Even N → ¬ IsResidualMidpointLiliu (N / 2) →
      ∃ p q p_next' : ℕ,
        Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next' ∧ IsPrimeNat p_next') ∧
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (liliuRetainedByLowerPrime (N / 2) (liliuRawSq1Catalog (N / 2)) =
        liliuSq1TailSet (liliuConcreteKbUpper (N / 2)) (liliuSqrtMidpointCutoff (N / 2)) ∧
       liliuRetainedByLowerPrime (N / 2) (liliuRawP2Catalog (N / 2)) =
        liliuP2TailSet (liliuConcreteKbUpper (N / 2)) (liliuSqrtMidpointCutoff (N / 2))) ∧
      (∀ H : Finset ℕ,
        (liliuRejectedByLowerComposite (N / 2) H).card =
          ∑ s ∈ liliuActiveRejectionMinFacOwners (N / 2) H,
            (liliuRejectionByMinFacFiber (N / 2) H s).card) ∧
      (∀ p1 p2 S1 S2 A1 A2 : ℕ,
        IsPrimeNat S1 → IsPrimeNat S2 →
        2 * (N / 2) < S1 * S1 → 2 * (N / 2) < S2 * S2 →
        p1 ≤ 2 * (N / 2) → p2 ≤ 2 * (N / 2) →
        2 ≤ A1 → 2 ≤ A2 →
        2 * (N / 2) - p1 = A1 * S1 → 2 * (N / 2) - p2 = A2 * S2 →
        p1 + S1 = p2 + S2 →
        S1 = S2 ∧ p1 = p2 ∧ A1 = A2) ∧
      (∀ q : ℕ,
        liliuPrimeSurvivorSet (liliuConcreteKbUpper (N / 2)) q =
          liliuPrimeSurvivorSet (liliuFullLowerMURUpper (N / 2)) q) := by
  obtain ⟨h_non_res, ⟨K, hK4, hCap87⟩⟩ :=
    master_87module_complete_r1_to_r10_structural_closure_capstone
  refine ⟨h_non_res, ⟨K, hK4, ?_⟩⟩
  intro N hNK hEven
  have hM := hCap87 N hNK hEven
  have h_raw := liliu_rawSq1_and_rawP2_retained_eq_exact_tails_and_zero_excess_loss (N / 2)
  refine ⟨hM.1,
          ⟨h_raw.1, h_raw.2.1⟩,
          fun H => (liliu_rejectedByLowerComposite_eq_sum_rejectionByMinFacFiber (N / 2) H).2,
          ?_,
          hM.2.2.1⟩
  intro p1 p2 S1 S2 A1 A2 hS1 hS2 hS1_sq hS2_sq hp1 hp2 hA1 hA2 h_g1 h_g2 h_tr
  exact (liliu_step218_varying_gpf_joint_translation_injective
    hS1 hS2 hS1_sq hS2_sq hp1 hp2 hA1 hA2 h_g1 h_g2 h_tr).2

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.liliu_retainedByLowerPrime_rawUpperInterval_eq_concreteKbUpper
#print axioms WuPaper.ESZerosBridge.liliu_rawSq1_and_rawP2_retained_eq_exact_tails_and_zero_excess_loss
#print axioms WuPaper.ESZerosBridge.liliu_rejectedByLowerComposite_eq_sum_rejectionByMinFacFiber
#print axioms WuPaper.ESZerosBridge.liliu_step218_varying_gpf_joint_translation_injective
#print axioms WuPaper.ESZerosBridge.liliu_zero_loss_neutral_absorber_routeB_realization
#print axioms WuPaper.ESZerosBridge.routeB_producer_iff_screened_prime_survivor_pos_liliu
#print axioms WuPaper.ESZerosBridge.master_89module_complete_v4_review_r1_to_r10_capstone
