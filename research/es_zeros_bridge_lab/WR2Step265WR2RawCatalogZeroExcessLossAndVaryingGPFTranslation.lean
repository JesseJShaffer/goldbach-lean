import WR2Step263WR2CompleteR1R2R3R4R8StructuralClosure

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step265WR2RawCatalogZeroExcessLossAndVaryingGPFTranslation.lean — `v4` Review Implementation: Concrete Raw `SQ-1` & `P-2` Catalogs with Zero Excess Retained Loss (`e_σ = 0`), Canonical First-Strike Rejection Partition, `Step218` Varying-GPF Joint Translation Injectivity & Explicit Neutral/Absorber R9 Equivalence (`WR2` Track 1)
-/

def rawUpperInterval (M : ℕ) : Finset ℕ :=
  (range (2 * M)).filter (fun u : ℕ =>
    M + 1 ≤ u ∧
    u ≤ 2 * M - 3 ∧
    1 ≤ (2 * M - u) % 2 ∧
    1 ≤ M % (2 * M - u))

def rawSq1Catalog (M : ℕ) : Finset ℕ :=
  sq1TailSet (rawUpperInterval M) (sqrtMidpointCutoff M)

def rawP2Catalog (M : ℕ) : Finset ℕ :=
  p2TailSet (rawUpperInterval M) (sqrtMidpointCutoff M)

theorem retainedByLowerPrime_rawUpperInterval_eq_concreteKbUpper (M : ℕ) :
    retainedByLowerPrime M (rawUpperInterval M) = concreteKbUpper M := by
  ext u
  rw [retainedByLowerPrime, mem_filter, rawUpperInterval, mem_filter, mem_range]
  constructor
  · rintro ⟨⟨hu_lt, hu_ge, hu_le, hu_npv2, hu_cop⟩, hu_isp⟩
    rw [concreteKbUpper, mem_image]
    refine ⟨u - M, ?_, by omega⟩
    rw [concreteKbRadii, mem_filter, mem_range]
    have h_sub : M - (u - M) = 2 * M - u := by omega
    rw [h_sub]
    exact ⟨by omega, by omega, hu_npv2, hu_isp, hu_cop⟩
  · intro hu_kb
    rw [concreteKbUpper, mem_image] at hu_kb
    obtain ⟨R, hR, rfl⟩ := hu_kb
    rw [concreteKbRadii, mem_filter, mem_range] at hR
    obtain ⟨hR_lt, hR1, hMR_npv2, hMR_isp, hMR_cop⟩ := hR
    have h_sub : 2 * M - (M + R) = M - R := by omega
    rw [h_sub]
    exact ⟨⟨by omega, by omega, by omega, hMR_npv2, hMR_cop⟩, hMR_isp⟩

theorem rawSq1_and_rawP2_retained_eq_exact_tails_and_zero_excess_loss (M : ℕ) :
    retainedByLowerPrime M (rawSq1Catalog M) =
      sq1TailSet (concreteKbUpper M) (sqrtMidpointCutoff M) ∧
    retainedByLowerPrime M (rawP2Catalog M) =
      p2TailSet (concreteKbUpper M) (sqrtMidpointCutoff M) ∧
    sq1TailSet (concreteKbUpper M) (sqrtMidpointCutoff M) ⊆ rawSq1Catalog M ∧
    p2TailSet (concreteKbUpper M) (sqrtMidpointCutoff M) ⊆ rawP2Catalog M ∧
    (rawSq1Catalog M).card =
      (sq1TailSet (concreteKbUpper M) (sqrtMidpointCutoff M)).card +
        (rejectedByLowerComposite M (rawSq1Catalog M)).card ∧
    (rawP2Catalog M).card =
      (p2TailSet (concreteKbUpper M) (sqrtMidpointCutoff M)).card +
        (rejectedByLowerComposite M (rawP2Catalog M)).card := by
  have h_base := retainedByLowerPrime_rawUpperInterval_eq_concreteKbUpper M
  have h_sq1_eq :
      retainedByLowerPrime M (rawSq1Catalog M) =
        sq1TailSet (concreteKbUpper M) (sqrtMidpointCutoff M) := by
    ext u
    rw [retainedByLowerPrime, mem_filter, rawSq1Catalog,
        sq1TailSet, sq1TailSet, mem_filter, mem_filter,
        pn1RoughCompositeTail, pn1RoughCompositeTail, mem_filter, mem_filter,
        ← h_base, retainedByLowerPrime, mem_filter]
    constructor
    · rintro ⟨⟨⟨hu_raw, hu_rest⟩, hu_sq⟩, hu_isp⟩
      exact ⟨⟨⟨hu_raw, hu_isp⟩, hu_rest⟩, hu_sq⟩
    · rintro ⟨⟨⟨hu_raw, hu_isp⟩, hu_rest⟩, hu_sq⟩
      exact ⟨⟨⟨hu_raw, hu_rest⟩, hu_sq⟩, hu_isp⟩
  have h_p2_eq :
      retainedByLowerPrime M (rawP2Catalog M) =
        p2TailSet (concreteKbUpper M) (sqrtMidpointCutoff M) := by
    ext u
    rw [retainedByLowerPrime, mem_filter, rawP2Catalog,
        p2TailSet, p2TailSet, mem_filter, mem_filter,
        nonSqTailSet, nonSqTailSet, mem_filter, mem_filter,
        pn1RoughCompositeTail, pn1RoughCompositeTail, mem_filter, mem_filter,
        ← h_base, retainedByLowerPrime, mem_filter]
    constructor
    · rintro ⟨⟨⟨⟨hu_raw, hu_rest⟩, hu_nsq⟩, hu_p2⟩, hu_isp⟩
      exact ⟨⟨⟨⟨hu_raw, hu_isp⟩, hu_rest⟩, hu_nsq⟩, hu_p2⟩
    · rintro ⟨⟨⟨⟨hu_raw, hu_isp⟩, hu_rest⟩, hu_nsq⟩, hu_p2⟩
      exact ⟨⟨⟨⟨hu_raw, hu_rest⟩, hu_nsq⟩, hu_p2⟩, hu_isp⟩
  have h_cov1 :
      sq1TailSet (concreteKbUpper M) (sqrtMidpointCutoff M) ⊆ rawSq1Catalog M := by
    rw [← h_sq1_eq]
    exact filter_subset _ _
  have h_cov2 :
      p2TailSet (concreteKbUpper M) (sqrtMidpointCutoff M) ⊆ rawP2Catalog M := by
    rw [← h_p2_eq]
    exact filter_subset _ _
  have h_bal1 := (routeB_retained_rejected_catalog_credit_balance M (rawSq1Catalog M)).2.2
  have h_bal2 := (routeB_retained_rejected_catalog_credit_balance M (rawP2Catalog M)).2.2
  rw [h_sq1_eq] at h_bal1
  rw [h_p2_eq] at h_bal2
  exact ⟨h_sq1_eq, h_p2_eq, h_cov1, h_cov2, h_bal1, h_bal2⟩

def rejectionByMinFacFiber (M : ℕ) (H : Finset ℕ) (s : ℕ) : Finset ℕ :=
  (rejectedByLowerComposite M H).filter (fun u : ℕ => (2 * M - u).minFac = s)

def activeRejectionMinFacOwners (M : ℕ) (H : Finset ℕ) : Finset ℕ :=
  (rejectedByLowerComposite M H).image (fun u : ℕ => (2 * M - u).minFac)

theorem rejectionByMinFacFiber_disjoint_of_ne
    (M : ℕ) (H : Finset ℕ) {s₁ s₂ : ℕ} (hne : s₁ ≠ s₂) :
    Disjoint (rejectionByMinFacFiber M H s₁) (rejectionByMinFacFiber M H s₂) := by
  apply Finset.disjoint_left.mpr
  intro u hu1 hu2
  rw [rejectionByMinFacFiber, mem_filter] at hu1 hu2
  have h1 : (2 * M - u).minFac = s₁ := hu1.2
  have h2 : (2 * M - u).minFac = s₂ := hu2.2
  omega

theorem rejectedByLowerComposite_eq_sum_rejectionByMinFacFiber (M : ℕ) (H : Finset ℕ) :
    rejectedByLowerComposite M H =
      (activeRejectionMinFacOwners M H).biUnion (fun s : ℕ =>
        rejectionByMinFacFiber M H s) ∧
    (rejectedByLowerComposite M H).card =
      ∑ s ∈ activeRejectionMinFacOwners M H, (rejectionByMinFacFiber M H s).card := by
  have h_bi :
      rejectedByLowerComposite M H =
        (activeRejectionMinFacOwners M H).biUnion (fun s : ℕ =>
          rejectionByMinFacFiber M H s) := by
    ext u
    rw [mem_biUnion]
    constructor
    · intro hu
      refine ⟨(2 * M - u).minFac, ?_, ?_⟩
      · rw [activeRejectionMinFacOwners, mem_image]
        exact ⟨u, hu, rfl⟩
      · rw [rejectionByMinFacFiber, mem_filter]
        exact ⟨hu, rfl⟩
    · rintro ⟨s, _, hu_fib⟩
      rw [rejectionByMinFacFiber, mem_filter] at hu_fib
      exact hu_fib.1
  have h_disj :
      (↑(activeRejectionMinFacOwners M H) : Set ℕ).PairwiseDisjoint
        (fun s : ℕ => rejectionByMinFacFiber M H s) := by
    intro s₁ _ s₂ _ hne
    exact rejectionByMinFacFiber_disjoint_of_ne M H hne
  have h_card :
      (rejectedByLowerComposite M H).card =
        ∑ s ∈ activeRejectionMinFacOwners M H, (rejectionByMinFacFiber M H s).card := by
    conv_lhs => rw [h_bi]
    exact card_biUnion h_disj
  exact ⟨h_bi, h_card⟩

theorem step218_varying_gpf_joint_translation_injective
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
      have hS2_prime : Nat.Prime S2 := isPrimeNat_to_natPrime hS2
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
        have hS1_prime : Nat.Prime S1 := isPrimeNat_to_natPrime hS1
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
    le_of_mul_le_mul_left_pos_wr2 hS1_pos (Nat.le_of_eq hA_mul_eq)
  have hA_le2 : A2 ≤ A1 :=
    le_of_mul_le_mul_left_pos_wr2 hS1_pos (Nat.le_of_eq hA_mul_eq.symm)
  exact ⟨h_prod_eq, hS_eq, hp_eq, Nat.le_antisymm hA_le1 hA_le2⟩

theorem routeB_loss_accounting_identity
    {K P S1 S2 H1 H2 R1 R2 Q1 Q2 C1 C2 L e1 e2 a1 a2 b1 b2 c : ℕ}
    (hK : K = P + S1 + S2)
    (hH1 : H1 = S1 + e1 + R1)
    (hH2 : H2 = S2 + e2 + R2)
    (hQ1 : Q1 = H1 + a1)
    (hQ2 : Q2 = H2 + a2)
    (hR1 : R1 = C1 + b1)
    (hR2 : R2 = C2 + b2)
    (hL : K = L + c) :
    (L + C1 + C2) + (c + (e1 + a1 + b1) + (e2 + a2 + b2)) = P + (Q1 + Q2) := by
  omega

theorem zero_loss_neutral_absorber_routeB_realization
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
  have h_zo := zero_absorber_and_one_neutral_pVen_laws (by omega : 2 ≤ 2) (P + S1 + S2)
  have h_add0 : (P + S1 + S2) + 0 = P + S1 + S2 := h_zo.2.1
  have hK_3 : K = P + S1 + S2 := by
    rw [h_h3_zero, h_add0] at h_part4
    exact h_part4
  refine ⟨Nat.zero_mul K, Nat.one_mul P, hK_3, by omega, by omega⟩

theorem routeB_producer_iff_screened_prime_survivor_pos_wr2
    {M : ℕ} (hM1 : 1 ≤ M) :
    (∃ (H_SQ1 H_P2 : Finset ℕ) (Q_SQ1 Q_P2 C_SQ1 C_P2 L : ℕ),
      sq1TailSet (concreteKbUpper M) (sqrtMidpointCutoff M) ⊆ H_SQ1 ∧
      p2TailSet (concreteKbUpper M) (sqrtMidpointCutoff M) ⊆ H_P2 ∧
      H_SQ1.card ≤ Q_SQ1 ∧
      H_P2.card ≤ Q_P2 ∧
      C_SQ1 ≤ (rejectedByLowerComposite M H_SQ1).card ∧
      C_P2 ≤ (rejectedByLowerComposite M H_P2).card ∧
      L ≤ (screenedConcreteKbRadii M).card ∧
      Q_SQ1 + Q_P2 + 1 ≤ L + C_SQ1 + C_P2) ↔
    1 ≤ (primeSurvivorSet (concreteKbUpper M) (sqrtMidpointCutoff M)).card := by
  constructor
  · rintro ⟨H_SQ1, H_P2, Q_SQ1, Q_P2, C_SQ1, C_P2, L,
            h_cov1, h_cov2, hQ1, hQ2, hC1, hC2, hL, h_star⟩
    exact ((routeB_species_credit_inequality_to_binary_goldbach_wr2
      hM1 h_cov1 h_cov2).2.2 Q_SQ1 Q_P2 C_SQ1 C_P2 L hQ1 hQ2 hC1 hC2 hL h_star).1
  · intro h_pos
    have h_raw := rawSq1_and_rawP2_retained_eq_exact_tails_and_zero_excess_loss M
    have h_part4 :
        (screenedConcreteKbRadii M).card =
          (primeSurvivorSet (concreteKbUpper M) (sqrtMidpointCutoff M)).card +
            (sq1TailSet (concreteKbUpper M) (sqrtMidpointCutoff M)).card +
            (p2TailSet (concreteKbUpper M) (sqrtMidpointCutoff M)).card +
            (higherSpeciesTailSet (concreteKbUpper M) (sqrtMidpointCutoff M)).card := by
      rw [(screenedConcreteKb_image_and_card_eq M).2]
      exact (exact_species_three_way_composite_tail_partition
        (concreteKbUpper M) (sqrtMidpointCutoff M)).2
    have h_h3_zero :
        (higherSpeciesTailSet (concreteKbUpper M) (sqrtMidpointCutoff M)).card = 0 :=
      (screenedConcreteKbUpper_exact_sq1_p2_balance hM1).1
    have h_real :=
      zero_loss_neutral_absorber_routeB_realization
        h_part4 h_h3_zero h_raw.2.2.2.2.1 h_raw.2.2.2.2.2 rfl
    exact ⟨rawSq1Catalog M,
           rawP2Catalog M,
           (rawSq1Catalog M).card,
           (rawP2Catalog M).card,
           (rejectedByLowerComposite M (rawSq1Catalog M)).card,
           (rejectedByLowerComposite M (rawP2Catalog M)).card,
           (screenedConcreteKbRadii M).card,
           h_raw.2.2.1,
           h_raw.2.2.2.1,
           Nat.le_refl _,
           Nat.le_refl _,
           Nat.le_refl _,
           Nat.le_refl _,
           Nat.le_refl _,
           h_real.2.2.2.2.mp h_pos⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.retainedByLowerPrime_rawUpperInterval_eq_concreteKbUpper
#print axioms WuPaper.ESZerosBridge.rawSq1_and_rawP2_retained_eq_exact_tails_and_zero_excess_loss
#print axioms WuPaper.ESZerosBridge.rejectedByLowerComposite_eq_sum_rejectionByMinFacFiber
#print axioms WuPaper.ESZerosBridge.step218_varying_gpf_joint_translation_injective
#print axioms WuPaper.ESZerosBridge.routeB_loss_accounting_identity
#print axioms WuPaper.ESZerosBridge.zero_loss_neutral_absorber_routeB_realization
#print axioms WuPaper.ESZerosBridge.routeB_producer_iff_screened_prime_survivor_pos_wr2
