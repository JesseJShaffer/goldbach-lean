import WR2Step223GlobalLowTargetDeduplicationAndTargetDivisorShield

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step225PureCosetOuterConeSubTwoQBlockAndZeroSumCollapse.lean — Pure-Coset Outer Cayley Cone (`Step203`/`Step205`), Sub-`2r` Multi-Block Cover (`Step208`) & Zero-Sum Frontier Collapse (`WR2` Track 1)

1. **Section 1 — Pure-Coset Outer Cayley Cone Unconditional Primality Discharge (`Step203` & `Step205`):**
   - `isPrimeNat_of_rough_below_sq_native`: proves in pure `Init` arithmetic that any `2 ≤ n < q_up * q_up`
     with `∀ d, 2 ≤ d → d < q_up → 1 ≤ n % d` satisfies `IsPrimeNat n` and `Nat.Prime n`.
   - `pureCosetOuterConeRadii M q_up` & `bilateralOuterConeRadii M q_up`: proves unconditionally
     that every lower slot `M - R` is prime, and every bilateral outer-cone radius `R` yields a
     certified Binary Goldbach pair `(M - R) + (M + R) = 2 * M` with zero `h_*` hypotheses.
2. **Section 2 — Quotient Wave Shear Sub-`2r` Multi-Block Cover (`Step208`):**
   - Formalizes `subTwoQBlock I r k` and `subTwoQBlockIndices I r`, proving unconditionally
     that `I = (subTwoQBlockIndices I r).biUnion (subTwoQBlock I r)`, blocks are pairwise
     disjoint, and every block has diameter `b0 - a0 < 2 * max r 1`.
3. **Section 3 — Unconditional Zero-Sum Collapse at `m_sieve = q_E`:**
   - Proves that for `IsFirstMissingOddPrime N q_E` and `N < q_E * (q_E + 2) + 2`,
     `∑ r ∈ wr2PinchedOddPrimes p_next N, (wr2TargetSievedFiber N r q_E).card = 0`,
     collapsing `(wr2CutlineSemiprimePrimes N).card ≤ q_E` unconditionally!
-/

/-!
## Section 1: Pure-Coset Outer Cayley Cone Unconditional Primality Discharge (`Step203` & `Step205`)
-/

/-- Pure native proof that if `d ∣ n` and `0 < d`, then `n % d = 0` and `d * (n / d) = n`. -/
theorem mod_eq_zero_and_mul_div_of_dvd_native
    {d n : ℕ} (hd_pos : 0 < d) (h_dvd : d ∣ n) :
    n % d = 0 ∧ d * (n / d) = n := by
  obtain ⟨k, hk⟩ := h_dvd
  have h_div_mod : d * (n / d) + n % d = d * k := by
    rw [← hk]
    exact Nat.div_add_mod n d
  have h_lt : n % d < d := Nat.mod_lt n hd_pos
  have h_rem0 : n % d = 0 := eq_zero_of_mul_add_eq_mul_of_lt h_lt h_div_mod
  exact ⟨h_rem0, by omega⟩

/-- **Theorem 1.1 (`isPrimeNat_of_rough_below_sq_native`):**
    Pure Native `Step203` Outer-Cone Primality Theorem:
    Every integer `n` satisfying `2 ≤ n`, `n < q_up * q_up`, and `q_up`-roughness
    (`∀ d, 2 ≤ d → d < q_up → 1 ≤ n % d`) is unconditionally prime (`IsPrimeNat n ∧ Nat.Prime n`)! -/
theorem isPrimeNat_of_rough_below_sq_native
    {n q_up : ℕ} (hn2 : 2 ≤ n) (h_lt_sq : n < q_up * q_up)
    (h_rough : ∀ d : ℕ, 2 ≤ d → d < q_up → 1 ≤ n % d) :
    IsPrimeNat n ∧ Nat.Prime n := by
  have h_isp : IsPrimeNat n := by
    refine ⟨hn2, ?_⟩
    intro d hd_dvd
    obtain ⟨k, hk⟩ := hd_dvd
    if hd0 : d = 0 then
      rw [hd0, Nat.zero_mul] at hk
      omega
    else if hd1 : d = 1 then
      exact Or.inl hd1
    else if hdn : d = n then
      exact Or.inr hdn
    else
      have hd_pos : 0 < d := by omega
      have hd2 : 2 ≤ d := by omega
      have hk_ne0 : k ≠ 0 := by
        intro hk0
        rw [hk0, Nat.mul_zero] at hk
        omega
      have hk_ne1 : k ≠ 1 := by
        intro hk1
        rw [hk1, Nat.mul_one] at hk
        omega
      have hk2 : 2 ≤ k := by omega
      have hk_pos : 0 < k := by omega
      have hd_dvd_n : d ∣ n := ⟨k, hk⟩
      have hk_dvd_n : k ∣ n := ⟨d, by rw [Nat.mul_comm k d]; exact hk⟩
      have hd_mod0 : n % d = 0 := (mod_eq_zero_and_mul_div_of_dvd_native hd_pos hd_dvd_n).1
      have hk_mod0 : n % k = 0 := (mod_eq_zero_and_mul_div_of_dvd_native hk_pos hk_dvd_n).1
      have hd_ge_qup : q_up ≤ d := by
        match Nat.lt_or_ge d q_up with
        | Or.inr hge => exact hge
        | Or.inl hlt =>
          have h_pos_rem := h_rough d hd2 hlt
          omega
      have hk_ge_qup : q_up ≤ k := by
        match Nat.lt_or_ge k q_up with
        | Or.inr hge => exact hge
        | Or.inl hlt =>
          have h_pos_rem := h_rough k hk2 hlt
          omega
      have h_sq_le : q_up * q_up ≤ n := by
        rw [hk]
        exact Nat.mul_le_mul hd_ge_qup hk_ge_qup
      exact False.elim (Nat.lt_irrefl n (Nat.lt_of_lt_of_le h_lt_sq h_sq_le))
  exact ⟨h_isp, isPrimeNat_to_natPrime h_isp⟩

/-- Pure-Coset Outer Cayley Cone Radius Carrier (`Step203`):
    selects radii `R ∈ [1, M - 3]` using ONLY the outer-cone ceiling `M - R < q_up * q_up`
    and modular `q_up`-roughness (`∀ d ∈ range q_up, 2 ≤ d → 1 ≤ (M - R) % d`). -/
def pureCosetOuterConeRadii (M q_up : ℕ) : Finset ℕ :=
  (range (M - 2)).filter (fun R : ℕ =>
    1 ≤ R ∧
    (M - R) % 2 = 1 ∧
    M - R < q_up * q_up ∧
    ∀ d ∈ range q_up, 2 ≤ d → 1 ≤ (M - R) % d)

/-- Bilateral Pure-Coset Outer Cayley Cone Radius Carrier (`Step205`):
    both `M - R` and `M + R` lie below `q_up * q_up` and are `q_up`-rough. -/
def bilateralOuterConeRadii (M q_up : ℕ) : Finset ℕ :=
  (pureCosetOuterConeRadii M q_up).filter (fun R : ℕ =>
    M + R < q_up * q_up ∧
    ∀ d ∈ range q_up, 2 ≤ d → 1 ≤ (M + R) % d)

/-- **Theorem 1.2 (`pureCosetOuterCone_unconditional_primality_and_goldbach_discharge`):**
    Discharges `Step203` and `Step205` unconditionally with zero `h_*` hypotheses:
    1. Every `R ∈ pureCosetOuterConeRadii M q_up` has `IsPrimeNat (M - R) ∧ Nat.Prime (M - R)`,
    2. Every `R ∈ bilateralOuterConeRadii M q_up` has `Nat.Prime (M - R) ∧ Nat.Prime (M + R)`
       and `(M - R) + (M + R) = 2 * M`, and
    3. Whenever `0 < (bilateralOuterConeRadii M q_up).card`, `2 * M` is unconditionally a
       Binary Goldbach sum `2 * M = p + q` paired with its Factorial Lighthouse next prime! -/
theorem pureCosetOuterCone_unconditional_primality_and_goldbach_discharge (M q_up : ℕ) :
    (∀ R ∈ pureCosetOuterConeRadii M q_up,
      IsPrimeNat (M - R) ∧ Nat.Prime (M - R)) ∧
    (∀ R ∈ bilateralOuterConeRadii M q_up,
      Nat.Prime (M - R) ∧ Nat.Prime (M + R) ∧ (M - R) + (M + R) = 2 * M) ∧
    (0 < (bilateralOuterConeRadii M q_up).card →
      ∃ p q p_next' : ℕ,
        Nat.Prime p ∧ Nat.Prime q ∧ 2 * M = p + q ∧
        p < p_next' ∧ Nat.Prime p_next' ∧ IsPrimeNat p_next') := by
  have h_low :
      ∀ R ∈ pureCosetOuterConeRadii M q_up,
        IsPrimeNat (M - R) ∧ Nat.Prime (M - R) := by
    intro R hR
    rw [pureCosetOuterConeRadii, mem_filter, mem_range] at hR
    obtain ⟨hR_lt, _, _, h_lt_sq, h_rough⟩ := hR
    have hMR2 : 2 ≤ M - R := by omega
    exact isPrimeNat_of_rough_below_sq_native hMR2 h_lt_sq
      (fun d hd2 hd_lt => h_rough d (mem_range.mpr hd_lt) hd2)
  have h_bil :
      ∀ R ∈ bilateralOuterConeRadii M q_up,
        Nat.Prime (M - R) ∧ Nat.Prime (M + R) ∧ (M - R) + (M + R) = 2 * M := by
    intro R hR
    rw [bilateralOuterConeRadii, mem_filter] at hR
    obtain ⟨hR_pure, h_up_sq, h_up_rough⟩ := hR
    have h_low_p := (h_low R hR_pure).2
    rw [pureCosetOuterConeRadii, mem_filter, mem_range] at hR_pure
    have hMR_pos : 2 ≤ M + R := by omega
    have h_up_p := (isPrimeNat_of_rough_below_sq_native hMR_pos h_up_sq
      (fun d hd2 hd_lt => h_up_rough d (mem_range.mpr hd_lt) hd2)).2
    exact ⟨h_low_p, h_up_p, by omega⟩
  refine ⟨h_low, h_bil, ?_⟩
  intro h_pos
  obtain ⟨R, hR⟩ := card_pos.mp h_pos
  have h_pair := h_bil R hR
  obtain ⟨p_next', hp_lt, hp_nat, hp_isp⟩ := hasNextPrimeMathlib_unconditional (M - R)
  exact ⟨M - R, M + R, p_next', h_pair.1, h_pair.2.1, h_pair.2.2.symm,
    hp_lt, hp_nat, hp_isp⟩

/-!
## Section 2: Quotient Wave Shear Sub-`2r` Multi-Block Cover (`Step208`)
-/

/-- Canonical Quotient Wave Shear sub-`2r` block `J_blk(I, r, k)` (`Step208`):
    elements `q ∈ I` with quotient `q / (2 * max r 1) = k`. -/
def subTwoQBlock (I : Finset ℕ) (r k : ℕ) : Finset ℕ :=
  I.filter (fun q : ℕ => q / (2 * max r 1) = k)

/-- Active Quotient Wave Shear block index set `Blocks(I, r)` (`Step208`). -/
def subTwoQBlockIndices (I : Finset ℕ) (r : ℕ) : Finset ℕ :=
  I.image (fun q : ℕ => q / (2 * max r 1))

/-- Standalone disjointness lemma for distinct Quotient Wave Shear block indices `k₁ ≠ k₂`. -/
theorem subTwoQBlock_disjoint_of_ne (I : Finset ℕ) (r : ℕ) {k₁ k₂ : ℕ} (hne : k₁ ≠ k₂) :
    Disjoint (subTwoQBlock I r k₁) (subTwoQBlock I r k₂) := by
  apply Finset.disjoint_left.mpr
  intro q hq1 hq2
  rw [subTwoQBlock, mem_filter] at hq1 hq2
  have hk1 : q / (2 * max r 1) = k₁ := hq1.2
  have hk2 : q / (2 * max r 1) = k₂ := hq2.2
  omega

/-- **Theorem 2.1 (`subTwoQBlock_unconditional_partition_and_diameter`):**
    Discharges `Step208`'s `h_cov_blk` and sub-`2r` diameter condition unconditionally
    for EVERY `I : Finset ℕ` and `r : ℕ`:
    1. `I = (subTwoQBlockIndices I r).biUnion (subTwoQBlock I r)`,
    2. Distinct block indices `k₁ ≠ k₂` have disjoint blocks,
    3. `I.card = ∑ k ∈ subTwoQBlockIndices I r, (subTwoQBlock I r k).card`, and
    4. Every block has diameter strictly less than `2 * max r 1`:
       `∀ a0 ∈ subTwoQBlock I r k, ∀ b0 ∈ subTwoQBlock I r k, a0 ≤ b0 → b0 - a0 < 2 * max r 1`. -/
theorem subTwoQBlock_unconditional_partition_and_diameter (I : Finset ℕ) (r : ℕ) :
    I = (subTwoQBlockIndices I r).biUnion (subTwoQBlock I r) ∧
    (↑(subTwoQBlockIndices I r) : Set ℕ).PairwiseDisjoint (subTwoQBlock I r) ∧
    I.card = ∑ k ∈ subTwoQBlockIndices I r, (subTwoQBlock I r k).card ∧
    (∀ k a0 b0 : ℕ,
      a0 ∈ subTwoQBlock I r k →
      b0 ∈ subTwoQBlock I r k →
      a0 ≤ b0 →
      b0 - a0 < 2 * max r 1) := by
  have h_eq : I = (subTwoQBlockIndices I r).biUnion (subTwoQBlock I r) := by
    ext q
    rw [mem_biUnion]
    constructor
    · intro hq
      refine ⟨q / (2 * max r 1), ?_, ?_⟩
      · rw [subTwoQBlockIndices, mem_image]
        exact ⟨q, hq, rfl⟩
      · rw [subTwoQBlock, mem_filter]
        exact ⟨hq, rfl⟩
    · intro hbi
      obtain ⟨_, _, hq_blk⟩ := hbi
      rw [subTwoQBlock, mem_filter] at hq_blk
      exact hq_blk.1
  have h_disj :
      (↑(subTwoQBlockIndices I r) : Set ℕ).PairwiseDisjoint (subTwoQBlock I r) := by
    intro k₁ _ k₂ _ hne
    exact subTwoQBlock_disjoint_of_ne I r hne
  have h_card : I.card = ∑ k ∈ subTwoQBlockIndices I r, (subTwoQBlock I r k).card := by
    conv_lhs => rw [h_eq]
    exact card_biUnion h_disj
  refine ⟨h_eq, h_disj, h_card, ?_⟩
  intro k a0 b0 ha0 hb0 h_le
  rw [subTwoQBlock, mem_filter] at ha0 hb0
  set D := 2 * max r 1
  have hD_pos : 0 < D := by omega
  have ha_div : D * (a0 / D) + a0 % D = a0 := Nat.div_add_mod a0 D
  have hb_div : D * (b0 / D) + b0 % D = b0 := Nat.div_add_mod b0 D
  have ha_lt : a0 % D < D := Nat.mod_lt a0 hD_pos
  have hb_lt : b0 % D < D := Nat.mod_lt b0 hD_pos
  rw [ha0.2] at ha_div
  rw [hb0.2] at hb_div
  omega

/-!
## Section 3: Unconditional Zero-Sum Collapse at `m_sieve = q_E` on `WR2`
-/

/-- Explicit native extraction of `r + 2 ≤ q` and `r * q + 2 ≤ N` from
    `q ∈ wr2ShearContractedFiber N r` without exposing large exponents to `omega`. -/
theorem wr2ShearContractedFiber_r2_le_q_and_rq_add2_le_N
    {N r q : ℕ} (hq : q ∈ wr2ShearContractedFiber N r) :
    r + 2 ≤ q ∧ r * q + 2 ≤ N := by
  have h_props := wr2ShearContractedFiber_to_hyperbolic_and_sum hq
  have hq_hyp := h_props.1
  have h_sum : r * q + (N - r * q) = N := h_props.2.2.2
  rw [hyperbolicPrimeFiber, mem_filter] at hq_hyp
  have h_r2_le_q : r + 2 ≤ q := hq_hyp.2.2.2.1
  have hp_two : 2 ≤ N - r * q := hq_hyp.2.2.2.2.2.1.1
  have h_add : r * q + 2 ≤ r * q + (N - r * q) := Nat.add_le_add_left hp_two (r * q)
  rw [h_sum] at h_add
  exact ⟨h_r2_le_q, h_add⟩

/-- **Theorem 3.1 (`wr2TargetSievedFiber_eq_empty_above_first_missing_prime`):**
    For any `r ≥ q_E` and any target `N < q_E * (q_E + 2) + 2`,
    `(wr2TargetSievedFiber N r m_sieve).card = 0` because every element `q` in the fiber
    satisfies `q_E * (q_E + 2) + 2 ≤ r * q + 2 ≤ N`. -/
theorem wr2TargetSievedFiber_eq_empty_above_first_missing_prime
    {N q_E r m_sieve : ℕ} (hr_ge : q_E ≤ r) (hN_lt : N < q_E * (q_E + 2) + 2) :
    (wr2TargetSievedFiber N r m_sieve).card = 0 := by
  match Nat.eq_zero_or_pos (wr2TargetSievedFiber N r m_sieve).card with
  | Or.inl h0 => exact h0
  | Or.inr hpos =>
    obtain ⟨q, hq⟩ := card_pos.mp hpos
    rw [wr2TargetSievedFiber, mem_filter] at hq
    have h_bounds := wr2ShearContractedFiber_r2_le_q_and_rq_add2_le_N hq.1
    have h_qE2_le_q : q_E + 2 ≤ q :=
      Nat.le_trans (Nat.add_le_add_right hr_ge 2) h_bounds.1
    have h_mul : q_E * (q_E + 2) ≤ r * q := Nat.mul_le_mul hr_ge h_qE2_le_q
    have h_ge : q_E * (q_E + 2) + 2 ≤ N :=
      Nat.le_trans (Nat.add_le_add_right h_mul 2) h_bounds.2
    exact False.elim (Nat.lt_irrefl N (Nat.lt_of_lt_of_le hN_lt h_ge))

/-- **Theorem 3.2 (`sum_wr2TargetSievedFibers_eq_zero_of_first_missing_prime_frontier`):**
    Unconditional Zero-Sum Collapse on `WR2`:
    Whenever `IsFirstMissingOddPrime N q_E` and `N < q_E * (q_E + 2) + 2`, EVERY fiber
    `r ∈ wr2PinchedOddPrimes p_next N` (both `r < q_E` and `r ≥ q_E`) vanishes at
    `m_sieve = q_E`, so the entire 1D fiber sum equals `0` and
    `(wr2CutlineSemiprimePrimes N).card ≤ q_E` unconditionally! -/
theorem sum_wr2TargetSievedFibers_eq_zero_of_first_missing_prime_frontier
    {p_next N q_E : ℕ} (hEven : N % 2 = 0) (hN_le : N ≤ (p_next + 1) ^ 2)
    (hqE : IsFirstMissingOddPrime N q_E) (hN_lt : N < q_E * (q_E + 2) + 2) :
    (∑ r ∈ wr2PinchedOddPrimes p_next N, (wr2TargetSievedFiber N r q_E).card) = 0 ∧
    (wr2CutlineSemiprimePrimes N).card ≤ q_E := by
  have h_sum_zero :
      (∑ r ∈ wr2PinchedOddPrimes p_next N, (wr2TargetSievedFiber N r q_E).card) = 0 := by
    apply sum_eq_zero
    intro r hr_pinch
    rw [wr2PinchedOddPrimes, mem_filter, oddPrimesBelow, mem_filter] at hr_pinch
    have hr_isp : IsPrimeNat r := hr_pinch.1.2.1
    have hr_odd : r % 2 = 1 := hr_pinch.1.2.2
    match Nat.lt_or_ge r q_E with
    | Or.inl hr_lt =>
      exact first_missing_prime_kills_all_lower_wr2_fibers hqE hr_isp hr_odd hr_lt
    | Or.inr hr_ge =>
      exact wr2TargetSievedFiber_eq_empty_above_first_missing_prime hr_ge hN_lt
  have h_cut_le := wr2CutlineSemiprimePrimes_card_le_one_add_odd N
  have h_odd_part := wr2OddCutlineSemiprimePrimes_card_eq_lowTarget_add_targetSieved q_E N
  have h_low_le : (wr2GlobalLowTargetSubfilter q_E N).card ≤ q_E - 1 :=
    (wr2GlobalLowTargetSubfilter_card_le q_E N).2.2
  have h_ts_sub :=
    wr2GlobalTargetSievedSubfilter_subset_image_biUnion (m_sieve := q_E) hEven hN_le
  have h_ts_le := Nat.le_trans (card_le_card h_ts_sub) card_image_le
  rw [card_biUnion_eq_sum_wr2TargetSievedFibers (wr2PinchedOddPrimes p_next N) N q_E,
      h_sum_zero] at h_ts_le
  have hqE_ge2 : 2 ≤ q_E := hqE.1.1
  exact ⟨h_sum_zero, by omega⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.isPrimeNat_of_rough_below_sq_native
#print axioms WuPaper.ESZerosBridge.pureCosetOuterCone_unconditional_primality_and_goldbach_discharge
#print axioms WuPaper.ESZerosBridge.subTwoQBlock_unconditional_partition_and_diameter
#print axioms WuPaper.ESZerosBridge.sum_wr2TargetSievedFibers_eq_zero_of_first_missing_prime_frontier
