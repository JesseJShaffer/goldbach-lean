import WR2Step221WR2ExactSpeciesLowTargetPartitionAndFullFiberBound

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step223GlobalLowTargetDeduplicationAndTargetDivisorShield.lean — Global Low-Target Deduplication, Target-Divisor Shield & First-Missing-Prime Pincer (`WR2` Track 1)

Implements the `WR2Step223` Handoff Specification on the `WR2ClassicalCertificate` (`4469, 5000`)
stack:

1. **Section 1 — Pure Native Divisibility & Target-Divisor Shield (`r ∣ N → N - r * q = r`):**
   - `mod_eq_zero_of_add_eq_of_mod_eq_zero_native`: proves `r * q + p = N → N % r = 0 → p % r = 0 ∧ r ∣ p`
     via `mul_add_mod_self_left_native` (`WR2Step217`) and `Nat.div_add_mod`.
   - `tight_fiber_dvd_target_forces_p_eq_r_and_q_eq`: proves that if `IsPrimeNat r`, `N % r = 0`,
     and `q ∈ wr2ShearContractedFiber N r`, then `N - r * q = r`, `q = (N - r) / r`,
     `nativeOmegaCofactorSpecies r = 2`, and connects `r` to `predictedNextPrime r`.
   - `targetSieved_fiber_eq_empty_of_dvd_target`: proves that for `N % r = 0` and `r ≤ m_sieve`,
     `(wr2TargetSievedFiber N r m_sieve).card = 0` and `(wr2TargetSievedFloorSubfiber N r m_sieve L).card = 0`.
2. **Section 2 — Global Low-Target Deduplication & Exact 1D Disjoint Fiber Sum:**
   - Partitions `wr2OddCutlineSemiprimePrimes N` globally at `p ≤ m_sieve` vs. `m_sieve < p`
     before projecting to `(r, q)`, paying `(lowTargetPrimes m_sieve).card ≤ m_sieve - 1` (`≤ 12` for
     `m_sieve = 13`) **once globally** rather than per fiber.
   - Proves pairwise disjointness of `wr2TargetSievedFiberPairs N m_sieve r` across `r` and
     converts the 2D `biUnion` cardinality into the exact 1D sum `∑ r, (wr2TargetSievedFiber N r m_sieve).card`.
3. **Section 3 — First-Missing-Prime (`q_E`) Square-Onset Wave Pincer & Track 1 Master Capstone:**
   - Formalizes `IsFirstMissingOddPrime N q_E`, proves `first_missing_prime_kills_all_lower_wr2_fibers`,
     and proves `first_missing_prime_square_frontier_forces_omega_one_goldbach`.
-/

/-!
## Section 1: Pure Native Divisibility & Target-Divisor Shield (`r ∣ N → N - r * q = r`)
-/

/-- **Lemma 1.1 (`mod_eq_zero_of_add_eq_of_mod_eq_zero_native`):**
    If `r * q + p = N` and `N % r = 0`, then `p % r = 0` and `r ∣ p`. -/
theorem mod_eq_zero_of_add_eq_of_mod_eq_zero_native
    {N r q p : ℕ} (h_sum : r * q + p = N) (hN_mod : N % r = 0) :
    p % r = 0 ∧ r ∣ p := by
  have h_mod : (r * q + p) % r = p % r := mul_add_mod_self_left_native r q p
  rw [h_sum] at h_mod
  have hp_mod : p % r = 0 := by omega
  have hp_div : r * (p / r) + p % r = p := Nat.div_add_mod p r
  refine ⟨hp_mod, ⟨p / r, by omega⟩⟩

/-- **Lemma 1.2 (`prime_eq_of_dvd_of_isPrimeNat`):**
    If `IsPrimeNat r`, `IsPrimeNat p`, and `r ∣ p`, then `p = r`. -/
theorem prime_eq_of_dvd_of_isPrimeNat
    {r p : ℕ} (hr : IsPrimeNat r) (hp : IsPrimeNat p) (h_dvd : r ∣ p) :
    p = r := by
  have hr2 : 2 ≤ r := hr.1
  cases hp.2 r h_dvd with
  | inl hr1 => omega
  | inr hrp => exact hrp.symm

/-- **Theorem 1.3 (`target_divisor_forces_p_eq_r`):**
    Target-Divisor Shield: whenever `N = p + r * q` with `IsPrimeNat p`, `IsPrimeNat r`,
    and `N % r = 0` (`r ∣ N`), `p` is forced to equal `r` (`p = r`). -/
theorem target_divisor_forces_p_eq_r
    {N p r q : ℕ} (hp : IsPrimeNat p) (hr : IsPrimeNat r)
    (hN : N = p + r * q) (hN_mod : N % r = 0) :
    p = r ∧ (r < p → False) := by
  have h_sum : r * q + p = N := by omega
  have h_dvd : r ∣ p := (mod_eq_zero_of_add_eq_of_mod_eq_zero_native h_sum hN_mod).2
  have h_eq : p = r := prime_eq_of_dvd_of_isPrimeNat hr hp h_dvd
  exact ⟨h_eq, fun h_lt => by omega⟩

/-- **Theorem 1.4 (`tight_fiber_dvd_target_forces_p_eq_r_and_q_eq`):**
    If `IsPrimeNat r`, `N % r = 0`, and `q ∈ wr2ShearContractedFiber N r`, then:
    1. `N - r * q = r`,
    2. `q = (N - r) / r` (via `mul_div_cancel_left_native`), and
    3. `nativeOmegaCofactorSpecies r = 2` and `predictedNextPrime r = nextPrimeBoundedAux (r + 1) (factorialNat r + 1)`. -/
theorem tight_fiber_dvd_target_forces_p_eq_r_and_q_eq
    {N r q : ℕ} (hr : IsPrimeNat r) (hN_mod : N % r = 0)
    (hq : q ∈ wr2ShearContractedFiber N r) :
    N - r * q = r ∧
    q = (N - r) / r ∧
    nativeOmegaCofactorSpecies r = 2 ∧
    predictedNextPrime r = nextPrimeBoundedAux (r + 1) (factorialNat r + 1) ∧
    (∃ r_next : ℕ, r < r_next ∧ IsPrimeNat r_next) := by
  have hr2 : 2 ≤ r := hr.1
  have hr_pos : 0 < r := by omega
  have h_props := wr2ShearContractedFiber_to_hyperbolic_and_sum hq
  have hq_hyp := h_props.1
  have h_sum : r * q + (N - r * q) = N := h_props.2.2.2
  rw [hyperbolicPrimeFiber, mem_filter] at hq_hyp
  have hp_isp : IsPrimeNat (N - r * q) := hq_hyp.2.2.2.2.2.1
  have h_dvd : r ∣ (N - r * q) :=
    (mod_eq_zero_of_add_eq_of_mod_eq_zero_native h_sum hN_mod).2
  have hp_eq_r : N - r * q = r := prime_eq_of_dvd_of_isPrimeNat hr hp_isp h_dvd
  have h_rq_eq : N - r = r * q := by omega
  have h_q_eq : q = (N - r) / r := by
    rw [h_rq_eq, mul_div_cancel_left_native hr_pos]
  exact ⟨hp_eq_r, h_q_eq, nativeOmegaCofactorSpecies_eq_two_of_prime hr,
    rfl, hasNextPrimeConnection_unconditional r⟩

/-- **Theorem 1.5 (`targetSieved_fiber_eq_empty_of_dvd_target`):**
    For every prime `r` with `N % r = 0` (`r ∣ N`) and every sieve level `m_sieve` with
    `r ≤ m_sieve`, both `wr2TargetSievedFiber N r m_sieve` and
    `wr2TargetSievedFloorSubfiber N r m_sieve L` have cardinality `0`. -/
theorem targetSieved_fiber_eq_empty_of_dvd_target
    {N r m_sieve L : ℕ} (hr : IsPrimeNat r) (hN_mod : N % r = 0) (hr_le : r ≤ m_sieve) :
    (wr2TargetSievedFiber N r m_sieve).card = 0 ∧
    (wr2TargetSievedFloorSubfiber N r m_sieve L).card = 0 := by
  have h_ts_zero : (wr2TargetSievedFiber N r m_sieve).card = 0 := by
    match Nat.eq_zero_or_pos (wr2TargetSievedFiber N r m_sieve).card with
    | Or.inl h0 => exact h0
    | Or.inr hpos =>
      obtain ⟨q, hq⟩ := card_pos.mp hpos
      rw [wr2TargetSievedFiber, mem_filter] at hq
      have hp_eq_r := (tight_fiber_dvd_target_forces_p_eq_r_and_q_eq hr hN_mod hq.1).1
      have h_gt : m_sieve < N - r * q := hq.2
      omega
  have h_sub := wr2TargetSievedFloorSubfiber_subset_targetSieved N r m_sieve L
  have h_fl_le : (wr2TargetSievedFloorSubfiber N r m_sieve L).card ≤ 0 := by
    rw [← h_ts_zero]
    exact card_le_card h_sub
  omega

/-- Target-coprime (`1 ≤ N % r`) pinched odd prime index set on `WR2`. -/
def wr2NonDividingPinchedOddPrimes (p_next N : ℕ) : Finset ℕ :=
  (wr2PinchedOddPrimes p_next N).filter (fun r : ℕ => 1 ≤ N % r)

/-!
## Section 2: Global Low-Target Deduplication & Exact 1D Disjoint Fiber Sum on `WR2`
-/

/-- Global Low-Target subset of `wr2OddCutlineSemiprimePrimes N` (`p ≤ m_sieve`). -/
def wr2GlobalLowTargetSubfilter (m_sieve N : ℕ) : Finset ℕ :=
  (wr2OddCutlineSemiprimePrimes N).filter (fun p : ℕ => p ≤ m_sieve)

/-- Global Target-Sieved subset of `wr2OddCutlineSemiprimePrimes N` (`m_sieve < p`). -/
def wr2GlobalTargetSievedSubfilter (m_sieve N : ℕ) : Finset ℕ :=
  (wr2OddCutlineSemiprimePrimes N).filter (fun p : ℕ => m_sieve < p)

theorem disjoint_wr2GlobalLowTarget_targetSieved (m_sieve N : ℕ) :
    Disjoint (wr2GlobalLowTargetSubfilter m_sieve N)
             (wr2GlobalTargetSievedSubfilter m_sieve N) := by
  rw [Finset.disjoint_left]
  intro p hlow hts
  rw [wr2GlobalLowTargetSubfilter, mem_filter] at hlow
  rw [wr2GlobalTargetSievedSubfilter, mem_filter] at hts
  have h1 : p ≤ m_sieve := hlow.2
  have h2 : m_sieve < p := hts.2
  omega

theorem wr2OddCutlineSemiprimePrimes_eq_lowTarget_union_targetSieved (m_sieve N : ℕ) :
    wr2OddCutlineSemiprimePrimes N =
      wr2GlobalLowTargetSubfilter m_sieve N ∪ wr2GlobalTargetSievedSubfilter m_sieve N := by
  ext p
  rw [mem_union, wr2GlobalLowTargetSubfilter, wr2GlobalTargetSievedSubfilter, mem_filter, mem_filter]
  constructor
  · intro hp
    match Nat.lt_or_ge m_sieve p with
    | Or.inl hgt => exact Or.inr ⟨hp, hgt⟩
    | Or.inr hle => exact Or.inl ⟨hp, hle⟩
  · intro hor
    cases hor with
    | inl hlow => exact hlow.1
    | inr hts => exact hts.1

/-- Exact additive cardinality partition of `wr2OddCutlineSemiprimePrimes N` at `m_sieve`. -/
theorem wr2OddCutlineSemiprimePrimes_card_eq_lowTarget_add_targetSieved (m_sieve N : ℕ) :
    (wr2OddCutlineSemiprimePrimes N).card =
      (wr2GlobalLowTargetSubfilter m_sieve N).card +
      (wr2GlobalTargetSievedSubfilter m_sieve N).card := by
  conv_lhs => rw [wr2OddCutlineSemiprimePrimes_eq_lowTarget_union_targetSieved m_sieve N]
  exact card_union_of_disjoint (disjoint_wr2GlobalLowTarget_targetSieved m_sieve N)

/-- **Theorem 2.1 (`wr2GlobalLowTargetSubfilter_card_le`):**
    Global Low-Target Deduplication on `WR2`: across ALL fibers `r` combined,
    `wr2GlobalLowTargetSubfilter m_sieve N ⊆ lowTargetPrimes m_sieve`, so its cardinality is
    at most `(lowTargetPrimes m_sieve).card ≤ m_sieve - 1` (`≤ 12` for `m_sieve = 13`). -/
theorem wr2GlobalLowTargetSubfilter_card_le (m_sieve N : ℕ) :
    wr2GlobalLowTargetSubfilter m_sieve N ⊆ lowTargetPrimes m_sieve ∧
    (wr2GlobalLowTargetSubfilter m_sieve N).card ≤ (lowTargetPrimes m_sieve).card ∧
    (wr2GlobalLowTargetSubfilter m_sieve N).card ≤ m_sieve - 1 := by
  have h_sub : wr2GlobalLowTargetSubfilter m_sieve N ⊆ lowTargetPrimes m_sieve := by
    intro p hp
    rw [wr2GlobalLowTargetSubfilter, mem_filter, wr2OddCutlineSemiprimePrimes, mem_filter,
        wr2CutlineSemiprimePrimes, mem_filter] at hp
    have hp_isp : IsPrimeNat p := natPrime_to_isPrimeNat hp.1.1.2.1
    have hp_le : p ≤ m_sieve := hp.2
    rw [lowTargetPrimes, mem_filter, mem_range]
    exact ⟨by omega, hp_isp⟩
  have h_c1 := card_le_card h_sub
  have h_c2 := Nat.le_trans h_c1 (lowTargetPrimes_card_le_sub_one m_sieve)
  exact ⟨h_sub, h_c1, h_c2⟩

/-- 2D fiber slice `{(r, q) | q ∈ wr2TargetSievedFiber N r m_sieve}`. -/
def wr2TargetSievedFiberPairs (N m_sieve r : ℕ) : Finset (ℕ × ℕ) :=
  (wr2TargetSievedFiber N r m_sieve).image (fun q : ℕ => (r, q))

/-- Cardinality of `wr2TargetSievedFiberPairs N m_sieve r` equals the 1D fiber cardinality. -/
theorem wr2TargetSievedFiberPairs_card_eq (N m_sieve r : ℕ) :
    (wr2TargetSievedFiberPairs N m_sieve r).card =
      (wr2TargetSievedFiber N r m_sieve).card := by
  have h1 :
      (wr2TargetSievedFiberPairs N m_sieve r).card ≤
        (wr2TargetSievedFiber N r m_sieve).card := card_image_le
  have h_sub :
      wr2TargetSievedFiber N r m_sieve ⊆
        (wr2TargetSievedFiberPairs N m_sieve r).image Prod.snd := by
    intro q hq
    rw [mem_image]
    refine ⟨(r, q), ?_, rfl⟩
    rw [wr2TargetSievedFiberPairs, mem_image]
    exact ⟨q, hq, rfl⟩
  have h2 := Nat.le_trans (card_le_card h_sub) card_image_le
  exact Nat.le_antisymm h1 h2

/-- Disjointness of `wr2TargetSievedFiberPairs N m_sieve r` across distinct primes `r₁ ≠ r₂`. -/
theorem wr2TargetSievedFiberPairs_disjoint_of_ne
    {N m_sieve r₁ r₂ : ℕ} (hne : r₁ ≠ r₂) :
    Disjoint (wr2TargetSievedFiberPairs N m_sieve r₁)
             (wr2TargetSievedFiberPairs N m_sieve r₂) := by
  rw [Finset.disjoint_left]
  intro pair hp1 hp2
  rw [wr2TargetSievedFiberPairs, mem_image] at hp1 hp2
  obtain ⟨q₁, _, h_eq1⟩ := hp1
  obtain ⟨q₂, _, h_eq2⟩ := hp2
  have hr1 : pair.1 = r₁ := by rw [← h_eq1]
  have hr2 : pair.1 = r₂ := by rw [← h_eq2]
  omega

theorem pairwiseDisjoint_wr2TargetSievedFiberPairs (S : Finset ℕ) (N m_sieve : ℕ) :
    (↑S : Set ℕ).PairwiseDisjoint (wr2TargetSievedFiberPairs N m_sieve) := by
  intro r₁ _ r₂ _ hne
  exact wr2TargetSievedFiberPairs_disjoint_of_ne hne

/-- **Theorem 2.2 (`card_biUnion_eq_sum_wr2TargetSievedFibers`):**
    Exact 1D Fiber Sum Identity: for any index set `S : Finset ℕ`, the cardinality of
    `S.biUnion (wr2TargetSievedFiberPairs N m_sieve)` equals the exact 1D sum
    `∑ r ∈ S, (wr2TargetSievedFiber N r m_sieve).card`. -/
theorem card_biUnion_eq_sum_wr2TargetSievedFibers (S : Finset ℕ) (N m_sieve : ℕ) :
    (S.biUnion (wr2TargetSievedFiberPairs N m_sieve)).card =
      ∑ r ∈ S, (wr2TargetSievedFiber N r m_sieve).card := by
  rw [card_biUnion (pairwiseDisjoint_wr2TargetSievedFiberPairs S N m_sieve)]
  apply sum_congr rfl
  intro r _
  exact wr2TargetSievedFiberPairs_card_eq N m_sieve r

/-- Reconstruction map `(r, q) ↦ N - r * q`. -/
def wr2ReconstructPrimeFromFactorPair (N : ℕ) (rq : ℕ × ℕ) : ℕ :=
  N - rq.1 * rq.2

/-- **Theorem 2.3 (`wr2GlobalTargetSievedSubfilter_subset_image_biUnion`):**
    Across any wave segment `N ≤ (p_next + 1) ^ 2` with `N % 2 = 0`, every prime
    `p ∈ wr2GlobalTargetSievedSubfilter m_sieve N` injects via `wr2ReconstructPrimeFromFactorPair N`
    into `(wr2PinchedOddPrimes p_next N).biUnion (wr2TargetSievedFiberPairs N m_sieve)`. -/
theorem wr2GlobalTargetSievedSubfilter_subset_image_biUnion
    {p_next m_sieve N : ℕ} (hEven : N % 2 = 0) (hN_le : N ≤ (p_next + 1) ^ 2) :
    wr2GlobalTargetSievedSubfilter m_sieve N ⊆
      ((wr2PinchedOddPrimes p_next N).biUnion (wr2TargetSievedFiberPairs N m_sieve)).image
        (wr2ReconstructPrimeFromFactorPair N) := by
  intro p hp
  rw [wr2GlobalTargetSievedSubfilter, mem_filter] at hp
  obtain ⟨hp_odd_sub, hm_lt_p⟩ := hp
  have hp_in_img :
      p ∈ (wr2TightChiralHalfChordBox N).image (reconstructPrimeFromHalfChordWR2 N) :=
    wr2OddCutlineSemiprimePrimes_subset_image_tight_box hEven hp_odd_sub
  rw [mem_image] at hp_in_img
  obtain ⟨pair, hpair_tight, h_p_eq⟩ := hp_in_img
  have h_part := wr2TightChiralHalfChordBox_eq_lowPrime_union_waveSieved p_next N
  rw [h_part, mem_union] at hpair_tight
  cases hpair_tight with
  | inr hwave =>
    have h_gt := wave_sieved_half_chord_forces_gt_succ_sq hwave
    omega
  | inl hlow =>
    have h_in_factor :=
      lowPrimeTightChiralBox_subset_image_lowPrimeFactorBox p_next N hlow
    rw [mem_image] at h_in_factor
    obtain ⟨rq, hrq_box, h_pair_eq⟩ := h_in_factor
    rw [lowPrimeFactorBox_eq_biUnion_pinched_shearContractedFibers p_next N,
        mem_biUnion] at hrq_box
    obtain ⟨r, hr_pinch, hrq_shear⟩ := hrq_box
    rw [wr2ShearContractedFiberPairs, mem_image] at hrq_shear
    obtain ⟨q, hq_shear, h_rq_eq⟩ := hrq_shear
    subst h_rq_eq
    have h_props := wr2ShearContractedFiber_to_hyperbolic_and_sum hq_shear
    have hq_hyp := h_props.1
    rw [hyperbolicPrimeFiber, mem_filter] at hq_hyp
    obtain ⟨_, hq_isp, hq_odd, h_r2_le_q, _⟩ := hq_hyp
    have hr_copy := hr_pinch
    rw [wr2PinchedOddPrimes, mem_filter, oddPrimesBelow, mem_filter] at hr_copy
    have hr_odd : r % 2 = 1 := hr_copy.1.2.2
    have h_r_le_q : r ≤ q := by omega
    have h_hc_sq := odd_pair_half_chord_sq_eq h_r_le_q hr_odd hq_odd
    have h_rec_eq :
        reconstructPrimeFromHalfChordWR2 N (factorPairToHalfChord (r, q)) = N - r * q := by
      unfold reconstructPrimeFromHalfChordWR2 factorPairToHalfChord
      dsimp only
      omega
    have h_N_sub_rq_eq_p : N - r * q = p := by
      rw [← h_rec_eq, h_pair_eq, h_p_eq]
    rw [mem_image]
    refine ⟨(r, q), ?_, ?_⟩
    · rw [mem_biUnion]
      refine ⟨r, hr_pinch, ?_⟩
      rw [wr2TargetSievedFiberPairs, mem_image]
      refine ⟨q, ?_, rfl⟩
      rw [wr2TargetSievedFiber, mem_filter]
      rw [h_N_sub_rq_eq_p]
      exact ⟨hq_shear, hm_lt_p⟩
    · unfold wr2ReconstructPrimeFromFactorPair
      exact h_N_sub_rq_eq_p

/-- **Theorem 2.4 (`wr2CutlineSemiprimePrimes_card_le_global_lowTarget_add_targetSieved_sum`):**
    Global Low-Target Deduplication & Exact 1D Sum Bound on `WR2`:
    For every even target `N ≤ (p_next + 1) ^ 2` at `m_sieve = 13`:
    `(wr2CutlineSemiprimePrimes N).card ≤ 13 + ∑ r ∈ wr2PinchedOddPrimes p_next N, (wr2TargetSievedFiber N r 13).card`,
    where every fiber in the sum has ZERO `+ 12` low-target boundary overhead! -/
theorem wr2CutlineSemiprimePrimes_card_le_global_lowTarget_add_targetSieved_sum
    {p_next N : ℕ} (hEven : N % 2 = 0) (hN_le : N ≤ (p_next + 1) ^ 2) :
    (wr2CutlineSemiprimePrimes N).card ≤
      13 + ∑ r ∈ wr2PinchedOddPrimes p_next N, (wr2TargetSievedFiber N r 13).card := by
  have h_cut_le := wr2CutlineSemiprimePrimes_card_le_one_add_odd N
  have h_odd_part := wr2OddCutlineSemiprimePrimes_card_eq_lowTarget_add_targetSieved 13 N
  have h_low_le : (wr2GlobalLowTargetSubfilter 13 N).card ≤ 12 :=
    (wr2GlobalLowTargetSubfilter_card_le 13 N).2.2
  have h_ts_sub :=
    wr2GlobalTargetSievedSubfilter_subset_image_biUnion (m_sieve := 13) hEven hN_le
  have h_ts_le := Nat.le_trans (card_le_card h_ts_sub) card_image_le
  rw [card_biUnion_eq_sum_wr2TargetSievedFibers (wr2PinchedOddPrimes p_next N) N 13] at h_ts_le
  omega

/-!
## Section 3: First-Missing-Prime (`q_E`) Square-Onset Wave Pincer & Track 1 Capstone
-/

/-- Predicate certifying that `q_E` is the First Missing Odd Prime for target `N`. -/
def IsFirstMissingOddPrime (N q_E : ℕ) : Prop :=
  IsPrimeNat q_E ∧
  q_E % 2 = 1 ∧
  1 ≤ N % q_E ∧
  ∀ r : ℕ, IsPrimeNat r → r % 2 = 1 → r < q_E → N % r = 0

/-- Pure native parity dichotomy for `IsPrimeNat p`: every prime is either `2` or odd (`p % 2 = 1`). -/
theorem isPrimeNat_eq_two_or_odd_wr2 {p : ℕ} (hp : IsPrimeNat p) :
    p = 2 ∨ p % 2 = 1 := by
  if hp0 : p % 2 = 0 then
    have h_div : 2 * (p / 2) + p % 2 = p := Nat.div_add_mod p 2
    have h_dvd : 2 ∣ p := ⟨p / 2, by omega⟩
    cases hp.2 2 h_dvd with
    | inl h1 => omega
    | inr h2 => exact Or.inl h2.symm
  else
    exact Or.inr (by omega)

/-- **Theorem 3.1 (`first_missing_prime_kills_all_lower_wr2_fibers`):**
    If `IsFirstMissingOddPrime N q_E`, then for EVERY odd prime `r < q_E`,
    `(wr2TargetSievedFiber N r q_E).card = 0`. -/
theorem first_missing_prime_kills_all_lower_wr2_fibers
    {N q_E r : ℕ} (hqE : IsFirstMissingOddPrime N q_E)
    (hr : IsPrimeNat r) (hr_odd : r % 2 = 1) (hr_lt : r < q_E) :
    (wr2TargetSievedFiber N r q_E).card = 0 := by
  have hN_mod : N % r = 0 := hqE.2.2.2 r hr hr_odd hr_lt
  have hr_le : r ≤ q_E := Nat.le_of_lt hr_lt
  exact (targetSieved_fiber_eq_empty_of_dvd_target (L := 0) hr hN_mod hr_le).1

/-- **Theorem 3.2 (`first_missing_prime_square_frontier_forces_omega_one_goldbach`):**
    First-Missing-Prime `q_E(q_E + 2)` Square-Onset Wave Pincer:
    For any even `N` (`N % 2 = 0`), `IsFirstMissingOddPrime N q_E`, and any pinched
    representation `N = p + r * q` (`a + (d + 1) = b`, `r ^ b ≤ q ^ a`) in the frontier
    window `q_E < p` and `N < p + q_E * (q_E + 2)`, all `r < q_E` vanish via the
    Target-Divisor Shield and all `r ≥ q_E` vanish via `q_E * (q_E + 2) ≤ r * q`,
    forcing `nativeOmegaCofactorSpecies r = 1` (`r = 1`, `N = p + q`) unconditionally! -/
theorem first_missing_prime_square_frontier_forces_omega_one_goldbach
    {N q_E p r q a d b : ℕ}
    (hEven : N % 2 = 0)
    (hqE : IsFirstMissingOddPrime N q_E)
    (hp : IsPrimeNat p)
    (hr_or : r = 1 ∨ IsPrimeNat r)
    (hq : IsPrimeNat q)
    (hN_eq : N = p + r * q)
    (h_exp : a + (d + 1) = b)
    (hpow : r ^ b ≤ q ^ a)
    (hp_gt_qE : q_E < p)
    (h_window : N < p + q_E * (q_E + 2)) :
    nativeOmegaCofactorSpecies r = 1 ∧
    r = 1 ∧
    N = p + q ∧
    predictedNextPrime p = nextPrimeBoundedAux (p + 1) (factorialNat p + 1) ∧
    predictedNextPrime q = nextPrimeBoundedAux (q + 1) (factorialNat q + 1) ∧
    (∃ p_next : ℕ, p < p_next ∧ Nat.Prime p_next ∧ IsPrimeNat p_next) ∧
    (∃ q_next : ℕ, q < q_next ∧ Nat.Prime q_next ∧ IsPrimeNat q_next) := by
  cases hr_or with
  | inl hr1 =>
    rw [hr1, Nat.one_mul] at hN_eq
    have h_om : nativeOmegaCofactorSpecies 1 = 1 :=
      (nativeOmegaCofactorSpecies_eq_one_iff 1).mpr rfl
    rw [hr1]
    exact ⟨h_om, rfl, hN_eq, rfl, rfl,
      hasNextPrimeMathlib_unconditional p,
      hasNextPrimeMathlib_unconditional q⟩
  | inr hr_prime =>
    have hq_two : 2 ≤ q := hq.1
    have hr_two : 2 ≤ r := hr_prime.1
    have h_cut := universal_pinch_strict_lt_and_cutline N p r q a d b hr_prime hN_eq h_exp hpow
    have h_r_lt_q : r < q := h_cut.1
    have hqE_ge2 : 2 ≤ q_E := hqE.1.1
    have hqE_odd : q_E % 2 = 1 := hqE.2.1
    have hp_ge4 : 4 ≤ p := by omega
    have hp_odd : p % 2 = 1 := by
      rcases isPrimeNat_eq_two_or_odd_wr2 hp with rfl | hp_o
      · omega
      · exact hp_o
    have h_rq_odd : (r * q) % 2 = 1 := by omega
    obtain ⟨hr_odd, hq_odd⟩ := mul_mod_two_eq_one_iff_wr2 h_rq_odd
    have h_r2_le_q : r + 2 ≤ q := by omega
    match Nat.lt_or_ge r q_E with
    | Or.inl hr_lt_qE =>
      have hN_mod_r : N % r = 0 := hqE.2.2.2 r hr_prime hr_odd hr_lt_qE
      have h_p_eq_r := (target_divisor_forces_p_eq_r hp hr_prime hN_eq hN_mod_r).1
      omega
    | Or.inr hr_ge_qE =>
      have hq_ge_qE2 : q_E + 2 ≤ q := Nat.le_trans (Nat.add_le_add_right hr_ge_qE 2) h_r2_le_q
      have h_mul : q_E * (q_E + 2) ≤ r * q := Nat.mul_le_mul hr_ge_qE hq_ge_qE2
      omega

/-- **Master Theorem 3.3 (`wr2_step223_first_missing_prime_and_global_deduplication_capstone`):**
    Track 1 (`WR2` `4469, 5000`) Master Synthesis uniting `classical_lower` (`17401 / 20000 ≤ classicalPart`),
    `one8938` (`0 < (wr2RepresentedPrimes N).card`), Global Low-Target Deduplication,
    the Target-Divisor Shield (`r ∣ N`), the Exact 1D Fiber Sum, and the First-Missing-Prime
    `q_E(q_E + 2)` Square-Onset Wave Pincer. -/
theorem wr2_step223_first_missing_prime_and_global_deduplication_capstone (p_n : ℕ) :
    ((17401 : ℝ) / 20000 ≤ R2Xi.SourceContinuousCount.classicalPart) ∧
    ∃ p_next T : ℕ,
      p_n < p_next ∧
      Nat.Prime p_next ∧
      IsPrimeNat p_next ∧
      512 ≤ T ∧
      ∀ N : ℕ, T ≤ N → N ≤ (p_next + 1) ^ 2 → Even N →
        0 < (wr2RepresentedPrimes N).card ∧
        (∀ r m_sieve : ℕ, IsPrimeNat r → N % r = 0 → r ≤ m_sieve →
          (wr2TargetSievedFiber N r m_sieve).card = 0) ∧
        (wr2CutlineSemiprimePrimes N).card ≤
          13 + ∑ r ∈ wr2PinchedOddPrimes p_next N, (wr2TargetSievedFiber N r 13).card ∧
        (13 + (∑ r ∈ wr2PinchedOddPrimes p_next N, (wr2TargetSievedFiber N r 13).card) <
            (wr2RepresentedPrimes N).card →
          ∃ p q p_next' : ℕ,
            Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧
            p < p_next' ∧ Nat.Prime p_next' ∧ IsPrimeNat p_next') := by
  obtain ⟨p_next, h_pn_lt, hp_nat, hp_isp⟩ := hasNextPrimeMathlib_unconditional p_n
  obtain ⟨hClass, T, hT512, hMaster⟩ := wr2_one8938_unconditional_master_goldbach_bridge
  refine ⟨hClass, p_next, T, h_pn_lt, hp_nat, hp_isp, hT512, ?_⟩
  intro N hNT hN_le hEven
  have hM := hMaster N hNT hEven
  rcases hEven with ⟨k, hk⟩
  have hMod2 : N % 2 = 0 := by omega
  have h_dedup := wr2CutlineSemiprimePrimes_card_le_global_lowTarget_add_targetSieved_sum hMod2 hN_le
  refine ⟨hM.1,
          fun r m_sieve hr hmod hr_le =>
            (targetSieved_fiber_eq_empty_of_dvd_target (L := 0) hr hmod hr_le).1,
          h_dedup, ?_⟩
  intro hSumLt
  have hCutLt : (wr2CutlineSemiprimePrimes N).card < (wr2RepresentedPrimes N).card :=
    Nat.lt_of_le_of_lt h_dedup hSumLt
  obtain ⟨p, q, p_next', hp, hq, hN_eq, hp_lt, hp_next_isp⟩ := hM.2.2 hCutLt
  exact ⟨p, q, p_next', hp, hq, hN_eq, hp_lt, isPrimeNat_to_natPrime hp_next_isp, hp_next_isp⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.mod_eq_zero_of_add_eq_of_mod_eq_zero_native
#print axioms WuPaper.ESZerosBridge.tight_fiber_dvd_target_forces_p_eq_r_and_q_eq
#print axioms WuPaper.ESZerosBridge.targetSieved_fiber_eq_empty_of_dvd_target
#print axioms WuPaper.ESZerosBridge.wr2GlobalLowTargetSubfilter_card_le
#print axioms WuPaper.ESZerosBridge.card_biUnion_eq_sum_wr2TargetSievedFibers
#print axioms WuPaper.ESZerosBridge.wr2CutlineSemiprimePrimes_card_le_global_lowTarget_add_targetSieved_sum
#print axioms WuPaper.ESZerosBridge.first_missing_prime_kills_all_lower_wr2_fibers
#print axioms WuPaper.ESZerosBridge.first_missing_prime_square_frontier_forces_omega_one_goldbach
#print axioms WuPaper.ESZerosBridge.wr2_step223_first_missing_prime_and_global_deduplication_capstone
