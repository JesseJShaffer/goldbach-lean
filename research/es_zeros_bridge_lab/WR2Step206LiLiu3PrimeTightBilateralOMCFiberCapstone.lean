import WR2Step204LiLiuShiftedWindowStrideAndAdmissibleDecomposition

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step206LiLiu3PrimeTightBilateralOMCFiberCapstone.lean — 3-Prime Tightness, Bilateral OMC Exclusion & General-Floor Strides for `D19 N`

Upgrades the Li–Liu `9/19` (`D19 N`) branch to full **3-Prime Tightness** (`IsPrimeNat (N - r * q)`)
and welds Division-Free Bilateral OMC Target-Side Exclusion, Native Next-Prime Generator
Connections, and Arbitrary-Floor Shifted Quotient Strides directly to `Goldbach.one_plus_one_nine_count`.
-/

/-!
## Section 1: Pure Native Euclidean Cancellation, Factor Bounds & Bilateral OMC Exclusion
-/

/-- Pure native additive-subtractive identity in isolated context: `a ≤ b - 2 → a + (b - a) = b`. -/
theorem add_sub_cancel_of_le_sub2_liliu {a b : ℕ} (h : a ≤ b - 2) :
    a + (b - a) = b := by
  omega

/-- Explicit native bound proving that if `2 ≤ q` and `r * q ≤ N`, then
    `r * 2 ≤ r * q`, `r ≤ N`, and `r < N + 1`. -/
theorem factor_lt_succ_of_mul_le_native
    {r q N : ℕ} (hq2 : 2 ≤ q) (h_rq_le_N : r * q ≤ N) :
    r * 2 ≤ r * q ∧ r ≤ N ∧ r < N + 1 := by
  have h_r2_le_rq : r * 2 ≤ r * q := Nat.mul_le_mul_left r hq2
  have h_r_le_N : r ≤ N := by omega
  have h_r_lt_N1 : r < N + 1 := by omega
  exact ⟨h_r2_le_rq, h_r_le_N, h_r_lt_N1⟩

/-- Pure native Euclidean remainder cancellation using `Nat.lt_or_ge`:
    if `r_rem < m` and `m * K1 + r_rem = m * K2`, then `r_rem = 0`. -/
theorem eq_zero_of_mul_add_eq_mul_of_lt_liliu
    {m K1 K2 r_rem : ℕ} (h_lt : r_rem < m) (h_eq : m * K1 + r_rem = m * K2) :
    r_rem = 0 := by
  match Nat.lt_or_ge K1 K2 with
  | Or.inl h_gt =>
    have h_succ : K1 + 1 ≤ K2 := h_gt
    have h_mul : m * (K1 + 1) ≤ m * K2 := Nat.mul_le_mul_left m h_succ
    rw [Nat.left_distrib m K1 1, Nat.mul_one] at h_mul
    omega
  | Or.inr h_le =>
    have h_mul : m * K2 ≤ m * K1 := Nat.mul_le_mul_left m h_le
    omega

/-- Division-free target-side OMC exclusion in pure `Init` arithmetic:
    if `r * q + p = N`, `0 < m`, and `1 ≤ p % m`, then `(r * (q % m)) % m ≠ N % m`. -/
theorem bilateral_omc_target_lane_ne_liliu
    {N r q p m : ℕ} (h_sum : r * q + p = N) (hm_pos : 0 < m) (hp_mod_pos : 1 ≤ p % m) :
    (r * (q % m)) % m ≠ N % m := by
  intro h_same
  have hq_div : m * (q / m) + q % m = q := Nat.div_add_mod q m
  have hrc_div : m * ((r * (q % m)) / m) + (r * (q % m)) % m = r * (q % m) :=
    Nat.div_add_mod (r * (q % m)) m
  have hp_div : m * (p / m) + p % m = p := Nat.div_add_mod p m
  have hN_div : m * (N / m) + N % m = N := Nat.div_add_mod N m
  have hrq_expand : r * q = m * (r * (q / m)) + r * (q % m) := by
    calc r * q
      _ = r * (m * (q / m) + q % m) := by rw [hq_div]
      _ = r * (m * (q / m)) + r * (q % m) := Nat.left_distrib r (m * (q / m)) (q % m)
      _ = (r * m) * (q / m) + r * (q % m) := by rw [← Nat.mul_assoc r m (q / m)]
      _ = (m * r) * (q / m) + r * (q % m) := by rw [Nat.mul_comm r m]
      _ = m * (r * (q / m)) + r * (q % m) := by rw [Nat.mul_assoc m r (q / m)]
  have hK1_expand :
      m * (r * (q / m) + (r * (q % m)) / m + p / m) =
        m * (r * (q / m)) + m * ((r * (q % m)) / m) + m * (p / m) := by
    rw [Nat.left_distrib m (r * (q / m) + (r * (q % m)) / m) (p / m),
        Nat.left_distrib m (r * (q / m)) ((r * (q % m)) / m)]
  have h_mul_eq :
      m * (r * (q / m) + (r * (q % m)) / m + p / m) + p % m = m * (N / m) := by
    omega
  have hp_lt_m : p % m < m := Nat.mod_lt p hm_pos
  have hp_zero : p % m = 0 := eq_zero_of_mul_add_eq_mul_of_lt_liliu hp_lt_m h_mul_eq
  omega

/-!
## Section 2: 3-Prime Tight Hyperbolic Fibers for `D19 N` & Direct Subfilter Injection
-/

/-- The 3-Prime Tight `9/19` Hyperbolic Fiber above `r`:
    restricts `liliuShearContractedFiber N r` to `q` where `p = N - r * q` is also prime
    (`IsPrimeNat (N - r * q)` and `r * q ≤ N - 2`). -/
def liliuTight3PrimeFiber (N r : ℕ) : Finset ℕ :=
  (liliuShearContractedFiber N r).filter (fun q : ℕ =>
    r * q ≤ N - 2 ∧ IsPrimeNat (N - r * q))

/-- Explicit bridge connecting `q ∈ liliuTight3PrimeFiber N r` directly to
    `liliuHyperbolicPrimeFiber_919_pinch_and_shear` (`WR2Step200`). -/
theorem liliuTight3PrimeFiber_mem_props
    {N r q : ℕ} (hq : q ∈ liliuTight3PrimeFiber N r) :
    q ∈ liliuShearContractedFiber N r ∧
    q ∈ liliuHyperbolicPrimeFiber N r ∧
    q ≤ N / r ∧
    r * q ≤ N - 2 ∧
    IsPrimeNat (N - r * q) ∧
    r * q + (N - r * q) = N := by
  rw [liliuTight3PrimeFiber, mem_filter] at hq
  obtain ⟨hq_shear, h_rq_sub2, h_pp⟩ := hq
  have hq_hyp : q ∈ liliuHyperbolicPrimeFiber N r := by
    have hq_copy := hq_shear
    rw [liliuShearContractedFiber, mem_filter] at hq_copy
    exact hq_copy.1
  have h_q_le : q ≤ N / r :=
    (liliuHyperbolicPrimeFiber_919_pinch_and_shear hq_hyp).2.1
  have h_sum : r * q + (N - r * q) = N :=
    add_sub_cancel_of_le_sub2_liliu h_rq_sub2
  exact ⟨hq_shear, hq_hyp, h_q_le, h_rq_sub2, h_pp, h_sum⟩

/-- Explicit connection from every `q ∈ liliuTight3PrimeFiber N r` to our native prime
    generator `predictedNextPrime` and `hasNextPrimeConnection_unconditional` for both
    `q` and the reconstructed prime `p = N - r * q`. -/
theorem liliuTight3PrimeFiber_next_prime_connections
    {N r q : ℕ} (hq : q ∈ liliuTight3PrimeFiber N r) :
    IsPrimeNat q ∧
    IsPrimeNat (N - r * q) ∧
    predictedNextPrime q = nextPrimeBoundedAux (q + 1) (factorialNat q + 1) ∧
    predictedNextPrime (N - r * q) =
      nextPrimeBoundedAux ((N - r * q) + 1) (factorialNat (N - r * q) + 1) ∧
    (∃ q_next : ℕ, q < q_next ∧ IsPrimeNat q_next) ∧
    (∃ p_next : ℕ, (N - r * q) < p_next ∧ IsPrimeNat p_next) := by
  have h_props := liliuTight3PrimeFiber_mem_props hq
  have hq_hyp := h_props.2.1
  have h_pp := h_props.2.2.2.2.1
  rw [liliuHyperbolicPrimeFiber, mem_filter] at hq_hyp
  have hq_isp : IsPrimeNat q := hq_hyp.2.1
  exact ⟨hq_isp, h_pp, rfl, rfl,
    hasNextPrimeConnection_unconditional q,
    hasNextPrimeConnection_unconditional (N - r * q)⟩

/-- The 2D fiber slice `{(r, q) | q ∈ liliuTight3PrimeFiber N r}`. -/
def liliuTight3PrimeFiberPairs (N r : ℕ) : Finset (ℕ × ℕ) :=
  (liliuTight3PrimeFiber N r).image (fun q : ℕ => (r, q))

/-- Reconstruction map `(r, q) ↦ N - r * q` recovering the candidate prime `p`. -/
def reconstructPrimeFromFactorPair (N : ℕ) (rq : ℕ × ℕ) : ℕ :=
  N - rq.1 * rq.2

/-- **Theorem 2.1 (`oddFiveupPinchedQRSubfilter_9_10_subset_image_tight3Prime_biUnion`):**
    For every even target `N`, `oddFiveupPinchedQRSubfilter 9 10 N` is contained in the
    image under `reconstructPrimeFromFactorPair N` of `(pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)`. -/
theorem oddFiveupPinchedQRSubfilter_9_10_subset_image_tight3Prime_biUnion
    {N : ℕ} (hEven : N % 2 = 0) :
    oddFiveupPinchedQRSubfilter 9 10 N ⊆
      ((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).image
        (reconstructPrimeFromFactorPair N) := by
  intro p hp
  rw [oddFiveupPinchedQRSubfilter, mem_filter] at hp
  obtain ⟨hp_sub, hp_odd⟩ := hp
  rw [fiveupPinchedQRSubfilter, mem_filter] at hp_sub
  obtain ⟨_, hp_prime, r, q, hr_prime, hq_prime, hN_eq, h_lt, _, _, _, _, h_homog⟩ := hp_sub
  have h_rq_odd : (r * q) % 2 = 1 := by omega
  obtain ⟨hr_odd, hq_odd⟩ := mul_mod_two_eq_one_iff h_rq_odd
  have hp_isp : IsPrimeNat p := natPrime_to_isPrimeNat hp_prime
  have hr_isp : IsPrimeNat r := natPrime_to_isPrimeNat hr_prime
  have hq_isp : IsPrimeNat q := natPrime_to_isPrimeNat hq_prime
  have hp_two : 2 ≤ p := hp_prime.two_le
  have hr_two : 2 ≤ r := hr_prime.two_le
  have hq_two : 2 ≤ q := hq_prime.two_le
  have hr_pos : 0 < r := by omega
  have h_r2_le_q : r + 2 ≤ q := by omega
  have h_rq_le_sub2 : r * q ≤ N - 2 := by omega
  have h_rq_le_N : r * q ≤ N := by omega
  have h_q_le_div : q ≤ N / r := le_div_of_mul_le_liliu hr_pos h_rq_le_N
  have h_sub_p : N - p = r * q := by rw [hN_eq, Nat.add_sub_cancel_left]
  have h_sub_rq : N - r * q = p := by omega
  have h_homog_rq : r ^ 19 ≤ (r * q) ^ 9 := by
    rw [← h_sub_p]
    exact h_homog
  have h_in_hyp : q ∈ liliuHyperbolicPrimeFiber N r := by
    rw [liliuHyperbolicPrimeFiber, mem_filter, mem_range]
    exact ⟨by omega, hq_isp, hq_odd, h_r2_le_q, h_rq_le_N, h_homog_rq⟩
  have h_pinch_shear := liliuHyperbolicPrimeFiber_919_pinch_and_shear h_in_hyp
  have h_qr := h_pinch_shear.2.2.2 hr_odd
  have h_pp_rq : IsPrimeNat (N - r * q) := by
    rw [h_sub_rq]
    exact hp_isp
  have h_r_lt_N1 : r < N + 1 :=
    (factor_lt_succ_of_mul_le_native hq_two h_rq_le_N).2.2
  rw [mem_image]
  refine ⟨(r, q), ?_, ?_⟩
  · rw [mem_biUnion]
    refine ⟨r, ?_, ?_⟩
    · rw [pinchedOddPrimes919, mem_filter, mem_range]
      exact ⟨h_r_lt_N1, hr_isp, hr_odd, h_pinch_shear.1⟩
    · rw [liliuTight3PrimeFiberPairs, mem_image]
      refine ⟨q, ?_, rfl⟩
      rw [liliuTight3PrimeFiber, mem_filter, liliuShearContractedFiber, mem_filter]
      exact ⟨⟨h_in_hyp, h_pinch_shear.1, h_pinch_shear.2.2.1, h_qr.1, h_qr.2.1, h_qr.2.2⟩,
        h_rq_le_sub2, h_pp_rq⟩
  · unfold reconstructPrimeFromFactorPair
    exact h_sub_rq

/-- **Theorem 2.2 (`fiveupPinchedQRSubfilter_9_10_card_le_one_add_tight3Prime_biUnion`):**
    For every even target `N`,
    `(fiveupPinchedQRSubfilter 9 10 N).card ≤ 1 + ((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).card`. -/
theorem fiveupPinchedQRSubfilter_9_10_card_le_one_add_tight3Prime_biUnion
    {N : ℕ} (hEven : N % 2 = 0) :
    (fiveupPinchedQRSubfilter 9 10 N).card ≤
      1 + ((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).card := by
  have h_sub := oddFiveupPinchedQRSubfilter_9_10_subset_image_tight3Prime_biUnion hEven
  have h_odd_le := Nat.le_trans (card_le_card h_sub) card_image_le
  exact Nat.le_trans
    (fiveupPinchedQRSubfilter_card_le_one_add_odd 9 10 N)
    (Nat.add_le_add_left h_odd_le 1)

/-!
## Section 3: Bilateral OMC Lane Exclusion & General-Floor Strides on `liliuTight3PrimeFiber`
-/

/-- Target-sieved subset of `liliuTight3PrimeFiber N r` (`m < N - r * q`). -/
def liliuTargetSieved3PrimeFiber (N r m : ℕ) : Finset ℕ :=
  (liliuTight3PrimeFiber N r).filter (fun q : ℕ => m < N - r * q)

/-- Bilateral OMC admissible residue classes modulo `m`:
    `{c ∈ range m | 1 ≤ c ∧ (r * c) % m ≠ N % m}`. -/
def liliuBilateralOMCResidues (N r m : ℕ) : Finset ℕ :=
  (range m).filter (fun c : ℕ => 1 ≤ c ∧ (r * c) % m ≠ N % m)

/-- **Theorem 3.1 (`liliuTargetSieved_admissible_subset_bilateralOMC`):**
    For every modulus `m` with `2 ≤ m ≤ r`, every residue class `c = q % m` populated by
    `liliuTargetSieved3PrimeFiber N r m` lies inside `liliuBilateralOMCResidues N r m`. -/
theorem liliuTargetSieved_admissible_subset_bilateralOMC
    {N r m : ℕ} (hm2 : 2 ≤ m) (hmr : m ≤ r) :
    (liliuTargetSieved3PrimeFiber N r m).image (fun q : ℕ => q % m) ⊆
      liliuBilateralOMCResidues N r m := by
  intro c hc
  rw [mem_image] at hc
  obtain ⟨q, hq, rfl⟩ := hc
  rw [liliuTargetSieved3PrimeFiber, mem_filter] at hq
  obtain ⟨hq_tight, hm_lt_p⟩ := hq
  have h_props := liliuTight3PrimeFiber_mem_props hq_tight
  have hq_shear := h_props.1
  have h_pp := h_props.2.2.2.2.1
  have h_sum := h_props.2.2.2.2.2
  have hm_pos : 0 < m := by omega
  have hr_pos : 0 < r := by omega
  have hq_mod_pos : 1 ≤ q % m :=
    (liliuShearContractedFiber_lower_pinch_10_9 hr_pos hq_shear).2.2 m hm2 hmr
  have hp_mod_pos : 1 ≤ (N - r * q) % m :=
    mod_pos_of_lt_isPrimeNat_liliu hm2 hm_lt_p h_pp
  have h_target_ne : (r * (q % m)) % m ≠ N % m :=
    bilateral_omc_target_lane_ne_liliu h_sum hm_pos hp_mod_pos
  have h_mod_lt : q % m < m := Nat.mod_lt q hm_pos
  rw [liliuBilateralOMCResidues, mem_filter, mem_range]
  exact ⟨h_mod_lt, hq_mod_pos, h_target_ne⟩

/-- General-floor sub-fiber of `liliuTight3PrimeFiber N r` (`L ≤ q`). -/
def liliuFloorSubfiber (N r L : ℕ) : Finset ℕ :=
  (liliuTight3PrimeFiber N r).filter (fun q : ℕ => L ≤ q)

/-- Residue slice of `liliuFloorSubfiber N r L` modulo `m`. -/
def liliuFloorResidueSlice (N r L m c : ℕ) : Finset ℕ :=
  (liliuFloorSubfiber N r L).filter (fun q : ℕ => q % m = c)

/-- **Theorem 3.2 (`liliuFloorResidueSlice_card_le_shifted_quotient_diff`):**
    For ANY certified lower floor `L : ℕ`, modulus `m > 0`, and residue class `c`,
    `(liliuFloorResidueSlice N r L m c).card ≤ ((N / r) / m - L / m) + 1`. -/
theorem liliuFloorResidueSlice_card_le_shifted_quotient_diff
    {N r L m : ℕ} (hm_pos : 0 < m) (c : ℕ) :
    (liliuFloorResidueSlice N r L m c).card ≤ ((N / r) / m - L / m) + 1 := by
  have h_sub :
      liliuFloorResidueSlice N r L m c ⊆
        (range (((N / r) / m - L / m) + 1)).image
          (liliuReconstructShiftedQuotient m (L / m) c) := by
    intro q hq
    rw [liliuFloorResidueSlice, mem_filter, liliuFloorSubfiber, mem_filter] at hq
    obtain ⟨⟨hq_tight, h_L_le_q⟩, h_mod_eq⟩ := hq
    have h_q_le : q ≤ N / r := (liliuTight3PrimeFiber_mem_props hq_tight).2.2.1
    have h_q_div_ge : L / m ≤ q / m := div_le_div_right_liliu hm_pos h_L_le_q
    have h_q_div_le : q / m ≤ (N / r) / m := div_le_div_right_liliu hm_pos h_q_le
    have h_div_mod : m * (q / m) + q % m = q := Nat.div_add_mod q m
    have h_add_sub : L / m + (q / m - L / m) = q / m := by omega
    rw [mem_image]
    refine ⟨q / m - L / m, ?_, ?_⟩
    · rw [mem_range]
      omega
    · unfold liliuReconstructShiftedQuotient
      rw [h_add_sub]
      omega
  have h_card := Nat.le_trans (card_le_card h_sub) card_image_le
  rw [card_range] at h_card
  exact h_card

/-- **Master 29-Module Capstone (`master_29module_D19_tight_3prime_bilateral_omc_capstone`):**
    Unites `Goldbach.one_plus_one_nine_count` (`liuMainTerm0004 N < (D19 N : ℝ)`),
    the 3-Prime Tight `9/19` Hyperbolic Fibers (`liliuTight3PrimeFiberPairs N`),
    Division-Free Bilateral OMC Target-Side Exclusion (`liliuBilateralOMCResidues N r m`),
    Arbitrary-Floor Shifted Quotient Strides, and the Factorial Lighthouse Next-Prime Generator. -/
theorem master_29module_D19_tight_3prime_bilateral_omc_capstone :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (∀ r m : ℕ, 2 ≤ m → m ≤ r →
        (liliuTargetSieved3PrimeFiber N r m).image (fun q : ℕ => q % m) ⊆
          liliuBilateralOMCResidues N r m) ∧
      (∀ r L c : ℕ,
        (liliuFloorResidueSlice N r L 65 c).card ≤ ((N / r) / 65 - L / 65) + 1) ∧
      (fiveupPinchedQRSubfilter 9 10 N).card ≤
        1 + ((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).card ∧
      ((((1 + ((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).card : ℕ) : ℝ) ≤
          liuMainTerm0004 N) →
        ∃ p q p_next' : ℕ,
          Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next' ∧ IsPrimeNat p_next') := by
  obtain ⟨K1, hK1, hCount⟩ := Goldbach.one_plus_one_nine_count
  obtain ⟨K2, _, hWeld⟩ := goldbach_one_plus_one_nine_welded_to_concrete_certificate
  refine ⟨max K1 K2, le_trans hK1 (le_max_left K1 K2), ?_⟩
  intro N hN hEven
  have hN1 : K1 ≤ N := le_trans (le_max_left K1 K2) hN
  have hN2 : K2 ≤ N := le_trans (le_max_right K1 K2) hN
  rcases hEven with ⟨k, hk⟩
  have hMod2 : N % 2 = 0 := by omega
  have h_sub_le := fiveupPinchedQRSubfilter_9_10_card_le_one_add_tight3Prime_biUnion hMod2
  refine ⟨hCount N hN1 ⟨k, hk⟩,
          fun r m hm2 hmr => liliuTargetSieved_admissible_subset_bilateralOMC hm2 hmr,
          fun r L c => liliuFloorResidueSlice_card_le_shifted_quotient_diff (by omega : 0 < 65) c,
          h_sub_le, ?_⟩
  intro hRealLe
  have hMain := hCount N hN1 ⟨k, hk⟩
  have hRealLt :
      (((1 + ((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).card : ℕ) : ℝ)) <
        (D19 N : ℝ) :=
    lt_of_le_of_lt hRealLe hMain
  have hNatLt :
      1 + ((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).card < D19 N := by
    exact_mod_cast hRealLt
  have hMargin : (fiveupPinchedQRSubfilter 9 10 N).card < D19 N :=
    Nat.lt_of_le_of_lt h_sub_le hNatLt
  exact hWeld N hN2 ⟨k, hk⟩ hMargin

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.factor_lt_succ_of_mul_le_native
#print axioms WuPaper.ESZerosBridge.liliuTight3PrimeFiber_next_prime_connections
#print axioms WuPaper.ESZerosBridge.bilateral_omc_target_lane_ne_liliu
#print axioms WuPaper.ESZerosBridge.fiveupPinchedQRSubfilter_9_10_card_le_one_add_tight3Prime_biUnion
#print axioms WuPaper.ESZerosBridge.liliuTargetSieved_admissible_subset_bilateralOMC
#print axioms WuPaper.ESZerosBridge.liliuFloorResidueSlice_card_le_shifted_quotient_diff
#print axioms WuPaper.ESZerosBridge.master_29module_D19_tight_3prime_bilateral_omc_capstone
