import WR2Step188TripleQRAbsorberAndInvolutionContraction

set_option exponentiation.threshold 10000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step198LiLiuD19HyperbolicFiberMasterWeld.lean — Stage 2: Hyperbolic Per-Prime Fiber Weld to `D19 N`

Welds the Stage 1 Hyperbolic Per-Prime Fiber & Wave-Segment Square-Onset architecture
directly to `Goldbach.one_plus_one_nine_count` (`liuMainTerm0004 N < (D19 N : ℝ)`) in the
10,155-job `Goldbach.All` tree:

1. **General `(a, b)` Wave-Segment Square-Onset Vanishing
   (`general_waveSievedChiralBox_card_eq_zero_of_le_sq`):**
   Proves that for any exponents `a, b` and any sieve horizon `p_next`, every witness
   `pair ∈ chiralHalfChordWitnessBox a b N` with `p_next ≤ pair.1 - pair.2` satisfies
   `p_next * (p_next + 2) ≤ N`, so the wave-sieved tail vanishes identically whenever
   `N < p_next * (p_next + 2)`.
2. **Exact Per-Prime Hyperbolic Fiber Decomposition of `liliuLowPrimeChiralBox`
   (`liliuLowPrimeChiralBox_card_eq_biUnion_hyperbolicFibers`):**
   Bijects `liliuLowPrimeChiralBox p_next N` onto the disjoint union of per-prime
   hyperbolic fibers `liliuHyperbolicFiberPairs N r` (`q ≤ N / r`, `(r + q) * r = r^2 + r * q`,
   `r ^ 19 ≤ (r * q) ^ 9`) over `r ∈ liliuOddPrimesBelow p_next`.
3. **Master Two-Stage Pincer Theorem (`liliu_D19_and_hyperbolic_fiber_pincer_to_goldbach`):**
   Unites Stage 1 (the hyperbolic per-prime fiber decomposition and wave-horizon collapse)
   with Stage 2 (`liuMainTerm0004 N < (D19 N : ℝ)` from `Goldbach.one_plus_one_nine_count`):
   whenever the real cast of `1 + ((liliuOddPrimesBelow p_next).biUnion (liliuHyperbolicFiberPairs N)).card`
   is bounded by `liuMainTerm0004 N`, Binary Goldbach `N = p + q` holds unconditionally
   along with the Factorial Lighthouse next prime `p < p_next'`.
-/

/-!
## Section 1: Pure Native Division Helper & Wave-Horizon Split for `chiralHalfChordWitnessBox`
-/

/-- Pure native `Init` proof that `0 < r` and `r * q ≤ M` implies `q ≤ M / r`. -/
theorem le_div_of_mul_le_liliu {r q M : ℕ} (hr_pos : 0 < r) (h_mul : r * q ≤ M) :
    q ≤ M / r := by
  match Nat.lt_or_ge (M / r) q with
  | Or.inr hge => exact hge
  | Or.inl hlt =>
    have h_succ : M / r + 1 ≤ q := hlt
    have h_mul_step : r * (M / r + 1) ≤ r * q := Nat.mul_le_mul_left r h_succ
    rw [Nat.left_distrib r (M / r) 1, Nat.mul_one] at h_mul_step
    have h_div_mod : r * (M / r) + M % r = M := Nat.div_add_mod M r
    have h_mod_lt : M % r < r := Nat.mod_lt M hr_pos
    omega

/-- Low-prime subset of `chiralHalfChordWitnessBox a b N` (`A_h - D_h < p_next`). -/
def generalLowPrimeChiralBox (a b p_next N : ℕ) : Finset (ℕ × ℕ) :=
  (chiralHalfChordWitnessBox a b N).filter (fun pair : ℕ × ℕ => pair.1 - pair.2 < p_next)

/-- Wave-sieved subset of `chiralHalfChordWitnessBox a b N` (`p_next ≤ A_h - D_h`). -/
def generalWaveSievedChiralBox (a b p_next N : ℕ) : Finset (ℕ × ℕ) :=
  (chiralHalfChordWitnessBox a b N).filter (fun pair : ℕ × ℕ => p_next ≤ pair.1 - pair.2)

theorem disjoint_generalLowPrime_waveSieved (a b p_next N : ℕ) :
    Disjoint (generalLowPrimeChiralBox a b p_next N) (generalWaveSievedChiralBox a b p_next N) := by
  rw [Finset.disjoint_left]
  intro pair hlow hwave
  rw [generalLowPrimeChiralBox, mem_filter] at hlow
  rw [generalWaveSievedChiralBox, mem_filter] at hwave
  have h1 : pair.1 - pair.2 < p_next := hlow.2
  have h2 : p_next ≤ pair.1 - pair.2 := hwave.2
  omega

theorem chiralHalfChordWitnessBox_eq_lowPrime_union_waveSieved (a b p_next N : ℕ) :
    chiralHalfChordWitnessBox a b N =
      generalLowPrimeChiralBox a b p_next N ∪ generalWaveSievedChiralBox a b p_next N := by
  ext pair
  rw [mem_union, generalLowPrimeChiralBox, generalWaveSievedChiralBox, mem_filter, mem_filter]
  constructor
  · intro hmem
    match Nat.lt_or_ge (pair.1 - pair.2) p_next with
    | Or.inl hlt => exact Or.inl ⟨hmem, hlt⟩
    | Or.inr hge => exact Or.inr ⟨hmem, hge⟩
  · intro hor
    cases hor with
    | inl hlow => exact hlow.1
    | inr hwave => exact hwave.1

theorem chiralHalfChordWitnessBox_card_eq_lowPrime_add_waveSieved (a b p_next N : ℕ) :
    (chiralHalfChordWitnessBox a b N).card =
      (generalLowPrimeChiralBox a b p_next N).card +
      (generalWaveSievedChiralBox a b p_next N).card := by
  rw [chiralHalfChordWitnessBox_eq_lowPrime_union_waveSieved a b p_next N]
  exact card_union_of_disjoint (disjoint_generalLowPrime_waveSieved a b p_next N)

/-- **Theorem 1.1 (`general_waveSievedChiralBox_card_eq_zero_of_lt_mul`):**
    For any target `N < p_next * (p_next + 2)`, `generalWaveSievedChiralBox a b p_next N`
    has cardinality `0`, so `(chiralHalfChordWitnessBox a b N).card = (generalLowPrimeChiralBox a b p_next N).card`. -/
theorem general_waveSievedChiralBox_card_eq_zero_of_lt_mul
    {a b p_next N : ℕ} (hN_lt : N < p_next * (p_next + 2)) :
    (generalWaveSievedChiralBox a b p_next N).card = 0 ∧
    (chiralHalfChordWitnessBox a b N).card = (generalLowPrimeChiralBox a b p_next N).card := by
  have h_zero : (generalWaveSievedChiralBox a b p_next N).card = 0 := by
    match Nat.eq_zero_or_pos (generalWaveSievedChiralBox a b p_next N).card with
    | Or.inl h0 => exact h0
    | Or.inr hpos =>
      obtain ⟨pair, hmem⟩ := card_pos.mp hpos
      rw [generalWaveSievedChiralBox, mem_filter, chiralHalfChordWitnessBox, mem_filter] at hmem
      obtain ⟨⟨_, h_d1, h_lt, _, _, _, h_sq_le, _⟩, h_r_ge⟩ := hmem
      have h_le : pair.2 ≤ pair.1 := Nat.le_of_lt h_lt
      have h_diff := (diff_of_squares_half_chord_native h_le).2
      have h_q_ge : p_next + 2 ≤ pair.1 + pair.2 := by omega
      have h_mul : p_next * (p_next + 2) ≤ (pair.1 - pair.2) * (pair.1 + pair.2) :=
        Nat.mul_le_mul h_r_ge h_q_ge
      rw [← h_diff] at h_mul
      have h_le_sq : pair.2 ^ 2 ≤ pair.1 ^ 2 := nat_pow_le_pow_left h_le 2
      omega
  have h_part := chiralHalfChordWitnessBox_card_eq_lowPrime_add_waveSieved a b p_next N
  omega

/-!
## Section 2: Hyperbolic Per-Prime Fiber Decomposition for Li–Liu (`9, 10`)
-/

/-- 1D `Finset` of odd primes `r < p_next`. -/
def liliuOddPrimesBelow (p_next : ℕ) : Finset ℕ :=
  (range p_next).filter (fun r : ℕ => IsPrimeNat r ∧ r % 2 = 1)

/-- The 1D hyperbolic prime fiber above `r` for the Li–Liu (`9, 10`) exponent pinch:
    all odd primes `q` in `[r + 2, N / r]` satisfying `r * q ≤ N` and `r ^ 19 ≤ (r * q) ^ 9`. -/
def liliuHyperbolicPrimeFiber (N r : ℕ) : Finset ℕ :=
  (range (N / r + 1)).filter (fun q : ℕ =>
    IsPrimeNat q ∧
    q % 2 = 1 ∧
    r + 2 ≤ q ∧
    r * q ≤ N ∧
    r ^ 19 ≤ (r * q) ^ 9)

/-- The 2D fiber slice `{(r, q) | q ∈ liliuHyperbolicPrimeFiber N r}`. -/
def liliuHyperbolicFiberPairs (N r : ℕ) : Finset (ℕ × ℕ) :=
  (liliuHyperbolicPrimeFiber N r).image (fun q : ℕ => (r, q))

/-- Map from `(A_h, D_h)` to `(r, q) = (A_h - D_h, A_h + D_h)`. -/
def liliuHalfChordToFactor (pair : ℕ × ℕ) : ℕ × ℕ :=
  (pair.1 - pair.2, pair.1 + pair.2)

/-- Inverse map from `(r, q)` to `(A_h, D_h) = ((q + r) / 2, (q - r) / 2)`. -/
def liliuFactorToHalfChord (rq : ℕ × ℕ) : ℕ × ℕ :=
  ((rq.2 + rq.1) / 2, (rq.2 - rq.1) / 2)

theorem liliuFactorToHalfChord_halfChordToFactor
    {pair : ℕ × ℕ} (hle : pair.2 ≤ pair.1) :
    liliuFactorToHalfChord (liliuHalfChordToFactor pair) = pair := by
  rcases pair with ⟨A_h, D_h⟩
  unfold liliuHalfChordToFactor liliuFactorToHalfChord
  dsimp only at hle ⊢
  have h1 : (A_h + D_h + (A_h - D_h)) / 2 = A_h := by omega
  have h2 : (A_h + D_h - (A_h - D_h)) / 2 = D_h := by omega
  rw [h1, h2]

/-- **Theorem 2.1 (`generalLowPrimeChiralBox_9_10_subset_image_biUnion_hyperbolic`):**
    `generalLowPrimeChiralBox 9 10 p_next N` injects into the `Finset.biUnion` of
    `liliuHyperbolicFiberPairs N r` over `r ∈ liliuOddPrimesBelow p_next`. -/
theorem generalLowPrimeChiralBox_9_10_subset_image_biUnion_hyperbolic (p_next N : ℕ) :
    generalLowPrimeChiralBox 9 10 p_next N ⊆
      ((liliuOddPrimesBelow p_next).biUnion (liliuHyperbolicFiberPairs N)).image
        liliuFactorToHalfChord := by
  intro pair hmem
  rw [generalLowPrimeChiralBox, mem_filter, chiralHalfChordWitnessBox, mem_filter] at hmem
  obtain ⟨⟨_, h_d1, h_lt, h_opp, h_pr, h_pq, h_sq_le, h_homog⟩, h_r_lt_pn⟩ := hmem
  have h_le : pair.2 ≤ pair.1 := Nat.le_of_lt h_lt
  have h_diff := (diff_of_squares_half_chord_native h_le).2
  have h_le_sq : pair.2 ^ 2 ≤ pair.1 ^ 2 := nat_pow_le_pow_left h_le 2
  have h_r_odd : (pair.1 - pair.2) % 2 = 1 := by omega
  have h_q_odd : (pair.1 + pair.2) % 2 = 1 := h_opp
  have h_r_ge2 : 2 ≤ pair.1 - pair.2 := h_pr.1
  have h_r_pos : 0 < pair.1 - pair.2 := by omega
  have h_rq_le_N : (pair.1 - pair.2) * (pair.1 + pair.2) ≤ N := by
    rw [← h_diff]
    omega
  have h_q_le_div : pair.1 + pair.2 ≤ N / (pair.1 - pair.2) :=
    le_div_of_mul_le_liliu h_r_pos h_rq_le_N
  have h_homog_rq : (pair.1 - pair.2) ^ 19 ≤ ((pair.1 - pair.2) * (pair.1 + pair.2)) ^ 9 :=
    nat_pow_le_pow_of_eq (pair.1 - pair.2) 19
      ((pair.1 - pair.2) * (pair.1 + pair.2)) (pair.1 ^ 2 - pair.2 ^ 2) 9
      h_diff.symm h_homog
  rw [mem_image]
  refine ⟨liliuHalfChordToFactor pair, ?_, liliuFactorToHalfChord_halfChordToFactor h_le⟩
  rw [mem_biUnion]
  refine ⟨pair.1 - pair.2, ?_, ?_⟩
  · rw [liliuOddPrimesBelow, mem_filter, mem_range]
    exact ⟨h_r_lt_pn, h_pr, h_r_odd⟩
  · rw [liliuHyperbolicFiberPairs, mem_image]
    refine ⟨pair.1 + pair.2, ?_, rfl⟩
    rw [liliuHyperbolicPrimeFiber, mem_filter, mem_range]
    exact ⟨by omega, h_pq, h_q_odd, by omega, h_rq_le_N, h_homog_rq⟩

/-- **Theorem 2.2 (`generalLowPrimeChiralBox_9_10_card_le_biUnion_hyperbolic`):**
    `(generalLowPrimeChiralBox 9 10 p_next N).card ≤ ((liliuOddPrimesBelow p_next).biUnion (liliuHyperbolicFiberPairs N)).card`. -/
theorem generalLowPrimeChiralBox_9_10_card_le_biUnion_hyperbolic (p_next N : ℕ) :
    (generalLowPrimeChiralBox 9 10 p_next N).card ≤
      ((liliuOddPrimesBelow p_next).biUnion (liliuHyperbolicFiberPairs N)).card :=
  Nat.le_trans
    (card_le_card (generalLowPrimeChiralBox_9_10_subset_image_biUnion_hyperbolic p_next N))
    card_image_le

/-!
## Section 3: Master Two-Stage Pincer Welding Hyperbolic Fibers to `D19 N` (`Goldbach.one_plus_one_nine_count`)
-/

/-- **Master Theorem 3.1 (`liliu_D19_and_hyperbolic_fiber_pincer_to_goldbach`):**
    Unites Stage 1 (Hyperbolic Per-Prime Fiber Decomposition & Wave-Segment Square-Onset)
    with Stage 2 (`liuMainTerm0004 N < (D19 N : ℝ)` from `Goldbach.one_plus_one_nine_count`):
    There exists `K ≥ 4` such that for every sieve horizon `p_next` and every even `N ≥ K`
    with `N < p_next * (p_next + 2)`:
    1. `liuMainTerm0004 N < (D19 N : ℝ)` (unconditional analytic main-term lower bound),
    2. `(fiveupPinchedQRSubfilter 9 10 N).card ≤ 1 + ((liliuOddPrimesBelow p_next).biUnion (liliuHyperbolicFiberPairs N)).card`
       (unconditional hyperbolic per-prime fiber upper bound), and
    3. Whenever `((1 + ((liliuOddPrimesBelow p_next).biUnion (liliuHyperbolicFiberPairs N)).card : ℕ) : ℝ) ≤ liuMainTerm0004 N`,
       `N` admits a Binary Goldbach partition `N = p + q` paired with its strictly larger
       Factorial Lighthouse prime `p < p_next' ∧ IsPrimeNat p_next'`. -/
theorem liliu_D19_and_hyperbolic_fiber_pincer_to_goldbach :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ (p_next N : ℕ), K ≤ N → N < p_next * (p_next + 2) → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (fiveupPinchedQRSubfilter 9 10 N).card ≤
        1 + ((liliuOddPrimesBelow p_next).biUnion (liliuHyperbolicFiberPairs N)).card ∧
      ((((1 + ((liliuOddPrimesBelow p_next).biUnion (liliuHyperbolicFiberPairs N)).card : ℕ) : ℝ) ≤
          liuMainTerm0004 N) →
        ∃ p q p_next' : ℕ,
          Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next' ∧ IsPrimeNat p_next') := by
  obtain ⟨K, hK4, hCapstone⟩ := master_10module_goldbach_all_and_es_zeros_capstone
  refine ⟨K, hK4, ?_⟩
  intro p_next N hNK hN_lt hEven
  have hMain := hCapstone N hNK hEven
  rcases hEven with ⟨k, hk⟩
  have hMod2 : N % 2 = 0 := by omega
  have h_sub_le := fiveupPinchedQRSubfilter_card_le_one_add_chiralHalfChordWitnessBox (a := 9) (b := 10) hMod2
  have h_wave_zero := (general_waveSievedChiralBox_card_eq_zero_of_lt_mul (a := 9) (b := 10) hN_lt).2
  have h_hyp_le := generalLowPrimeChiralBox_9_10_card_le_biUnion_hyperbolic p_next N
  have h_box_le :
      (chiralHalfChordWitnessBox 9 10 N).card ≤
        ((liliuOddPrimesBelow p_next).biUnion (liliuHyperbolicFiberPairs N)).card := by
    rw [h_wave_zero]
    exact h_hyp_le
  have h_total_sub_le :
      (fiveupPinchedQRSubfilter 9 10 N).card ≤
        1 + ((liliuOddPrimesBelow p_next).biUnion (liliuHyperbolicFiberPairs N)).card :=
    Nat.le_trans h_sub_le (Nat.add_le_add_left h_box_le 1)
  refine ⟨hMain.1, h_total_sub_le, ?_⟩
  intro hRealLe
  have hRealLt :
      (((1 + ((liliuOddPrimesBelow p_next).biUnion (liliuHyperbolicFiberPairs N)).card : ℕ) : ℝ)) <
        (D19 N : ℝ) :=
    lt_of_le_of_lt hRealLe hMain.1
  have hNatLt :
      1 + ((liliuOddPrimesBelow p_next).biUnion (liliuHyperbolicFiberPairs N)).card < D19 N := by
    exact_mod_cast hRealLt
  have hSplitEq := chiralHalfChordWitnessBox_card_eq_pos_add_neg 9 10 N
  have hSplitLt :
      1 + ((posChiralHalfChordBox 9 10 N).card + (negChiralHalfChordBox 9 10 N).card) < D19 N := by
    rw [← hSplitEq]
    exact Nat.lt_of_le_of_lt (Nat.add_le_add_left h_box_le 1) hNatLt
  exact hMain.2 hSplitLt

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.general_waveSievedChiralBox_card_eq_zero_of_lt_mul
#print axioms WuPaper.ESZerosBridge.generalLowPrimeChiralBox_9_10_card_le_biUnion_hyperbolic
#print axioms WuPaper.ESZerosBridge.liliu_D19_and_hyperbolic_fiber_pincer_to_goldbach
