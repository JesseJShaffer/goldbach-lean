import WR2Step195ChiralBoxMod16And65ResidueFiberContraction

set_option exponentiation.threshold 10000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step196FactorPairBijectionAndBoxBound.lean — Factor-Pair Bijection & 1D Prime-Slice Box Bound

Bounds `lowPrimeTightChiralBox p_next N` and `wr2CutlineSemiprimePrimes N` by proving an
exact cardinality bijection between half-chord coordinates `(A_h, D_h)` and prime-factor
coordinates `(r, q) = (A_h - D_h, A_h + D_h)`, and bounding the 2D factor box by the
product of its 1D prime slices:

1. **Odd Prime Factor Parity & `q ≤ N / 3` Horizon (`tight_box_factors_odd_and_q_le_div_three`):**
   Proves in pure native `Nat` arithmetic that every `(A_h, D_h) ∈ wr2TightChiralHalfChordBox N`
   has odd prime factors `r = A_h - D_h ≥ 3` and `q = A_h + D_h ≥ 5` satisfying
   `r * q + 2 ≤ N`, `q ≤ N / 3`, and `q < N + 1`.
2. **Exact Bijection Between `lowPrimeTightChiralBox` and `lowPrimeFactorBox`
   (`lowPrimeTightChiralBox_card_eq_lowPrimeFactorBox`):**
   Uses mutual `Finset.image` inclusions under `halfChordToFactorPair` and
   `factorPairToHalfChord` to prove
   `(lowPrimeTightChiralBox p_next N).card = (lowPrimeFactorBox p_next N).card`.
3. **1D Prime-Slice Product Bound (`lowPrimeTightChiralBox_card_le_product_prime_slices`):**
   Embeds `lowPrimeFactorBox p_next N` into `oddPrimesBelow p_next ×ˢ oddPrimesUpToThird N`
   and applies `Finset.card_product` to bound `(lowPrimeTightChiralBox p_next N).card` and
   `(wr2CutlineSemiprimePrimes N).card`.
-/

/-!
## Section 1: Forward & Inverse Coordinate Maps and `q ≤ N / 3` Bound
-/

/-- Forward map from half-chord coordinates `(A_h, D_h)` to factor coordinates `(r, q) = (A_h - D_h, A_h + D_h)`. -/
def halfChordToFactorPair (pair : ℕ × ℕ) : ℕ × ℕ :=
  (pair.1 - pair.2, pair.1 + pair.2)

/-- Inverse map from factor coordinates `(r, q)` to half-chord coordinates `(A_h, D_h) = ((q + r) / 2, (q - r) / 2)`. -/
def factorPairToHalfChord (rq : ℕ × ℕ) : ℕ × ℕ :=
  ((rq.2 + rq.1) / 2, (rq.2 - rq.1) / 2)

/-- Exact round-trip identity `factorPairToHalfChord (halfChordToFactorPair (A_h, D_h)) = (A_h, D_h)`
    whenever `D_h ≤ A_h`. -/
theorem factorPairToHalfChord_halfChordToFactorPair
    {pair : ℕ × ℕ} (hle : pair.2 ≤ pair.1) :
    factorPairToHalfChord (halfChordToFactorPair pair) = pair := by
  rcases pair with ⟨A_h, D_h⟩
  unfold halfChordToFactorPair factorPairToHalfChord
  dsimp only at hle ⊢
  have h1 : (A_h + D_h + (A_h - D_h)) / 2 = A_h := by omega
  have h2 : (A_h + D_h - (A_h - D_h)) / 2 = D_h := by omega
  rw [h1, h2]

/-- Exact round-trip identity `halfChordToFactorPair (factorPairToHalfChord (r, q)) = (r, q)`
    whenever `r ≤ q` and `r % 2 = 1` and `q % 2 = 1`. -/
theorem halfChordToFactorPair_factorPairToHalfChord
    {rq : ℕ × ℕ} (hle : rq.1 ≤ rq.2) (hr_odd : rq.1 % 2 = 1) (hq_odd : rq.2 % 2 = 1) :
    halfChordToFactorPair (factorPairToHalfChord rq) = rq := by
  rcases rq with ⟨r, q⟩
  unfold factorPairToHalfChord halfChordToFactorPair
  dsimp only at hle hr_odd hq_odd ⊢
  have h1 : (q + r) / 2 - (q - r) / 2 = r := by omega
  have h2 : (q + r) / 2 + (q - r) / 2 = q := by omega
  rw [h1, h2]

/-- **Theorem 1.1 (`tight_box_factors_odd_and_q_le_div_three`):**
    Every `pair ∈ wr2TightChiralHalfChordBox N` satisfies:
    1. `(pair.1 - pair.2) % 2 = 1` and `(pair.1 + pair.2) % 2 = 1` (both `r` and `q` are odd),
    2. `3 ≤ pair.1 - pair.2` (`3 ≤ r`),
    3. `(pair.1 - pair.2) * (pair.1 + pair.2) + 2 ≤ N` (`r * q + 2 ≤ N`), and
    4. `pair.1 + pair.2 ≤ N / 3` and `pair.1 + pair.2 < N + 1` (`q ≤ N / 3`). -/
theorem tight_box_factors_odd_and_q_le_div_three
    {N : ℕ} {pair : ℕ × ℕ} (hmem : pair ∈ wr2TightChiralHalfChordBox N) :
    (pair.1 - pair.2) % 2 = 1 ∧
    (pair.1 + pair.2) % 2 = 1 ∧
    3 ≤ pair.1 - pair.2 ∧
    (pair.1 - pair.2) * (pair.1 + pair.2) + 2 ≤ N ∧
    pair.1 + pair.2 ≤ N / 3 ∧
    pair.1 + pair.2 < N + 1 := by
  rw [wr2TightChiralHalfChordBox, mem_filter] at hmem
  obtain ⟨_, h_d1, h_lt, h_opp, h_pr, _, h_sq_le, h_pp, _⟩ := hmem
  have h_le : pair.2 ≤ pair.1 := Nat.le_of_lt h_lt
  have h_r_odd : (pair.1 - pair.2) % 2 = 1 := by omega
  have h_q_odd : (pair.1 + pair.2) % 2 = 1 := h_opp
  have h_r_ge2 : 2 ≤ pair.1 - pair.2 := h_pr.1
  have h_r_ge3 : 3 ≤ pair.1 - pair.2 := by omega
  have h_diff := (half_chord_diff_of_squares_wr2 h_le).2
  have h_le_sq : pair.2 ^ 2 ≤ pair.1 ^ 2 := nat_pow_le_pow_left h_le 2
  have h_p_ge2 : 2 ≤ (N + pair.2 ^ 2) - pair.1 ^ 2 := h_pp.1
  have h_sq_add2 : (pair.1 ^ 2 - pair.2 ^ 2) + 2 ≤ N := by omega
  have h_rq_add2 : (pair.1 - pair.2) * (pair.1 + pair.2) + 2 ≤ N := by
    rw [← h_diff]
    exact h_sq_add2
  have h_3q_le : 3 * (pair.1 + pair.2) ≤ (pair.1 - pair.2) * (pair.1 + pair.2) :=
    Nat.mul_le_mul_right (pair.1 + pair.2) h_r_ge3
  have h_q_div3 : pair.1 + pair.2 ≤ N / 3 := by omega
  have h_q_lt : pair.1 + pair.2 < N + 1 := by omega
  exact ⟨h_r_odd, h_q_odd, h_r_ge3, h_rq_add2, h_q_div3, h_q_lt⟩

/-!
## Section 2: Exact Bijection with `lowPrimeFactorBox` & 1D Prime-Slice Product Bound
-/

/-- 1D `Finset` of odd primes `r < p_next` (`IsPrimeNat r ∧ r % 2 = 1`). -/
def oddPrimesBelow (p_next : ℕ) : Finset ℕ :=
  (range p_next).filter (fun r : ℕ => IsPrimeNat r ∧ r % 2 = 1)

/-- 1D `Finset` of odd primes `q ≤ N / 3` (`IsPrimeNat q ∧ q % 2 = 1`). -/
def oddPrimesUpToThird (N : ℕ) : Finset ℕ :=
  (range (N / 3 + 1)).filter (fun q : ℕ => IsPrimeNat q ∧ q % 2 = 1)

/-- The 2D Prime-Factor Box `lowPrimeFactorBox p_next N` over `(r, q) ∈ oddPrimesBelow p_next ×ˢ oddPrimesUpToThird N`. -/
def lowPrimeFactorBox (p_next N : ℕ) : Finset (ℕ × ℕ) :=
  (oddPrimesBelow p_next ×ˢ oddPrimesUpToThird N).filter (fun rq : ℕ × ℕ =>
    rq.1 + 2 ≤ rq.2 ∧
    rq.1 * rq.2 ≤ N ∧
    IsPrimeNat (N - rq.1 * rq.2) ∧
    rq.1 ^ 9469 ≤ (rq.1 * rq.2) ^ 4469)

/-- Forward image inclusion: `lowPrimeTightChiralBox p_next N` is contained in the image
    of `lowPrimeFactorBox p_next N` under `factorPairToHalfChord`. -/
theorem lowPrimeTightChiralBox_subset_image_lowPrimeFactorBox (p_next N : ℕ) :
    lowPrimeTightChiralBox p_next N ⊆
      (lowPrimeFactorBox p_next N).image factorPairToHalfChord := by
  intro pair hmem
  rw [lowPrimeTightChiralBox, mem_filter] at hmem
  obtain ⟨h_tight, h_r_lt_pn⟩ := hmem
  have h_props := tight_box_factors_odd_and_q_le_div_three h_tight
  rw [wr2TightChiralHalfChordBox, mem_filter] at h_tight
  obtain ⟨_, h_d1, h_lt, _, h_pr, h_pq, h_sq_le, h_pp, h_homog⟩ := h_tight
  have h_le : pair.2 ≤ pair.1 := Nat.le_of_lt h_lt
  have h_diff := (half_chord_diff_of_squares_wr2 h_le).2
  have h_le_sq : pair.2 ^ 2 ≤ pair.1 ^ 2 := nat_pow_le_pow_left h_le 2
  have h_sub_eq : (N + pair.2 ^ 2) - pair.1 ^ 2 = N - (pair.1 - pair.2) * (pair.1 + pair.2) := by
    rw [← h_diff]
    omega
  have h_pp_rq : IsPrimeNat (N - (pair.1 - pair.2) * (pair.1 + pair.2)) := by
    rw [← h_sub_eq]
    exact h_pp
  have h_homog_rq : (pair.1 - pair.2) ^ 9469 ≤ ((pair.1 - pair.2) * (pair.1 + pair.2)) ^ 4469 :=
    nat_pow_le_pow_of_eq (pair.1 - pair.2) 9469
      ((pair.1 - pair.2) * (pair.1 + pair.2)) (pair.1 ^ 2 - pair.2 ^ 2) 4469
      h_diff.symm h_homog
  rw [mem_image]
  refine ⟨halfChordToFactorPair pair, ?_, factorPairToHalfChord_halfChordToFactorPair h_le⟩
  rw [lowPrimeFactorBox, mem_filter, mem_product,
      oddPrimesBelow, mem_filter, mem_range,
      oddPrimesUpToThird, mem_filter, mem_range]
  unfold halfChordToFactorPair
  dsimp only
  refine ⟨⟨⟨h_r_lt_pn, h_pr, h_props.1⟩, ⟨by omega, h_pq, h_props.2.1⟩⟩,
    by omega, by omega, h_pp_rq, h_homog_rq⟩

/-- Reverse image inclusion: `lowPrimeFactorBox p_next N` is contained in the image
    of `lowPrimeTightChiralBox p_next N` under `halfChordToFactorPair`. -/
theorem lowPrimeFactorBox_subset_image_lowPrimeTightChiralBox (p_next N : ℕ) :
    lowPrimeFactorBox p_next N ⊆
      (lowPrimeTightChiralBox p_next N).image halfChordToFactorPair := by
  intro rq hrq
  rw [lowPrimeFactorBox, mem_filter, mem_product,
      oddPrimesBelow, mem_filter, mem_range,
      oddPrimesUpToThird, mem_filter, mem_range] at hrq
  obtain ⟨⟨⟨hr_lt_pn, hr_isp, hr_odd⟩, ⟨hq_lt_div3, hq_isp, hq_odd⟩⟩,
          h_r2_le_q, h_rq_le_N, h_pp, h_homog⟩ := hrq
  have h_r_le_q : rq.1 ≤ rq.2 := by omega
  set A_h := (rq.2 + rq.1) / 2
  set D_h := (rq.2 - rq.1) / 2
  have h_sub_r : A_h - D_h = rq.1 := by omega
  have h_add_q : A_h + D_h = rq.2 := by omega
  have h_d1 : 1 ≤ D_h := by omega
  have h_d_lt_a : D_h < A_h := by omega
  have h_d_le_a : D_h ≤ A_h := Nat.le_of_lt h_d_lt_a
  have h_a_lt_N1 : A_h < N + 1 := by omega
  have h_d_lt_N1 : D_h < N + 1 := by omega
  have h_diff := (half_chord_diff_of_squares_wr2 h_d_le_a).2
  have h_diff_rq : A_h ^ 2 - D_h ^ 2 = rq.1 * rq.2 := by
    rw [h_diff, h_sub_r, h_add_q]
  have h_le_sq : D_h ^ 2 ≤ A_h ^ 2 := nat_pow_le_pow_left h_d_le_a 2
  have h_sq_le_N : A_h ^ 2 ≤ N + D_h ^ 2 := by omega
  have h_rec_eq : (N + D_h ^ 2) - A_h ^ 2 = N - rq.1 * rq.2 := by omega
  have h_pp_hc : IsPrimeNat ((N + D_h ^ 2) - A_h ^ 2) := by
    rw [h_rec_eq]
    exact h_pp
  have h_pr_hc : IsPrimeNat (A_h - D_h) := by
    rw [h_sub_r]
    exact hr_isp
  have h_pq_hc : IsPrimeNat (A_h + D_h) := by
    rw [h_add_q]
    exact hq_isp
  have h_opp_hc : (A_h + D_h) % 2 = 1 := by
    rw [h_add_q]
    exact hq_odd
  have h_homog_r : (A_h - D_h) ^ 9469 ≤ (rq.1 * rq.2) ^ 4469 := by
    rw [h_sub_r]
    exact h_homog
  have h_homog_hc : (A_h - D_h) ^ 9469 ≤ (A_h ^ 2 - D_h ^ 2) ^ 4469 :=
    nat_pow_le_pow_of_eq (A_h - D_h) 9469 (A_h ^ 2 - D_h ^ 2) (rq.1 * rq.2) 4469
      h_diff_rq h_homog_r
  have h_low_r : A_h - D_h < p_next := by
    rw [h_sub_r]
    exact hr_lt_pn
  rw [mem_image]
  refine ⟨factorPairToHalfChord rq, ?_,
    halfChordToFactorPair_factorPairToHalfChord h_r_le_q hr_odd hq_odd⟩
  rw [lowPrimeTightChiralBox, mem_filter, wr2TightChiralHalfChordBox, mem_filter,
      mem_product, mem_range, mem_range]
  show ((A_h < N + 1 ∧ D_h < N + 1) ∧
    1 ≤ D_h ∧ D_h < A_h ∧ (A_h + D_h) % 2 = 1 ∧
    IsPrimeNat (A_h - D_h) ∧ IsPrimeNat (A_h + D_h) ∧
    A_h ^ 2 ≤ N + D_h ^ 2 ∧ IsPrimeNat ((N + D_h ^ 2) - A_h ^ 2) ∧
    (A_h - D_h) ^ 9469 ≤ (A_h ^ 2 - D_h ^ 2) ^ 4469) ∧ A_h - D_h < p_next
  exact ⟨⟨⟨h_a_lt_N1, h_d_lt_N1⟩, h_d1, h_d_lt_a, h_opp_hc,
    h_pr_hc, h_pq_hc, h_sq_le_N, h_pp_hc, h_homog_hc⟩, h_low_r⟩

/-- **Theorem 2.1 (`lowPrimeTightChiralBox_card_eq_lowPrimeFactorBox`):**
    Exact cardinality equality between `lowPrimeTightChiralBox p_next N` and
    `lowPrimeFactorBox p_next N`. -/
theorem lowPrimeTightChiralBox_card_eq_lowPrimeFactorBox (p_next N : ℕ) :
    (lowPrimeTightChiralBox p_next N).card = (lowPrimeFactorBox p_next N).card := by
  have h1 : (lowPrimeTightChiralBox p_next N).card ≤ (lowPrimeFactorBox p_next N).card :=
    Nat.le_trans
      (card_le_card (lowPrimeTightChiralBox_subset_image_lowPrimeFactorBox p_next N))
      card_image_le
  have h2 : (lowPrimeFactorBox p_next N).card ≤ (lowPrimeTightChiralBox p_next N).card :=
    Nat.le_trans
      (card_le_card (lowPrimeFactorBox_subset_image_lowPrimeTightChiralBox p_next N))
      card_image_le
  exact Nat.le_antisymm h1 h2

/-- **Theorem 2.2 (`lowPrimeTightChiralBox_card_le_product_prime_slices`):**
    Explicit 1D prime-slice product bound on `lowPrimeTightChiralBox p_next N`:
    `(lowPrimeTightChiralBox p_next N).card ≤ (oddPrimesBelow p_next).card * (oddPrimesUpToThird N).card`. -/
theorem lowPrimeTightChiralBox_card_le_product_prime_slices (p_next N : ℕ) :
    (lowPrimeTightChiralBox p_next N).card ≤
      (oddPrimesBelow p_next).card * (oddPrimesUpToThird N).card := by
  rw [lowPrimeTightChiralBox_card_eq_lowPrimeFactorBox p_next N]
  have h_sub : lowPrimeFactorBox p_next N ⊆ oddPrimesBelow p_next ×ˢ oddPrimesUpToThird N :=
    filter_subset _ _
  have h_le := card_le_card h_sub
  rw [card_product] at h_le
  exact h_le

/-- **Master Theorem 3.1 (`wr2_cutline_card_le_prime_slice_product_on_wave_segment`):**
    Across any wave segment `N ≤ (p_next + 1) ^ 2` with `N % 2 = 0`:
    1. `(wr2CutlineSemiprimePrimes N).card ≤ 1 + (lowPrimeFactorBox p_next N).card`, and
    2. `(wr2CutlineSemiprimePrimes N).card ≤ 1 + (oddPrimesBelow p_next).card * (oddPrimesUpToThird N).card`. -/
theorem wr2_cutline_card_le_prime_slice_product_on_wave_segment
    {p_next N : ℕ} (hEven : N % 2 = 0) (hN_le : N ≤ (p_next + 1) ^ 2) :
    (wr2CutlineSemiprimePrimes N).card ≤ 1 + (lowPrimeFactorBox p_next N).card ∧
    (wr2CutlineSemiprimePrimes N).card ≤
      1 + (oddPrimesBelow p_next).card * (oddPrimesUpToThird N).card := by
  have h_base := wr2CutlineSemiprimePrimes_card_le_one_add_lowPrime_of_le_succ_sq hEven hN_le
  have h_eq := lowPrimeTightChiralBox_card_eq_lowPrimeFactorBox p_next N
  have h_prod := lowPrimeTightChiralBox_card_le_product_prime_slices p_next N
  refine ⟨?_, ?_⟩
  · rw [← h_eq]
    exact h_base
  · exact Nat.le_trans h_base (Nat.add_le_add_left h_prod 1)

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.tight_box_factors_odd_and_q_le_div_three
#print axioms WuPaper.ESZerosBridge.lowPrimeTightChiralBox_card_eq_lowPrimeFactorBox
#print axioms WuPaper.ESZerosBridge.lowPrimeTightChiralBox_card_le_product_prime_slices
#print axioms WuPaper.ESZerosBridge.wr2_cutline_card_le_prime_slice_product_on_wave_segment
