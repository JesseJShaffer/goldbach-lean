import WR2Step185ChiralMod4HalfChordAndMasterSuite

set_option exponentiation.threshold 10000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step186ExplicitHalfChordFinsetInjectiveBound.lean — Global `Finset` Half-Chord Box Bound

Lifts the pointwise Half-Chord Hyperbola & Chiral Mod-4 theorems from `WR2Step184` and
`WR2Step185` into an unconditional `Finset` cardinality bound on `fiveupPinchedQRSubfilter`:

1. **Explicit Native Additive-to-Subtractive Bridges (`le_of_add_eq_native`, `sub_eq_of_add_eq_native`,
   `sub_eq_of_eq_add_native`):**
   Establishes explicit native arithmetic links connecting `p + A_h ^ 2 = N + D_h ^ 2` and
   `A_h ^ 2 = (N - p) + D_h ^ 2` to `(N + D_h ^ 2) - A_h ^ 2 = p` and `A_h ^ 2 - D_h ^ 2 = N - p`.
2. **Odd Subfilter & Even-Prime Split (`fiveupPinchedQRSubfilter_card_le_one_add_odd`):**
   Proves `(fiveupPinchedQRSubfilter a b N).card ≤ 1 + (oddFiveupPinchedQRSubfilter a b N).card`.
3. **Explicit 2D Chiral Half-Chord Witness Box (`chiralHalfChordWitnessBox a b N`):**
   Proves that `reconstructPrimeFromHalfChord N (A_h, D_h) = (N + D_h ^ 2) - A_h ^ 2` maps
   `chiralHalfChordWitnessBox a b N` onto `oddFiveupPinchedQRSubfilter a b N`, yielding
   `(fiveupPinchedQRSubfilter a b N).card ≤ 1 + (chiralHalfChordWitnessBox a b N).card`.
-/

/-!
## Section 1: Explicit Native Arithmetic Bridges for Half-Chord Reconstruction
-/

/-- Explicit native bridge: `p + a = b → a ≤ b`. -/
theorem le_of_add_eq_native {p a b : ℕ} (h : p + a = b) : a ≤ b := by
  rw [← h]
  exact Nat.le_add_left a p

/-- Explicit native bridge: `p + a = b → b - a = p`. -/
theorem sub_eq_of_add_eq_native {p a b : ℕ} (h : p + a = b) : b - a = p := by
  rw [← h, Nat.add_sub_cancel_right]

/-- Explicit native bridge: `a = m + d → a - d = m`. -/
theorem sub_eq_of_eq_add_native {a m d : ℕ} (h : a = m + d) : a - d = m := by
  rw [h, Nat.add_sub_cancel_right]

/-!
## Section 2: Odd Subfilter Split & 2D Chiral Half-Chord Witness Box
-/

/-- The odd-prime subset of `fiveupPinchedQRSubfilter a b N` (`p % 2 = 1`). -/
def oddFiveupPinchedQRSubfilter (a b N : ℕ) : Finset ℕ :=
  (fiveupPinchedQRSubfilter a b N).filter (fun p : ℕ => p % 2 = 1)

/-- Every prime `p ∈ fiveupPinchedQRSubfilter a b N` is either `2` or an odd prime (`p % 2 = 1`). -/
theorem fiveupPinchedQRSubfilter_subset_two_union_odd (a b N : ℕ) :
    fiveupPinchedQRSubfilter a b N ⊆ ({2} : Finset ℕ) ∪ oddFiveupPinchedQRSubfilter a b N := by
  intro p hp
  have hp_unfold := hp
  rw [fiveupPinchedQRSubfilter, mem_filter] at hp_unfold
  have hp_prime : Nat.Prime p := hp_unfold.2.1
  rw [mem_union, mem_singleton, oddFiveupPinchedQRSubfilter, mem_filter]
  rcases hp_prime.eq_two_or_odd with rfl | hp_odd
  · exact Or.inl rfl
  · exact Or.inr ⟨hp, hp_odd⟩

/-- **Theorem 2.1 (`fiveupPinchedQRSubfilter_card_le_one_add_odd`):**
    `(fiveupPinchedQRSubfilter a b N).card ≤ 1 + (oddFiveupPinchedQRSubfilter a b N).card`. -/
theorem fiveupPinchedQRSubfilter_card_le_one_add_odd (a b N : ℕ) :
    (fiveupPinchedQRSubfilter a b N).card ≤ 1 + (oddFiveupPinchedQRSubfilter a b N).card := by
  have h_sub := fiveupPinchedQRSubfilter_subset_two_union_odd a b N
  have h_le := Nat.le_trans (card_le_card h_sub) (card_union_le ({2} : Finset ℕ) _)
  rw [card_singleton] at h_le
  exact h_le

/-- The explicit 2D Chiral Half-Chord Witness Box `chiralHalfChordWitnessBox a b N`
    over `(A_h, D_h) ∈ range (N + 1) ×ˢ range (N + 1)`. -/
def chiralHalfChordWitnessBox (a b N : ℕ) : Finset (ℕ × ℕ) :=
  (range (N + 1) ×ˢ range (N + 1)).filter (fun pair : ℕ × ℕ =>
    1 ≤ pair.2 ∧
    pair.2 < pair.1 ∧
    (pair.1 + pair.2) % 2 = 1 ∧
    IsPrimeNat (pair.1 - pair.2) ∧
    IsPrimeNat (pair.1 + pair.2) ∧
    pair.1 ^ 2 ≤ N + pair.2 ^ 2 ∧
    (pair.1 - pair.2) ^ (a + b) ≤ (pair.1 ^ 2 - pair.2 ^ 2) ^ a)

/-- Reconstruction map recovering the candidate prime `p = (N + D_h ^ 2) - A_h ^ 2`
    from a half-chord coordinate pair `(A_h, D_h)`. -/
def reconstructPrimeFromHalfChord (N : ℕ) (pair : ℕ × ℕ) : ℕ :=
  (N + pair.2 ^ 2) - pair.1 ^ 2

/-- Pure native bound proving that for `2 ≤ r < q` with `N = p + r * q`,
    the half-chord `A_h = (q + r) / 2` satisfies `A_h < N + 1` and `D_h = (q - r) / 2 < N + 1`. -/
theorem half_chord_lt_succ_target
    {N p r q : ℕ} (hr2 : 2 ≤ r) (h_lt : r < q) (hN : N = p + r * q) :
    (q + r) / 2 < N + 1 ∧ (q - r) / 2 < N + 1 := by
  have h_2q_le_rq : 2 * q ≤ r * q := Nat.mul_le_mul_right q hr2
  omega

/-- **Theorem 2.2 (`oddFiveupPinchedQRSubfilter_subset_image_chiralHalfChordWitnessBox`):**
    For every even target `N`, `oddFiveupPinchedQRSubfilter a b N` is contained in the
    image of `chiralHalfChordWitnessBox a b N` under `reconstructPrimeFromHalfChord N`. -/
theorem oddFiveupPinchedQRSubfilter_subset_image_chiralHalfChordWitnessBox
    {a b N : ℕ} (hEven : N % 2 = 0) :
    oddFiveupPinchedQRSubfilter a b N ⊆
      (chiralHalfChordWitnessBox a b N).image (reconstructPrimeFromHalfChord N) := by
  intro p hp
  rw [oddFiveupPinchedQRSubfilter, mem_filter] at hp
  obtain ⟨hp_sub, hp_odd⟩ := hp
  rw [fiveupPinchedQRSubfilter, mem_filter] at hp_sub
  obtain ⟨_, _, r, q, hr_prime, hq_prime, hN_eq, h_lt, _, _, _, _, h_homog⟩ := hp_sub
  have h_rq_odd : (r * q) % 2 = 1 := by omega
  obtain ⟨hr_odd, hq_odd⟩ := mul_mod_two_eq_one_iff h_rq_odd
  have h_hc := half_chord_hyperbola_identity hN_eq h_lt hr_odd hq_odd
  set A_h := (q + r) / 2
  set D_h := (q - r) / 2
  have h_d_ge : 1 ≤ D_h := h_hc.1
  have h_d_lt : D_h < A_h := h_hc.2.1
  have h_sub_r : A_h - D_h = r := h_hc.2.2.1
  have h_add_q : A_h + D_h = q := h_hc.2.2.2.1
  have h_hyp : A_h ^ 2 = (N - p) + D_h ^ 2 := h_hc.2.2.2.2.1
  have h_rec : p + A_h ^ 2 = N + D_h ^ 2 := h_hc.2.2.2.2.2
  have h_rem_odd : (N - p) % 2 = 1 := by
    have h_sub : N - p = r * q := by rw [hN_eq, Nat.add_sub_cancel_left]
    rw [h_sub]
    exact h_rq_odd
  have h_chiral := half_chord_chiral_mod4_parity_lock h_hyp h_rem_odd
  have h_bounds := half_chord_lt_succ_target hr_prime.two_le h_lt hN_eq
  have h_pr_nat : IsPrimeNat (A_h - D_h) := by
    rw [h_sub_r]
    exact natPrime_to_isPrimeNat hr_prime
  have h_pq_nat : IsPrimeNat (A_h + D_h) := by
    rw [h_add_q]
    exact natPrime_to_isPrimeNat hq_prime
  have h_sq_le : A_h ^ 2 ≤ N + D_h ^ 2 :=
    le_of_add_eq_native h_rec
  have h_diff_sq : A_h ^ 2 - D_h ^ 2 = N - p :=
    sub_eq_of_eq_add_native h_hyp
  have h_homog_r : (A_h - D_h) ^ (a + b) ≤ (N - p) ^ a := by
    rw [h_sub_r]
    exact h_homog
  have h_homog_box : (A_h - D_h) ^ (a + b) ≤ (A_h ^ 2 - D_h ^ 2) ^ a :=
    nat_pow_le_pow_of_eq (A_h - D_h) (a + b) (A_h ^ 2 - D_h ^ 2) (N - p) a
      h_diff_sq h_homog_r
  have h_reconstruct_eq : reconstructPrimeFromHalfChord N (A_h, D_h) = p :=
    sub_eq_of_add_eq_native h_rec
  rw [mem_image]
  refine ⟨(A_h, D_h), ?_, h_reconstruct_eq⟩
  rw [chiralHalfChordWitnessBox, mem_filter, mem_product, mem_range, mem_range]
  dsimp only
  exact ⟨⟨h_bounds.1, h_bounds.2⟩, h_d_ge, h_d_lt, h_chiral.1,
    h_pr_nat, h_pq_nat, h_sq_le, h_homog_box⟩

/-- **Theorem 2.3 (`oddFiveupPinchedQRSubfilter_card_le_chiralHalfChordWitnessBox`):**
    Unconditional global `Finset` cardinality bound:
    `(oddFiveupPinchedQRSubfilter a b N).card ≤ (chiralHalfChordWitnessBox a b N).card`. -/
theorem oddFiveupPinchedQRSubfilter_card_le_chiralHalfChordWitnessBox
    {a b N : ℕ} (hEven : N % 2 = 0) :
    (oddFiveupPinchedQRSubfilter a b N).card ≤ (chiralHalfChordWitnessBox a b N).card := by
  have h_sub := oddFiveupPinchedQRSubfilter_subset_image_chiralHalfChordWitnessBox (a := a) (b := b) hEven
  exact Nat.le_trans (card_le_card h_sub) card_image_le

/-- **Theorem 2.4 (`fiveupPinchedQRSubfilter_card_le_one_add_chiralHalfChordWitnessBox`):**
    Global upper bound on `fiveupPinchedQRSubfilter a b N` in terms of the 2D Chiral
    Half-Chord Witness Box:
    `(fiveupPinchedQRSubfilter a b N).card ≤ 1 + (chiralHalfChordWitnessBox a b N).card`. -/
theorem fiveupPinchedQRSubfilter_card_le_one_add_chiralHalfChordWitnessBox
    {a b N : ℕ} (hEven : N % 2 = 0) :
    (fiveupPinchedQRSubfilter a b N).card ≤ 1 + (chiralHalfChordWitnessBox a b N).card :=
  Nat.le_trans
    (fiveupPinchedQRSubfilter_card_le_one_add_odd a b N)
    (Nat.add_le_add_left (oddFiveupPinchedQRSubfilter_card_le_chiralHalfChordWitnessBox hEven) 1)

/-- **Master Theorem 3.1 (`goldbach_from_chiral_half_chord_box_bound`):**
    Welds `Goldbach.one_plus_one_nine_count` (`D19 N`) directly to the 2D Chiral Half-Chord
    Witness Box: for every even `N ≥ K`, if `1 + (chiralHalfChordWitnessBox 9 10 N).card < D19 N`,
    then Binary Goldbach `N = p + q` holds along with the Factorial Lighthouse next prime `p < p_next`. -/
theorem goldbach_from_chiral_half_chord_box_bound :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N →
      1 + (chiralHalfChordWitnessBox 9 10 N).card < D19 N →
      ∃ p q p_next : ℕ,
        Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next ∧ IsPrimeNat p_next := by
  obtain ⟨K, hK4, hWeld⟩ := goldbach_one_plus_one_nine_welded_to_concrete_certificate
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven hBoxLt
  rcases hEven with ⟨k, hk⟩
  have hMod2 : N % 2 = 0 := by omega
  have hSubLe := fiveupPinchedQRSubfilter_card_le_one_add_chiralHalfChordWitnessBox (a := 9) (b := 10) hMod2
  have hMargin : (fiveupPinchedQRSubfilter 9 10 N).card < D19 N :=
    Nat.lt_of_le_of_lt hSubLe hBoxLt
  exact hWeld N hNK ⟨k, hk⟩ hMargin

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.fiveupPinchedQRSubfilter_card_le_one_add_odd
#print axioms WuPaper.ESZerosBridge.oddFiveupPinchedQRSubfilter_card_le_chiralHalfChordWitnessBox
#print axioms WuPaper.ESZerosBridge.fiveupPinchedQRSubfilter_card_le_one_add_chiralHalfChordWitnessBox
#print axioms WuPaper.ESZerosBridge.goldbach_from_chiral_half_chord_box_bound
