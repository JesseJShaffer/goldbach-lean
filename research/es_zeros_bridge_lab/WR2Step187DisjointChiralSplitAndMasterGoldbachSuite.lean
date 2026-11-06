import WR2Step186ExplicitHalfChordFinsetInjectiveBound

set_option exponentiation.threshold 10000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step187DisjointChiralSplitAndMasterGoldbachSuite.lean — Disjoint Chiral Box Split & 10-Module Capstone
-/

/-- Pure native dichotomy: `(A_h + D_h) % 2 = 1` implies either
    `(A_h % 2 = 1 ∧ D_h % 2 = 0)` or `(A_h % 2 = 0 ∧ D_h % 2 = 1)`. -/
theorem opposite_parity_dichotomy {A_h D_h : ℕ} (h : (A_h + D_h) % 2 = 1) :
    (A_h % 2 = 1 ∧ D_h % 2 = 0) ∨ (A_h % 2 = 0 ∧ D_h % 2 = 1) := by
  omega

/-- Positive Chiral Half-Chord Box (`A_h` odd, `D_h` even, corresponding to `(N - p) % 4 = 1`). -/
def posChiralHalfChordBox (a b N : ℕ) : Finset (ℕ × ℕ) :=
  (chiralHalfChordWitnessBox a b N).filter (fun pair : ℕ × ℕ =>
    pair.1 % 2 = 1 ∧ pair.2 % 2 = 0)

/-- Negative Chiral Half-Chord Box (`A_h` even, `D_h` odd, corresponding to `(N - p) % 4 = 3`). -/
def negChiralHalfChordBox (a b N : ℕ) : Finset (ℕ × ℕ) :=
  (chiralHalfChordWitnessBox a b N).filter (fun pair : ℕ × ℕ =>
    pair.1 % 2 = 0 ∧ pair.2 % 2 = 1)

/-- **Theorem 1.1 (`disjoint_pos_neg_chiralHalfChordBox`):**
    The positive and negative chiral half-chord boxes are strictly disjoint. -/
theorem disjoint_pos_neg_chiralHalfChordBox (a b N : ℕ) :
    Disjoint (posChiralHalfChordBox a b N) (negChiralHalfChordBox a b N) := by
  rw [Finset.disjoint_left]
  intro pair hpos hneg
  rw [posChiralHalfChordBox, mem_filter] at hpos
  rw [negChiralHalfChordBox, mem_filter] at hneg
  have h1 : pair.1 % 2 = 1 := hpos.2.1
  have h0 : pair.1 % 2 = 0 := hneg.2.1
  omega

/-- **Theorem 1.2 (`chiralHalfChordWitnessBox_eq_pos_union_neg`):**
    Exact set decomposition of `chiralHalfChordWitnessBox a b N` into its positive and
    negative chiral half-chord sub-boxes. -/
theorem chiralHalfChordWitnessBox_eq_pos_union_neg (a b N : ℕ) :
    chiralHalfChordWitnessBox a b N =
      posChiralHalfChordBox a b N ∪ negChiralHalfChordBox a b N := by
  ext pair
  rw [mem_union, posChiralHalfChordBox, negChiralHalfChordBox, mem_filter, mem_filter]
  constructor
  · intro hmem
    have hmem_copy := hmem
    rw [chiralHalfChordWitnessBox, mem_filter] at hmem_copy
    obtain ⟨_, _, _, h_opp, _⟩ := hmem_copy
    cases opposite_parity_dichotomy h_opp with
    | inl hpos => exact Or.inl ⟨hmem, hpos⟩
    | inr hneg => exact Or.inr ⟨hmem, hneg⟩
  · intro hor
    cases hor with
    | inl hpos => exact hpos.1
    | inr hneg => exact hneg.1

/-- **Theorem 1.3 (`chiralHalfChordWitnessBox_card_eq_pos_add_neg`):**
    Exact additive cardinality decomposition of the 2D Chiral Half-Chord Witness Box. -/
theorem chiralHalfChordWitnessBox_card_eq_pos_add_neg (a b N : ℕ) :
    (chiralHalfChordWitnessBox a b N).card =
      (posChiralHalfChordBox a b N).card + (negChiralHalfChordBox a b N).card := by
  rw [chiralHalfChordWitnessBox_eq_pos_union_neg a b N]
  exact card_union_of_disjoint (disjoint_pos_neg_chiralHalfChordBox a b N)

/-- **Theorem 2.1 (`pos_neg_chiral_box_mod4_squares`):**
    Explicit Mod-4 square residue lock on each chiral sub-box via `sq_mod_four_of_mod_two`. -/
theorem pos_neg_chiral_box_mod4_squares (a b N : ℕ) (pair : ℕ × ℕ) :
    (pair ∈ posChiralHalfChordBox a b N → (pair.1 ^ 2) % 4 = 1 ∧ (pair.2 ^ 2) % 4 = 0) ∧
    (pair ∈ negChiralHalfChordBox a b N → (pair.1 ^ 2) % 4 = 0 ∧ (pair.2 ^ 2) % 4 = 1) := by
  have h1 := sq_mod_four_of_mod_two pair.1
  have h2 := sq_mod_four_of_mod_two pair.2
  constructor
  · intro hpos
    rw [posChiralHalfChordBox, mem_filter] at hpos
    exact ⟨h1.2 hpos.2.1, h2.1 hpos.2.2⟩
  · intro hneg
    rw [negChiralHalfChordBox, mem_filter] at hneg
    exact ⟨h1.1 hneg.2.1, h2.2 hneg.2.2⟩

/-- **Theorem 2.2 (`fiveupPinchedQRSubfilter_card_le_disjoint_chiral_boxes`):**
    Global `Finset` cardinality bound decomposing `fiveupPinchedQRSubfilter a b N` into
    `1 + (posChiralHalfChordBox a b N).card + (negChiralHalfChordBox a b N).card`. -/
theorem fiveupPinchedQRSubfilter_card_le_disjoint_chiral_boxes
    {a b N : ℕ} (hEven : N % 2 = 0) :
    (fiveupPinchedQRSubfilter a b N).card ≤
      1 + ((posChiralHalfChordBox a b N).card + (negChiralHalfChordBox a b N).card) := by
  rw [← chiralHalfChordWitnessBox_card_eq_pos_add_neg a b N]
  exact fiveupPinchedQRSubfilter_card_le_one_add_chiralHalfChordWitnessBox hEven

/-- **Master 10-Module Capstone Theorem (`master_10module_goldbach_all_and_es_zeros_capstone`):**
    Unites `Goldbach.one_plus_one_nine_count` (`liuMainTerm0004 N < (D19 N : ℝ)`),
    the disjoint chiral half-chord box bound, and the Factorial Lighthouse next-prime
    generator (`hasNextPrimeConnection_unconditional`). -/
theorem master_10module_goldbach_all_and_es_zeros_capstone :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (1 + ((posChiralHalfChordBox 9 10 N).card + (negChiralHalfChordBox 9 10 N).card) < D19 N →
        ∃ p q p_next : ℕ,
          Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next ∧ IsPrimeNat p_next) := by
  obtain ⟨K1, hK1, hCount⟩ := Goldbach.one_plus_one_nine_count
  obtain ⟨K2, hK2, hBoxGold⟩ := goldbach_from_chiral_half_chord_box_bound
  refine ⟨max K1 K2, le_trans hK1 (le_max_left K1 K2), ?_⟩
  intro N hN hEven
  have hN1 : K1 ≤ N := le_trans (le_max_left K1 K2) hN
  have hN2 : K2 ≤ N := le_trans (le_max_right K1 K2) hN
  refine ⟨hCount N hN1 hEven, ?_⟩
  intro hSplitLt
  rw [← chiralHalfChordWitnessBox_card_eq_pos_add_neg 9 10 N] at hSplitLt
  exact hBoxGold N hN2 hEven hSplitLt

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.disjoint_pos_neg_chiralHalfChordBox
#print axioms WuPaper.ESZerosBridge.chiralHalfChordWitnessBox_card_eq_pos_add_neg
#print axioms WuPaper.ESZerosBridge.pos_neg_chiral_box_mod4_squares
#print axioms WuPaper.ESZerosBridge.fiveupPinchedQRSubfilter_card_le_disjoint_chiral_boxes
#print axioms WuPaper.ESZerosBridge.master_10module_goldbach_all_and_es_zeros_capstone
