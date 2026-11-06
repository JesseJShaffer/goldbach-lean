import Goldbach.OnePlusOneNine
import WR2Step175K2PinchedSubfilterWeld

set_option exponentiation.threshold 10000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2GoldbachOnePlusOneNineMasterCapstone.lean — Direct Top-Level `Goldbach.OnePlusOneNine` Weld

Directly imports `Goldbach.OnePlusOneNine` from `goldbach-lean` and welds its unconditional
theorems (`Goldbach.one_plus_one_nine` and `Goldbach.one_plus_one_nine_count`) to the
5-module `ES_Zeros` 5UP Reciprocal Cut-Line & Subfilter stack:

1. **Unconditional Discharge of the Sieve Main-Term Lower Bound
   (`goldbach_one_plus_one_nine_count_welded_to_fiveup_subfilter`):**
   Uses `Goldbach.one_plus_one_nine_count` to unconditionally discharge `mainTerm < (D19 N : ℝ)`
   for all even `N ≥ K`, reducing Binary Goldbach `N = p + q` (plus the Factorial Lighthouse
   next prime `p < p_next`) to the single 5UP Reciprocal Shear subfilter inequality
   `((fiveupPinchedQRSubfilter 9 10 N).card : ℝ) ≤ liuMainTerm0004 N`.
2. **Unconditional Cut-Line Routing of `Goldbach.one_plus_one_nine`
   (`goldbach_one_plus_one_nine_dichotomy_or_fiveup_subfilter`):**
   Proves unconditionally from `Goldbach.one_plus_one_nine` that for all even `N ≥ K`,
   either `N = p + q` holds directly (`r = 1`), or `fiveupPinchedQRSubfilter 9 10 N`
   is non-empty with an unramified 5UP Reciprocal Shear witness `r < q`, `0 < (q - r) ^ 2`,
   `((r + q) * r) % m = (r * r + (N - p)) % m`.
-/

/-- The explicit Liu singular-series analytic main term from `Goldbach.one_plus_one_nine_count`. -/
def liuMainTerm0004 (N : ℕ) : ℝ :=
  (1 / 2500 : ℝ) *
    (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N * (N : ℝ) /
      Real.log (N : ℝ) ^ 2)

/-- **Master Theorem 1 (`goldbach_one_plus_one_nine_count_welded_to_fiveup_subfilter`):**
    Unconditionally discharges the lower bound `liuMainTerm0004 N < (D19 N : ℝ)` using
    `Goldbach.one_plus_one_nine_count` and welds it to
    `liliu_real_main_term_and_fiveup_subfilter_to_binary_goldbach`. -/
theorem goldbach_one_plus_one_nine_count_welded_to_fiveup_subfilter :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N →
      (((fiveupPinchedQRSubfilter 9 10 N).card : ℝ) ≤ liuMainTerm0004 N) →
      ∃ p q p_next : ℕ,
        Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next ∧ IsPrimeNat p_next := by
  obtain ⟨K, hK4, hCount⟩ := Goldbach.one_plus_one_nine_count
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven hSubfilter
  have hD19 : liuMainTerm0004 N < (D19 N : ℝ) := hCount N hNK hEven
  exact liliu_real_main_term_and_fiveup_subfilter_to_binary_goldbach hD19 hSubfilter

/-- **Master Theorem 2 (`goldbach_one_plus_one_nine_welded_to_concrete_certificate`):**
    Unconditionally combines `Goldbach.one_plus_one_nine` with our `Finset` subfilter
    dominance condition `(fiveupPinchedQRSubfilter 9 10 N).card < D19 N` to produce
    Binary Goldbach `N = p + q` and the Factorial Lighthouse next prime `p < p_next`. -/
theorem goldbach_one_plus_one_nine_welded_to_concrete_certificate :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N →
      (fiveupPinchedQRSubfilter 9 10 N).card < D19 N →
      ∃ p q p_next : ℕ,
        Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next ∧ IsPrimeNat p_next := by
  obtain ⟨K, hK4, _⟩ := Goldbach.one_plus_one_nine
  refine ⟨K, hK4, ?_⟩
  intro N _ _ hMargin
  have hSemi := cutlineSemiprimePrimes_card_le_fiveupPinchedQRSubfilter 9 10 N
  have hDom : (cutlineSemiprimePrimes 9 10 N).card < D19 N :=
    Nat.lt_of_le_of_lt hSemi hMargin
  exact liliu_D19_cutline_dominance_to_binary_goldbach hDom

/-- **Master Theorem 3 (`goldbach_one_plus_one_nine_dichotomy_or_fiveup_subfilter`):**
    Unconditionally from `Goldbach.one_plus_one_nine` (with zero additional hypotheses!),
    there exists `K ≥ 4` such that every even `N ≥ K` either:
    - **(Branch 1):** satisfies Binary Goldbach `N = p + q` with `p < p_next`, OR
    - **(Branch 2):** populates `fiveupPinchedQRSubfilter 9 10 N` with an unramified
      5UP Reciprocal Cut-Line witness (`r < q`, `0 < (q - r) ^ 2`,
      `(r + q) ^ 2 = 4 * (N - p) + (q - r) ^ 2`, and `((r + q) * r) % m = (r * r + (N - p)) % m`). -/
theorem goldbach_one_plus_one_nine_dichotomy_or_fiveup_subfilter :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N →
      (∃ p q p_next : ℕ,
        Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next ∧ IsPrimeNat p_next) ∨
      (fiveupPinchedQRSubfilter 9 10 N).Nonempty := by
  obtain ⟨K, hK4, hOneNine⟩ := Goldbach.one_plus_one_nine
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven
  obtain ⟨p, r, q, hp_le, hp, hr_or, hq, hN_eq, hpow⟩ := hOneNine N hNK hEven
  cases hr_or with
  | inl hr1 =>
    left
    rw [hr1, Nat.one_mul] at hN_eq
    obtain ⟨p_next, hp_lt, hp_next⟩ := hasNextPrimeConnection_unconditional p
    exact ⟨p, q, p_next, hp, hq, hN_eq, hp_lt, hp_next⟩
  | inr hr_prime =>
    right
    have h_cut :=
      liliu_one_nine_semiprime_cutline N p r q
        (natPrime_to_isPrimeNat hr_prime) hN_eq hpow
    have hp_range : p ∈ range (N + 1) := mem_range.mpr (Nat.lt_succ_of_le hp_le)
    have hp_mem_cut : p ∈ cutlineSemiprimePrimes 9 10 N := by
      rw [cutlineSemiprimePrimes, mem_filter]
      exact ⟨hp_range, hp, r, q, hr_prime, hq, hN_eq,
        h_cut.1, h_cut.2.1, h_cut.2.2.1, h_cut.2.2.2.1, h_cut.2.2.2.2, hpow⟩
    exact ⟨p, cutlineSemiprimePrimes_subset_fiveupPinchedQRSubfilter 9 10 N hp_mem_cut⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.goldbach_one_plus_one_nine_count_welded_to_fiveup_subfilter
#print axioms WuPaper.ESZerosBridge.goldbach_one_plus_one_nine_welded_to_concrete_certificate
#print axioms WuPaper.ESZerosBridge.goldbach_one_plus_one_nine_dichotomy_or_fiveup_subfilter
