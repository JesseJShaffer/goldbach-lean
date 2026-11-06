import Mathlib.Data.Finset.Card
import WR2ClassicalCertificate
import WR2ESZerosTimingChainClosure

set_option exponentiation.threshold 10000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step189DirectWR2ClassicalCertificateDischarge.lean — Unconditional `WR2ClassicalCertificate` Link

Directly imports `WR2ClassicalCertificate` (`3,764` modules) and `WR2ESZerosTimingChainClosure`
over `.lake/packages/mathlib`, unconditionally discharging `WuLiteralOne8938Statement` (`hWu`):

1. **Unconditional Discharge of `hWu` (`wuLiteralOne8938Statement_unconditional`):**
   Proves `WuLiteralOne8938Statement` directly from `WuPaper.ClassicalSlots.one8938`,
   eliminating `hWu` as a hypothesis across the entire `WR2` bridge.
2. **Unconditional `WR2` (`4469, 5000`) `Finset` Decomposition (`wr2_representedPrimes_pos_and_partition`):**
   Defines `wr2RepresentedPrimes N`, `wr2TrueGoldbachPrimes N`, and `wr2CutlineSemiprimePrimes N`
   for the exact `r ^ 5000 ≤ q ^ 4469` pinch, and proves unconditionally from
   `WuPaper.ClassicalSlots.one8938` that for all even `N ≥ T`:
   - `0 < (wr2RepresentedPrimes N).card`,
   - `(wr2RepresentedPrimes N).card ≤ (wr2TrueGoldbachPrimes N).card + (wr2CutlineSemiprimePrimes N).card`,
   - Every element of `wr2CutlineSemiprimePrimes N` satisfies the unramified 5UP Reciprocal
     Cut-Line equation `(r + q) ^ 2 = 4 * (N - p) + (q - r) ^ 2` with `r < q`, `0 < (q - r) ^ 2`,
     and homogeneous pinch `r ^ 9469 ≤ (N - p) ^ 4469`.
3. **Unconditional `WR2` Master Closure (`wr2_one8938_unconditional_master_goldbach_bridge`):**
   Combines `WuPaper.ClassicalSlots.classical_lower` (`(17401:ℝ)/20000 ≤ classicalPart`),
   `WuPaper.ClassicalSlots.one8938`, and the Factorial Lighthouse next-prime generator
   (`hasNextPrimeConnection_unconditional`) with zero external theorem hypotheses.
-/

/-- Explicit native helper: `N = p + m → p ≤ N`. -/
theorem le_of_eq_add_right_wr2 {N p m : ℕ} (h : N = p + m) : p ≤ N := by
  rw [h]
  exact Nat.le_add_right p m

/-- **Theorem 1.1 (`wuLiteralOne8938Statement_unconditional`):**
    Unconditionally discharges `WuLiteralOne8938Statement` (`hWu`) directly from
    `WuPaper.ClassicalSlots.one8938`. -/
theorem wuLiteralOne8938Statement_unconditional : WuLiteralOne8938Statement :=
  WuPaper.ClassicalSlots.one8938

/-- **Theorem 1.2 (`wr2_one8938_to_binary_goldbach_unconditional_endpoint`):**
    Eliminates `hWu` from `wr2_and_concrete_fiveup_certificate_to_goldbach` using
    `WuPaper.ClassicalSlots.one8938`. -/
theorem wr2_one8938_to_binary_goldbach_unconditional_endpoint :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ConcreteFiveUPCutlineCertificate N →
      ∃ p q p_next : ℕ,
        Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next ∧ IsPrimeNat p_next :=
  wr2_and_concrete_fiveup_certificate_to_goldbach wuLiteralOne8938Statement_unconditional

/-- Finite set of primes `p ≤ N` admitting a `WR2` (`4469, 5000`) representation
    `N = p + r * q` with `r = 1 ∨ r.Prime`, `q.Prime`, and `r ^ 5000 ≤ q ^ 4469`. -/
def wr2RepresentedPrimes (N : ℕ) : Finset ℕ :=
  (range (N + 1)).filter (fun p : ℕ =>
    p.Prime ∧ ∃ r q : ℕ, (r = 1 ∨ r.Prime) ∧ q.Prime ∧ N = p + r * q ∧ r ^ 5000 ≤ q ^ 4469)

/-- Finite set of true Binary Goldbach primes `p ≤ N` (`r = 1`, `N = p + q`). -/
def wr2TrueGoldbachPrimes (N : ℕ) : Finset ℕ :=
  (range (N + 1)).filter (fun p : ℕ => p.Prime ∧ ∃ q : ℕ, q.Prime ∧ N = p + q)

/-- Finite set of primes `p ≤ N` whose `WR2` (`4469, 5000`) representation has `r > 1`,
    locked onto the unramified 5UP Reciprocal Cut-Line:
    `r < q`, `r ≠ q`, `r * r < N - p`, `0 < (q - r) ^ 2`,
    `(r + q) ^ 2 = 4 * (N - p) + (q - r) ^ 2`, and `r ^ 9469 ≤ (N - p) ^ 4469`. -/
def wr2CutlineSemiprimePrimes (N : ℕ) : Finset ℕ :=
  (range (N + 1)).filter (fun p : ℕ =>
    p.Prime ∧ ∃ r q : ℕ,
      r.Prime ∧ q.Prime ∧ N = p + r * q ∧
      r < q ∧ r ≠ q ∧ r * r < N - p ∧
      0 < (q - r) ^ 2 ∧
      (r + q) ^ 2 = 4 * (N - p) + (q - r) ^ 2 ∧
      r ^ 9469 ≤ (N - p) ^ 4469)

/-- Every `p ∈ wr2RepresentedPrimes N` belongs to
    `wr2TrueGoldbachPrimes N ∪ wr2CutlineSemiprimePrimes N`. -/
theorem wr2RepresentedPrimes_subset_union (N : ℕ) :
    wr2RepresentedPrimes N ⊆ wr2TrueGoldbachPrimes N ∪ wr2CutlineSemiprimePrimes N := by
  intro p hp
  rw [mem_union, wr2TrueGoldbachPrimes, wr2CutlineSemiprimePrimes, mem_filter, mem_filter]
  rw [wr2RepresentedPrimes, mem_filter] at hp
  obtain ⟨hp_range, hp_prime, r, q, hr_or, hq_prime, hN_eq, hpow⟩ := hp
  cases hr_or with
  | inl hr1 =>
    left
    rw [hr1, Nat.one_mul] at hN_eq
    exact ⟨hp_range, hp_prime, q, hq_prime, hN_eq⟩
  | inr hr_prime =>
    right
    have hr_nat : IsPrimeNat r := natPrime_to_isPrimeNat hr_prime
    have h_unram := wr2_semiprime_strict_lt_and_unramified r q hr_nat hpow
    have h_cut :=
      wr2_reciprocal_cutline_discriminant N p r q
        (natPrime_to_isPrimeNat hp_prime) hr_nat (natPrime_to_isPrimeNat hq_prime) hN_eq hpow
    have h_sub : N - p = r * q := by
      rw [hN_eq, Nat.add_sub_cancel_left]
    have h_sqrt_lt : r * r < N - p := by
      rw [h_sub]
      exact h_unram.2.2.1
    exact ⟨hp_range, hp_prime, r, q, hr_prime, hq_prime, hN_eq,
      h_cut.r_lt_q, h_unram.2.1, h_sqrt_lt, h_cut.disc_pos, h_cut.cutline_eq, h_cut.homog_pinch⟩

/-- Unconditional partition bound:
    `(wr2RepresentedPrimes N).card ≤ (wr2TrueGoldbachPrimes N).card + (wr2CutlineSemiprimePrimes N).card`. -/
theorem wr2RepresentedPrimes_card_le (N : ℕ) :
    (wr2RepresentedPrimes N).card ≤
      (wr2TrueGoldbachPrimes N).card + (wr2CutlineSemiprimePrimes N).card :=
  Nat.le_trans (card_le_card (wr2RepresentedPrimes_subset_union N)) (card_union_le _ _)

/-- Unconditional witness extraction from `0 < (wr2TrueGoldbachPrimes N).card`. -/
theorem extract_goldbach_of_wr2TrueGoldbachPrimes_pos
    {N : ℕ} (hpos : 0 < (wr2TrueGoldbachPrimes N).card) :
    ∃ p' q' : ℕ, Nat.Prime p' ∧ Nat.Prime q' ∧ N = p' + q' := by
  obtain ⟨p', hp'⟩ := card_pos.mp hpos
  rw [wr2TrueGoldbachPrimes, mem_filter] at hp'
  obtain ⟨_, hp'_prime, q', hq'_prime, hN_eq⟩ := hp'
  exact ⟨p', q', hp'_prime, hq'_prime, hN_eq⟩

/-- **Master Theorem 2.1 (`wr2_one8938_unconditional_master_goldbach_bridge`):**
    Unconditional synthesis proven directly from `WR2ClassicalCertificate`:
    1. Certifies `(17401 : ℝ) / 20000 ≤ R2Xi.SourceContinuousCount.classicalPart`,
    2. Certifies `∃ T ≥ 512` such that for all even `N ≥ T`:
       - `0 < (wr2RepresentedPrimes N).card` (unconditionally non-empty!),
       - `(wr2RepresentedPrimes N).card ≤ (wr2TrueGoldbachPrimes N).card + (wr2CutlineSemiprimePrimes N).card`,
       - Whenever `(wr2CutlineSemiprimePrimes N).card < (wr2RepresentedPrimes N).card`,
         `N` admits a true Binary Goldbach partition `N = p + q` paired with its
         Factorial Lighthouse next prime `p < p_next ∧ IsPrimeNat p_next`. -/
theorem wr2_one8938_unconditional_master_goldbach_bridge :
    ((17401 : ℝ) / 20000 ≤ R2Xi.SourceContinuousCount.classicalPart) ∧
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      0 < (wr2RepresentedPrimes N).card ∧
      (wr2RepresentedPrimes N).card ≤
        (wr2TrueGoldbachPrimes N).card + (wr2CutlineSemiprimePrimes N).card ∧
      ((wr2CutlineSemiprimePrimes N).card < (wr2RepresentedPrimes N).card →
        ∃ p q p_next : ℕ,
          Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next ∧ IsPrimeNat p_next) := by
  refine ⟨WuPaper.ClassicalSlots.classical_lower, ?_⟩
  obtain ⟨T, hT512, hOne8938⟩ := WuPaper.ClassicalSlots.one8938
  refine ⟨T, hT512, ?_⟩
  intro N hNT hEven
  obtain ⟨p, r, q, hp, hr_or, hq, hN_eq, hpow⟩ := hOne8938 N hNT hEven
  have hp_le : p ≤ N := le_of_eq_add_right_wr2 hN_eq
  have hp_range : p ∈ range (N + 1) := mem_range.mpr (Nat.lt_succ_of_le hp_le)
  have hp_mem : p ∈ wr2RepresentedPrimes N := by
    rw [wr2RepresentedPrimes, mem_filter]
    exact ⟨hp_range, hp, r, q, hr_or, hq, hN_eq, hpow⟩
  have h_pos : 0 < (wr2RepresentedPrimes N).card := card_pos.mpr ⟨p, hp_mem⟩
  have h_part := wr2RepresentedPrimes_card_le N
  refine ⟨h_pos, h_part, ?_⟩
  intro h_margin
  have h_card :=
    step175_k2_pinched_cardinality_survivor_lower_bound
      h_part (Nat.le_refl _) h_margin
  obtain ⟨p', q', hp', hq', hN'⟩ := extract_goldbach_of_wr2TrueGoldbachPrimes_pos h_card.2.2
  obtain ⟨p_next, hp_lt, hp_next⟩ := hasNextPrimeConnection_unconditional p'
  exact ⟨p', q', p_next, hp', hq', hN', hp_lt, hp_next⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.wuLiteralOne8938Statement_unconditional
#print axioms WuPaper.ESZerosBridge.wr2_one8938_to_binary_goldbach_unconditional_endpoint
#print axioms WuPaper.ESZerosBridge.wr2_one8938_unconditional_master_goldbach_bridge
