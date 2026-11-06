import Mathlib.Data.Finset.Card
import MathlibNt.SieveTheory.LiLiuGoldbachOnePlusOneNineFinite
import WR2ESZerosTimingChainClosure

set_option exponentiation.threshold 10000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2FinsetPartitionDischarge.lean — Direct `goldbach-lean` Link & `Finset` Partition Discharge

Imports `MathlibNt.SieveTheory.LiLiuGoldbachOnePlusOneNineFinite` directly from `goldbach-lean`
and proves unconditionally over `Finset ℕ`:

1. **General Pinched `Finset` Decomposition (`pinchedRepresentedPrimes_card_le`):**
   For any exponents `a + (d + 1) = b` (including Wu `1+1.8938` `4469, 5000`, Wu `1+1.894`
   `447, 500`, and Li–Liu `1+1.9` `9, 10`), the set of represented primes decomposes into
   `trueGoldbachPrimes N` (`r = 1`) and `cutlineSemiprimePrimes a b N` (`r < q`, `0 < (q-r)^2`,
   `(r+q)^2 = 4(N-p) + (q-r)^2`), discharging `partition_cover` unconditionally.
2. **Direct `goldbach-lean` `D19 N` Decomposition (`liliu_D19_le_trueGoldbach_add_cutlineSemiprime`):**
   Proves directly on `goldbach-lean`'s `D19 N` that
   `D19 N ≤ (trueGoldbachPrimes N).card + (cutlineSemiprimePrimes 9 10 N).card`.
3. **Unconditional `Finset` Witness Extractor (`extract_goldbach_of_trueGoldbachPrimes_pos`):**
   Discharges `extract_goldbach_pair` unconditionally from `0 < (trueGoldbachPrimes N).card`.
4. **Automatic Construction of `ConcreteFiveUPCutlineCertificate N` (`mkConcreteFiveUPCutlineCertificate`):**
   Reduces `ConcreteFiveUPCutlineCertificate N` to the single 5UP Cut-Line contraction bound
   `(cutlineSemiprimePrimes a b N).card < (pinchedRepresentedPrimes a b N).card`.
-/

/-- General `(a, b)`-pinched prime representation predicate (covers Wu `4469, 5000` and Li–Liu `9, 10`). -/
def IsPinchedRepresentation (a b N p : ℕ) : Prop :=
  p.Prime ∧ ∃ r q : ℕ, (r = 1 ∨ r.Prime) ∧ q.Prime ∧ N = p + r * q ∧ r ^ b ≤ q ^ a

/-- Finite set of primes `p ≤ N` admitting an `(a, b)`-pinched representation `N = p + r * q`. -/
def pinchedRepresentedPrimes (a b N : ℕ) : Finset ℕ :=
  (range (N + 1)).filter (IsPinchedRepresentation a b N)

/-- Finite set of true Binary Goldbach primes `p ≤ N` (`r = 1`, `N = p + q` with `p, q` prime). -/
def trueGoldbachPrimes (N : ℕ) : Finset ℕ :=
  (range (N + 1)).filter (fun p : ℕ => p.Prime ∧ ∃ q : ℕ, q.Prime ∧ N = p + q)

/-- Finite set of primes `p ≤ N` whose `(a, b)`-pinched representation has `r > 1`,
    forced by `ES_Zeros` onto the unramified 5UP Reciprocal Cut-Line:
    `r < q`, `r ≠ q`, `r * r < r * q`, `0 < (q - r) ^ 2`, and `(r + q) ^ 2 = 4 * (N - p) + (q - r) ^ 2`. -/
def cutlineSemiprimePrimes (a b N : ℕ) : Finset ℕ :=
  (range (N + 1)).filter (fun p : ℕ =>
    p.Prime ∧ ∃ r q : ℕ,
      r.Prime ∧ q.Prime ∧ N = p + r * q ∧
      r < q ∧ r ≠ q ∧ r * r < r * q ∧
      0 < (q - r) ^ 2 ∧ (r + q) ^ 2 = 4 * (N - p) + (q - r) ^ 2 ∧ r ^ b ≤ q ^ a)

/-- **Theorem 1.1 (`pinchedRepresentedPrimes_subset_union`):**
    For any exponents `a + (d + 1) = b`, every `p ∈ pinchedRepresentedPrimes a b N`
    belongs to `trueGoldbachPrimes N ∪ cutlineSemiprimePrimes a b N`. -/
theorem pinchedRepresentedPrimes_subset_union
    (a d b N : ℕ) (h_exp : a + (d + 1) = b) :
    pinchedRepresentedPrimes a b N ⊆ trueGoldbachPrimes N ∪ cutlineSemiprimePrimes a b N := by
  intro p hp
  rw [mem_union, trueGoldbachPrimes, cutlineSemiprimePrimes, mem_filter, mem_filter]
  rw [pinchedRepresentedPrimes, mem_filter] at hp
  obtain ⟨hp_range, hp_prime, r, q, hr_or, hq_prime, hN_eq, hpow⟩ := hp
  cases hr_or with
  | inl hr1 =>
    left
    rw [hr1, Nat.one_mul] at hN_eq
    exact ⟨hp_range, hp_prime, q, hq_prime, hN_eq⟩
  | inr hr_prime =>
    right
    have h_cut :=
      universal_pinch_strict_lt_and_cutline N p r q a d b
        (natPrime_to_isPrimeNat hr_prime) hN_eq h_exp hpow
    exact ⟨hp_range, hp_prime, r, q, hr_prime, hq_prime, hN_eq,
      h_cut.1, h_cut.2.1, h_cut.2.2.1, h_cut.2.2.2.1, h_cut.2.2.2.2, hpow⟩

/-- **Theorem 1.2 (`pinchedRepresentedPrimes_card_le`):**
    Unconditional discharge of `partition_cover`:
    `(pinchedRepresentedPrimes a b N).card ≤ (trueGoldbachPrimes N).card + (cutlineSemiprimePrimes a b N).card`. -/
theorem pinchedRepresentedPrimes_card_le
    (a d b N : ℕ) (h_exp : a + (d + 1) = b) :
    (pinchedRepresentedPrimes a b N).card ≤
      (trueGoldbachPrimes N).card + (cutlineSemiprimePrimes a b N).card := by
  have h_sub := pinchedRepresentedPrimes_subset_union a d b N h_exp
  exact Nat.le_trans (card_le_card h_sub) (card_union_le _ _)

/-- **Theorem 2.1 (`liliu_D19_le_trueGoldbach_add_cutlineSemiprime`):**
    Direct link to `goldbach-lean`'s `D19 N` (`onePlusOneNineRepresentedPrimes N`):
    proves that `D19 N ≤ (trueGoldbachPrimes N).card + (cutlineSemiprimePrimes 9 10 N).card`. -/
theorem liliu_D19_le_trueGoldbach_add_cutlineSemiprime (N : ℕ) :
    D19 N ≤ (trueGoldbachPrimes N).card + (cutlineSemiprimePrimes 9 10 N).card := by
  have h_eq : onePlusOneNineRepresentedPrimes N = pinchedRepresentedPrimes 9 10 N := rfl
  unfold D19
  rw [h_eq]
  exact pinchedRepresentedPrimes_card_le 9 0 10 N rfl

/-- **Theorem 3.1 (`extract_goldbach_of_trueGoldbachPrimes_pos`):**
    Unconditional discharge of `extract_goldbach_pair`:
    if `0 < (trueGoldbachPrimes N).card`, then `∃ p' q' : ℕ, Nat.Prime p' ∧ Nat.Prime q' ∧ N = p' + q'`. -/
theorem extract_goldbach_of_trueGoldbachPrimes_pos
    {N : ℕ} (hpos : 0 < (trueGoldbachPrimes N).card) :
    ∃ p' q' : ℕ, Nat.Prime p' ∧ Nat.Prime q' ∧ N = p' + q' := by
  obtain ⟨p', hp'⟩ := card_pos.mp hpos
  rw [trueGoldbachPrimes, mem_filter] at hp'
  obtain ⟨_, hp'_prime, q', hq'_prime, hN_eq⟩ := hp'
  exact ⟨p', q', hp'_prime, hq'_prime, hN_eq⟩

/-- **Theorem 4.1 (`mkConcreteFiveUPCutlineCertificate`):**
    Automatically builds a `ConcreteFiveUPCutlineCertificate N` from the single
    cardinality inequality `(cutlineSemiprimePrimes a b N).card < (pinchedRepresentedPrimes a b N).card`. -/
def mkConcreteFiveUPCutlineCertificate
    (a d b N : ℕ) (h_exp : a + (d + 1) = b)
    (h_margin : (cutlineSemiprimePrimes a b N).card < (pinchedRepresentedPrimes a b N).card) :
    ConcreteFiveUPCutlineCertificate N where
  card_total := (pinchedRepresentedPrimes a b N).card
  card_r1 := (trueGoldbachPrimes N).card
  card_semi := (cutlineSemiprimePrimes a b N).card
  pinched_cutline_bound := (cutlineSemiprimePrimes a b N).card
  partition_cover := pinchedRepresentedPrimes_card_le a d b N h_exp
  involution_qr_contraction := Nat.le_refl _
  strict_survivor_margin := h_margin
  extract_goldbach_pair := extract_goldbach_of_trueGoldbachPrimes_pos

/-- **Theorem 4.2 (`liliu_D19_cutline_dominance_to_binary_goldbach`):**
    Direct theorem over `goldbach-lean`'s `D19 N`: whenever the 5UP Reciprocal Cut-Line
    semiprime subset has strictly smaller cardinality than `D19 N`, Binary Goldbach
    `N = p + q` holds at `N` along with the Factorial Lighthouse next prime `p < p_next`. -/
theorem liliu_D19_cutline_dominance_to_binary_goldbach
    {N : ℕ} (h_dom : (cutlineSemiprimePrimes 9 10 N).card < D19 N) :
    ∃ p q p_next : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next ∧ IsPrimeNat p_next := by
  have h_part := liliu_D19_le_trueGoldbach_add_cutlineSemiprime N
  have h_pos : 0 < (trueGoldbachPrimes N).card := by omega
  obtain ⟨p, q, hp, hq, hN_eq⟩ := extract_goldbach_of_trueGoldbachPrimes_pos h_pos
  obtain ⟨p_next, hp_lt, hp_next⟩ := hasNextPrimeConnection_unconditional p
  exact ⟨p, q, p_next, hp, hq, hN_eq, hp_lt, hp_next⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.pinchedRepresentedPrimes_card_le
#print axioms WuPaper.ESZerosBridge.liliu_D19_le_trueGoldbach_add_cutlineSemiprime
#print axioms WuPaper.ESZerosBridge.extract_goldbach_of_trueGoldbachPrimes_pos
#print axioms WuPaper.ESZerosBridge.liliu_D19_cutline_dominance_to_binary_goldbach
