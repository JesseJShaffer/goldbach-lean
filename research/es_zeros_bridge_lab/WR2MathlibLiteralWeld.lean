import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.Parity
import WR2ESZerosGoldbachBridge

set_option exponentiation.threshold 10000

namespace WuPaper.ESZerosBridge

/-!
# WR2MathlibLiteralWeld.lean — Direct Mathlib & `WR2ClassicalCertificate` Literal Weld

Links the pure native `WR2ESZerosGoldbachBridge` kernel directly to Mathlib's `Nat.Prime`
and `Even` types used by `WuPaper.ClassicalSlots.one8938` in `WR2ClassicalCertificate.lean`.
-/

/-- Direct conversion from Mathlib's `Nat.Prime p` to our native `IsPrimeNat p`. -/
theorem natPrime_to_isPrimeNat {p : ℕ} (hp : Nat.Prime p) : IsPrimeNat p :=
  ⟨hp.two_le, fun d hd => hp.eq_one_or_self_of_dvd d hd⟩

/-- Exact literal type of `WuPaper.ClassicalSlots.one8938` from `WR2ClassicalCertificate.lean`
    and `research/wu2008/check_classical.py`. -/
def WuLiteralOne8938Statement : Prop :=
  ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
    ∃ p r q : ℕ, Nat.Prime p ∧ (r = 1 ∨ Nat.Prime r) ∧ Nat.Prime q ∧
    N = p + r * q ∧ r ^ 5000 ≤ q ^ 4469

/-- Mathlib-typed `ES_Zeros` `K_2` Pinched / 5UP Cut-Line Portfolio at target `N`. -/
def ESZerosK2PinchedCutlinePortfolioMathlib (N : ℕ) : Prop :=
  (∃ p r q : ℕ, IsFiveUPPinchedSemiprimeWitness N p r q) →
  ∃ card_total card_r1 card_semi pinched_cutline_bound : ℕ,
    card_total ≤ card_r1 + card_semi ∧
    card_semi ≤ pinched_cutline_bound ∧
    pinched_cutline_bound < card_total ∧
    (0 < card_r1 → ∃ p' q' : ℕ, Nat.Prime p' ∧ Nat.Prime q' ∧ N = p' + q')

/-- **Master Theorem (`wr2_literal_one8938_to_binary_goldbach`):**
    Consumes the exact `WuPaper.ClassicalSlots.one8938` statement (`WuLiteralOne8938Statement`),
    routes any `r > 1` witness into `IsFiveUPPinchedSemiprimeWitness N p r q`, applies the
    `Step175` `K_2` Pinched survivor bound, and pairs the binary Goldbach witness `(p, q)`
    with its native Factorial Lighthouse next-prime witness `p_next > p`. -/
theorem wr2_literal_one8938_to_binary_goldbach
    (hWu : WuLiteralOne8938Statement) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ESZerosK2PinchedCutlinePortfolioMathlib N →
      ∃ p q p_next : ℕ,
        Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next ∧ IsPrimeNat p_next := by
  obtain ⟨T, hT512, hMain⟩ := hWu
  refine ⟨T, hT512, ?_⟩
  intro N hN hEven hPortfolio
  obtain ⟨p, r, q, hp, hr_or, hq, hN_eq, hpow⟩ := hMain N hN hEven
  cases hr_or with
  | inl hr1 =>
    rw [hr1, Nat.one_mul] at hN_eq
    obtain ⟨p_next, hp_lt, hp_next⟩ := hasNextPrimeConnection_unconditional p
    exact ⟨p, q, p_next, hp, hq, hN_eq, hp_lt, hp_next⟩
  | inr hr_prime =>
    have hPinched : IsFiveUPPinchedSemiprimeWitness N p r q :=
      wr2_reciprocal_cutline_discriminant N p r q
        (natPrime_to_isPrimeNat hp)
        (natPrime_to_isPrimeNat hr_prime)
        (natPrime_to_isPrimeNat hq)
        hN_eq hpow
    obtain ⟨card_total, card_r1, card_semi, pinched_bound,
            h_part, h_semi_le, h_margin, h_extract⟩ := hPortfolio ⟨p, r, q, hPinched⟩
    have h_card :=
      step175_k2_pinched_cardinality_survivor_lower_bound h_part h_semi_le h_margin
    obtain ⟨p', q', hp', hq', hN'⟩ := h_extract h_card.2.2
    obtain ⟨p_next, hp_lt, hp_next⟩ := hasNextPrimeConnection_unconditional p'
    exact ⟨p', q', p_next, hp', hq', hN', hp_lt, hp_next⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.natPrime_to_isPrimeNat
#print axioms WuPaper.ESZerosBridge.wr2_literal_one8938_to_binary_goldbach
