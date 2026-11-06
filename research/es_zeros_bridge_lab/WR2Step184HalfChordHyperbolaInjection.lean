import Goldbach.All
import WR2GoldbachOnePlusOneNineMasterCapstone

set_option exponentiation.threshold 10000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step184HalfChordHyperbolaInjection.lean — 5UP Half-Chord Hyperbola & Injective Witness Map

Imports `Goldbach.All` (both Chen `1+2` and Li–Liu `1+1.9`) and proves the `ES_Zeros`
Half-Chord Hyperbola decomposition and injective witness reconstruction for
`fiveupPinchedQRSubfilter`:

1. **Odd Semiprime Factor Parity (`mul_mod_two_eq_one_iff`):**
   Proves that for even `N` and odd prime `p`, `N = p + r * q` forces `r % 2 = 1`
   and `q % 2 = 1`.
2. **Exact Half-Chord Hyperbola Identity (`half_chord_hyperbola_identity`):**
   For any odd semiprime factors `r < q`, the integer half-chords
   `A_h = (q + r) / 2` and `Δ_h = (q - r) / 2` satisfy `1 ≤ Δ_h`,
   `r = A_h - Δ_h`, `q = A_h + Δ_h`, and `A_h ^ 2 = (N - p) + Δ_h ^ 2`.
3. **Injective Reconstruction of `p` from `(A_h, Δ_h)` (`half_chord_uniquely_determines_p`):**
   Proves that `p + A_h ^ 2 = N + Δ_h ^ 2` and `p = (N + Δ_h ^ 2) - A_h ^ 2`, so distinct
   candidate primes `p₁ ≠ p₂` cannot collide on the same half-chord pair `(A_h, Δ_h)`.
-/

/-- If `(r * q) % 2 = 1`, then both `r` and `q` are odd (`r % 2 = 1 ∧ q % 2 = 1`). -/
theorem mul_mod_two_eq_one_iff {r q : ℕ} (h : (r * q) % 2 = 1) :
    r % 2 = 1 ∧ q % 2 = 1 := by
  have h_mul : ((r % 2) * (q % 2)) % 2 = 1 := by
    rw [← Nat.mul_mod]
    exact h
  if hr0 : r % 2 = 0 then
    rw [hr0, Nat.zero_mul] at h_mul
    omega
  else if hq0 : q % 2 = 0 then
    rw [hq0, Nat.mul_zero] at h_mul
    omega
  else
    omega

/-- Pure native proof of the half-chord hyperbolic identity `(r + d) * (r + d) = r * (r + 2 * d) + d * d`. -/
theorem half_chord_hyperbola_add (r d : ℕ) :
    (r + d) * (r + d) = r * (r + 2 * d) + d * d := by
  have h1 : (r + d) * (r + d) = (r * r + r * d) + (d * r + d * d) := by
    rw [Nat.right_distrib r d (r + d)]
    rw [Nat.left_distrib r r d]
    rw [Nat.left_distrib d r d]
  have h2 : d * r = r * d := Nat.mul_comm d r
  have h3 : r * (r + 2 * d) = r * r + 2 * (r * d) := by
    rw [Nat.left_distrib r r (2 * d)]
    rw [← Nat.mul_assoc r 2 d, Nat.mul_comm r 2, Nat.mul_assoc 2 r d]
  omega

/-- **Theorem 1.1 (`half_chord_hyperbola_identity`):**
    For any odd prime factors `r < q` (`r % 2 = 1`, `q % 2 = 1`) with `N = p + r * q`,
    the integer half-chords `A_h = (q + r) / 2` and `Δ_h = (q - r) / 2` satisfy:
    1. `1 ≤ Δ_h` and `Δ_h < A_h`,
    2. `A_h - Δ_h = r` and `A_h + Δ_h = q`,
    3. `A_h ^ 2 = (N - p) + Δ_h ^ 2` (exact 5UP Half-Chord Hyperbola), and
    4. `p + A_h ^ 2 = N + Δ_h ^ 2` (exact linear reconstruction of `p`). -/
theorem half_chord_hyperbola_identity
    {N p r q : ℕ} (hN : N = p + r * q) (h_lt : r < q)
    (hr_odd : r % 2 = 1) (hq_odd : q % 2 = 1) :
    let A_h := (q + r) / 2
    let D_h := (q - r) / 2
    1 ≤ D_h ∧
    D_h < A_h ∧
    A_h - D_h = r ∧
    A_h + D_h = q ∧
    A_h ^ 2 = (N - p) + D_h ^ 2 ∧
    p + A_h ^ 2 = N + D_h ^ 2 := by
  dsimp only
  have h_d_ge : 1 ≤ (q - r) / 2 := by omega
  have h_d_lt : (q - r) / 2 < (q + r) / 2 := by omega
  have h_sub_r : (q + r) / 2 - (q - r) / 2 = r := by omega
  have h_add_q : (q + r) / 2 + (q - r) / 2 = q := by omega
  have h_a_eq : (q + r) / 2 = r + (q - r) / 2 := by omega
  have h_q_eq : q = r + 2 * ((q - r) / 2) := by omega
  have h_N_sub : N - p = r * q := by
    rw [hN, Nat.add_sub_cancel_left]
  have h_hyp : ((q + r) / 2) ^ 2 = (N - p) + ((q - r) / 2) ^ 2 := by
    rw [nat_sq_eq_mul ((q + r) / 2), nat_sq_eq_mul ((q - r) / 2), h_N_sub]
    have h_id := half_chord_hyperbola_add r ((q - r) / 2)
    rw [← h_a_eq, ← h_q_eq] at h_id
    exact h_id
  have h_rec : p + ((q + r) / 2) ^ 2 = N + ((q - r) / 2) ^ 2 := by
    omega
  exact ⟨h_d_ge, h_d_lt, h_sub_r, h_add_q, h_hyp, h_rec⟩

/-- **Theorem 1.2 (`half_chord_uniquely_determines_p`):**
    Injectivity of the 5UP Half-Chord map: if two candidate primes `p₁, p₂` produce the
    same half-chord coordinates `(A_h, Δ_h)` at target `N` (`p₁ + A_h ^ 2 = N + Δ_h ^ 2`
    and `p₂ + A_h ^ 2 = N + Δ_h ^ 2`), then `p₁ = p₂`. -/
theorem half_chord_uniquely_determines_p
    {N p₁ p₂ A_h D_h : ℕ}
    (h1 : p₁ + A_h ^ 2 = N + D_h ^ 2)
    (h2 : p₂ + A_h ^ 2 = N + D_h ^ 2) :
    p₁ = p₂ := by
  omega

/-- **Theorem 1.3 (`odd_subfilter_witness_has_half_chord_hyperbola`):**
    Every odd prime `p ∈ fiveupPinchedQRSubfilter a b N` (`p % 2 = 1`) for an even target
    `N` (`N % 2 = 0`) possesses an integer half-chord witness `(A_h, Δ_h)` with `1 ≤ Δ_h < A_h`,
    `A_h ^ 2 = (N - p) + Δ_h ^ 2`, `p + A_h ^ 2 = N + Δ_h ^ 2`, and
    `(A_h - Δ_h) ^ (a + b) ≤ (N - p) ^ a`. -/
theorem odd_subfilter_witness_has_half_chord_hyperbola
    {a b N p : ℕ} (hEven : N % 2 = 0) (hp_odd : p % 2 = 1)
    (hp_mem : p ∈ fiveupPinchedQRSubfilter a b N) :
    ∃ A_h D_h : ℕ,
      1 ≤ D_h ∧
      D_h < A_h ∧
      IsPrimeNat (A_h - D_h) ∧
      IsPrimeNat (A_h + D_h) ∧
      A_h ^ 2 = (N - p) + D_h ^ 2 ∧
      p + A_h ^ 2 = N + D_h ^ 2 ∧
      (A_h - D_h) ^ (a + b) ≤ (N - p) ^ a := by
  rw [fiveupPinchedQRSubfilter, mem_filter] at hp_mem
  obtain ⟨_, _, r, q, hr_prime, hq_prime, hN_eq,
          h_lt, _, _, _, _, h_homog⟩ := hp_mem
  have h_rq_odd : (r * q) % 2 = 1 := by omega
  obtain ⟨hr_odd, hq_odd⟩ := mul_mod_two_eq_one_iff h_rq_odd
  have h_hc := half_chord_hyperbola_identity hN_eq h_lt hr_odd hq_odd
  refine ⟨(q + r) / 2, (q - r) / 2, h_hc.1, h_hc.2.1, ?_, ?_,
    h_hc.2.2.2.2.1, h_hc.2.2.2.2.2, ?_⟩
  · rw [h_hc.2.2.1]
    exact natPrime_to_isPrimeNat hr_prime
  · rw [h_hc.2.2.2.1]
    exact natPrime_to_isPrimeNat hq_prime
  · exact nat_pow_le_pow_of_eq ((q + r) / 2 - (q - r) / 2) (a + b) (N - p) (N - p) a rfl
      (by rw [h_hc.2.2.1]; exact h_homog)

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.half_chord_hyperbola_identity
#print axioms WuPaper.ESZerosBridge.half_chord_uniquely_determines_p
#print axioms WuPaper.ESZerosBridge.odd_subfilter_witness_has_half_chord_hyperbola
