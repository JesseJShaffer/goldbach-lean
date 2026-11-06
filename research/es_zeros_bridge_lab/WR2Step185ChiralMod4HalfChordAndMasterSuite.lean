import WR2Step184HalfChordHyperbolaInjection

set_option exponentiation.threshold 10000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step185ChiralMod4HalfChordAndMasterSuite.lean — Chiral Mod-4 Half-Chord Lock & 8-Module Suite

Completes the 8-module `goldbach-lean` x `ES_Zeros` formal bridge suite:

1. **Native Mod-4 Square Dichotomy (`sq_mod_four_of_mod_two`):**
   Proves in pure native `Nat` arithmetic that `x % 2 = 0 → (x ^ 2) % 4 = 0` and
   `x % 2 = 1 → (x ^ 2) % 4 = 1`.
2. **Chiral Mod-4 Half-Chord Parity Lock (`half_chord_chiral_mod4_parity_lock`):**
   Proves that whenever `A_h ^ 2 = (N - p) + D_h ^ 2` with `(N - p) % 2 = 1`:
   - `(A_h + D_h) % 2 = 1` (strict opposite parity of half-chords),
   - `(N - p) % 4 = 1 → A_h % 2 = 1 ∧ D_h % 2 = 0 ∧ (D_h ^ 2) % 4 = 0` (even `Δ_h`, `16 ∣ (q - r)^2`),
   - `(N - p) % 4 = 3 → A_h % 2 = 0 ∧ D_h % 2 = 1 ∧ (D_h ^ 2) % 4 = 1` (odd `Δ_h`, even `A_h`).
3. **Full Subfilter Chiral Half-Chord Decomposition (`odd_subfilter_witness_chiral_half_chord_lock`):**
   Unites the injective half-chord hyperbola, the Chiral Mod-4 parity lock, and the
   homogeneous exponent pinch `(A_h - D_h) ^ (a + b) ≤ (N - p) ^ a` on `fiveupPinchedQRSubfilter`.
-/

/-- Pure native expansion `(2 * k) * (2 * k) = 4 * (k * k)`. -/
theorem even_mul_self_expand (k : ℕ) :
    (2 * k) * (2 * k) = 4 * (k * k) := by
  calc (2 * k) * (2 * k)
    _ = 2 * (k * (2 * k)) := Nat.mul_assoc 2 k (2 * k)
    _ = 2 * ((2 * k) * k) := by rw [Nat.mul_comm k (2 * k)]
    _ = 2 * (2 * (k * k)) := by rw [Nat.mul_assoc 2 k k]
    _ = (2 * 2) * (k * k) := (Nat.mul_assoc 2 2 (k * k)).symm
    _ = 4 * (k * k) := rfl

/-- Pure native expansion `(2 * k + 1) * (2 * k + 1) = 4 * (k * k + k) + 1`. -/
theorem odd_mul_self_expand (k : ℕ) :
    (2 * k + 1) * (2 * k + 1) = 4 * (k * k + k) + 1 := by
  have h1 : (2 * k + 1) * (2 * k + 1) =
      ((2 * k) * (2 * k) + (2 * k) * 1) + (1 * (2 * k) + 1 * 1) := by
    rw [Nat.right_distrib (2 * k) 1 (2 * k + 1)]
    rw [Nat.left_distrib (2 * k) (2 * k) 1]
    rw [Nat.left_distrib 1 (2 * k) 1]
  have h2 : (2 * k) * (2 * k) = 4 * (k * k) := even_mul_self_expand k
  have h3 : 4 * (k * k + k) = 4 * (k * k) + 4 * k := Nat.left_distrib 4 (k * k) k
  omega

/-- **Theorem 1.1 (`sq_mod_four_of_mod_two`):**
    Pure native proof that even squares are `0 (mod 4)` and odd squares are `1 (mod 4)`. -/
theorem sq_mod_four_of_mod_two (x : ℕ) :
    (x % 2 = 0 → (x ^ 2) % 4 = 0) ∧
    (x % 2 = 1 → (x ^ 2) % 4 = 1) := by
  rw [nat_sq_eq_mul x]
  constructor
  · intro h0
    have hx : x = 2 * (x / 2) := by omega
    have hsq : x * x = 4 * ((x / 2) * (x / 2)) := by
      calc x * x
        _ = (2 * (x / 2)) * (2 * (x / 2)) := by rw [← hx]
        _ = 4 * ((x / 2) * (x / 2)) := even_mul_self_expand (x / 2)
    omega
  · intro h1
    have hx : x = 2 * (x / 2) + 1 := by omega
    have hsq : x * x = 4 * ((x / 2) * (x / 2) + (x / 2)) + 1 := by
      calc x * x
        _ = (2 * (x / 2) + 1) * (2 * (x / 2) + 1) := by rw [← hx]
        _ = 4 * ((x / 2) * (x / 2) + (x / 2)) + 1 := odd_mul_self_expand (x / 2)
    omega

/-- **Theorem 2.1 (`half_chord_chiral_mod4_parity_lock`):**
    For any half-chord pair `(A_h, D_h)` satisfying `A_h ^ 2 = (N - p) + D_h ^ 2` with
    `(N - p) % 2 = 1`, the parities of `A_h` and `D_h` are strictly opposite and locked
    to the mod-4 chiral class of `N - p`. -/
theorem half_chord_chiral_mod4_parity_lock
    {N p A_h D_h : ℕ}
    (h_hyp : A_h ^ 2 = (N - p) + D_h ^ 2)
    (h_rem_odd : (N - p) % 2 = 1) :
    (A_h + D_h) % 2 = 1 ∧
    ((N - p) % 4 = 1 → A_h % 2 = 1 ∧ D_h % 2 = 0 ∧ (D_h ^ 2) % 4 = 0) ∧
    ((N - p) % 4 = 3 → A_h % 2 = 0 ∧ D_h % 2 = 1 ∧ (D_h ^ 2) % 4 = 1) := by
  have hA := sq_mod_four_of_mod_two A_h
  have hD := sq_mod_four_of_mod_two D_h
  omega

/-- **Theorem 3.1 (`odd_subfilter_witness_chiral_half_chord_lock`):**
    Complete 5UP Half-Chord & Chiral Mod-4 decomposition for any odd prime
    `p ∈ fiveupPinchedQRSubfilter a b N` at even target `N`. -/
theorem odd_subfilter_witness_chiral_half_chord_lock
    {a b N p : ℕ} (hEven : N % 2 = 0) (hp_odd : p % 2 = 1)
    (hp_mem : p ∈ fiveupPinchedQRSubfilter a b N) :
    ∃ A_h D_h : ℕ,
      1 ≤ D_h ∧
      D_h < A_h ∧
      IsPrimeNat (A_h - D_h) ∧
      IsPrimeNat (A_h + D_h) ∧
      A_h ^ 2 = (N - p) + D_h ^ 2 ∧
      p + A_h ^ 2 = N + D_h ^ 2 ∧
      (A_h + D_h) % 2 = 1 ∧
      ((N - p) % 4 = 1 → A_h % 2 = 1 ∧ D_h % 2 = 0 ∧ (D_h ^ 2) % 4 = 0) ∧
      ((N - p) % 4 = 3 → A_h % 2 = 0 ∧ D_h % 2 = 1 ∧ (D_h ^ 2) % 4 = 1) ∧
      (A_h - D_h) ^ (a + b) ≤ (N - p) ^ a := by
  obtain ⟨A_h, D_h, h1, h2, hpr, hpq, h_hyp, h_rec, h_homog⟩ :=
    odd_subfilter_witness_has_half_chord_hyperbola hEven hp_odd hp_mem
  rw [fiveupPinchedQRSubfilter, mem_filter] at hp_mem
  obtain ⟨_, _, r, q, _, _, hN_eq, _, h_sq_lt, _⟩ := hp_mem
  have h_pos : 0 < N - p := Nat.lt_of_le_of_lt (Nat.zero_le (r * r)) h_sq_lt
  have h_rem_odd : (N - p) % 2 = 1 := by omega
  have h_chiral := half_chord_chiral_mod4_parity_lock h_hyp h_rem_odd
  exact ⟨A_h, D_h, h1, h2, hpr, hpq, h_hyp, h_rec,
    h_chiral.1, h_chiral.2.1, h_chiral.2.2, h_homog⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.sq_mod_four_of_mod_two
#print axioms WuPaper.ESZerosBridge.half_chord_chiral_mod4_parity_lock
#print axioms WuPaper.ESZerosBridge.odd_subfilter_witness_chiral_half_chord_lock
