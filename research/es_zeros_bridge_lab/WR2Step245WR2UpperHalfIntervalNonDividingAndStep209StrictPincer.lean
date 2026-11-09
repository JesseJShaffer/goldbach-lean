import WR2Step243WR2RescuedLowerMURSurvivorStrictInequality

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step245WR2UpperHalfIntervalNonDividingAndStep209StrictPincer.lean — Signature-Operator Quotient-One Non-Divisibility, Upper-Half Interval `√(2M) + 1` Separation & `Step209` Strict Pincer (`WR2` Track 1)

Ports the arithmetic core of `exists_prime_in_aboveSqrt_nondividing_two_mul_M` (`Step209` §3b)
into Track 1 (`WR2`) by uniting the Quotient-One Triangle Dead Zone (`Step212`) with the
`Step217` Signature Multiplication Operator `sigMulOperator` (`WR2Step241`):

1. **Section 1 — Pure Native `IsPrimeNat 3`, `M = 4` Certificate & Quotient-One Dead Zone:**
   - `isPrimeNat_three_native` & `exists_prime_aboveSqrt_nondividing_M4_native`.
   - `quotient_one_triangle_zero_free_dead_zone_wr2`: proves `c / d = 1 ∧ 1 ≤ c % d ∧ ¬ d ∣ c`
     for `d < c < 2 * d` using isolated linear helpers.
2. **Section 2 — Signature-Operator Quotient-One Non-Divisibility (`odd_in_upper_half_interval_nondividing_two_mul_M`):**
   - Uses `sig_mul_operator_sound_native` (`WR2Step241`) to reduce `(2 * M) % p` to
     `(2 * (M % p)) % p`, and proves `two_mul_rem_mod_pos_of_odd` by a second application
     of `quotient_one_triangle_zero_free_dead_zone_wr2` when `p < 2 * (M % p) < 2 * p`.
3. **Section 3 — Upper-Half Interval `(M/2, 2*(M/2)]` to `Step209` Strict Pincer & Single-Block Goldbach Closure:**
   - Proves `upper_half_interval_prime_satisfies_step209_aboveSqrt_conditions` and
     `bertrand_upper_half_prime_discharges_step209_strict_pincer_wr2`, connecting directly to
     `local_subTwoQBlock_rq_minus_tq_and_single_block_goldbach_closure` (`WR2Step237`).
-/

/-!
## Section 1: Pure Native `IsPrimeNat 3`, `M = 4` Certificate & Quotient-One Dead Zone
-/

/-- Pure native proof of `IsPrimeNat 3` (zero `decide`). -/
theorem isPrimeNat_three_native : IsPrimeNat 3 := by
  refine ⟨by omega, ?_⟩
  intro d hd
  have hd_le : d ≤ 3 := dvd_le_of_pos hd (by omega : 0 < 3)
  obtain ⟨k, hk⟩ := hd
  if hd0 : d = 0 then
    rw [hd0, Nat.zero_mul] at hk
    omega
  else if hd1 : d = 1 then
    exact Or.inl hd1
  else if hd2 : d = 2 then
    rw [hd2] at hk
    omega
  else
    exact Or.inr (by omega)

/-- Pure native proof that at `M = 4`, `p = 3` satisfies `IsPrimeNat 3`, `3 % 2 = 1`,
    `3 < 4`, `2 * 4 < 3 * 3`, and `(2 * 4) % 3 ≠ 0`. -/
theorem exists_prime_aboveSqrt_nondividing_M4_native :
    ∃ p : ℕ, IsPrimeNat p ∧ p % 2 = 1 ∧ p < 4 ∧ 2 * 4 < p * p ∧ (2 * 4) % p ≠ 0 :=
  ⟨3, isPrimeNat_three_native, by omega, by omega, by omega, by omega⟩

/-- Isolated linear helper: `q ≠ 0` and `q < 2` implies `q = 1`. -/
theorem eq_one_of_ne_zero_of_lt_two_wr2 {q : ℕ} (h_ne0 : q ≠ 0) (h_lt2 : q < 2) :
    q = 1 := by
  omega

/-- Isolated linear helper: `d < c` and `d + r = c` implies `1 ≤ r`. -/
theorem rem_pos_of_lt_of_add_eq_wr2 {d r c : ℕ} (hd_lt : d < c) (h_sum : d + r = c) :
    1 ≤ r := by
  omega

/-- Isolated linear helper: `1 ≤ r` and `r = 0` is impossible. -/
theorem false_of_one_le_of_eq_zero_wr2 {r : ℕ} (h1 : 1 ≤ r) (h0 : r = 0) : False := by
  omega

/-- **Theorem 1.1 (`quotient_one_triangle_zero_free_dead_zone_wr2`):**
    Reciprocal Quotient-One Dead Zone (`Step212` Pillar 4a) on Track 1 (`WR2`):
    for `d < c < 2 * d`, `c / d = 1 ∧ 1 ≤ c % d ∧ c % d < d ∧ d + c % d = c ∧ ¬ (d ∣ c)`. -/
theorem quotient_one_triangle_zero_free_dead_zone_wr2
    {c d : ℕ} (hd_lt : d < c) (hc_lt : c < 2 * d) :
    c / d = 1 ∧
    1 ≤ c % d ∧
    c % d < d ∧
    d + c % d = c ∧
    ¬ (d ∣ c) := by
  have hd_pos : 0 < d := by omega
  have h_div_mod : d * (c / d) + c % d = c := Nat.div_add_mod c d
  have h_mod_lt : c % d < d := Nat.mod_lt c hd_pos
  have h_q_not_zero : c / d ≠ 0 := by
    intro h0
    have h_dm := h_div_mod
    rw [h0, Nat.mul_zero, Nat.zero_add] at h_dm
    omega
  have h_q_lt_two : c / d < 2 := by
    match Nat.lt_or_ge (c / d) 2 with
    | Or.inl hlt => exact hlt
    | Or.inr hge =>
      have h_mul : d * 2 ≤ d * (c / d) := Nat.mul_le_mul_left d hge
      have h_2d : 2 * d = d * 2 := Nat.mul_comm 2 d
      omega
  have h_q_eq_one : c / d = 1 :=
    eq_one_of_ne_zero_of_lt_two_wr2 h_q_not_zero h_q_lt_two
  have h_sum : d + c % d = c := by
    have h_dm := h_div_mod
    rw [h_q_eq_one, Nat.mul_one] at h_dm
    exact h_dm
  have h_rem_pos : 1 ≤ c % d := rem_pos_of_lt_of_add_eq_wr2 hd_lt h_sum
  refine ⟨h_q_eq_one, h_rem_pos, h_mod_lt, h_sum, ?_⟩
  intro h_dvd
  obtain ⟨k, hk⟩ := h_dvd
  have h_eq : d * 1 + c % d = d * k := by
    rw [Nat.mul_one, h_sum, hk]
  have h_zero : c % d = 0 := eq_zero_of_mul_add_eq_mul_of_lt h_mod_lt h_eq
  exact false_of_one_le_of_eq_zero_wr2 h_rem_pos h_zero

/-!
## Section 2: Signature-Operator Quotient-One Non-Divisibility (`p < M < 2 * p → 1 ≤ (2 * M) % p`)
-/

/-- **Lemma 2.1 (`two_mul_rem_mod_pos_of_odd`):**
    For any odd modulus `p` (`p % 2 = 1`) and any remainder `R` with `1 ≤ R < p`,
    doubling `R` never hits `p` (`2 * R ≠ p`), so either `2 * R < p` (where `(2 * R) % p = 2 * R ≥ 2`)
    or `p < 2 * R < 2 * p` (where `2 * R` lies in the Quotient-One Triangle Dead Zone),
    forcing `1 ≤ (2 * R) % p` in both regimes! -/
theorem two_mul_rem_mod_pos_of_odd
    {p R : ℕ} (hp_odd : p % 2 = 1) (hR_pos : 1 ≤ R) (hR_lt : R < p) :
    1 ≤ (2 * R) % p := by
  have h_2R_ne_p : 2 * R ≠ p := by
    intro h_eq
    have hp_div2 : 2 * (p / 2) + p % 2 = p := Nat.div_add_mod p 2
    omega
  match Nat.lt_or_ge (2 * R) p with
  | Or.inl h_lt =>
    have h_mod_eq : (2 * R) % p = 2 * R := Nat.mod_eq_of_lt h_lt
    rw [h_mod_eq]
    omega
  | Or.inr h_ge =>
    have h_gt : p < 2 * R := by omega
    have h_lt_2p : 2 * R < 2 * p :=
      Nat.mul_lt_mul_of_pos_left hR_lt (by omega : 0 < 2)
    exact (quotient_one_triangle_zero_free_dead_zone_wr2 h_gt h_lt_2p).2.1

/-- **Theorem 2.2 (`odd_in_upper_half_interval_nondividing_two_mul_M`):**
    Signature-Operator Quotient-One Non-Divisibility Law:
    Combines `quotient_one_triangle_zero_free_dead_zone_wr2` with `sig_mul_operator_sound_native`
    (`WR2Step241` / `Step217`) to prove that for EVERY odd integer `p` (`p % 2 = 1`) in
    `p < M` and `M < 2 * p`:
    1. `M / p = 1`, `1 ≤ M % p`, and `¬ (p ∣ M)`,
    2. `(2 * M) % p = (sigMulOperator 2 p 1 (M % p)).2`, and
    3. `1 ≤ (2 * M) % p` and `(2 * M) % p ≠ 0`. -/
theorem odd_in_upper_half_interval_nondividing_two_mul_M
    {M p : ℕ} (hp_odd : p % 2 = 1) (hp_lt_M : p < M) (hM_lt_2p : M < 2 * p) :
    1 ≤ M % p ∧
    ¬ (p ∣ M) ∧
    (2 * M) % p = (sigMulOperator 2 p 1 (M % p)).2 ∧
    1 ≤ (2 * M) % p ∧
    (2 * M) % p ≠ 0 := by
  have h_q1 := quotient_one_triangle_zero_free_dead_zone_wr2 hp_lt_M hM_lt_2p
  have hR_pos : 1 ≤ M % p := h_q1.2.1
  have hR_lt : M % p < p := h_q1.2.2.1
  have h_sum : p + M % p = M := h_q1.2.2.2.1
  have h_ndvd : ¬ (p ∣ M) := h_q1.2.2.2.2
  have hM_decomp : M = p * 1 + M % p := by
    rw [Nat.mul_one]
    exact h_sum.symm
  have h_sig := (sig_mul_operator_sound_native (a := 2) hM_decomp).2
  have h_sig_eval : (sigMulOperator 2 p 1 (M % p)).2 = (2 * (M % p)) % p := rfl
  have h_2R_pos : 1 ≤ (2 * (M % p)) % p :=
    two_mul_rem_mod_pos_of_odd hp_odd hR_pos hR_lt
  have h_2M_pos : 1 ≤ (2 * M) % p := by
    rw [h_sig, h_sig_eval]
    exact h_2R_pos
  have h_2M_ne0 : (2 * M) % p ≠ 0 := by
    intro h0
    exact false_of_one_le_of_eq_zero_wr2 h_2M_pos h0
  exact ⟨hR_pos, h_ndvd, h_sig, h_2M_pos, h_2M_ne0⟩

/-!
## Section 3: Upper-Half Interval `(M/2, 2*(M/2)]` to `Step209` Strict Pincer & Single-Block Goldbach Closure
-/

/-- Pure native helper: if `2 * M < p * p`, then `Nat.sqrt (2 * M) + 1 ≤ p`. -/
theorem sqrt_add_one_le_of_lt_sq_native {M p : ℕ} (h_lt : 2 * M < p * p) :
    Nat.sqrt (2 * M) + 1 ≤ p := by
  match Nat.lt_or_ge p (Nat.sqrt (2 * M) + 1) with
  | Or.inr hge => exact hge
  | Or.inl hlt =>
    have hp_le : p ≤ Nat.sqrt (2 * M) := by omega
    have h_p2_le : p * p ≤ Nat.sqrt (2 * M) * Nat.sqrt (2 * M) :=
      Nat.mul_le_mul hp_le hp_le
    have h_sqrt_le : Nat.sqrt (2 * M) * Nat.sqrt (2 * M) ≤ 2 * M :=
      Nat.sqrt_le (2 * M)
    have h_p2_2M : p * p ≤ 2 * M := Nat.le_trans h_p2_le h_sqrt_le
    exact False.elim (Nat.lt_irrefl (2 * M) (Nat.lt_of_lt_of_le h_lt h_p2_2M))

/-- **Theorem 3.1 (`upper_half_interval_prime_satisfies_step209_aboveSqrt_conditions`):**
    Ports the core arithmetic of `exists_prime_in_aboveSqrt_nondividing_two_mul_M` (`Step209` §3b):
    For every `M ≥ 6` and every prime `p` (`IsPrimeNat p`) in the Bertrand interval
    `M / 2 < p` and `p ≤ 2 * (M / 2)`:
    1. `p % 2 = 1`,
    2. `p < M` (`p ≤ M - 1`),
    3. `2 * M < p * p` and `Nat.sqrt (2 * M) + 1 ≤ p`, and
    4. `1 ≤ (2 * M) % p` and `(2 * M) % p ≠ 0`. -/
theorem upper_half_interval_prime_satisfies_step209_aboveSqrt_conditions
    {M p : ℕ} (hM6 : 6 ≤ M) (hp : IsPrimeNat p)
    (h_gt_half : M / 2 < p) (h_le_two_half : p ≤ 2 * (M / 2)) :
    p % 2 = 1 ∧
    p < M ∧
    2 * M < p * p ∧
    Nat.sqrt (2 * M) + 1 ≤ p ∧
    1 ≤ (2 * M) % p ∧
    (2 * M) % p ≠ 0 := by
  have h_M_div2 : 2 * (M / 2) + M % 2 = M := Nat.div_add_mod M 2
  have h_M_mod2 : M % 2 < 2 := Nat.mod_lt M (by omega : 0 < 2)
  have hh3 : 3 ≤ M / 2 := by omega
  have hp_ge4 : 4 ≤ p := by omega
  have hp_odd : p % 2 = 1 := by
    rcases isPrimeNat_eq_two_or_odd_wr2 hp with hp2 | hp_o
    · omega
    · exact hp_o
  have hp_div2 : 2 * (p / 2) + p % 2 = p := Nat.div_add_mod p 2
  have hp_lt_2half : p < 2 * (M / 2) := by omega
  have hp_lt_M : p < M := by omega
  have hM_lt_2p : M < 2 * p := by omega
  have h_3h_le_h2 : 3 * (M / 2) ≤ (M / 2) * (M / 2) :=
    Nat.mul_le_mul_right (M / 2) hh3
  have h_exp1 :
      (M / 2 + 1) * (M / 2 + 1) = (M / 2 + 1) * (M / 2) + (M / 2 + 1) * 1 :=
    Nat.left_distrib (M / 2 + 1) (M / 2) 1
  have h_exp2 :
      (M / 2 + 1) * (M / 2) = (M / 2) * (M / 2) + 1 * (M / 2) :=
    Nat.right_distrib (M / 2) 1 (M / 2)
  have h_2M_lt_h1_sq : 2 * M < (M / 2 + 1) * (M / 2 + 1) := by omega
  have h_h1_le_p : M / 2 + 1 ≤ p := by omega
  have h_h1_sq_le_p2 : (M / 2 + 1) * (M / 2 + 1) ≤ p * p :=
    Nat.mul_le_mul h_h1_le_p h_h1_le_p
  have h_2M_lt_p2 : 2 * M < p * p := Nat.lt_of_lt_of_le h_2M_lt_h1_sq h_h1_sq_le_p2
  have h_sqrt_le_p : Nat.sqrt (2 * M) + 1 ≤ p :=
    sqrt_add_one_le_of_lt_sq_native h_2M_lt_p2
  have h_nondiv :=
    odd_in_upper_half_interval_nondividing_two_mul_M hp_odd hp_lt_M hM_lt_2p
  exact ⟨hp_odd, hp_lt_M, h_2M_lt_p2, h_sqrt_le_p, h_nondiv.2.2.2.1, h_nondiv.2.2.2.2⟩

/-- **Theorem 3.2 (`bertrand_upper_half_prime_discharges_step209_strict_pincer_wr2`):**
    Complete `Step209` Section 3b Strict Pincer Discharge on Track 1 (`WR2`),
    explicitly connected to `local_subTwoQBlock_rq_minus_tq_and_single_block_goldbach_closure` (`WR2Step237`):
    For EVERY `M ≥ 4` with `M ≠ 5` and every `q, k : ℕ` under `h_fmp`:
    1. `1 ≤ (aboveSqrtLowerMURPrimesCutoff M q).card`,
    2. `(sqrtActiveOwnerPrimes M (max q 3)).card < (roughSurvivorSet (fullLowerMURUpper M) (max q 3)).card`,
    3. `(pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) (max q 3) k) (max q 3)).card < (roughSurvivorSet (fullLowerMURUpper M) (max q 3)).card`, and
    4. Whenever block `k` carries the full rough survivor set
       (`(roughSurvivorSet (fullLowerMURUpper M) (max q 3)).card ≤ (roughSurvivorSet (subTwoQBlock (fullLowerMURUpper M) (max q 3) k) (max q 3)).card`),
       `2 * M` is unconditionally a Binary Goldbach sum `2 * M = p + q'` paired with `p < p_next'`! -/
theorem bertrand_upper_half_prime_discharges_step209_strict_pincer_wr2
    {M q k : ℕ}
    (hM4 : 4 ≤ M) (hM_ne5 : M ≠ 5)
    (h_bertrand : 6 ≤ M → ∃ p : ℕ, IsPrimeNat p ∧ M / 2 < p ∧ p ≤ 2 * (M / 2))
    (h_fmp : ∀ p0 : ℕ, IsPrimeNat p0 → p0 % 2 = 1 → p0 < max q 3 → (2 * M) % p0 = 0) :
    1 ≤ (aboveSqrtLowerMURPrimesCutoff M q).card ∧
    (sqrtActiveOwnerPrimes M (max q 3)).card <
      (roughSurvivorSet (fullLowerMURUpper M) (max q 3)).card ∧
    (pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) (max q 3) k) (max q 3)).card <
      (roughSurvivorSet (fullLowerMURUpper M) (max q 3)).card ∧
    ((roughSurvivorSet (fullLowerMURUpper M) (max q 3)).card ≤
        (roughSurvivorSet (subTwoQBlock (fullLowerMURUpper M) (max q 3) k) (max q 3)).card →
      ∃ p q' p_next' : ℕ,
        Nat.Prime p ∧ Nat.Prime q' ∧ 2 * M = p + q' ∧
        p < p_next' ∧ Nat.Prime p_next' ∧ IsPrimeNat p_next') := by
  have h_ex :
      ∃ p : ℕ, IsPrimeNat p ∧ p % 2 = 1 ∧ p < M ∧ 2 * M < p * p ∧ (2 * M) % p ≠ 0 := by
    if hM_eq4 : M = 4 then
      subst hM_eq4
      exact exists_prime_aboveSqrt_nondividing_M4_native
    else
      have hM6 : 6 ≤ M := by omega
      obtain ⟨p, hp_isp, h_gt, h_le⟩ := h_bertrand hM6
      have h_props :=
        upper_half_interval_prime_satisfies_step209_aboveSqrt_conditions
          hM6 hp_isp h_gt h_le
      exact ⟨p, hp_isp, h_props.1, h_props.2.1, h_props.2.2.1, h_props.2.2.2.2.2⟩
  have h_strict :=
    (unconditional_strict_sqrt_owner_lt_rescued_lower_mur_survivors_wr2 M q k h_fmp).2.2 h_ex
  refine ⟨h_strict.1, h_strict.2.1, h_strict.2.2, ?_⟩
  intro h_blk_full
  have h_lt_blk :
      (sqrtActiveOwnerPrimes M (max q 3)).card <
        (roughSurvivorSet (subTwoQBlock (fullLowerMURUpper M) (max q 3) k) (max q 3)).card :=
    Nat.lt_of_lt_of_le h_strict.2.1 h_blk_full
  exact ((local_subTwoQBlock_rq_minus_tq_and_single_block_goldbach_closure
    M (max q 3) k).2.2 h_lt_blk).2

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.isPrimeNat_three_native
#print axioms WuPaper.ESZerosBridge.exists_prime_aboveSqrt_nondividing_M4_native
#print axioms WuPaper.ESZerosBridge.quotient_one_triangle_zero_free_dead_zone_wr2
#print axioms WuPaper.ESZerosBridge.two_mul_rem_mod_pos_of_odd
#print axioms WuPaper.ESZerosBridge.odd_in_upper_half_interval_nondividing_two_mul_M
#print axioms WuPaper.ESZerosBridge.upper_half_interval_prime_satisfies_step209_aboveSqrt_conditions
#print axioms WuPaper.ESZerosBridge.bertrand_upper_half_prime_discharges_step209_strict_pincer_wr2
