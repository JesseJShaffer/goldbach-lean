import WR2Step235WR2PrimorialWaveSegmentLadderAndBitwiseFlickerBridge

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step237WR2DyadicPrimorialStaircaseAndLocalSubTwoQCombClosure.lean — `Step211` Generalized Dyadic/Primorial Staircase, PrefixCoset Phase-Return Period & Local Sub-`2q` Block Closure (`WR2` Track 1)

Ports Sections 2–4 of `Step211_PrimorialWaveSegmentSteppingAndCosetFlickerBridge_v1.lean`
into the `goldbach-lean` Track 1 (`WR2`) bridge:

1. **Section 1 — Generalized Dyadic (`E / 2^m`) & Primorial (`E / W`) Quotient-Cofactor Staircase (`Step211` §2):**
   - `div_le_div_left_of_le_native`: proves in pure `Init` arithmetic that `0 < A → A ≤ B → E / B ≤ E / A`.
   - `generalized_dyadic_and_primorial_quotient_cofactor_staircase`: proves monotonicity of
     `dyadicQuotientStair E m := E / (2 ^ m)` (`m₁ ≤ m₂ → E / 2^m₂ ≤ E / 2^m₁`), exact OMC
     reconstruction `(2 ^ m) * dyadicQuotientStair E m + E % (2 ^ m) = E`, the concrete
     dyadic chain `E / 16 ≤ E / 8 ≤ E / 4 ≤ E / 2 ≤ E`, and the primorial product contraction
     `E / (W * Q) ≤ E / W` for `0 < W` and `0 < Q`.
2. **Section 2 — PrefixCoset Tensor Phase-Return Period `P_{q,e}(W) = q^e / gcd(q^e, W)` (`Step211` §2 & `Step195`):**
   - Proves for every `0 < q` and `e, W : ℕ` that `1 ≤ prefixCosetReturnPeriod q e W ≤ q ^ e`,
     `Nat.gcd (q ^ e) W * prefixCosetReturnPeriod q e W = q ^ e`,
     `q ^ e ∣ W * prefixCosetReturnPeriod q e W`, and pairs `q` with `predictedNextPrime q`.
3. **Section 3 — Bridge Option 2: Local Sub-`2q` Block `|R_Q(J)| - |T_Q(J)|` Survivor Bound & Single-Block Goldbach Closure (`Step211` §3–§4):**
   - Proves on each individual Quotient Wave Shear block `J_k := subTwoQBlock (fullLowerMURUpper M) q k`
     that `(roughSurvivorSet J_k q).card - (sqrtActiveOwnerPrimes M q).card ≤ (primeSurvivorSet J_k q).card`,
     so ANY single block `k` with `(sqrtActiveOwnerPrimes M q).card < (roughSurvivorSet J_k q).card`
     unconditionally yields a certified Binary Goldbach partition `2 * M = p + q'`.
-/

/-!
## Section 1: Generalized Dyadic & Primorial Quotient-Cofactor Staircase (`Step211` §2)
-/

/-- Pure native proof that if `0 < A` and `A ≤ B`, then `E / B ≤ E / A` for all `E : ℕ`. -/
theorem div_le_div_left_of_le_native
    {A B E : ℕ} (hA_pos : 0 < A) (hAB : A ≤ B) :
    E / B ≤ E / A := by
  have hB_div : B * (E / B) + E % B = E := Nat.div_add_mod E B
  have hB_mul_le : B * (E / B) ≤ E := by omega
  have hA_mul_B : A * (E / B) ≤ B * (E / B) := Nat.mul_le_mul_right (E / B) hAB
  have hA_mul_le : A * (E / B) ≤ E := Nat.le_trans hA_mul_B hB_mul_le
  exact le_div_of_mul_le_native hA_pos hA_mul_le

/-- Monotonicity of `b ^ m` in the exponent `m` for `1 ≤ b` (with explicit base exponent `m₁`). -/
theorem nat_pow_le_pow_right_native {b : ℕ} (hb1 : 1 ≤ b) (m₁ : ℕ) :
    ∀ d : ℕ, b ^ m₁ ≤ b ^ (m₁ + d)
  | 0 => Nat.le_refl (b ^ m₁)
  | d + 1 => by
    have ih := nat_pow_le_pow_right_native hb1 m₁ d
    have h_step : b ^ (m₁ + d) * 1 ≤ b ^ (m₁ + d) * b :=
      Nat.mul_le_mul_left (b ^ (m₁ + d)) hb1
    rw [Nat.mul_one] at h_step
    exact Nat.le_trans ih h_step

/-- Generalized dyadic quotient staircase rung `E / (2 ^ m)` (`Step211` §2). -/
def dyadicQuotientStair (E m : ℕ) : ℕ :=
  E / (2 ^ m)

/-- **Theorem 1.1 (`generalized_dyadic_and_primorial_quotient_cofactor_staircase`):**
    Ports `Step211` Section 2 (`generalized_dyadic_and_primorial_quotient_cofactor_staircase`):
    For all `E, m₁, m₂, W, Q : ℕ`:
    1. `dyadicQuotientStair E 0 = E`, `dyadicQuotientStair E 1 = E / 2`, and
       `(2 ^ m₁) * dyadicQuotientStair E m₁ + E % (2 ^ m₁) = E`,
    2. `E / 16 ≤ E / 8 ∧ E / 8 ≤ E / 4 ∧ E / 4 ≤ E / 2 ∧ E / 2 ≤ E`,
    3. If `m₁ ≤ m₂`, then `dyadicQuotientStair E m₂ ≤ dyadicQuotientStair E m₁`, and
    4. If `0 < W` and `0 < Q`, then `E / (W * Q) ≤ E / W` and `E / (W * W) ≤ E / W`. -/
theorem generalized_dyadic_and_primorial_quotient_cofactor_staircase
    (E m₁ m₂ W Q : ℕ) :
    (dyadicQuotientStair E 0 = E ∧
     dyadicQuotientStair E 1 = E / 2 ∧
     (2 ^ m₁) * dyadicQuotientStair E m₁ + E % (2 ^ m₁) = E) ∧
    (E / 16 ≤ E / 8 ∧ E / 8 ≤ E / 4 ∧ E / 4 ≤ E / 2 ∧ E / 2 ≤ E) ∧
    (m₁ ≤ m₂ → dyadicQuotientStair E m₂ ≤ dyadicQuotientStair E m₁) ∧
    (0 < W → 0 < Q → E / (W * Q) ≤ E / W ∧ E / (W * W) ≤ E / W) := by
  have h_base :
      dyadicQuotientStair E 0 = E ∧
      dyadicQuotientStair E 1 = E / 2 ∧
      (2 ^ m₁) * dyadicQuotientStair E m₁ + E % (2 ^ m₁) = E := by
    unfold dyadicQuotientStair
    exact ⟨Nat.div_one E, rfl, Nat.div_add_mod E (2 ^ m₁)⟩
  have h_fixed : E / 16 ≤ E / 8 ∧ E / 8 ≤ E / 4 ∧ E / 4 ≤ E / 2 ∧ E / 2 ≤ E := by
    omega
  have h_mono : m₁ ≤ m₂ → dyadicQuotientStair E m₂ ≤ dyadicQuotientStair E m₁ := by
    intro hle
    unfold dyadicQuotientStair
    have h_add : m₁ + (m₂ - m₁) = m₂ := Nat.add_sub_of_le hle
    have h_pow_le : 2 ^ m₁ ≤ 2 ^ m₂ := by
      rw [← h_add]
      exact nat_pow_le_pow_right_native (by omega : 1 ≤ 2) m₁ (m₂ - m₁)
    have h_pow_pos : 0 < 2 ^ m₁ := nat_pow_pos (by omega : 0 < 2) m₁
    exact div_le_div_left_of_le_native h_pow_pos h_pow_le
  refine ⟨h_base, h_fixed, h_mono, ?_⟩
  intro hW_pos hQ_pos
  have h_WQ_ge : W ≤ W * Q := by
    have h1 : W * 1 ≤ W * Q := Nat.mul_le_mul_left W hQ_pos
    rw [Nat.mul_one] at h1
    exact h1
  have h_WW_ge : W ≤ W * W := by
    have h1 : W * 1 ≤ W * W := Nat.mul_le_mul_left W hW_pos
    rw [Nat.mul_one] at h1
    exact h1
  exact ⟨div_le_div_left_of_le_native hW_pos h_WQ_ge,
         div_le_div_left_of_le_native hW_pos h_WW_ge⟩

/-!
## Section 2: PrefixCoset Tensor Phase-Return Period `P_{q,e}(W) = q^e / gcd(q^e, W)` (`Step211` §2)
-/

/-- The PrefixCoset Tensor Phase-Return Period `P_{q,e}(W) := (q ^ e) / gcd(q ^ e, W)` (`Step195` & `Step211`). -/
def prefixCosetReturnPeriod (q e W : ℕ) : ℕ :=
  (q ^ e) / Nat.gcd (q ^ e) W

/-- **Theorem 2.1 (`prefixCosetReturnPeriod_exact_mul_and_wave_dvd`):**
    Ports the PrefixCoset Tensor Phase-Return Period theorem (`Step195` & `Step211` §2)
    and explicitly connects `q` to our native prime generator `predictedNextPrime q`:
    For every `q > 0` and `e, W : ℕ`:
    1. `1 ≤ prefixCosetReturnPeriod q e W`,
    2. `prefixCosetReturnPeriod q e W ≤ q ^ e`,
    3. `Nat.gcd (q ^ e) W * prefixCosetReturnPeriod q e W = q ^ e`,
    4. `q ^ e ∣ W * prefixCosetReturnPeriod q e W`, and
    5. `predictedNextPrime q = nextPrimeBoundedAux (q + 1) (factorialNat q + 1)` and
       `∃ q_next, q < q_next ∧ IsPrimeNat q_next`. -/
theorem prefixCosetReturnPeriod_exact_mul_and_wave_dvd
    {q : ℕ} (hq_pos : 0 < q) (e W : ℕ) :
    1 ≤ prefixCosetReturnPeriod q e W ∧
    prefixCosetReturnPeriod q e W ≤ q ^ e ∧
    Nat.gcd (q ^ e) W * prefixCosetReturnPeriod q e W = q ^ e ∧
    q ^ e ∣ W * prefixCosetReturnPeriod q e W ∧
    predictedNextPrime q = nextPrimeBoundedAux (q + 1) (factorialNat q + 1) ∧
    (∃ q_next : ℕ, q < q_next ∧ IsPrimeNat q_next) := by
  have h_qe_pos : 0 < q ^ e := nat_pow_pos hq_pos e
  have h_gcd_pos : 0 < Nat.gcd (q ^ e) W := Nat.gcd_pos_of_pos_left W h_qe_pos
  have h_gcd_dvd_qe : Nat.gcd (q ^ e) W ∣ q ^ e := Nat.gcd_dvd_left (q ^ e) W
  have h_gcd_dvd_W : Nat.gcd (q ^ e) W ∣ W := Nat.gcd_dvd_right (q ^ e) W
  have h_gcd_le_qe : Nat.gcd (q ^ e) W ≤ q ^ e := dvd_le_of_pos h_gcd_dvd_qe h_qe_pos
  have h_mul_eq : Nat.gcd (q ^ e) W * prefixCosetReturnPeriod q e W = q ^ e :=
    (mod_eq_zero_and_mul_div_of_dvd_native h_gcd_pos h_gcd_dvd_qe).2
  have h_ge1 : 1 ≤ prefixCosetReturnPeriod q e W := by
    unfold prefixCosetReturnPeriod
    have h_m1 : Nat.gcd (q ^ e) W * 1 ≤ q ^ e := by
      rw [Nat.mul_one]
      exact h_gcd_le_qe
    exact le_div_of_mul_le_native h_gcd_pos h_m1
  have h_le_qe : prefixCosetReturnPeriod q e W ≤ q ^ e := by
    unfold prefixCosetReturnPeriod
    have h_1_le_gcd : 1 ≤ Nat.gcd (q ^ e) W := h_gcd_pos
    have h_div1 := div_le_div_left_of_le_native (E := q ^ e) (by omega : 0 < 1) h_1_le_gcd
    rw [Nat.div_one] at h_div1
    exact h_div1
  have h_dvd_wave : q ^ e ∣ W * prefixCosetReturnPeriod q e W := by
    obtain ⟨m, hm⟩ := h_gcd_dvd_W
    refine ⟨m, ?_⟩
    calc W * prefixCosetReturnPeriod q e W
      _ = (Nat.gcd (q ^ e) W * m) * prefixCosetReturnPeriod q e W := by rw [← hm]
      _ = (m * Nat.gcd (q ^ e) W) * prefixCosetReturnPeriod q e W := by
          rw [Nat.mul_comm (Nat.gcd (q ^ e) W) m]
      _ = m * (Nat.gcd (q ^ e) W * prefixCosetReturnPeriod q e W) :=
          Nat.mul_assoc m (Nat.gcd (q ^ e) W) (prefixCosetReturnPeriod q e W)
      _ = m * (q ^ e) := by rw [h_mul_eq]
      _ = (q ^ e) * m := Nat.mul_comm m (q ^ e)
  exact ⟨h_ge1, h_le_qe, h_mul_eq, h_dvd_wave, rfl, hasNextPrimeConnection_unconditional q⟩

/-!
## Section 3: Local Sub-`2q` Block `|R_Q(J)| - |T_Q(J)|` Survivor Bound & Single-Block Goldbach Closure (`Step211` §3–§4)
-/

/-- **Theorem 3.1 (`local_subTwoQBlock_rq_minus_tq_and_single_block_goldbach_closure`):**
    Ports `Step211` Sections 3–4 (Bridge Option 2 — Local Sub-`2q` Block Survivor Closure):
    For EVERY `M, q, k : ℕ`, let `J_k := subTwoQBlock (fullLowerMURUpper M) q k`. Then:
    1. Exact block survivor identity:
       `(roughSurvivorSet J_k q).card = (primeSurvivorSet J_k q).card + (pn1RoughCompositeTail J_k q).card`,
    2. Local `|R_Q(J_k)| - |sqrtOwners|` lower bound (no `Blocks.card` factor):
       `(roughSurvivorSet J_k q).card - (sqrtActiveOwnerPrimes M q).card ≤ (primeSurvivorSet J_k q).card`, and
    3. Single-Block Goldbach Closure: if `(sqrtActiveOwnerPrimes M q).card < (roughSurvivorSet J_k q).card`
       on ANY single block `k`, then `0 < (primeSurvivorSet J_k q).card` and `2 * M` is
       unconditionally a Binary Goldbach sum `2 * M = p + q'` paired with `p < p_next'`! -/
theorem local_subTwoQBlock_rq_minus_tq_and_single_block_goldbach_closure
    (M q k : ℕ) :
    let J_k := subTwoQBlock (fullLowerMURUpper M) q k
    (roughSurvivorSet J_k q).card =
      (primeSurvivorSet J_k q).card + (pn1RoughCompositeTail J_k q).card ∧
    (roughSurvivorSet J_k q).card - (sqrtActiveOwnerPrimes M q).card ≤
      (primeSurvivorSet J_k q).card ∧
    ((sqrtActiveOwnerPrimes M q).card < (roughSurvivorSet J_k q).card →
      0 < (primeSurvivorSet J_k q).card ∧
      ∃ p q' p_next' : ℕ,
        Nat.Prime p ∧ Nat.Prime q' ∧ 2 * M = p + q' ∧
        p < p_next' ∧ Nat.Prime p_next' ∧ IsPrimeNat p_next') := by
  dsimp only
  have h_part :=
    roughSurvivorSet_card_eq_primeSurvivors_add_compositeTail
      (subTwoQBlock (fullLowerMURUpper M) q k) q
  have h_tail_le :=
    subTwoQBlock_roughCompositeTail_card_le_sqrtActiveOwnerPrimes M q k
  have h_sub_le :
      (roughSurvivorSet (subTwoQBlock (fullLowerMURUpper M) q k) q).card -
        (sqrtActiveOwnerPrimes M q).card ≤
      (primeSurvivorSet (subTwoQBlock (fullLowerMURUpper M) q k) q).card := by
    omega
  refine ⟨h_part, h_sub_le, ?_⟩
  intro h_lt
  have h_pos :
      0 < (primeSurvivorSet (subTwoQBlock (fullLowerMURUpper M) q k) q).card := by
    omega
  refine ⟨h_pos, ?_⟩
  obtain ⟨u, hu⟩ := card_pos.mp h_pos
  rw [primeSurvivorSet, mem_filter, subTwoQBlock, mem_filter] at hu
  obtain ⟨⟨hu_full, _⟩, _, _, hu_isp⟩ := hu
  have h_props := fullLowerMURUpper_mem_props hu_full
  have hp_nat : Nat.Prime (2 * M - u) := isPrimeNat_to_natPrime h_props.2.2.2.2.1
  have hu_nat : Nat.Prime u := isPrimeNat_to_natPrime hu_isp
  obtain ⟨p_next', hp_lt, hp_next_nat, hp_next_isp⟩ :=
    hasNextPrimeMathlib_unconditional (2 * M - u)
  exact ⟨2 * M - u, u, p_next', hp_nat, hu_nat, h_props.2.2.2.2.2.symm,
    hp_lt, hp_next_nat, hp_next_isp⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.div_le_div_left_of_le_native
#print axioms WuPaper.ESZerosBridge.generalized_dyadic_and_primorial_quotient_cofactor_staircase
#print axioms WuPaper.ESZerosBridge.prefixCosetReturnPeriod_exact_mul_and_wave_dvd
#print axioms WuPaper.ESZerosBridge.local_subTwoQBlock_rq_minus_tq_and_single_block_goldbach_closure
