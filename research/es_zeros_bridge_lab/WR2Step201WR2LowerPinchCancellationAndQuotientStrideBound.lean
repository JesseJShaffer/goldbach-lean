import WR2Step199WR2PinchCutoffAndReciprocalShearFiberContraction

set_option exponentiation.threshold 10000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step201WR2LowerPinchCancellationAndQuotientStrideBound.lean — Lower Pinch Cancellation, OMC Zero-Slice & Quotient Stride Bound

Tightens each per-prime fiber `wr2ShearContractedFiber N r` in the `WR2ClassicalCertificate`
stack via three pure native arithmetic theorems:

1. **Exact Multiplicative Cancellation of Homogeneous Pinches (`lower_pinch_of_homog_pinch_wr2`):**
   Cancels `r ^ 4469 > 0` from `r ^ 9469 ≤ (r * q) ^ 4469` to recover the lower exponent
   pinch `r ^ 5000 ≤ q ^ 4469` on every `q ∈ wr2ShearContractedFiber N r`.
2. **Bilateral OMC Zero-Slice Elimination (`mod_pos_of_lt_isPrimeNat`,
   `wr2ShearContractedFiber_zero_slice_eq_zero`):**
   Proves that for every modulus `m` with `2 ≤ m ≤ r`, `1 ≤ q % m` for all
   `q ∈ wr2ShearContractedFiber N r`, so the `c = 0` residue slice has cardinality `0`,
   and whenever `m < N - r * q`, `1 ≤ (N - r * q) % m` (bilateral OMC).
3. **Constructive Quotient-Stride Slice Bound (`wr2ShearContractedFiber_slice_card_le_quotient_stride`,
   `wr2ShearContractedFiber_card_le_half_div`):**
   Reconstructs each residue class `q % m = c` from its quotient `q / m ∈ range (((N - 2) / r) / m + 1)`,
   proving `(residueClassSlice (wr2ShearContractedFiber N r) m c).card ≤ ((N - 2) / r) / m + 1`
   for all `m > 0` (including `m = 65`, `64`, `63`, and `m = 2` parity halving).
-/

/-!
## Section 1: Pure Native Power Cancellation (`r ^ (a + b) ≤ (r * q) ^ a → r ^ b ≤ q ^ a`)
-/

theorem mul_pow_local_wr2 (x y : ℕ) : ∀ n : ℕ, (x * y) ^ n = x ^ n * y ^ n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, mul_pow_local_wr2 x y n]
    calc (x ^ n * y ^ n) * (x * y)
      _ = x ^ n * (y ^ n * (x * y)) := Nat.mul_assoc _ _ _
      _ = x ^ n * ((y ^ n * x) * y) := by rw [Nat.mul_assoc (y ^ n) x y]
      _ = x ^ n * ((x * y ^ n) * y) := by rw [Nat.mul_comm (y ^ n) x]
      _ = x ^ n * (x * (y ^ n * y)) := by rw [Nat.mul_assoc x (y ^ n) y]
      _ = (x ^ n * x) * (y ^ n * y) := (Nat.mul_assoc (x ^ n) x (y ^ n * y)).symm

theorem pow_add_local_wr2 (x m : ℕ) : ∀ n : ℕ, x ^ (m + n) = x ^ m * x ^ n
  | 0 => by rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | n + 1 => by
    rw [Nat.add_succ, Nat.pow_succ, Nat.pow_succ, pow_add_local_wr2 x m n, Nat.mul_assoc]

theorem pow_pos_of_pos_wr2 {r : ℕ} (hr : 0 < r) : ∀ n : ℕ, 0 < r ^ n
  | 0 => by simp
  | n + 1 => by
    rw [Nat.pow_succ]
    have hn : 0 < r ^ n := pow_pos_of_pos_wr2 hr n
    have h1 : 1 * 1 ≤ r ^ n * r := Nat.mul_le_mul hn hr
    omega

theorem le_of_mul_le_mul_left_pos_wr2 {a b c : ℕ} (ha : 0 < a) (h : a * b ≤ a * c) :
    b ≤ c := by
  match Nat.lt_or_ge c b with
  | Or.inr hle => exact hle
  | Or.inl hlt =>
    have h_succ : c + 1 ≤ b := hlt
    have h_mul : a * (c + 1) ≤ a * b := Nat.mul_le_mul_left a h_succ
    rw [Nat.left_distrib a c 1, Nat.mul_one] at h_mul
    omega

/-- **Theorem 1.1 (`lower_pinch_of_homog_pinch_wr2`):**
    Pure native multiplicative cancellation: if `0 < r` and `r ^ (a + b) ≤ (r * q) ^ a`,
    then `r ^ b ≤ q ^ a`. -/
theorem lower_pinch_of_homog_pinch_wr2
    {r q a b : ℕ} (hr_pos : 0 < r) (h_homog : r ^ (a + b) ≤ (r * q) ^ a) :
    r ^ b ≤ q ^ a := by
  rw [pow_add_local_wr2 r a b, mul_pow_local_wr2 r q a] at h_homog
  have hra_pos : 0 < r ^ a := pow_pos_of_pos_wr2 hr_pos a
  exact le_of_mul_le_mul_left_pos_wr2 hra_pos h_homog

/-!
## Section 2: Bilateral OMC Exclusion & Zero-Slice Elimination on `wr2ShearContractedFiber`
-/

/-- Pure native proof that if `2 ≤ m < p` and `IsPrimeNat p`, then `1 ≤ p % m`. -/
theorem mod_pos_of_lt_isPrimeNat {m p : ℕ} (hm2 : 2 ≤ m) (h_lt : m < p) (hp : IsPrimeNat p) :
    1 ≤ p % m := by
  if h0 : p % m = 0 then
    have h_div_mod : m * (p / m) + p % m = p := Nat.div_add_mod p m
    have h_dvd : m ∣ p := ⟨p / m, by omega⟩
    cases hp.2 m h_dvd with
    | inl h1 => omega
    | inr hp_eq => omega
  else
    omega

/-- **Theorem 2.1 (`wr2ShearContractedFiber_lower_pinch_and_bilateral_omc`):**
    Every `q ∈ wr2ShearContractedFiber N r` (with `0 < r`) satisfies:
    1. `r ^ 5000 ≤ q ^ 4469` (the lower exponent pinch recovered by cancelling `r ^ 4469`),
    2. For every modulus `m` with `2 ≤ m ≤ r`, `1 ≤ q % m` (factor-side OMC non-divisibility),
    3. For every modulus `m` with `2 ≤ m` and `m < N - r * q`, `1 ≤ (N - r * q) % m`
       (target-side bilateral OMC non-divisibility). -/
theorem wr2ShearContractedFiber_lower_pinch_and_bilateral_omc
    {N r q : ℕ} (hr_pos : 0 < r) (hq : q ∈ wr2ShearContractedFiber N r) :
    r ^ 5000 ≤ q ^ 4469 ∧
    (∀ m : ℕ, 2 ≤ m → m ≤ r → 1 ≤ q % m) ∧
    (∀ m : ℕ, 2 ≤ m → m < N - r * q → 1 ≤ (N - r * q) % m) := by
  rw [wr2ShearContractedFiber, mem_filter, hyperbolicPrimeFiber, mem_filter] at hq
  obtain ⟨⟨_, hq_isp, _, h_r2_le_q, _, h_pp, h_homog⟩, _⟩ := hq
  have h_sum_exp : (4469 : ℕ) + 5000 = 9469 := rfl
  rw [← h_sum_exp] at h_homog
  have h_lower_pinch : r ^ 5000 ≤ q ^ 4469 :=
    lower_pinch_of_homog_pinch_wr2 hr_pos h_homog
  refine ⟨h_lower_pinch, ?_, ?_⟩
  · intro m hm2 hmr
    have h_m_lt_q : m < q := by omega
    exact mod_pos_of_lt_isPrimeNat hm2 h_m_lt_q hq_isp
  · intro m hm2 hm_lt_p
    exact mod_pos_of_lt_isPrimeNat hm2 hm_lt_p h_pp

/-!
## Section 3: Constructive Quotient-Stride Cardinality Bound on Residue Slices
-/

/-- The `c`-th residue progression slice of a `Finset ℕ` modulo `m`. -/
def residueClassSlice (S : Finset ℕ) (m c : ℕ) : Finset ℕ :=
  S.filter (fun q : ℕ => q % m = c)

/-- Linear quotient reconstruction map `k ↦ m * k + c`. -/
def reconstructFromQuotient (m c k : ℕ) : ℕ :=
  m * k + c

/-- **Theorem 3.1 (`wr2ShearContractedFiber_zero_slice_eq_zero`):**
    For every modulus `m` with `2 ≤ m ≤ r`, the `c = 0` residue slice of
    `wr2ShearContractedFiber N r` has cardinality `0`. -/
theorem wr2ShearContractedFiber_zero_slice_eq_zero
    {N r m : ℕ} (hm2 : 2 ≤ m) (hmr : m ≤ r) :
    (residueClassSlice (wr2ShearContractedFiber N r) m 0).card = 0 := by
  match Nat.eq_zero_or_pos (residueClassSlice (wr2ShearContractedFiber N r) m 0).card with
  | Or.inl h0 => exact h0
  | Or.inr hpos =>
    obtain ⟨q, hq⟩ := card_pos.mp hpos
    rw [residueClassSlice, mem_filter] at hq
    have hr_pos : 0 < r := by omega
    have h_omc := (wr2ShearContractedFiber_lower_pinch_and_bilateral_omc hr_pos hq.1).2.1 m hm2 hmr
    omega

/-- **Theorem 3.2 (`wr2ShearContractedFiber_slice_card_le_quotient_stride`):**
    For EVERY modulus `m > 0` (including `m = 65`, `64`, `63`, and `2`) and EVERY residue
    class `c : ℕ`, the cardinality of `residueClassSlice (wr2ShearContractedFiber N r) m c`
    is bounded by the quotient stride `((N - 2) / r) / m + 1`. -/
theorem wr2ShearContractedFiber_slice_card_le_quotient_stride
    {N r m : ℕ} (hm_pos : 0 < m) (c : ℕ) :
    (residueClassSlice (wr2ShearContractedFiber N r) m c).card ≤
      ((N - 2) / r) / m + 1 := by
  have h_sub :
      residueClassSlice (wr2ShearContractedFiber N r) m c ⊆
        (range (((N - 2) / r) / m + 1)).image (reconstructFromQuotient m c) := by
    intro q hq
    rw [residueClassSlice, mem_filter, wr2ShearContractedFiber, mem_filter,
        hyperbolicPrimeFiber, mem_filter, mem_range] at hq
    obtain ⟨⟨⟨hq_lt_div, _⟩, _⟩, h_mod_eq⟩ := hq
    have h_q_le : q ≤ (N - 2) / r := by omega
    have h_div_mod : m * (q / m) + q % m = q := Nat.div_add_mod q m
    have h_mul_le : m * (q / m) ≤ (N - 2) / r := by omega
    have h_quot_le : q / m ≤ ((N - 2) / r) / m :=
      le_div_of_mul_le_native hm_pos h_mul_le
    rw [mem_image]
    refine ⟨q / m, ?_, ?_⟩
    · rw [mem_range]
      omega
    · unfold reconstructFromQuotient
      omega
  have h_card := Nat.le_trans (card_le_card h_sub) card_image_le
  rw [card_range] at h_card
  exact h_card

/-- **Theorem 3.3 (`wr2ShearContractedFiber_card_le_half_div`):**
    Because every `q ∈ wr2ShearContractedFiber N r` is odd (`q % 2 = 1`),
    `wr2ShearContractedFiber N r = residueClassSlice (wr2ShearContractedFiber N r) 2 1`,
    cutting the fiber cardinality bound in half to `((N - 2) / r) / 2 + 1`. -/
theorem wr2ShearContractedFiber_card_le_half_div (N r : ℕ) :
    (wr2ShearContractedFiber N r).card ≤ ((N - 2) / r) / 2 + 1 ∧
    ∀ c : ℕ, (residueClassSlice (wr2ShearContractedFiber N r) 65 c).card ≤
      ((N - 2) / r) / 65 + 1 := by
  have h_eq : wr2ShearContractedFiber N r =
      residueClassSlice (wr2ShearContractedFiber N r) 2 1 := by
    ext q
    rw [residueClassSlice, mem_filter]
    constructor
    · intro hq
      have hq_copy := hq
      rw [wr2ShearContractedFiber, mem_filter, hyperbolicPrimeFiber, mem_filter] at hq_copy
      exact ⟨hq, hq_copy.1.2.2.1⟩
    · intro hq
      exact hq.1
  refine ⟨?_, ?_⟩
  · rw [h_eq]
    exact wr2ShearContractedFiber_slice_card_le_quotient_stride (by omega : 0 < 2) 1
  · intro c
    exact wr2ShearContractedFiber_slice_card_le_quotient_stride (by omega : 0 < 65) c

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.lower_pinch_of_homog_pinch_wr2
#print axioms WuPaper.ESZerosBridge.wr2ShearContractedFiber_lower_pinch_and_bilateral_omc
#print axioms WuPaper.ESZerosBridge.wr2ShearContractedFiber_zero_slice_eq_zero
#print axioms WuPaper.ESZerosBridge.wr2ShearContractedFiber_slice_card_le_quotient_stride
#print axioms WuPaper.ESZerosBridge.wr2ShearContractedFiber_card_le_half_div
