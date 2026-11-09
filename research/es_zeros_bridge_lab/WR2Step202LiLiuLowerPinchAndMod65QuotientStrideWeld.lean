import WR2Step200LiLiu919PinchCutoffAndShearFiberContraction

set_option exponentiation.threshold 10000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step202LiLiuLowerPinchAndMod65QuotientStrideWeld.lean — `10/9` Lower Pinch Cancellation & Mod-65 Stride Weld to `D19 N`

Completes the per-prime fiber contraction on the `Goldbach.All` (`D19 N`) branch:

1. **Exact `10/9` Lower Pinch Cancellation (`liliuShearContractedFiber_lower_pinch_10_9`):**
   Cancels `r ^ 9 > 0` from `r ^ 19 ≤ (r * q) ^ 9` to prove `r ^ 10 ≤ q ^ 9` on every
   `q ∈ liliuShearContractedFiber N r`.
2. **Mod-65 & Parity Quotient-Stride Contraction (`liliuShearContractedFiber_stride_bounds`):**
   Proves that for every `r` and every residue class `c`,
   `(liliuResidueSlice N r 65 c).card ≤ (N / r) / 65 + 1` and
   `(liliuShearContractedFiber N r).card ≤ (N / r) / 2 + 1`, with zero-slice elimination
   `(liliuResidueSlice N r m 0).card = 0` for all `2 ≤ m ≤ r`.
3. **Master 25-Module `D19 N` & Quotient-Stride Capstone (`master_25module_D19_pinched_stride_goldbach_capstone`):**
   Unites `Goldbach.one_plus_one_nine_count` (`liuMainTerm0004 N < (D19 N : ℝ)`), the
   intrinsic `9/19` upper pinch (`r ^ 19 ≤ N ^ 9`), the `10/9` lower pinch (`r ^ 10 ≤ q ^ 9`),
   the Mod-65 quotient-stride bounds, and the Factorial Lighthouse next-prime generator.
-/

/-!
## Section 1: Pure Native `10/9` Lower Pinch Cancellation (`r ^ 19 ≤ (r * q) ^ 9 → r ^ 10 ≤ q ^ 9`)
-/

theorem mul_pow_local_liliu (x y : ℕ) : ∀ n : ℕ, (x * y) ^ n = x ^ n * y ^ n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, mul_pow_local_liliu x y n]
    calc (x ^ n * y ^ n) * (x * y)
      _ = x ^ n * (y ^ n * (x * y)) := Nat.mul_assoc _ _ _
      _ = x ^ n * ((y ^ n * x) * y) := by rw [Nat.mul_assoc (y ^ n) x y]
      _ = x ^ n * ((x * y ^ n) * y) := by rw [Nat.mul_comm (y ^ n) x]
      _ = x ^ n * (x * (y ^ n * y)) := by rw [Nat.mul_assoc x (y ^ n) y]
      _ = (x ^ n * x) * (y ^ n * y) := (Nat.mul_assoc (x ^ n) x (y ^ n * y)).symm

theorem pow_add_local_liliu (x m : ℕ) : ∀ n : ℕ, x ^ (m + n) = x ^ m * x ^ n
  | 0 => by rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | n + 1 => by
    rw [Nat.add_succ, Nat.pow_succ, Nat.pow_succ, pow_add_local_liliu x m n, Nat.mul_assoc]

theorem pow_pos_of_pos_liliu {r : ℕ} (hr : 0 < r) : ∀ n : ℕ, 0 < r ^ n
  | 0 => by simp
  | n + 1 => by
    rw [Nat.pow_succ]
    have hn : 0 < r ^ n := pow_pos_of_pos_liliu hr n
    have h1 : 1 * 1 ≤ r ^ n * r := Nat.mul_le_mul hn hr
    omega

theorem le_of_mul_le_mul_left_pos_liliu {a b c : ℕ} (ha : 0 < a) (h : a * b ≤ a * c) :
    b ≤ c := by
  match Nat.lt_or_ge c b with
  | Or.inr hle => exact hle
  | Or.inl hlt =>
    have h_succ : c + 1 ≤ b := hlt
    have h_mul : a * (c + 1) ≤ a * b := Nat.mul_le_mul_left a h_succ
    rw [Nat.left_distrib a c 1, Nat.mul_one] at h_mul
    omega

/-- **Theorem 1.1 (`lower_pinch_of_homog_pinch_liliu`):**
    Cancels `r ^ a > 0` from `r ^ (a + b) ≤ (r * q) ^ a` to prove `r ^ b ≤ q ^ a`. -/
theorem lower_pinch_of_homog_pinch_liliu
    {r q a b : ℕ} (hr_pos : 0 < r) (h_homog : r ^ (a + b) ≤ (r * q) ^ a) :
    r ^ b ≤ q ^ a := by
  rw [pow_add_local_liliu r a b, mul_pow_local_liliu r q a] at h_homog
  have hra_pos : 0 < r ^ a := pow_pos_of_pos_liliu hr_pos a
  exact le_of_mul_le_mul_left_pos_liliu hra_pos h_homog

/-- Pure native proof that `2 ≤ m < p` and `IsPrimeNat p` implies `1 ≤ p % m`. -/
theorem mod_pos_of_lt_isPrimeNat_liliu {m p : ℕ} (hm2 : 2 ≤ m) (h_lt : m < p) (hp : IsPrimeNat p) :
    1 ≤ p % m := by
  if h0 : p % m = 0 then
    have h_div_mod : m * (p / m) + p % m = p := Nat.div_add_mod p m
    have h_dvd : m ∣ p := ⟨p / m, by omega⟩
    cases hp.2 m h_dvd with
    | inl h1 => omega
    | inr hp_eq => omega
  else
    omega

/-- **Theorem 1.2 (`liliuShearContractedFiber_lower_pinch_10_9`):**
    Every `q ∈ liliuShearContractedFiber N r` (with `0 < r`) satisfies the explicit
    lower exponent pinch `r ^ 10 ≤ q ^ 9` together with `1 ≤ q % m` for all `2 ≤ m ≤ r`. -/
theorem liliuShearContractedFiber_lower_pinch_10_9
    {N r q : ℕ} (hr_pos : 0 < r) (hq : q ∈ liliuShearContractedFiber N r) :
    r ^ 10 ≤ q ^ 9 ∧
    r ^ 19 ≤ N ^ 9 ∧
    ∀ m : ℕ, 2 ≤ m → m ≤ r → 1 ≤ q % m := by
  rw [liliuShearContractedFiber, mem_filter, liliuHyperbolicPrimeFiber, mem_filter] at hq
  obtain ⟨⟨_, hq_isp, _, h_r2_le_q, _, h_homog⟩, h_r19_le_N9, _⟩ := hq
  have h_sum_exp : (9 : ℕ) + 10 = 19 := rfl
  rw [← h_sum_exp] at h_homog
  have h_lower : r ^ 10 ≤ q ^ 9 := lower_pinch_of_homog_pinch_liliu hr_pos h_homog
  refine ⟨h_lower, h_r19_le_N9, ?_⟩
  intro m hm2 hmr
  have h_lt : m < q := by omega
  exact mod_pos_of_lt_isPrimeNat_liliu hm2 h_lt hq_isp

/-!
## Section 2: Quotient-Stride Contraction Bounds on `liliuShearContractedFiber N r`
-/

/-- The `c`-th residue slice of `liliuShearContractedFiber N r` modulo `m`. -/
def liliuResidueSlice (N r m c : ℕ) : Finset ℕ :=
  (liliuShearContractedFiber N r).filter (fun q : ℕ => q % m = c)

/-- Linear quotient reconstruction map `k ↦ m * k + c`. -/
def liliuReconstructQuotient (m c k : ℕ) : ℕ :=
  m * k + c

/-- **Theorem 2.1 (`liliuResidueSlice_card_le_quotient_stride`):**
    For every modulus `m > 0` and residue class `c`,
    `(liliuResidueSlice N r m c).card ≤ (N / r) / m + 1`. -/
theorem liliuResidueSlice_card_le_quotient_stride
    {N r m : ℕ} (hm_pos : 0 < m) (c : ℕ) :
    (liliuResidueSlice N r m c).card ≤ (N / r) / m + 1 := by
  have h_sub :
      liliuResidueSlice N r m c ⊆
        (range ((N / r) / m + 1)).image (liliuReconstructQuotient m c) := by
    intro q hq
    rw [liliuResidueSlice, mem_filter, liliuShearContractedFiber, mem_filter,
        liliuHyperbolicPrimeFiber, mem_filter, mem_range] at hq
    obtain ⟨⟨⟨hq_lt_div, _⟩, _⟩, h_mod_eq⟩ := hq
    have h_q_le : q ≤ N / r := by omega
    have h_div_mod : m * (q / m) + q % m = q := Nat.div_add_mod q m
    have h_mul_le : m * (q / m) ≤ N / r := by omega
    have h_quot_le : q / m ≤ (N / r) / m :=
      le_div_of_mul_le_liliu hm_pos h_mul_le
    rw [mem_image]
    refine ⟨q / m, ?_, ?_⟩
    · rw [mem_range]
      omega
    · unfold liliuReconstructQuotient
      omega
  have h_card := Nat.le_trans (card_le_card h_sub) card_image_le
  rw [card_range] at h_card
  exact h_card

/-- **Theorem 2.2 (`liliuShearContractedFiber_stride_bounds`):**
    For every `N, r`:
    1. `(liliuShearContractedFiber N r).card ≤ (N / r) / 2 + 1` (odd-prime parity halving),
    2. For every residue class `c`, `(liliuResidueSlice N r 65 c).card ≤ (N / r) / 65 + 1`
       (Mod-65 Triple-QR / Reciprocal Shear stride bound), and
    3. For every `m` with `2 ≤ m ≤ r`, `(liliuResidueSlice N r m 0).card = 0` (OMC zero-slice elimination). -/
theorem liliuShearContractedFiber_stride_bounds (N r : ℕ) :
    (liliuShearContractedFiber N r).card ≤ (N / r) / 2 + 1 ∧
    (∀ c : ℕ, (liliuResidueSlice N r 65 c).card ≤ (N / r) / 65 + 1) ∧
    (∀ m : ℕ, 2 ≤ m → m ≤ r → (liliuResidueSlice N r m 0).card = 0) := by
  have h_eq : liliuShearContractedFiber N r = liliuResidueSlice N r 2 1 := by
    ext q
    rw [liliuResidueSlice, mem_filter]
    constructor
    · intro hq
      have hq_copy := hq
      rw [liliuShearContractedFiber, mem_filter, liliuHyperbolicPrimeFiber, mem_filter] at hq_copy
      exact ⟨hq, hq_copy.1.2.2.1⟩
    · intro hq
      exact hq.1
  refine ⟨?_, ?_, ?_⟩
  · rw [h_eq]
    exact liliuResidueSlice_card_le_quotient_stride (by omega : 0 < 2) 1
  · intro c
    exact liliuResidueSlice_card_le_quotient_stride (by omega : 0 < 65) c
  · intro m hm2 hmr
    match Nat.eq_zero_or_pos (liliuResidueSlice N r m 0).card with
    | Or.inl h0 => exact h0
    | Or.inr hpos =>
      obtain ⟨q, hq⟩ := card_pos.mp hpos
      rw [liliuResidueSlice, mem_filter] at hq
      have hr_pos : 0 < r := by omega
      have h_omc := (liliuShearContractedFiber_lower_pinch_10_9 hr_pos hq.1).2.2 m hm2 hmr
      omega

/-!
## Section 3: Master 25-Module Capstone Welding `D19 N`, Bilateral Pinches & Quotient Strides
-/

/-- **Master Theorem 3.1 (`master_25module_D19_pinched_stride_goldbach_capstone`):**
    Complete 25-Module Capstone uniting `Goldbach.one_plus_one_nine_count` (`D19 N`),
    the intrinsic `9/19` upper pinch (`r ^ 19 ≤ N ^ 9`), the cancelled `10/9` lower pinch
    (`r ^ 10 ≤ q ^ 9`), the Mod-65 & Parity quotient-stride bounds, and the Factorial
    Lighthouse next-prime generator (`hasNextPrimeConnection_unconditional`). -/
theorem master_25module_D19_pinched_stride_goldbach_capstone :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (∀ r : ℕ, N ^ 9 < r ^ 19 → (liliuHyperbolicPrimeFiber N r).card = 0) ∧
      (∀ r q : ℕ, 0 < r → q ∈ liliuShearContractedFiber N r →
        r ^ 10 ≤ q ^ 9 ∧ r ^ 19 ≤ N ^ 9) ∧
      (∀ r : ℕ,
        (liliuShearContractedFiber N r).card ≤ (N / r) / 2 + 1 ∧
        ∀ c : ℕ, (liliuResidueSlice N r 65 c).card ≤ (N / r) / 65 + 1) ∧
      (fiveupPinchedQRSubfilter 9 10 N).card ≤
        1 + ((pinchedOddPrimes919 N).biUnion (liliuShearContractedFiberPairs N)).card ∧
      ((((1 + ((pinchedOddPrimes919 N).biUnion (liliuShearContractedFiberPairs N)).card : ℕ) : ℝ) ≤
          liuMainTerm0004 N) →
        ∃ p q p_next' : ℕ,
          Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next' ∧ IsPrimeNat p_next') := by
  obtain ⟨K, hK4, hCap⟩ := liliu_D19_intrinsic_919_pinched_shear_fiber_capstone
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven
  have hM := hCap N hNK hEven
  refine ⟨hM.1, hM.2.1, ?_, ?_, hM.2.2.1, hM.2.2.2⟩
  · intro r q hr_pos hq
    have h_lp := liliuShearContractedFiber_lower_pinch_10_9 hr_pos hq
    exact ⟨h_lp.1, h_lp.2.1⟩
  · intro r
    have h_st := liliuShearContractedFiber_stride_bounds N r
    exact ⟨h_st.1, h_st.2.1⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.lower_pinch_of_homog_pinch_liliu
#print axioms WuPaper.ESZerosBridge.liliuShearContractedFiber_lower_pinch_10_9
#print axioms WuPaper.ESZerosBridge.liliuResidueSlice_card_le_quotient_stride
#print axioms WuPaper.ESZerosBridge.liliuShearContractedFiber_stride_bounds
#print axioms WuPaper.ESZerosBridge.master_25module_D19_pinched_stride_goldbach_capstone
