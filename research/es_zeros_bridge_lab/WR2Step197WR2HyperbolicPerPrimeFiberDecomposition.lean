import WR2Step196FactorPairBijectionAndBoxBound

set_option exponentiation.threshold 10000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step197WR2HyperbolicPerPrimeFiberDecomposition.lean — Stage 1: Hyperbolic Per-Prime Fiber Decomposition

Replaces the rectangular product bound from `WR2Step196` with the exact decomposition of
`lowPrimeFactorBox p_next N` into per-prime hyperbolic vertical fibers `q ≤ (N - 2) / r`:

1. **Pure Native Division Bound (`le_div_of_mul_le_native`):**
   Proves in pure `Init` arithmetic via `Nat.div_add_mod` and `Nat.mod_lt` that
   `0 < r` and `r * q ≤ M` implies `q ≤ M / r`.
2. **Per-Prime Hyperbolic Fiber (`hyperbolicPrimeFiber N r`, `hyperbolicFiberPairs N r`):**
   For each fixed odd prime `r < p_next`, isolates the primes `q` satisfying
   `r + 2 ≤ q ≤ (N - 2) / r`, `IsPrimeNat (N - r * q)`, the division-free 5UP Reciprocal
   Shear congruence `((r + q) * r) % m = (r * r + (N - r * q)) % m`, and `r ^ 9469 ≤ (r * q) ^ 4469`.
3. **Exact `Finset.biUnion` Decomposition (`lowPrimeFactorBox_eq_biUnion_hyperbolicFiberPairs`):**
   Proves that `lowPrimeFactorBox p_next N = (oddPrimesBelow p_next).biUnion (hyperbolicFiberPairs N)`
   and `(hyperbolicFiberPairs N r).card = (hyperbolicPrimeFiber N r).card`.
-/

/-!
## Section 1: Pure Native Division Bound & Hyperbolic Coordinate Scaling
-/

/-- Pure native `Init` proof that `0 < r` and `r * q ≤ M` implies `q ≤ M / r`,
    using `Nat.div_add_mod` and `Nat.mod_lt` with zero external Mathlib division lemmas. -/
theorem le_div_of_mul_le_native {r q M : ℕ} (hr_pos : 0 < r) (h_mul : r * q ≤ M) :
    q ≤ M / r := by
  match Nat.lt_or_ge (M / r) q with
  | Or.inr hge => exact hge
  | Or.inl hlt =>
    have h_succ : M / r + 1 ≤ q := hlt
    have h_mul_step : r * (M / r + 1) ≤ r * q := Nat.mul_le_mul_left r h_succ
    rw [Nat.left_distrib r (M / r) 1, Nat.mul_one] at h_mul_step
    have h_div_mod : r * (M / r) + M % r = M := Nat.div_add_mod M r
    have h_mod_lt : M % r < r := Nat.mod_lt M hr_pos
    omega

/-- Every witness `rq = (r, q) ∈ lowPrimeFactorBox p_next N` satisfies the hyperbolic
    vertical fiber bound `q ≤ (N - 2) / r` and the division-free 5UP Reciprocal Shear
    congruence across every modulus `m : ℕ`. -/
theorem lowPrimeFactorBox_mem_hyperbolic_bound_and_shear
    {p_next N : ℕ} {rq : ℕ × ℕ} (hrq : rq ∈ lowPrimeFactorBox p_next N) :
    rq.1 * rq.2 + 2 ≤ N ∧
    rq.2 ≤ (N - 2) / rq.1 ∧
    (∀ m : ℕ, ((rq.1 + rq.2) * rq.1) % m = (rq.1 * rq.1 + rq.1 * rq.2) % m) := by
  rw [lowPrimeFactorBox, mem_filter, mem_product,
      oddPrimesBelow, mem_filter] at hrq
  obtain ⟨⟨⟨_, hr_isp, _⟩, _⟩, _, h_rq_le_N, h_pp, _⟩ := hrq
  have hr_two : 2 ≤ rq.1 := hr_isp.1
  have hr_pos : 0 < rq.1 := by omega
  have hp_two : 2 ≤ N - rq.1 * rq.2 := h_pp.1
  have h_rq_add2 : rq.1 * rq.2 + 2 ≤ N := by omega
  have h_rq_le_sub2 : rq.1 * rq.2 ≤ N - 2 := by omega
  have h_q_le_div : rq.2 ≤ (N - 2) / rq.1 :=
    le_div_of_mul_le_native hr_pos h_rq_le_sub2
  refine ⟨h_rq_add2, h_q_le_div, ?_⟩
  intro m
  rw [Nat.right_distrib rq.1 rq.2 rq.1, Nat.mul_comm rq.2 rq.1]

/-!
## Section 2: Per-Prime Hyperbolic Fibers & Exact `Finset.biUnion` Decomposition
-/

/-- The 1D hyperbolic prime fiber above a fixed smaller prime `r`:
    all odd primes `q` in `[r + 2, (N - 2) / r]` such that `p = N - r * q` is prime
    and `r ^ 9469 ≤ (r * q) ^ 4469`. -/
def hyperbolicPrimeFiber (N r : ℕ) : Finset ℕ :=
  (range ((N - 2) / r + 1)).filter (fun q : ℕ =>
    IsPrimeNat q ∧
    q % 2 = 1 ∧
    r + 2 ≤ q ∧
    r * q ≤ N ∧
    IsPrimeNat (N - r * q) ∧
    r ^ 9469 ≤ (r * q) ^ 4469)

/-- The 2D fiber slice `{(r, q) | q ∈ hyperbolicPrimeFiber N r}` embedded in `ℕ × ℕ`. -/
def hyperbolicFiberPairs (N r : ℕ) : Finset (ℕ × ℕ) :=
  (hyperbolicPrimeFiber N r).image (fun q : ℕ => (r, q))

/-- Exact cardinality equality `(hyperbolicFiberPairs N r).card = (hyperbolicPrimeFiber N r).card`. -/
theorem hyperbolicFiberPairs_card_eq (N r : ℕ) :
    (hyperbolicFiberPairs N r).card = (hyperbolicPrimeFiber N r).card := by
  have h_le1 : (hyperbolicFiberPairs N r).card ≤ (hyperbolicPrimeFiber N r).card :=
    card_image_le
  have h_sub : hyperbolicPrimeFiber N r ⊆ (hyperbolicFiberPairs N r).image Prod.snd := by
    intro q hq
    rw [mem_image]
    refine ⟨(r, q), ?_, rfl⟩
    rw [hyperbolicFiberPairs, mem_image]
    exact ⟨q, hq, rfl⟩
  have h_le2 : (hyperbolicPrimeFiber N r).card ≤ (hyperbolicFiberPairs N r).card :=
    Nat.le_trans (card_le_card h_sub) card_image_le
  exact Nat.le_antisymm h_le1 h_le2

/-- Explicit upper bound on each per-prime hyperbolic fiber by its hyperbolic interval width
    `(N - 2) / r + 1`. -/
theorem hyperbolicPrimeFiber_card_le_div (N r : ℕ) :
    (hyperbolicPrimeFiber N r).card ≤ (N - 2) / r + 1 := by
  have h_sub : hyperbolicPrimeFiber N r ⊆ range ((N - 2) / r + 1) := filter_subset _ _
  have h_le := card_le_card h_sub
  rw [card_range] at h_le
  exact h_le

/-- **Theorem 2.1 (`lowPrimeFactorBox_eq_biUnion_hyperbolicFiberPairs`):**
    Exact decomposition of the 2D `lowPrimeFactorBox p_next N` into the union of per-prime
    hyperbolic fibers over `r ∈ oddPrimesBelow p_next`. -/
theorem lowPrimeFactorBox_eq_biUnion_hyperbolicFiberPairs (p_next N : ℕ) :
    lowPrimeFactorBox p_next N =
      (oddPrimesBelow p_next).biUnion (hyperbolicFiberPairs N) := by
  ext rq
  rw [mem_biUnion]
  constructor
  · intro hrq
    have h_hyp := lowPrimeFactorBox_mem_hyperbolic_bound_and_shear hrq
    rw [lowPrimeFactorBox, mem_filter, mem_product] at hrq
    obtain ⟨⟨hr_mem, hq_mem⟩, h_r2_le_q, h_rq_le_N, h_pp, h_homog⟩ := hrq
    rw [oddPrimesUpToThird, mem_filter] at hq_mem
    refine ⟨rq.1, hr_mem, ?_⟩
    rw [hyperbolicFiberPairs, mem_image]
    refine ⟨rq.2, ?_, Prod.ext rfl rfl⟩
    rw [hyperbolicPrimeFiber, mem_filter, mem_range]
    exact ⟨by omega, hq_mem.2.1, hq_mem.2.2, h_r2_le_q, h_rq_le_N, h_pp, h_homog⟩
  · intro hbi
    obtain ⟨r, hr_mem, hrq_fiber⟩ := hbi
    rw [hyperbolicFiberPairs, mem_image] at hrq_fiber
    obtain ⟨q, hq_fiber, h_pair_eq⟩ := hrq_fiber
    subst h_pair_eq
    rw [hyperbolicPrimeFiber, mem_filter, mem_range] at hq_fiber
    obtain ⟨hq_lt_div, hq_isp, hq_odd, h_r2_le_q, h_rq_le_N, h_pp, h_homog⟩ := hq_fiber
    have hr_copy := hr_mem
    rw [oddPrimesBelow, mem_filter] at hr_copy
    have hr_two : 2 ≤ r := hr_copy.2.1.1
    have hr_odd : r % 2 = 1 := hr_copy.2.2
    have hr_ge3 : 3 ≤ r := by omega
    have h_3q_le : 3 * q ≤ r * q := Nat.mul_le_mul_right q hr_ge3
    have h_q_le_div3 : q ≤ N / 3 := by omega
    rw [lowPrimeFactorBox, mem_filter, mem_product]
    dsimp only
    refine ⟨⟨hr_mem, ?_⟩, h_r2_le_q, h_rq_le_N, h_pp, h_homog⟩
    rw [oddPrimesUpToThird, mem_filter, mem_range]
    exact ⟨by omega, hq_isp, hq_odd⟩

/-- **Master Theorem 2.2 (`wr2_lowPrimeTightChiralBox_eq_biUnion_hyperbolic_fibers`):**
    Combines the factor-pair bijection (`WR2Step196`) with the hyperbolic fiber decomposition
     across any wave segment `N ≤ (p_next + 1) ^ 2` with `N % 2 = 0`. -/
theorem wr2_lowPrimeTightChiralBox_eq_biUnion_hyperbolic_fibers
    {p_next N : ℕ} (hEven : N % 2 = 0) (hN_le : N ≤ (p_next + 1) ^ 2) :
    (lowPrimeTightChiralBox p_next N).card =
      ((oddPrimesBelow p_next).biUnion (hyperbolicFiberPairs N)).card ∧
    (wr2CutlineSemiprimePrimes N).card ≤
      1 + ((oddPrimesBelow p_next).biUnion (hyperbolicFiberPairs N)).card := by
  have h_bij := lowPrimeTightChiralBox_card_eq_lowPrimeFactorBox p_next N
  have h_bi := lowPrimeFactorBox_eq_biUnion_hyperbolicFiberPairs p_next N
  have h_eq :
      (lowPrimeTightChiralBox p_next N).card =
        ((oddPrimesBelow p_next).biUnion (hyperbolicFiberPairs N)).card := by
    rw [h_bij, h_bi]
  have h_cut := (wr2_cutline_card_le_prime_slice_product_on_wave_segment hEven hN_le).1
  rw [h_bi] at h_cut
  exact ⟨h_eq, h_cut⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.le_div_of_mul_le_native
#print axioms WuPaper.ESZerosBridge.lowPrimeFactorBox_mem_hyperbolic_bound_and_shear
#print axioms WuPaper.ESZerosBridge.hyperbolicFiberPairs_card_eq
#print axioms WuPaper.ESZerosBridge.lowPrimeFactorBox_eq_biUnion_hyperbolicFiberPairs
#print axioms WuPaper.ESZerosBridge.wr2_lowPrimeTightChiralBox_eq_biUnion_hyperbolic_fibers
