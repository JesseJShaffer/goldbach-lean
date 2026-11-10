import WR2Step253WR2ExactSpeciesSQ1P2AndCubeTailPartition

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step255WR2ScreenedConcreteKbExactSpeciesAndExponentSeparation.lean — R1–R4 Implementation: Screened Native `concreteKb` Equality, Unconditional `SQ-1` + `P-2` Balance, Route B Credit Split & `M ≥ 2^18` Exponent Separation (`WR2` Track 1)

Implements Recommendations R1, R2, R3, and R4 of the November 9 closure plan:

1. **Section 1 (R1 & R2) — Screened Native `concreteKb` Carrier (`screenedConcreteKbRadii`,
   `screenedConcreteKbUpper`) & Unconditional Sub-Cubic `SQ-1` + `P-2` Balance:**
   - Defines `sqrtMidpointCutoff M := Nat.sqrt M + 1`, `screenedConcreteKbRadii M`, and
     `screenedConcreteKbUpper M := roughSurvivorSet (concreteKbUpper M) (sqrtMidpointCutoff M)`.
   - Proves `(screenedConcreteKbRadii M).image (fun R => M + R) = screenedConcreteKbUpper M`
     and `(screenedConcreteKbRadii M).card = (screenedConcreteKbUpper M).card`.
   - Proves that for ALL `M ≥ 1`, `2 * M < (sqrtMidpointCutoff M) ^ 3`, so
     `(higherSpeciesTailSet (concreteKbUpper M) (sqrtMidpointCutoff M)).card = 0` and
     `(screenedConcreteKbUpper M).card = (primeSurvivorSet (concreteKbUpper M) q_b).card + (sq1TailSet (concreteKbUpper M) q_b).card + (p2TailSet (concreteKbUpper M) q_b).card`!
2. **Section 2 (R3) — Route B Retained vs. Rejected Catalog Credit Balance:**
   - Splits any upper composite catalog `H : Finset ℕ` into `retainedByLowerPrime M H`
     (`IsPrimeNat (2 * M - u)`) and `rejectedByLowerComposite M H` (`¬ IsPrimeNat (2 * M - u)`),
     proving `H.card = (retainedByLowerPrime M H).card + (rejectedByLowerComposite M H).card`.
3. **Section 3 (R4) — Uniform Algebraic Exponent Separation for `M ≥ 2^18 = 262144`:**
   - Proves in pure native `Init` arithmetic that for `262144 ≤ M` and `sqrtMidpointCutoff M ≤ r`,
     BOTH `(2 * M) ^ 9 < r ^ 19` (the `(9, 19)` pinch separation) AND
     `(2 * M) ^ 4469 < r ^ 9469` (the literal `goldbach-lean` `(4469, 9469)` pinch separation) hold,
     forcing the pinched subset of `pn1RoughCompositeTail (concreteKbUpper M) (sqrtMidpointCutoff M)`
     to be identically empty (`card = 0`)!
-/

/-!
## Section 1 (R1 & R2): Screened Native `concreteKb` Carrier & Unconditional `SQ-1` + `P-2` Balance
-/

/-- The native `Step24` square-root screening horizon `b + 1 = ⌊√M⌋ + 1`. -/
def sqrtMidpointCutoff (M : ℕ) : ℕ :=
  Nat.sqrt M + 1

/-- The native `Step24` screened radius carrier `K(M)` (R1):
    radii `R ∈ concreteKbRadii M` whose upper partner `M + R` survives all proper
    divisor strikes `< sqrtMidpointCutoff M`. -/
def screenedConcreteKbRadii (M : ℕ) : Finset ℕ :=
  (concreteKbRadii M).filter (fun R : ℕ =>
    2 ≤ M + R ∧ ∀ d ∈ range (sqrtMidpointCutoff M), 2 ≤ d → 1 ≤ (M + R) % d)

/-- The reflected upper `Step24` screened carrier `K_upper(M)` (R1). -/
def screenedConcreteKbUpper (M : ℕ) : Finset ℕ :=
  roughSurvivorSet (concreteKbUpper M) (sqrtMidpointCutoff M)

/-- **Theorem 1.1 (`screenedConcreteKb_image_and_card_eq` — R1):**
    Exact set and cardinality correspondence between `screenedConcreteKbRadii M` and
    `screenedConcreteKbUpper M`. -/
theorem screenedConcreteKb_image_and_card_eq (M : ℕ) :
    (screenedConcreteKbRadii M).image (fun R : ℕ => M + R) =
      screenedConcreteKbUpper M ∧
    (screenedConcreteKbRadii M).card = (screenedConcreteKbUpper M).card := by
  have h_img :
      (screenedConcreteKbRadii M).image (fun R : ℕ => M + R) =
        screenedConcreteKbUpper M := by
    ext u
    rw [mem_image, screenedConcreteKbUpper, roughSurvivorSet, mem_filter]
    constructor
    · rintro ⟨R, hR, rfl⟩
      rw [screenedConcreteKbRadii, mem_filter] at hR
      refine ⟨?_, hR.2.1, hR.2.2⟩
      rw [concreteKbUpper, mem_image]
      exact ⟨R, hR.1, rfl⟩
    · rintro ⟨hu_kb, hu2, hu_rough⟩
      rw [concreteKbUpper, mem_image] at hu_kb
      obtain ⟨R, hR, rfl⟩ := hu_kb
      refine ⟨R, ?_, rfl⟩
      rw [screenedConcreteKbRadii, mem_filter]
      exact ⟨hR, hu2, hu_rough⟩
  have h_inj : Set.InjOn (fun R : ℕ => M + R) (↑(screenedConcreteKbRadii M) : Set ℕ) := by
    intro a _ b _ hab
    dsimp only at hab
    omega
  have h_card :
      ((screenedConcreteKbRadii M).image (fun R : ℕ => M + R)).card =
        (screenedConcreteKbRadii M).card :=
    Finset.card_image_of_injOn h_inj
  rw [h_img] at h_card
  exact ⟨h_img, h_card.symm⟩

/-- **Lemma 1.2 (`two_mul_M_lt_sqrtMidpointCutoff_cube`):**
    For EVERY `M ≥ 1`, `2 ≤ sqrtMidpointCutoff M`, `M + 1 ≤ (sqrtMidpointCutoff M) ^ 2`,
    and `2 * M < (sqrtMidpointCutoff M) ^ 3`. -/
theorem two_mul_M_lt_sqrtMidpointCutoff_cube {M : ℕ} (hM1 : 1 ≤ M) :
    2 ≤ sqrtMidpointCutoff M ∧
    2 * M < (sqrtMidpointCutoff M) ^ 3 := by
  unfold sqrtMidpointCutoff
  have h_sqrt_pos : 1 ≤ Nat.sqrt M := by
    match Nat.eq_zero_or_pos (Nat.sqrt M) with
    | Or.inr hpos => exact hpos
    | Or.inl h0 =>
      have h_lt := Nat.lt_succ_sqrt M
      rw [h0] at h_lt
      omega
  set q_b := Nat.sqrt M + 1
  have hqb_ge2 : 2 ≤ q_b := by omega
  have hM_lt_sq : M < q_b * q_b := Nat.lt_succ_sqrt M
  have hM1_le_sq : M + 1 ≤ q_b * q_b := hM_lt_sq
  have h_2M2_le : 2 * (M + 1) ≤ q_b * (q_b * q_b) :=
    Nat.mul_le_mul hqb_ge2 hM1_le_sq
  have h_cube_eq : q_b ^ 3 = q_b * (q_b * q_b) := by
    show (1 * q_b) * q_b * q_b = q_b * (q_b * q_b)
    rw [Nat.one_mul, Nat.mul_assoc q_b q_b q_b]
  rw [← h_cube_eq] at h_2M2_le
  exact ⟨hqb_ge2, by omega⟩

/-- **Theorem 1.3 (`screenedConcreteKbUpper_exact_sq1_p2_balance` — R1 & R2):**
    Unconditional Sub-Cubic Species Balance on `screenedConcreteKbUpper M`:
    For EVERY `M ≥ 1`, let `q_b := sqrtMidpointCutoff M`. Then:
    1. `(higherSpeciesTailSet (concreteKbUpper M) q_b).card = 0` (zero `Ω ≥ 3` composites),
    2. `(pn1RoughCompositeTail (concreteKbUpper M) q_b).card = (sq1TailSet (concreteKbUpper M) q_b).card + (p2TailSet (concreteKbUpper M) q_b).card`, and
    3. `(screenedConcreteKbRadii M).card = (primeSurvivorSet (concreteKbUpper M) q_b).card + (sq1TailSet (concreteKbUpper M) q_b).card + (p2TailSet (concreteKbUpper M) q_b).card`! -/
theorem screenedConcreteKbUpper_exact_sq1_p2_balance {M : ℕ} (hM1 : 1 ≤ M) :
    let q_b := sqrtMidpointCutoff M
    (higherSpeciesTailSet (concreteKbUpper M) q_b).card = 0 ∧
    (pn1RoughCompositeTail (concreteKbUpper M) q_b).card =
      (sq1TailSet (concreteKbUpper M) q_b).card +
        (p2TailSet (concreteKbUpper M) q_b).card ∧
    (screenedConcreteKbRadii M).card =
      (primeSurvivorSet (concreteKbUpper M) q_b).card +
        (sq1TailSet (concreteKbUpper M) q_b).card +
        (p2TailSet (concreteKbUpper M) q_b).card := by
  dsimp only
  have h_cube_bound : ∀ u ∈ concreteKbUpper M, u < (sqrtMidpointCutoff M) ^ 3 := by
    intro u hu
    have hu_full :=
      (concreteKbUpper_subset_fullLowerMURUpper_and_non_self_obstructing M).2.1 hu
    have hu_lt_2M : u < 2 * M := (fullLowerMURUpper_mem_props hu_full).2.2.1
    have h_2M_lt := (two_mul_M_lt_sqrtMidpointCutoff_cube hM1).2
    exact Nat.lt_trans hu_lt_2M h_2M_lt
  have h_empty := higherSpeciesTailSet_eq_empty_below_cube h_cube_bound
  have h_part :=
    (exact_species_three_way_composite_tail_partition
      (concreteKbUpper M) (sqrtMidpointCutoff M)).2
  have h_card_eq := (screenedConcreteKb_image_and_card_eq M).2
  unfold screenedConcreteKbUpper at h_card_eq
  exact ⟨h_empty.1, h_empty.2, by omega⟩

/-!
## Section 2 (R3): Route B Retained vs. Rejected Catalog Credit Balance
-/

/-- Subset of an upper composite catalog `H` retained by the lower-MUR primality test (`IsPrimeNat (2 * M - u)`). -/
def retainedByLowerPrime (M : ℕ) (H : Finset ℕ) : Finset ℕ :=
  H.filter (fun u : ℕ => IsPrimeNat (2 * M - u))

/-- Subset of an upper composite catalog `H` rejected by having a composite lower partner (`¬ IsPrimeNat (2 * M - u)`). -/
def rejectedByLowerComposite (M : ℕ) (H : Finset ℕ) : Finset ℕ :=
  H.filter (fun u : ℕ => ¬ IsPrimeNat (2 * M - u))

/-- **Theorem 2.1 (`routeB_retained_rejected_catalog_credit_balance` — R3):**
    For any upper catalog `H : Finset ℕ` (and in particular for `H_SQ1` and `H_P2`),
    `retainedByLowerPrime M H` and `rejectedByLowerComposite M H` are disjoint and
    satisfy the exact Route B conservation law:
    `H.card = (retainedByLowerPrime M H).card + (rejectedByLowerComposite M H).card`. -/
theorem routeB_retained_rejected_catalog_credit_balance (M : ℕ) (H : Finset ℕ) :
    Disjoint (retainedByLowerPrime M H) (rejectedByLowerComposite M H) ∧
    H = retainedByLowerPrime M H ∪ rejectedByLowerComposite M H ∧
    H.card =
      (retainedByLowerPrime M H).card + (rejectedByLowerComposite M H).card := by
  have h_disj : Disjoint (retainedByLowerPrime M H) (rejectedByLowerComposite M H) := by
    apply Finset.disjoint_left.mpr
    intro u h1 h2
    rw [retainedByLowerPrime, mem_filter] at h1
    rw [rejectedByLowerComposite, mem_filter] at h2
    exact h2.2 h1.2
  have h_eq : H = retainedByLowerPrime M H ∪ rejectedByLowerComposite M H := by
    ext u
    simp only [mem_union, retainedByLowerPrime, rejectedByLowerComposite, mem_filter]
    constructor
    · intro hu
      cases Classical.em (IsPrimeNat (2 * M - u)) with
      | inl hp => exact Or.inl ⟨hu, hp⟩
      | inr hnp => exact Or.inr ⟨hu, hnp⟩
    · intro hor
      cases hor with
      | inl h1 => exact h1.1
      | inr h2 => exact h2.1
  have h_card :
      H.card =
        (retainedByLowerPrime M H).card + (rejectedByLowerComposite M H).card := by
    conv_lhs => rw [h_eq]
    exact card_union_of_disjoint h_disj
  exact ⟨h_disj, h_eq, h_card⟩

/-!
## Section 3 (R4): Uniform Algebraic Exponent Separation for `M ≥ 2^18 = 262144`
-/

/-- Pure `Init` monotonicity of `a ^ n` in the base `a`. -/
theorem pow_le_pow_left_native {a b : ℕ} (hab : a ≤ b) : ∀ n : ℕ, a ^ n ≤ b ^ n
  | 0 => Nat.le_refl 1
  | n + 1 => Nat.mul_le_mul (pow_le_pow_left_native hab n) hab

/-- Pure `Init` strict monotonicity of `a ^ (n + 1)` in the base `a` for `a < b`. -/
theorem pow_succ_lt_pow_succ_of_lt_native {a b : ℕ} (hab : a < b) :
    ∀ n : ℕ, a ^ (n + 1) < b ^ (n + 1)
  | 0 => by
    show 1 * a < 1 * b
    omega
  | n + 1 => by
    have ih := pow_succ_lt_pow_succ_of_lt_native hab n
    have hb_pos : 0 < b := by omega
    have h1 : a ^ (n + 1) * a ≤ a ^ (n + 1) * b :=
      Nat.mul_le_mul_left (a ^ (n + 1)) (Nat.le_of_lt hab)
    have h2 : a ^ (n + 1) * b < b ^ (n + 1) * b :=
      Nat.mul_lt_mul_of_pos_right ih hb_pos
    exact Nat.lt_of_le_of_lt h1 h2

/-- Pure `Init` proof of `(a * b) ^ n = a ^ n * b ^ n`. -/
theorem mul_pow_native (a b : ℕ) : ∀ n : ℕ, (a * b) ^ n = a ^ n * b ^ n
  | 0 => rfl
  | n + 1 => by
    show (a * b) ^ n * (a * b) = (a ^ n * a) * (b ^ n * b)
    rw [mul_pow_native a b n]
    calc (a ^ n * b ^ n) * (a * b)
      _ = a ^ n * (b ^ n * (a * b)) := Nat.mul_assoc (a ^ n) (b ^ n) (a * b)
      _ = a ^ n * ((b ^ n * a) * b) := by rw [Nat.mul_assoc (b ^ n) a b]
      _ = a ^ n * ((a * b ^ n) * b) := by rw [Nat.mul_comm (b ^ n) a]
      _ = a ^ n * (a * (b ^ n * b)) := by rw [Nat.mul_assoc a (b ^ n) b]
      _ = (a ^ n * a) * (b ^ n * b) := (Nat.mul_assoc (a ^ n) a (b ^ n * b)).symm

/-- Pure `Init` proof of `a ^ (m + n) = a ^ m * a ^ n`. -/
theorem pow_add_native (a m : ℕ) : ∀ n : ℕ, a ^ (m + n) = a ^ m * a ^ n
  | 0 => (Nat.mul_one (a ^ m)).symm
  | n + 1 => by
    show a ^ (m + n) * a = a ^ m * (a ^ n * a)
    rw [pow_add_native a m n, Nat.mul_assoc (a ^ m) (a ^ n) a]

/-- Pure `Init` proof of `a ^ (m * n) = (a ^ m) ^ n`. -/
theorem pow_mul_native (a m : ℕ) : ∀ n : ℕ, a ^ (m * n) = (a ^ m) ^ n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.mul_succ m n, pow_add_native a (m * n) m, pow_mul_native a m n]
    rfl

/-- **Theorem 3.1 (`exponent_separation_above_sqrt_M_ge_262144` — R4):**
    For EVERY `M ≥ 2^18 = 262144` and every factor `r ≥ sqrtMidpointCutoff M`:
    1. `513 ≤ r` (`2 ^ 9 < r`) and `M < r ^ 2`,
    2. `(2 * M) ^ 9 < r ^ 19` (R4 `(9, 19)` pinch separation), and
    3. `(2 * M) ^ 4469 < r ^ 9469` (literal `goldbach-lean` `(4469, 9469)` pinch separation). -/
theorem exponent_separation_above_sqrt_M_ge_262144
    {M r : ℕ} (hM : 262144 ≤ M) (hr : sqrtMidpointCutoff M ≤ r) :
    513 ≤ r ∧
    (2 * M) ^ 9 < r ^ 19 ∧
    (2 * M) ^ 4469 < r ^ 9469 := by
  unfold sqrtMidpointCutoff at hr
  have h_512_le_sqrt : 512 ≤ Nat.sqrt M := by
    match Nat.lt_or_ge (Nat.sqrt M) 512 with
    | Or.inr hge => exact hge
    | Or.inl hlt =>
      have h_succ_le : Nat.sqrt M + 1 ≤ 512 := hlt
      have h_sq_le : (Nat.sqrt M + 1) * (Nat.sqrt M + 1) ≤ 512 * 512 :=
        Nat.mul_le_mul h_succ_le h_succ_le
      have h_M_lt : M < (Nat.sqrt M + 1) * (Nat.sqrt M + 1) := Nat.lt_succ_sqrt M
      omega
  have hr_ge_513 : 513 ≤ r := by omega
  have h_2pow9_lt_r : 2 ^ 9 < r := by
    have h_2pow9 : 2 ^ 9 = 512 := rfl
    omega
  have hM_lt_sq : M < (Nat.sqrt M + 1) * (Nat.sqrt M + 1) := Nat.lt_succ_sqrt M
  have h_sq_mono : (Nat.sqrt M + 1) * (Nat.sqrt M + 1) ≤ r * r :=
    Nat.mul_le_mul hr hr
  have hM_lt_r2 : M < r ^ 2 := by
    rw [nat_sq_eq_mul r]
    exact Nat.lt_of_lt_of_le hM_lt_sq h_sq_mono
  have h_M9_lt_r18 : M ^ 9 < r ^ 18 := by
    have h1 : M ^ 9 < (r ^ 2) ^ 9 := pow_succ_lt_pow_succ_of_lt_native hM_lt_r2 8
    rw [← pow_mul_native r 2 9] at h1
    exact h1
  have h_2M9_lt_r19 : (2 * M) ^ 9 < r ^ 19 := by
    rw [mul_pow_native 2 M 9]
    have h_r19 : r ^ 19 = r * r ^ 18 := by
      have h_add := pow_add_native r 1 18
      have hr1 : r ^ 1 = r := Nat.pow_one r
      rw [hr1] at h_add
      exact h_add
    rw [h_r19]
    have h_le1 : 2 ^ 9 * M ^ 9 ≤ r * M ^ 9 :=
      Nat.mul_le_mul_right (M ^ 9) (Nat.le_of_lt h_2pow9_lt_r)
    have h_lt2 : r * M ^ 9 < r * r ^ 18 :=
      Nat.mul_lt_mul_of_pos_left h_M9_lt_r18 (by omega : 0 < r)
    exact Nat.lt_of_le_of_lt h_le1 h_lt2
  have h_M4469_lt_r8938 : M ^ 4469 < r ^ 8938 := by
    have h1 : M ^ 4469 < (r ^ 2) ^ 4469 :=
      pow_succ_lt_pow_succ_of_lt_native hM_lt_r2 4468
    rw [← pow_mul_native r 2 4469] at h1
    exact h1
  have h_2pow4469_le_r531 : 2 ^ 4469 ≤ r ^ 531 := by
    have h_step1 : 2 ^ 4469 ≤ 2 ^ (4469 + 310) :=
      nat_pow_le_pow_right_native (by omega : 1 ≤ 2) 4469 310
    have h_eq_4779 : 4469 + 310 = 9 * 531 := rfl
    rw [h_eq_4779, pow_mul_native 2 9 531] at h_step1
    have h_step2 : (2 ^ 9) ^ 531 ≤ r ^ 531 :=
      pow_le_pow_left_native (Nat.le_of_lt h_2pow9_lt_r) 531
    exact Nat.le_trans h_step1 h_step2
  have h_2M4469_lt_r9469 : (2 * M) ^ 4469 < r ^ 9469 := by
    rw [mul_pow_native 2 M 4469]
    have h_r9469 : r ^ 9469 = r ^ 531 * r ^ 8938 :=
      pow_add_native r 531 8938
    rw [h_r9469]
    have h_le1 : 2 ^ 4469 * M ^ 4469 ≤ r ^ 531 * M ^ 4469 :=
      Nat.mul_le_mul_right (M ^ 4469) h_2pow4469_le_r531
    have hr531_pos : 0 < r ^ 531 := nat_pow_pos (by omega : 0 < r) 531
    have h_lt2 : r ^ 531 * M ^ 4469 < r ^ 531 * r ^ 8938 :=
      Nat.mul_lt_mul_of_pos_left h_M4469_lt_r8938 hr531_pos
    exact Nat.lt_of_le_of_lt h_le1 h_lt2
  exact ⟨hr_ge_513, h_2M9_lt_r19, h_2M4469_lt_r9469⟩

/-- **Theorem 3.2 (`screenedConcreteKb_has_zero_pinched_composites_M_ge_262144` — R4):**
    For all `M ≥ 2^18 = 262144`, EVERY composite `u ∈ pn1RoughCompositeTail (concreteKbUpper M) (sqrtMidpointCutoff M)`
    satisfies `(2 * M) ^ 9 < u.minFac ^ 19` and `(2 * M) ^ 4469 < u.minFac ^ 9469`, so the
    subset of pinched composites in `screenedConcreteKbUpper M` has cardinality `0`! -/
theorem screenedConcreteKb_has_zero_pinched_composites_M_ge_262144
    {M : ℕ} (hM : 262144 ≤ M) :
    ((pn1RoughCompositeTail (concreteKbUpper M) (sqrtMidpointCutoff M)).filter
      (fun u : ℕ => u.minFac ^ 19 ≤ (2 * M) ^ 9)).card = 0 ∧
    ((pn1RoughCompositeTail (concreteKbUpper M) (sqrtMidpointCutoff M)).filter
      (fun u : ℕ => u.minFac ^ 9469 ≤ (2 * M) ^ 4469)).card = 0 := by
  have h_forall :
      ∀ u ∈ pn1RoughCompositeTail (concreteKbUpper M) (sqrtMidpointCutoff M),
        (2 * M) ^ 9 < u.minFac ^ 19 ∧ (2 * M) ^ 4469 < u.minFac ^ 9469 := by
    intro u hu
    rw [pn1RoughCompositeTail, mem_filter] at hu
    obtain ⟨_, hu2, hu_rough, hu_comp⟩ := hu
    have h_mf_isp : IsPrimeNat u.minFac :=
      (minFac_mul_self_le_of_not_isPrimeNat hu2 hu_comp).1
    have h_mf_two : 2 ≤ u.minFac := h_mf_isp.1
    have h_mf_mod0 : u % u.minFac = 0 :=
      (minFac_mul_self_le_of_not_isPrimeNat hu2 hu_comp).2.1
    have h_qb_le_mf : sqrtMidpointCutoff M ≤ u.minFac := by
      match Nat.lt_or_ge u.minFac (sqrtMidpointCutoff M) with
      | Or.inr hge => exact hge
      | Or.inl hlt =>
        have h_pos := hu_rough u.minFac (mem_range.mpr hlt) h_mf_two
        omega
    have h_sep := exponent_separation_above_sqrt_M_ge_262144 hM h_qb_le_mf
    exact ⟨h_sep.2.1, h_sep.2.2⟩
  constructor
  · match Nat.eq_zero_or_pos
      (((pn1RoughCompositeTail (concreteKbUpper M) (sqrtMidpointCutoff M)).filter
        (fun u : ℕ => u.minFac ^ 19 ≤ (2 * M) ^ 9)).card) with
    | Or.inl h0 => exact h0
    | Or.inr hpos =>
      obtain ⟨u, hu⟩ := card_pos.mp hpos
      rw [mem_filter] at hu
      have h_gt := (h_forall u hu.1).1
      have h_le := hu.2
      exact False.elim (Nat.lt_irrefl ((2 * M) ^ 9) (Nat.lt_of_lt_of_le h_gt h_le))
  · match Nat.eq_zero_or_pos
      (((pn1RoughCompositeTail (concreteKbUpper M) (sqrtMidpointCutoff M)).filter
        (fun u : ℕ => u.minFac ^ 9469 ≤ (2 * M) ^ 4469)).card) with
    | Or.inl h0 => exact h0
    | Or.inr hpos =>
      obtain ⟨u, hu⟩ := card_pos.mp hpos
      rw [mem_filter] at hu
      have h_gt := (h_forall u hu.1).2
      have h_le := hu.2
      exact False.elim (Nat.lt_irrefl ((2 * M) ^ 4469) (Nat.lt_of_lt_of_le h_gt h_le))

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.screenedConcreteKb_image_and_card_eq
#print axioms WuPaper.ESZerosBridge.screenedConcreteKbUpper_exact_sq1_p2_balance
#print axioms WuPaper.ESZerosBridge.routeB_retained_rejected_catalog_credit_balance
#print axioms WuPaper.ESZerosBridge.exponent_separation_above_sqrt_M_ge_262144
#print axioms WuPaper.ESZerosBridge.screenedConcreteKb_has_zero_pinched_composites_M_ge_262144
