import WR2Step241WR2PreArgonStep217SignatureOperatorAndDivisorFiberSingleton

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step243WR2RescuedLowerMURSurvivorStrictInequality.lean — `Step209` Rescued Lower-MUR Survivor Injection into `roughSurvivorSet` & Unconditional Strict Inequality (`WR2` Track 1)

Ports the final `Step209` Section 3b theorem (`unconditional_strict_sqrt_owner_lt_rescued_lower_mur_survivors`)
into Track 1 (`WR2`) using `fullLowerMURUpper_shielded_from_target_prime_divisors` (`WR2Step239`)
and `nonPVen_divisor_inheritance_native` (`WR2Step229`):

1. **Section 1 — First-Missing-Prime Rescued Lower-MUR Survivor Shield (`mirror_mem_roughSurvivorSet_of_first_missing_prime`):**
   Proves in pure native arithmetic that whenever `q3` satisfies the First-Missing-Prime
   prefix condition `∀ p0 : ℕ, IsPrimeNat p0 → p0 % 2 = 1 → p0 < q3 → (2 * M) % p0 = 0`,
   every lower-MUR odd prime `p` with `max q3 3 ≤ p < M` has its reflected upper partner
   `mirrorUpperFromLowerPrime M p = 2 * M - p` inside `roughSurvivorSet (fullLowerMURUpper M) (max q3 3)`.
2. **Section 2 — Disjoint Decomposition into `sqrtActiveOwnerPrimes` + `aboveSqrtLowerMURPrimesCutoff`
   & Unconditional Strict Inequality (`unconditional_strict_sqrt_owner_lt_rescued_lower_mur_survivors_wr2`):**
   Proves for ALL `M, q, k : ℕ` under the First-Missing-Prime prefix condition on `q3 := max q 3`:
   - `(sqrtActiveOwnerPrimes M q3).card + (aboveSqrtLowerMURPrimesCutoff M q3).card ≤ (roughSurvivorSet (fullLowerMURUpper M) q3).card`,
   - `(pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) q3 k) q3).card + (aboveSqrtLowerMURPrimesCutoff M q3).card ≤ (roughSurvivorSet (fullLowerMURUpper M) q3).card`, and
   - Given any non-dividing prime `p` above `√(2M)` (`IsPrimeNat p ∧ p < M ∧ 2 * M < p * p ∧ (2 * M) % p ≠ 0`),
     `q3 ≤ p` holds automatically and forces the strict inequality:
     `(pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) q3 k) q3).card ≤ (sqrtActiveOwnerPrimes M q3).card < (roughSurvivorSet (fullLowerMURUpper M) q3).card`!
-/

/-!
## Section 1: First-Missing-Prime Rescued Lower-MUR Survivor Shield
-/

/-- Rescued Lower-MUR primes `p ∈ [max q 3, M - 1]`: odd primes strictly below `M` and at or above `max q 3`. -/
def rescuedLowerMURPrimes (M q : ℕ) : Finset ℕ :=
  (range M).filter (fun p : ℕ =>
    IsPrimeNat p ∧ p % 2 = 1 ∧ max q 3 ≤ p)

/-- Above-`√(2M)` subset of `rescuedLowerMURPrimes M q` (`2 * M < p * p`). -/
def aboveSqrtLowerMURPrimesCutoff (M q : ℕ) : Finset ℕ :=
  (range M).filter (fun p : ℕ =>
    IsPrimeNat p ∧ p % 2 = 1 ∧ max q 3 ≤ p ∧ 2 * M < p * p)

/-- **Theorem 1.1 (`mirror_mem_roughSurvivorSet_of_first_missing_prime`):**
    If every odd prime `p0 < max q 3` divides `2 * M` (`(2 * M) % p0 = 0`), then for every
    lower-MUR prime `p ∈ rescuedLowerMURPrimes M q`, its reflected upper partner
    `mirrorUpperFromLowerPrime M p = 2 * M - p` belongs to
    `roughSurvivorSet (fullLowerMURUpper M) (max q 3)`. -/
theorem mirror_mem_roughSurvivorSet_of_first_missing_prime
    {M q p : ℕ}
    (h_fmp : ∀ p0 : ℕ, IsPrimeNat p0 → p0 % 2 = 1 → p0 < max q 3 → (2 * M) % p0 = 0)
    (hp : p ∈ rescuedLowerMURPrimes M q) :
    p < M ∧
    mirrorUpperFromLowerPrime M p ∈ roughSurvivorSet (fullLowerMURUpper M) (max q 3) := by
  rw [rescuedLowerMURPrimes, mem_filter, mem_range] at hp
  obtain ⟨hp_lt_M, hp_isp, hp_odd, hq3_le_p⟩ := hp
  have hp3 : 3 ≤ p := by omega
  have hu_full : mirrorUpperFromLowerPrime M p ∈ fullLowerMURUpper M := by
    rw [fullLowerMURUpper, mem_image]
    refine ⟨M - p, ?_, ?_⟩
    · rw [fullLowerMURPrimeRadii, mem_filter, mem_range]
      have h_sub : M - (M - p) = p := by omega
      rw [h_sub]
      exact ⟨by omega, by omega, by omega, hp_isp⟩
    · unfold mirrorUpperFromLowerPrime
      omega
  have hu_props := fullLowerMURUpper_mem_props hu_full
  have hu2 : 2 ≤ mirrorUpperFromLowerPrime M p := by omega
  have hu_odd : (mirrorUpperFromLowerPrime M p) % 2 = 1 := hu_props.2.2.2.1
  have hu_npv2 : 1 ≤ (mirrorUpperFromLowerPrime M p) % 2 := by omega
  have h_sub_u : 2 * M - mirrorUpperFromLowerPrime M p = p := by
    unfold mirrorUpperFromLowerPrime
    omega
  refine ⟨hp_lt_M, ?_⟩
  rw [roughSurvivorSet, mem_filter]
  refine ⟨hu_full, hu2, ?_⟩
  intro d hd_range hd2
  rw [mem_range] at hd_range
  obtain ⟨p0, hp0_isp, hp0_dvd_d⟩ :=
    exists_prime_divisor_aux d d hd2 (Nat.le_refl d)
  have hd_pos : 0 < d := by omega
  have hp0_pos : 0 < p0 := isPrimeNat_pos hp0_isp
  have hp0_le_d : p0 ≤ d := dvd_le_of_pos hp0_dvd_d hd_pos
  have hp0_lt_q3 : p0 < max q 3 := Nat.lt_of_le_of_lt hp0_le_d hd_range
  have hu_npv_p0 : 1 ≤ (mirrorUpperFromLowerPrime M p) % p0 := by
    rcases isPrimeNat_eq_two_or_odd_wr2 hp0_isp with hp0_eq2 | hp0_odd
    · rw [hp0_eq2]
      exact hu_npv2
    · have h2M_mod_p0 : (2 * M) % p0 = 0 := h_fmp p0 hp0_isp hp0_odd hp0_lt_q3
      have hp0_ne_p : p0 ≠ 2 * M - mirrorUpperFromLowerPrime M p := by
        rw [h_sub_u]
        omega
      exact (fullLowerMURUpper_shielded_from_target_prime_divisors
        hu_full hp0_isp h2M_mod_p0 hp0_ne_p).1
  if hu_mod_d0 : (mirrorUpperFromLowerPrime M p) % d = 0 then
    have hd_dvd_u : d ∣ mirrorUpperFromLowerPrime M p := by
      have h_div :
          d * (mirrorUpperFromLowerPrime M p / d) +
            (mirrorUpperFromLowerPrime M p) % d =
          mirrorUpperFromLowerPrime M p :=
        Nat.div_add_mod (mirrorUpperFromLowerPrime M p) d
      exact ⟨mirrorUpperFromLowerPrime M p / d, by omega⟩
    have hp0_dvd_u : p0 ∣ mirrorUpperFromLowerPrime M p :=
      Nat.dvd_trans hp0_dvd_d hd_dvd_u
    have hu_mod_p0_0 : (mirrorUpperFromLowerPrime M p) % p0 = 0 :=
      (mod_eq_zero_and_mul_div_of_dvd_native hp0_pos hp0_dvd_u).1
    omega
  else
    omega

/-!
## Section 2: Unconditional Strict Inequality (`Step209` §3b)
-/

theorem disjoint_sqrtActiveOwnerPrimes_aboveSqrtCutoff (M q : ℕ) :
    Disjoint (sqrtActiveOwnerPrimes M (max q 3)) (aboveSqrtLowerMURPrimesCutoff M q) := by
  apply Finset.disjoint_left.mpr
  intro p h_le h_gt
  rw [sqrtActiveOwnerPrimes, mem_filter] at h_le
  rw [aboveSqrtLowerMURPrimesCutoff, mem_filter] at h_gt
  have h1 : p * p ≤ 2 * M := h_le.2.2.2.2
  have h2 : 2 * M < p * p := h_gt.2.2.2.2
  omega

theorem sqrtActiveOwnerPrimes_subset_rescuedLowerMURPrimes (M q : ℕ) :
    sqrtActiveOwnerPrimes M (max q 3) ⊆ rescuedLowerMURPrimes M q := by
  intro p hp
  have hp_lt_M : p < M := (sqrtActiveOwnerPrimes_mirror_mem_fullLowerMURUpper hp).1
  rw [sqrtActiveOwnerPrimes, mem_filter] at hp
  rw [rescuedLowerMURPrimes, mem_filter, mem_range]
  exact ⟨hp_lt_M, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩

theorem aboveSqrtCutoff_subset_rescuedLowerMURPrimes (M q : ℕ) :
    aboveSqrtLowerMURPrimesCutoff M q ⊆ rescuedLowerMURPrimes M q := by
  intro p hp
  rw [aboveSqrtLowerMURPrimesCutoff, mem_filter] at hp
  rw [rescuedLowerMURPrimes, mem_filter]
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩

/-- **Theorem 2.1 (`unconditional_strict_sqrt_owner_lt_rescued_lower_mur_survivors_wr2`):**
    Ports the Final Capstone Inequality of `Step209` (`unconditional_strict_sqrt_owner_lt_rescued_lower_mur_survivors`):
    Let `q3 := max q 3`. Whenever `h_fmp : ∀ p0 : ℕ, IsPrimeNat p0 → p0 % 2 = 1 → p0 < q3 → (2 * M) % p0 = 0`:
    1. `(sqrtActiveOwnerPrimes M q3).card + (aboveSqrtLowerMURPrimesCutoff M q).card ≤ (roughSurvivorSet (fullLowerMURUpper M) q3).card`,
    2. `(pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) q3 k) q3).card + (aboveSqrtLowerMURPrimesCutoff M q).card ≤ (roughSurvivorSet (fullLowerMURUpper M) q3).card`, and
    3. Given ANY odd prime `p < M` with `2 * M < p * p` and `(2 * M) % p ≠ 0`, `q3 ≤ p` holds
       automatically, `1 ≤ (aboveSqrtLowerMURPrimesCutoff M q).card`, and the strict inequality holds:
       `(pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) q3 k) q3).card ≤ (sqrtActiveOwnerPrimes M q3).card < (roughSurvivorSet (fullLowerMURUpper M) q3).card`! -/
theorem unconditional_strict_sqrt_owner_lt_rescued_lower_mur_survivors_wr2
    (M q k : ℕ)
    (h_fmp : ∀ p0 : ℕ, IsPrimeNat p0 → p0 % 2 = 1 → p0 < max q 3 → (2 * M) % p0 = 0) :
    (sqrtActiveOwnerPrimes M (max q 3)).card +
      (aboveSqrtLowerMURPrimesCutoff M q).card ≤
      (roughSurvivorSet (fullLowerMURUpper M) (max q 3)).card ∧
    (pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) (max q 3) k) (max q 3)).card +
      (aboveSqrtLowerMURPrimesCutoff M q).card ≤
      (roughSurvivorSet (fullLowerMURUpper M) (max q 3)).card ∧
    ((∃ p : ℕ, IsPrimeNat p ∧ p % 2 = 1 ∧ p < M ∧ 2 * M < p * p ∧ (2 * M) % p ≠ 0) →
      1 ≤ (aboveSqrtLowerMURPrimesCutoff M q).card ∧
      (sqrtActiveOwnerPrimes M (max q 3)).card <
        (roughSurvivorSet (fullLowerMURUpper M) (max q 3)).card ∧
      (pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) (max q 3) k) (max q 3)).card <
        (roughSurvivorSet (fullLowerMURUpper M) (max q 3)).card) := by
  set U_resc := sqrtActiveOwnerPrimes M (max q 3) ∪ aboveSqrtLowerMURPrimesCutoff M q
  have h_u_card :
      U_resc.card =
        (sqrtActiveOwnerPrimes M (max q 3)).card +
          (aboveSqrtLowerMURPrimesCutoff M q).card :=
    card_union_of_disjoint (disjoint_sqrtActiveOwnerPrimes_aboveSqrtCutoff M q)
  have h_u_sub_resc : U_resc ⊆ rescuedLowerMURPrimes M q :=
    union_subset
      (sqrtActiveOwnerPrimes_subset_rescuedLowerMURPrimes M q)
      (aboveSqrtCutoff_subset_rescuedLowerMURPrimes M q)
  have h_sub_rough :
      U_resc.image (mirrorUpperFromLowerPrime M) ⊆
        roughSurvivorSet (fullLowerMURUpper M) (max q 3) := by
    intro u hu
    rw [mem_image] at hu
    obtain ⟨p, hp_u, rfl⟩ := hu
    exact (mirror_mem_roughSurvivorSet_of_first_missing_prime h_fmp (h_u_sub_resc hp_u)).2
  have h_inj : Set.InjOn (mirrorUpperFromLowerPrime M) (↑U_resc : Set ℕ) := by
    intro a ha b hb h_eq
    rw [mem_coe] at ha hb
    have ha_lt : a < M :=
      (mirror_mem_roughSurvivorSet_of_first_missing_prime h_fmp (h_u_sub_resc ha)).1
    have hb_lt : b < M :=
      (mirror_mem_roughSurvivorSet_of_first_missing_prime h_fmp (h_u_sub_resc hb)).1
    unfold mirrorUpperFromLowerPrime at h_eq
    omega
  have h_img_card :
      (U_resc.image (mirrorUpperFromLowerPrime M)).card = U_resc.card :=
    Finset.card_image_of_injOn h_inj
  have h_sum_le :
      (sqrtActiveOwnerPrimes M (max q 3)).card +
        (aboveSqrtLowerMURPrimesCutoff M q).card ≤
      (roughSurvivorSet (fullLowerMURUpper M) (max q 3)).card := by
    rw [← h_u_card, ← h_img_card]
    exact card_le_card h_sub_rough
  have h_tail_le :=
    subTwoQBlock_roughCompositeTail_card_le_sqrtActiveOwnerPrimes M (max q 3) k
  refine ⟨h_sum_le, by omega, ?_⟩
  intro h_ex
  obtain ⟨p, hp_isp, hp_odd, hp_lt_M, hp_sq, hp_nmod⟩ := h_ex
  have hq3_le_p : max q 3 ≤ p := by
    match Nat.lt_or_ge p (max q 3) with
    | Or.inr hge => exact hge
    | Or.inl hlt =>
      have h0 := h_fmp p hp_isp hp_odd hlt
      exact False.elim (hp_nmod h0)
  have hp_mem : p ∈ aboveSqrtLowerMURPrimesCutoff M q := by
    rw [aboveSqrtLowerMURPrimesCutoff, mem_filter, mem_range]
    exact ⟨hp_lt_M, hp_isp, hp_odd, hq3_le_p, hp_sq⟩
  have h_pos : 0 < (aboveSqrtLowerMURPrimesCutoff M q).card :=
    card_pos.mpr ⟨p, hp_mem⟩
  exact ⟨by omega, by omega, by omega⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.mirror_mem_roughSurvivorSet_of_first_missing_prime
#print axioms WuPaper.ESZerosBridge.unconditional_strict_sqrt_owner_lt_rescued_lower_mur_survivors_wr2
