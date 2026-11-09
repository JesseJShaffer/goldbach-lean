import WR2Step251WR2FiberSpaceConcreteKbCarrierWeld

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step253WR2ExactSpeciesSQ1P2AndCubeTailPartition.lean — Exact-Species `SQ-1` vs. `P-2` vs. `Ω ≥ 3` Composite Partition (`Step190` + `Step191` + `Step220` on `WR2` Track 1)

Partitions `pn1RoughCompositeTail S q` by Exact Composite Species (`SQ-1` prime squares,
`P-2` distinct-prime semiprimes, and `Ω ≥ 3` higher-order composites) and proves the
tighter per-species combinatorial caps:

1. **Section 1 — Exact 3-Species Partition of `pn1RoughCompositeTail S q` (`sq1TailSet`,
   `p2TailSet`, `higherSpeciesTailSet`):**
   - `(pn1RoughCompositeTail S q).card = (sq1TailSet S q).card + (p2TailSet S q).card + (higherSpeciesTailSet S q).card`.
   - `(roughSurvivorSet S q).card = (primeSurvivorSet S q).card + (sq1TailSet S q).card + (p2TailSet S q).card + (higherSpeciesTailSet S q).card`.
2. **Section 2 — Unconditional Sub-Cubic Vanishing of `higherSpeciesTailSet` (`Step190` & `Step220`):**
   - `higherSpeciesTailSet_eq_empty_below_cube`: proves that whenever `∀ u ∈ S, u < q ^ 3`,
     `(higherSpeciesTailSet S q).card = 0`, collapsing `pn1RoughCompositeTail S q` purely
     to `sq1TailSet S q ∪ p2TailSet S q`!
3. **Section 3 — `Step191` Sub-`2q` Block `SQ-1` Singleton Cap & Tighter `P-2` Owner Horizon `p(p + 2) + 3 ≤ 2M`:**
   - `sq1TailSet_subTwoQBlock_card_le_one`: proves that any two `SQ-1` squares `u1 < u2` in
     `sq1TailSet I q` satisfy `2 * max q 1 + 1 ≤ u2 - u1`, so EVERY Quotient Wave Shear
     block `subTwoQBlock I q k` has `(sq1TailSet (subTwoQBlock I q k) q).card ≤ 1` in total!
   - `p2TailSet_subTwoQBlock_card_le_p2ActiveOwnerPrimes`: proves that every `P-2` semiprime
     `u ∈ p2TailSet (fullLowerMURUpper M) q` has odd prime factors `q ≤ p1 < p2` with
     `p1 + 2 ≤ p2`, so `p1 * (p1 + 2) + 3 ≤ 2 * M` and `(p2TailSet (subTwoQBlock (fullLowerMURUpper M) q k) q).card ≤ (p2ActiveOwnerPrimes M q).card`!
-/

/-!
## Section 1: Exact 3-Species Partition of `pn1RoughCompositeTail S q`
-/

/-- Species 1 (`SQ-1`): Pure prime squares `u = p^2` in `pn1RoughCompositeTail S q` (`Step191`). -/
def sq1TailSet (S : Finset ℕ) (q : ℕ) : Finset ℕ :=
  (pn1RoughCompositeTail S q).filter (fun u : ℕ => u.minFac * u.minFac = u)

/-- Non-square composite slice of `pn1RoughCompositeTail S q`. -/
def nonSqTailSet (S : Finset ℕ) (q : ℕ) : Finset ℕ :=
  (pn1RoughCompositeTail S q).filter (fun u : ℕ => u.minFac * u.minFac ≠ u)

/-- Species 2 (`P-2`): Distinct-prime semiprimes `u = p1 * p2` (`p1 < p2`, `IsPrimeNat (u / p1)`)
    in `pn1RoughCompositeTail S q` (`Step191`). -/
def p2TailSet (S : Finset ℕ) (q : ℕ) : Finset ℕ :=
  (nonSqTailSet S q).filter (fun u : ℕ => IsPrimeNat (u / u.minFac))

/-- Species 3 (`Ω ≥ 3`): Higher-order composites (`¬ IsPrimeNat (u / u.minFac)`)
    in `pn1RoughCompositeTail S q` (`Step190` & `Step220`). -/
def higherSpeciesTailSet (S : Finset ℕ) (q : ℕ) : Finset ℕ :=
  (nonSqTailSet S q).filter (fun u : ℕ => ¬ IsPrimeNat (u / u.minFac))

theorem disjoint_sq1TailSet_nonSqTailSet (S : Finset ℕ) (q : ℕ) :
    Disjoint (sq1TailSet S q) (nonSqTailSet S q) := by
  apply Finset.disjoint_left.mpr
  intro u h1 h2
  rw [sq1TailSet, mem_filter] at h1
  rw [nonSqTailSet, mem_filter] at h2
  exact h2.2 h1.2

theorem pn1RoughCompositeTail_eq_sq1_union_nonSq (S : Finset ℕ) (q : ℕ) :
    pn1RoughCompositeTail S q = sq1TailSet S q ∪ nonSqTailSet S q := by
  ext u
  simp only [mem_union, sq1TailSet, nonSqTailSet, mem_filter]
  constructor
  · intro hu
    if hsq : u.minFac * u.minFac = u then
      exact Or.inl ⟨hu, hsq⟩
    else
      exact Or.inr ⟨hu, hsq⟩
  · intro hor
    cases hor with
    | inl h1 => exact h1.1
    | inr h2 => exact h2.1

theorem disjoint_p2TailSet_higherSpeciesTailSet (S : Finset ℕ) (q : ℕ) :
    Disjoint (p2TailSet S q) (higherSpeciesTailSet S q) := by
  apply Finset.disjoint_left.mpr
  intro u h1 h2
  rw [p2TailSet, mem_filter] at h1
  rw [higherSpeciesTailSet, mem_filter] at h2
  exact h2.2 h1.2

theorem nonSqTailSet_eq_p2_union_higherSpecies (S : Finset ℕ) (q : ℕ) :
    nonSqTailSet S q = p2TailSet S q ∪ higherSpeciesTailSet S q := by
  ext u
  simp only [mem_union, p2TailSet, higherSpeciesTailSet, mem_filter]
  constructor
  · intro hu
    cases Classical.em (IsPrimeNat (u / u.minFac)) with
    | inl hp => exact Or.inl ⟨hu, hp⟩
    | inr hnp => exact Or.inr ⟨hu, hnp⟩
  · intro hor
    cases hor with
    | inl h1 => exact h1.1
    | inr h2 => exact h2.1

/-- **Theorem 1.1 (`exact_species_three_way_composite_tail_partition`):**
    Exact additive decomposition of `pn1RoughCompositeTail S q` and `roughSurvivorSet S q`
    into `primeSurvivorSet`, `sq1TailSet` (`SQ-1`), `p2TailSet` (`P-2`), and `higherSpeciesTailSet` (`Ω ≥ 3`). -/
theorem exact_species_three_way_composite_tail_partition (S : Finset ℕ) (q : ℕ) :
    (pn1RoughCompositeTail S q).card =
      (sq1TailSet S q).card + (p2TailSet S q).card + (higherSpeciesTailSet S q).card ∧
    (roughSurvivorSet S q).card =
      (primeSurvivorSet S q).card + (sq1TailSet S q).card +
        (p2TailSet S q).card + (higherSpeciesTailSet S q).card := by
  have h1 :
      (pn1RoughCompositeTail S q).card =
        (sq1TailSet S q).card + (nonSqTailSet S q).card := by
    conv_lhs => rw [pn1RoughCompositeTail_eq_sq1_union_nonSq S q]
    exact card_union_of_disjoint (disjoint_sq1TailSet_nonSqTailSet S q)
  have h2 :
      (nonSqTailSet S q).card =
        (p2TailSet S q).card + (higherSpeciesTailSet S q).card := by
    conv_lhs => rw [nonSqTailSet_eq_p2_union_higherSpecies S q]
    exact card_union_of_disjoint (disjoint_p2TailSet_higherSpeciesTailSet S q)
  have h_rough := roughSurvivorSet_card_eq_primeSurvivors_add_compositeTail S q
  exact ⟨by omega, by omega⟩

/-!
## Section 2: Unconditional Sub-Cubic Vanishing of `higherSpeciesTailSet` (`Step190` & `Step220`)
-/

/-- **Theorem 2.1 (`higherSpeciesTailSet_eq_empty_below_cube`):**
    Unconditional Sub-Cubic Species Collapse (`Step190` & `Step220`):
    Every `u ∈ higherSpeciesTailSet S q` satisfies `q ^ 3 ≤ u`. Consequently, whenever
    `∀ u ∈ S, u < q ^ 3`, `(higherSpeciesTailSet S q).card = 0` and
    `(pn1RoughCompositeTail S q).card = (sq1TailSet S q).card + (p2TailSet S q).card`! -/
theorem higherSpeciesTailSet_eq_empty_below_cube
    {S : Finset ℕ} {q : ℕ} (h_cube : ∀ u ∈ S, u < q ^ 3) :
    (higherSpeciesTailSet S q).card = 0 ∧
    (pn1RoughCompositeTail S q).card = (sq1TailSet S q).card + (p2TailSet S q).card := by
  have h_zero : (higherSpeciesTailSet S q).card = 0 := by
    match Nat.eq_zero_or_pos (higherSpeciesTailSet S q).card with
    | Or.inl h0 => exact h0
    | Or.inr hpos =>
      obtain ⟨u, hu⟩ := card_pos.mp hpos
      rw [higherSpeciesTailSet, mem_filter, nonSqTailSet, mem_filter,
          pn1RoughCompositeTail, mem_filter] at hu
      obtain ⟨⟨⟨hu_S, hu2, hu_rough, hu_comp⟩, _⟩, hk_comp⟩ := hu
      have hu_lt_cube : u < q ^ 3 := h_cube u hu_S
      have h_mf_u := minFac_mul_self_le_of_not_isPrimeNat hu2 hu_comp
      set p1 := u.minFac
      set k := u / p1
      have hp1_isp : IsPrimeNat p1 := h_mf_u.1
      have hp1_two : 2 ≤ p1 := hp1_isp.1
      have hp1_pos : 0 < p1 := by omega
      have h_p1_k_eq : p1 * k = u :=
        (mod_eq_zero_and_mul_div_of_dvd_native hp1_pos (Nat.minFac_dvd u)).2
      have hq_le_p1 : q ≤ p1 := by
        match Nat.lt_or_ge p1 q with
        | Or.inr hge => exact hge
        | Or.inl hlt =>
          have h_pos := hu_rough p1 (mem_range.mpr hlt) hp1_two
          have h_m0 := h_mf_u.2.1
          omega
      have hp1_sq_le_p1k : p1 * p1 ≤ p1 * k := by
        rw [h_p1_k_eq]
        exact h_mf_u.2.2.2
      have hp1_le_k : p1 ≤ k := le_of_mul_le_mul_left_pos_wr2 hp1_pos hp1_sq_le_p1k
      have hk2 : 2 ≤ k := Nat.le_trans hp1_two hp1_le_k
      have h_mf_k := minFac_mul_self_le_of_not_isPrimeNat hk2 hk_comp
      have h_kmf_prime : Nat.Prime k.minFac := isPrimeNat_to_natPrime h_mf_k.1
      have hk_dvd_u : k ∣ u := ⟨p1, by rw [Nat.mul_comm k p1]; exact h_p1_k_eq.symm⟩
      have h_kmf_dvd_u : k.minFac ∣ u := Nat.dvd_trans (Nat.minFac_dvd k) hk_dvd_u
      have hp1_le_kmf : p1 ≤ k.minFac :=
        Nat.minFac_le_of_dvd h_kmf_prime.two_le h_kmf_dvd_u
      have hq_le_kmf : q ≤ k.minFac := Nat.le_trans hq_le_p1 hp1_le_kmf
      have hq2_le_kmf2 : q * q ≤ k.minFac * k.minFac :=
        Nat.mul_le_mul hq_le_kmf hq_le_kmf
      have hq2_le_k : q * q ≤ k := Nat.le_trans hq2_le_kmf2 h_mf_k.2.2.2
      have hq3_le_p1k : q * (q * q) ≤ p1 * k := Nat.mul_le_mul hq_le_p1 hq2_le_k
      have h_cube_eq : q ^ 3 = q * (q * q) := by
        show (1 * q) * q * q = q * (q * q)
        rw [Nat.one_mul, Nat.mul_assoc q q q]
      rw [h_p1_k_eq, ← h_cube_eq] at hq3_le_p1k
      exact False.elim (Nat.lt_irrefl u (Nat.lt_of_lt_of_le hu_lt_cube hq3_le_p1k))
  have h_part := (exact_species_three_way_composite_tail_partition S q).1
  exact ⟨h_zero, by omega⟩

/-!
## Section 3: `Step191` Sub-`2q` Block `SQ-1` Singleton Cap & Tighter `P-2` Owner Horizon
-/

/-- **Theorem 3.1 (`sq1TailSet_subTwoQBlock_card_le_one`):**
    Ports `Step191` Theorem 1.1.3 (`SQ-1` Sub-`2q` Block Singleton Cap):
    Any two squares `a0 < b0` in `sq1TailSet I q` satisfy `a0.minFac + 1 ≤ b0.minFac`
    and `2 * max q 1 + 1 ≤ b0 - a0`. Since every Quotient Wave Shear block
    `subTwoQBlock I q k` has diameter `< 2 * max q 1`, EVERY block contains at most
    ONE `SQ-1` square in total:
    `(sq1TailSet (subTwoQBlock I q k) q).card ≤ 1`! -/
theorem sq1TailSet_subTwoQBlock_card_le_one (I : Finset ℕ) (q k : ℕ) :
    (sq1TailSet (subTwoQBlock I q k) q).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a0 ha0 b0 hb0
  have h_diam_fn := (subTwoQBlock_unconditional_partition_and_diameter I q).2.2.2 k
  rw [sq1TailSet, mem_filter, pn1RoughCompositeTail, mem_filter] at ha0 hb0
  obtain ⟨⟨ha_blk, ha2, ha_rough, ha_comp⟩, ha_sq⟩ := ha0
  obtain ⟨⟨hb_blk, hb2, hb_rough, hb_comp⟩, hb_sq⟩ := hb0
  have ha_mf_isp : IsPrimeNat a0.minFac := (minFac_mul_self_le_of_not_isPrimeNat ha2 ha_comp).1
  have hb_mf_isp : IsPrimeNat b0.minFac := (minFac_mul_self_le_of_not_isPrimeNat hb2 hb_comp).1
  have ha_mf2 : 2 ≤ a0.minFac := ha_mf_isp.1
  have hb_mf2 : 2 ≤ b0.minFac := hb_mf_isp.1
  have hq_le_pa : q ≤ a0.minFac := by
    match Nat.lt_or_ge a0.minFac q with
    | Or.inr hge => exact hge
    | Or.inl hlt =>
      have h_pos := ha_rough a0.minFac (mem_range.mpr hlt) ha_mf2
      have h_m0 := (minFac_mul_self_le_of_not_isPrimeNat ha2 ha_comp).2.1
      omega
  have hq_le_pb : q ≤ b0.minFac := by
    match Nat.lt_or_ge b0.minFac q with
    | Or.inr hge => exact hge
    | Or.inl hlt =>
      have h_pos := hb_rough b0.minFac (mem_range.mpr hlt) hb_mf2
      have h_m0 := (minFac_mul_self_le_of_not_isPrimeNat hb2 hb_comp).2.1
      omega
  match Nat.lt_or_ge a0 b0 with
  | Or.inl hlt =>
    have hle : a0 ≤ b0 := Nat.le_of_lt hlt
    have h_diam : b0 - a0 < 2 * max q 1 := h_diam_fn a0 b0 ha_blk hb_blk hle
    have h_pa1_le_pb : a0.minFac + 1 ≤ b0.minFac := by
      match Nat.lt_or_ge b0.minFac (a0.minFac + 1) with
      | Or.inr hge => exact hge
      | Or.inl hlt_p =>
        have h_pb_le_pa : b0.minFac ≤ a0.minFac := by omega
        have h_sq_le : b0.minFac * b0.minFac ≤ a0.minFac * a0.minFac :=
          Nat.mul_le_mul h_pb_le_pa h_pb_le_pa
        rw [ha_sq, hb_sq] at h_sq_le
        omega
    have h_sq_gap : (a0.minFac + 1) * (a0.minFac + 1) ≤ b0 := by
      rw [← hb_sq]
      exact Nat.mul_le_mul h_pa1_le_pb h_pa1_le_pb
    have h_exp1 :
        (a0.minFac + 1) * (a0.minFac + 1) =
          (a0.minFac + 1) * a0.minFac + (a0.minFac + 1) * 1 :=
      Nat.left_distrib (a0.minFac + 1) a0.minFac 1
    have h_exp2 :
        (a0.minFac + 1) * a0.minFac = a0.minFac * a0.minFac + 1 * a0.minFac :=
      Nat.right_distrib a0.minFac 1 a0.minFac
    rw [ha_sq] at h_exp2
    have h_max_le : max q 1 ≤ a0.minFac := by omega
    have h_2max_le : 2 * max q 1 ≤ 2 * a0.minFac := Nat.mul_le_mul_left 2 h_max_le
    omega
  | Or.inr hge =>
    match Nat.lt_or_ge b0 a0 with
    | Or.inr hge2 => exact Nat.le_antisymm hge2 hge
    | Or.inl hlt2 =>
      have h_diam : a0 - b0 < 2 * max q 1 := h_diam_fn b0 a0 hb_blk ha_blk hge
      have h_pb1_le_pa : b0.minFac + 1 ≤ a0.minFac := by
        match Nat.lt_or_ge a0.minFac (b0.minFac + 1) with
        | Or.inr hge_p => exact hge_p
        | Or.inl hlt_p =>
          have h_pa_le_pb : a0.minFac ≤ b0.minFac := by omega
          have h_sq_le : a0.minFac * a0.minFac ≤ b0.minFac * b0.minFac :=
            Nat.mul_le_mul h_pa_le_pb h_pa_le_pb
          rw [ha_sq, hb_sq] at h_sq_le
          omega
      have h_sq_gap : (b0.minFac + 1) * (b0.minFac + 1) ≤ a0 := by
        rw [← ha_sq]
        exact Nat.mul_le_mul h_pb1_le_pa h_pb1_le_pa
      have h_exp1 :
          (b0.minFac + 1) * (b0.minFac + 1) =
            (b0.minFac + 1) * b0.minFac + (b0.minFac + 1) * 1 :=
        Nat.left_distrib (b0.minFac + 1) b0.minFac 1
      have h_exp2 :
          (b0.minFac + 1) * b0.minFac = b0.minFac * b0.minFac + 1 * b0.minFac :=
        Nat.right_distrib b0.minFac 1 b0.minFac
      rw [hb_sq] at h_exp2
      have h_max_le : max q 1 ≤ b0.minFac := by omega
      have h_2max_le : 2 * max q 1 ≤ 2 * b0.minFac := Nat.mul_le_mul_left 2 h_max_le
      omega

/-- Tighter `P-2` Active Owner Prime Set (`p * (p + 2) + 3 ≤ 2 * M`):
    excludes primes near `√(2M)` that can only form `p^2` (`SQ-1`) and cannot form `p * (p + 2)` (`P-2`). -/
def p2ActiveOwnerPrimes (M q : ℕ) : Finset ℕ :=
  (sqrtActiveOwnerPrimes M q).filter (fun p : ℕ => p * (p + 2) + 3 ≤ 2 * M)

/-- **Theorem 3.2 (`p2TailSet_subTwoQBlock_card_le_p2ActiveOwnerPrimes`):**
    Every `P-2` semiprime `u ∈ p2TailSet (subTwoQBlock (fullLowerMURUpper M) q k) q`
    has odd prime factors `p1 = u.minFac` and `p2 = u / p1` with `p1 + 2 ≤ p2`, so
    `p1 * (p1 + 2) + 3 ≤ 2 * M` (`p1 ∈ p2ActiveOwnerPrimes M q`) and:
    `(p2TailSet (subTwoQBlock (fullLowerMURUpper M) q k) q).card ≤ (p2ActiveOwnerPrimes M q).card`! -/
theorem p2TailSet_subTwoQBlock_card_le_p2ActiveOwnerPrimes (M q k : ℕ) :
    (p2TailSet (subTwoQBlock (fullLowerMURUpper M) q k) q).card ≤
      (p2ActiveOwnerPrimes M q).card ∧
    (p2ActiveOwnerPrimes M q).card ≤ (sqrtActiveOwnerPrimes M q).card := by
  have h_p2_le_sqrt :
      (p2ActiveOwnerPrimes M q).card ≤ (sqrtActiveOwnerPrimes M q).card :=
    card_le_card (filter_subset _ _)
  have h_sub_p2 :
      (p2TailSet (subTwoQBlock (fullLowerMURUpper M) q k) q).image Nat.minFac ⊆
        p2ActiveOwnerPrimes M q := by
    intro p hp
    rw [mem_image] at hp
    obtain ⟨u, hu, rfl⟩ := hp
    rw [p2TailSet, mem_filter, nonSqTailSet, mem_filter] at hu
    obtain ⟨⟨hu_tail, h_not_sq⟩, hp2_isp⟩ := hu
    have h_sqrt_mem := (roughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes hu_tail).1
    have hu_odd : u % 2 = 1 := (roughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes hu_tail).2.2.2.2
    have hp1_odd : u.minFac % 2 = 1 := (roughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes hu_tail).2.2.2.1
    rw [pn1RoughCompositeTail, mem_filter, subTwoQBlock, mem_filter] at hu_tail
    have hu_full := hu_tail.1.1
    have hu_le_2M3 : u ≤ 2 * M - 3 := (fullLowerMURUpper_mem_props hu_full).2.1
    have hu_ge_M1 : M + 1 ≤ u := (fullLowerMURUpper_mem_props hu_full).1
    set p1 := u.minFac
    set p2 := u / p1
    have hp1_pos : 0 < p1 := by omega
    have h_p1p2_eq : p1 * p2 = u :=
      (mod_eq_zero_and_mul_div_of_dvd_native hp1_pos (Nat.minFac_dvd u)).2
    have hp1_sq_le : p1 * p1 ≤ p1 * p2 := by
      rw [h_p1p2_eq]
      exact (minFac_mul_self_le_of_not_isPrimeNat hu_tail.2.1 hu_tail.2.2.2).2.2.2
    have hp1_le_p2 : p1 ≤ p2 := le_of_mul_le_mul_left_pos_wr2 hp1_pos hp1_sq_le
    have hp1_ne_p2 : p1 ≠ p2 := by
      intro h_eq
      rw [← h_eq] at h_p1p2_eq
      exact h_not_sq h_p1p2_eq
    have hp2_dvd_u : p2 ∣ u := ⟨p1, by rw [Nat.mul_comm p2 p1]; exact h_p1p2_eq.symm⟩
    have hu_npv2 : 1 ≤ u % 2 := by omega
    have hp2_npv2 : 1 ≤ p2 % 2 :=
      (nonPVen_divisor_inheritance_native (by omega : 0 < 2) hp2_dvd_u hu_npv2).1
    have hp2_lt2 : p2 % 2 < 2 := Nat.mod_lt p2 (by omega : 0 < 2)
    have hp2_odd : p2 % 2 = 1 := by omega
    have hp1_div2 : 2 * (p1 / 2) + p1 % 2 = p1 := Nat.div_add_mod p1 2
    have hp2_div2 : 2 * (p2 / 2) + p2 % 2 = p2 := Nat.div_add_mod p2 2
    have hp1_add2_le_p2 : p1 + 2 ≤ p2 := by omega
    have h_mul_p12 : p1 * (p1 + 2) ≤ u := by
      rw [← h_p1p2_eq]
      exact Nat.mul_le_mul_left p1 hp1_add2_le_p2
    rw [p2ActiveOwnerPrimes, mem_filter]
    exact ⟨h_sqrt_mem, by omega⟩
  have h_p2_sub_tail :
      p2TailSet (subTwoQBlock (fullLowerMURUpper M) q k) q ⊆
        pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) q k) q := by
    intro u hu
    rw [p2TailSet, mem_filter, nonSqTailSet, mem_filter] at hu
    exact hu.1.1
  have h_inj :
      Set.InjOn Nat.minFac
        (↑(p2TailSet (subTwoQBlock (fullLowerMURUpper M) q k) q) : Set ℕ) := by
    intro a0 ha0 b0 hb0 h_mf_eq
    rw [mem_coe] at ha0 hb0
    have ha_t := h_p2_sub_tail ha0
    have hb_t := h_p2_sub_tail hb0
    have ha_props := roughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes ha_t
    have hb_props := roughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes hb_t
    have ha_blk : a0 ∈ subTwoQBlock (fullLowerMURUpper M) q k := by
      rw [pn1RoughCompositeTail, mem_filter] at ha_t
      exact ha_t.1
    have hb_blk : b0 ∈ subTwoQBlock (fullLowerMURUpper M) q k := by
      rw [pn1RoughCompositeTail, mem_filter] at hb_t
      exact hb_t.1
    have h_diam_fn :=
      (subTwoQBlock_unconditional_partition_and_diameter (fullLowerMURUpper M) q).2.2.2 k
    have hp_odd : a0.minFac % 2 = 1 := ha_props.2.2.2.1
    have ha_odd : a0 % 2 = 1 := ha_props.2.2.2.2
    have hb_odd : b0 % 2 = 1 := hb_props.2.2.2.2
    have ha_mod_p : a0 % a0.minFac = 0 := ha_props.2.2.1
    have hb_mod_p : b0 % a0.minFac = 0 := by
      rw [h_mf_eq]
      exact hb_props.2.2.1
    have h_mod_eq : a0 % a0.minFac = b0 % a0.minFac := by rw [ha_mod_p, hb_mod_p]
    have hq_le_p : q ≤ a0.minFac := ha_props.2.1
    have h_max_le1 : max q 1 ≤ max a0.minFac 1 := by omega
    have h_max_le : 2 * max q 1 ≤ 2 * max a0.minFac 1 :=
      Nat.mul_le_mul_left 2 h_max_le1
    match Nat.lt_or_ge a0 b0 with
    | Or.inl hlt =>
      have hle : a0 ≤ b0 := Nat.le_of_lt hlt
      have h_d_q : b0 - a0 < 2 * max q 1 := h_diam_fn a0 b0 ha_blk hb_blk hle
      have h_d_p : b0 - a0 < 2 * max a0.minFac 1 := Nat.lt_of_lt_of_le h_d_q h_max_le
      exact eq_of_sub_lt_two_max_of_odd_of_mod_eq hp_odd hle h_d_p ha_odd hb_odd h_mod_eq
    | Or.inr hge =>
      have h_d_q : a0 - b0 < 2 * max q 1 := h_diam_fn b0 a0 hb_blk ha_blk hge
      have h_d_p : a0 - b0 < 2 * max a0.minFac 1 := Nat.lt_of_lt_of_le h_d_q h_max_le
      exact (eq_of_sub_lt_two_max_of_odd_of_mod_eq hp_odd hge h_d_p hb_odd ha_odd h_mod_eq.symm).symm
  have h_card_img :
      ((p2TailSet (subTwoQBlock (fullLowerMURUpper M) q k) q).image Nat.minFac).card =
        (p2TailSet (subTwoQBlock (fullLowerMURUpper M) q k) q).card :=
    Finset.card_image_of_injOn h_inj
  refine ⟨?_, h_p2_le_sqrt⟩
  rw [← h_card_img]
  exact card_le_card h_sub_p2

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.exact_species_three_way_composite_tail_partition
#print axioms WuPaper.ESZerosBridge.higherSpeciesTailSet_eq_empty_below_cube
#print axioms WuPaper.ESZerosBridge.sq1TailSet_subTwoQBlock_card_le_one
#print axioms WuPaper.ESZerosBridge.p2TailSet_subTwoQBlock_card_le_p2ActiveOwnerPrimes
