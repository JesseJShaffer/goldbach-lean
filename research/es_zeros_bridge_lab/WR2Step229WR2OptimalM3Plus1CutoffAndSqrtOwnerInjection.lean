import WR2Step227WR2SubTwoQSingleHitAnd2Pn1FirstSemiprimeFilter

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step229WR2OptimalM3Plus1CutoffAndSqrtOwnerInjection.lean — Zero-One Neutral/Absorber Laws, Non-`p`-ven Divisor Inheritance, `Step209` Optimal `M_3 + 1` Cutoff & Per-Block `√(2M)` Owner Injection (`WR2` Track 1)

Ports Sections 1–3 of `Step209_OptimalM3Plus1RefinementAndFinalUnconditionalInequalityCapstone_v1.lean`
into the `goldbach-lean` Track 1 (`WR2`) bridge:

1. **Section 1 — Zero-One Neutral/Absorber Laws, Non-`p`-ven Divisor Inheritance & Optimal `q_opt := max M 3 + 1` Cutoff:**
   - `zero_absorber_and_one_neutral_pVen_laws`: proves the multiplicative absorber (`0 * u = 0`, `0 % p = 0`),
     additive neutral (`u + 0 = u`), and multiplicative neutral (`1 * u = u`, `1 % p = 1`, `1 ≤ 1 % p`) laws.
   - `nonPVen_divisor_inheritance_native`: proves via `Nat.dvd_trans` and `mod_eq_zero_and_mul_div_of_dvd_native`
     that if `0 < p`, `d ∣ u`, and `1 ≤ u % p` (`u ∈ nonPVenDomain`), then `1 ≤ d % p` and `¬ (p ∣ d)`.
   - `optimal_M3_plus_1_cutoff_vanishes_composite_tail_and_embeds_goldbach`: proves unconditionally
     that at `q_opt := max M 3 + 1`, `(pn1RoughCompositeTail U_full q_opt).card = 0`.
2. **Section 2 — Square-Absorber `minFac` Bound & Per-Block `√(2M)` Injection (`Step209` §3a):**
   - `minFac_mul_self_le_of_not_isPrimeNat`: proves for any `2 ≤ u` with `¬ IsPrimeNat u` that
     `IsPrimeNat u.minFac`, `u % u.minFac = 0`, `u.minFac ≤ u`, and `u.minFac * u.minFac ≤ u`.
   - `subTwoQBlock_roughCompositeTail_card_le_sqrtActiveOwnerPrimes`: proves for ALL `M, q, k : ℕ`
     that `(pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) q k) q).card ≤ (sqrtActiveOwnerPrimes M q).card`.
-/

/-!
## Section 1: Zero-One Neutral/Absorber Laws, Non-`p`-ven Divisor Inheritance & Optimal `q_opt := max M 3 + 1` Cutoff
-/

/-- **Lemma 1.0 (`zero_absorber_and_one_neutral_pVen_laws`):**
    Explicit Zero-Absorber (`0`) and One-Neutral (`1`) laws across all `p`-ven domains (`Step121`):
    - `0` is the multiplicative absorber (`0 * u = 0`) and additive neutral (`u + 0 = u`),
      and lies in every `p`-ven kernel (`0 % p = 0`).
    - `1` is the multiplicative neutral element (`1 * u = u`) and lies in every
      non-`p`-ven survivor domain for `2 ≤ p` (`1 % p = 1`, `1 ≤ 1 % p`). -/
theorem zero_absorber_and_one_neutral_pVen_laws {p : ℕ} (hp2 : 2 ≤ p) (u : ℕ) :
    0 * u = 0 ∧
    u + 0 = u ∧
    0 % p = 0 ∧
    1 * u = u ∧
    1 % p = 1 ∧
    1 ≤ 1 % p := by
  have h0_mod : 0 % p = 0 := Nat.zero_mod p
  have h1_mod : 1 % p = 1 := Nat.mod_eq_of_lt (by omega : 1 < p)
  exact ⟨Nat.zero_mul u, Nat.add_zero u, h0_mod, Nat.one_mul u, h1_mod, by omega⟩

/-- **Lemma 1.1 (`nonPVen_divisor_inheritance_native`):**
    Universal Non-`p`-ven Divisor Inheritance: if `0 < p`, `d ∣ u`, and `1 ≤ u % p`
    (`u` is non-`p`-ven), then `1 ≤ d % p` (`d` is also non-`p`-ven) and `¬ (p ∣ d)`. -/
theorem nonPVen_divisor_inheritance_native
    {p d u : ℕ} (hp_pos : 0 < p) (h_dvd : d ∣ u) (hu_npv : 1 ≤ u % p) :
    1 ≤ d % p ∧ ¬ (p ∣ d) := by
  have hd_npv : 1 ≤ d % p := by
    if hd0 : d % p = 0 then
      have h_p_dvd_d : p ∣ d := by
        have h_div : p * (d / p) + d % p = d := Nat.div_add_mod d p
        exact ⟨d / p, by omega⟩
      have h_p_dvd_u : p ∣ u := Nat.dvd_trans h_p_dvd_d h_dvd
      have h_u_mod0 : u % p = 0 :=
        (mod_eq_zero_and_mul_div_of_dvd_native hp_pos h_p_dvd_u).1
      omega
    else
      omega
  refine ⟨hd_npv, ?_⟩
  intro hp_dvd_d
  have hd_mod0 : d % p = 0 := (mod_eq_zero_and_mul_div_of_dvd_native hp_pos hp_dvd_d).1
  omega

/-- The `q`-rough survivor subset of any finite set `S : Finset ℕ`
    (intersection of `nonPVenDomain S d` across all `2 ≤ d < q`). -/
def roughSurvivorSet (S : Finset ℕ) (q : ℕ) : Finset ℕ :=
  S.filter (fun u : ℕ => 2 ≤ u ∧ ∀ d ∈ range q, 2 ≤ d → 1 ≤ u % d)

/-- **Theorem 1.2 (`roughSurvivorSet_subset_nonPVenDomain`):**
    For every `p` with `2 ≤ p < q`, `roughSurvivorSet S q ⊆ nonPVenDomain S p` and
    `(pVenDomain (roughSurvivorSet S q) p).card = 0`. -/
theorem roughSurvivorSet_subset_nonPVenDomain
    (S : Finset ℕ) {p q : ℕ} (hp2 : 2 ≤ p) (hp_lt : p < q) :
    roughSurvivorSet S q ⊆ nonPVenDomain S p ∧
    (pVenDomain (roughSurvivorSet S q) p).card = 0 := by
  have h_sub : roughSurvivorSet S q ⊆ nonPVenDomain S p := by
    intro u hu
    rw [roughSurvivorSet, mem_filter] at hu
    rw [nonPVenDomain, mem_filter]
    exact ⟨hu.1, hu.2.2 p (mem_range.mpr hp_lt) hp2⟩
  have h_pv_zero : (pVenDomain (roughSurvivorSet S q) p).card = 0 := by
    match Nat.eq_zero_or_pos (pVenDomain (roughSurvivorSet S q) p).card with
    | Or.inl h0 => exact h0
    | Or.inr hpos =>
      obtain ⟨u, hu⟩ := card_pos.mp hpos
      rw [pVenDomain, mem_filter] at hu
      have hu_npv := h_sub hu.1
      rw [nonPVenDomain, mem_filter] at hu_npv
      have h0 : u % p = 0 := hu.2
      have h1 : 1 ≤ u % p := hu_npv.2
      omega
  exact ⟨h_sub, h_pv_zero⟩

/-- Full Lower-MUR Prime Radius Carrier: radii `1 ≤ R < M - 2` where `M - R` is non-2-ven
    (`1 ≤ (M - R) % 2`) and prime (`IsPrimeNat (M - R)`). -/
def fullLowerMURPrimeRadii (M : ℕ) : Finset ℕ :=
  (range (M - 2)).filter (fun R : ℕ =>
    1 ≤ R ∧ 1 ≤ (M - R) % 2 ∧ IsPrimeNat (M - R))

/-- Reflected Upper-MUR Carrier `U_full(M) = {M + R | R ∈ fullLowerMURPrimeRadii M}`. -/
def fullLowerMURUpper (M : ℕ) : Finset ℕ :=
  (fullLowerMURPrimeRadii M).image (fun R : ℕ => M + R)

/-- Every `u ∈ fullLowerMURUpper M` satisfies `M + 1 ≤ u`, `u < 2 * M`, `1 ≤ u % 2` (`u % 2 = 1`),
    and `IsPrimeNat (2 * M - u)`. -/
theorem fullLowerMURUpper_mem_props {M u : ℕ} (hu : u ∈ fullLowerMURUpper M) :
    M + 1 ≤ u ∧
    u ≤ 2 * M - 3 ∧
    u < 2 * M ∧
    u % 2 = 1 ∧
    IsPrimeNat (2 * M - u) ∧
    (2 * M - u) + u = 2 * M := by
  rw [fullLowerMURUpper, mem_image] at hu
  obtain ⟨R, hR, rfl⟩ := hu
  rw [fullLowerMURPrimeRadii, mem_filter, mem_range] at hR
  obtain ⟨hR_lt, hR1, hMR_npv, hMR_isp⟩ := hR
  have h_sub : 2 * M - (M + R) = M - R := by omega
  rw [h_sub]
  exact ⟨by omega, by omega, by omega, by omega, hMR_isp, by omega⟩

/-- Optimal non-self-obstructing `2 · P_{n+1}` cutoff `q_opt := max M 3 + 1` (`Step209`). -/
def optimalUpperCutoff (M : ℕ) : ℕ :=
  max M 3 + 1

/-- **Theorem 1.3 (`optimal_M3_plus_1_cutoff_vanishes_composite_tail_and_embeds_goldbach`):**
    Ports `Step209` Sections 1–2 unconditionally:
    Let `M3 := max M 3`, `q_opt := optimalUpperCutoff M`, and `U_full := fullLowerMURUpper M3`.
    1. Every `u ∈ U_full` satisfies `q_opt ≤ u ∧ u < 2 * q_opt`,
    2. `(pn1RoughCompositeTail U_full q_opt).card = 0`,
    3. Every `u ∈ roughSurvivorSet U_full q_opt` satisfies `IsPrimeNat u ∧ Nat.Prime u`, and
    4. Whenever `0 < (roughSurvivorSet U_full q_opt).card`, `2 * M3` is unconditionally a
       Binary Goldbach sum `2 * M3 = p + q` paired with its Factorial Lighthouse next prime! -/
theorem optimal_M3_plus_1_cutoff_vanishes_composite_tail_and_embeds_goldbach (M : ℕ) :
    let M3 := max M 3
    let q_opt := optimalUpperCutoff M
    let U_full := fullLowerMURUpper M3
    (∀ u ∈ U_full, q_opt ≤ u ∧ u < 2 * q_opt) ∧
    (pn1RoughCompositeTail U_full q_opt).card = 0 ∧
    (∀ u ∈ roughSurvivorSet U_full q_opt,
      IsPrimeNat u ∧ Nat.Prime u ∧ Nat.Prime (2 * M3 - u) ∧ (2 * M3 - u) + u = 2 * M3) ∧
    (0 < (roughSurvivorSet U_full q_opt).card →
      ∃ p q p_next' : ℕ,
        Nat.Prime p ∧ Nat.Prime q ∧ 2 * M3 = p + q ∧
        p < p_next' ∧ Nat.Prime p_next' ∧ IsPrimeNat p_next') := by
  dsimp only
  have hM3_ge3 : 3 ≤ max M 3 := Nat.le_max_right M 3
  have h_bounds :
      ∀ u ∈ fullLowerMURUpper (max M 3),
        optimalUpperCutoff M ≤ u ∧ u < 2 * optimalUpperCutoff M := by
    intro u hu
    have hp := fullLowerMURUpper_mem_props hu
    unfold optimalUpperCutoff
    omega
  have h_tail_zero :
      (pn1RoughCompositeTail (fullLowerMURUpper (max M 3)) (optimalUpperCutoff M)).card = 0 :=
    pn1RoughCompositeTail_eq_empty_below_two_mul_Pn1 (fun u hu => (h_bounds u hu).2)
  have h_surv :
      ∀ u ∈ roughSurvivorSet (fullLowerMURUpper (max M 3)) (optimalUpperCutoff M),
        IsPrimeNat u ∧ Nat.Prime u ∧
        Nat.Prime (2 * max M 3 - u) ∧ (2 * max M 3 - u) + u = 2 * max M 3 := by
    intro u hu
    rw [roughSurvivorSet, mem_filter] at hu
    obtain ⟨hu_full, hu2, hu_rough⟩ := hu
    have hu_lt : u < 2 * optimalUpperCutoff M := (h_bounds u hu_full).2
    have hu_p := rough_below_two_mul_Pn1_isPrimeNat hu2 hu_lt
      (fun d hd2 hd_lt => hu_rough d (mem_range.mpr hd_lt) hd2)
    have hp_props := fullLowerMURUpper_mem_props hu_full
    exact ⟨hu_p.1, hu_p.2, isPrimeNat_to_natPrime hp_props.2.2.2.2.1, hp_props.2.2.2.2.2⟩
  refine ⟨h_bounds, h_tail_zero, h_surv, ?_⟩
  intro h_pos
  obtain ⟨u, hu⟩ := card_pos.mp h_pos
  have h_all := h_surv u hu
  obtain ⟨p_next', hp_lt, hp_nat, hp_isp⟩ :=
    hasNextPrimeMathlib_unconditional (2 * max M 3 - u)
  exact ⟨2 * max M 3 - u, u, p_next', h_all.2.2.1, h_all.2.1, h_all.2.2.2.symm,
    hp_lt, hp_nat, hp_isp⟩

/-!
## Section 2: Square-Absorber `minFac` Bound & Per-Block `√(2M)` Injection (`Step209` §3a)
-/

/-- **Lemma 2.1 (`minFac_mul_self_le_of_not_isPrimeNat`):**
    For every composite integer `u` (`2 ≤ u`, `¬ IsPrimeNat u`), its least prime factor
    `u.minFac` satisfies `IsPrimeNat u.minFac`, `u % u.minFac = 0`, `u.minFac ≤ u`,
    and `u.minFac * u.minFac ≤ u`. -/
theorem minFac_mul_self_le_of_not_isPrimeNat
    {u : ℕ} (hu2 : 2 ≤ u) (h_comp : ¬ IsPrimeNat u) :
    IsPrimeNat u.minFac ∧
    u % u.minFac = 0 ∧
    u.minFac ≤ u ∧
    u.minFac * u.minFac ≤ u := by
  have hu_ne1 : u ≠ 1 := by omega
  have h_mf_prime : Nat.Prime u.minFac := Nat.minFac_prime hu_ne1
  have h_mf_isp : IsPrimeNat u.minFac := natPrime_to_isPrimeNat h_mf_prime
  have h_mf_two : 2 ≤ u.minFac := h_mf_isp.1
  have h_mf_pos : 0 < u.minFac := by omega
  have h_mf_dvd : u.minFac ∣ u := Nat.minFac_dvd u
  have h_mf_mod0 : u % u.minFac = 0 :=
    (mod_eq_zero_and_mul_div_of_dvd_native h_mf_pos h_mf_dvd).1
  obtain ⟨k, hk⟩ := h_mf_dvd
  have hk_ne0 : k ≠ 0 := by
    intro hk0
    rw [hk0, Nat.mul_zero] at hk
    omega
  have hk_ne1 : k ≠ 1 := by
    intro hk1
    rw [hk1, Nat.mul_one] at hk
    rw [hk] at h_comp
    exact h_comp h_mf_isp
  have hk_pos : 0 < k := by omega
  have hk_mf_prime : Nat.Prime k.minFac := Nat.minFac_prime hk_ne1
  have hk_mf_dvd_k : k.minFac ∣ k := Nat.minFac_dvd k
  have hk_mf_le_k : k.minFac ≤ k := dvd_le_of_pos hk_mf_dvd_k hk_pos
  have hk_dvd_u : k ∣ u := ⟨u.minFac, by rw [Nat.mul_comm k u.minFac]; exact hk⟩
  have hk_mf_dvd_u : k.minFac ∣ u := Nat.dvd_trans hk_mf_dvd_k hk_dvd_u
  have h_mf_le_kmf : u.minFac ≤ k.minFac :=
    Nat.minFac_le_of_dvd hk_mf_prime.two_le hk_mf_dvd_u
  have h_mf_le_k : u.minFac ≤ k := Nat.le_trans h_mf_le_kmf hk_mf_le_k
  have h_sq_le : u.minFac * u.minFac ≤ u.minFac * k :=
    Nat.mul_le_mul_left u.minFac h_mf_le_k
  rw [← hk] at h_sq_le
  have h_mf_le_sq : u.minFac ≤ u.minFac * u.minFac := by
    have h1 : u.minFac * 1 ≤ u.minFac * u.minFac :=
      Nat.mul_le_mul_left u.minFac (by omega : 1 ≤ u.minFac)
    rw [Nat.mul_one] at h1
    exact h1
  have h_mf_le_u : u.minFac ≤ u := Nat.le_trans h_mf_le_sq h_sq_le
  exact ⟨h_mf_isp, h_mf_mod0, h_mf_le_u, h_sq_le⟩

/-- Active `√(2M)` LPF Owner Prime Set (`Step209` §3):
    non-2-ven primes `p` satisfying `q ≤ p` and `p * p ≤ 2 * M`. -/
def sqrtActiveOwnerPrimes (M q : ℕ) : Finset ℕ :=
  (range (2 * M + 1)).filter (fun p : ℕ =>
    IsPrimeNat p ∧ p % 2 = 1 ∧ q ≤ p ∧ p * p ≤ 2 * M)

/-- Every composite `u ∈ pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) q k) q`
    has `u.minFac ∈ sqrtActiveOwnerPrimes M q` and `q ≤ u.minFac`, proved via
    `nonPVen_divisor_inheritance_native` (`p = 2`) and explicit native order transitivity. -/
theorem roughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes
    {M q k u : ℕ}
    (hu : u ∈ pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) q k) q) :
    u.minFac ∈ sqrtActiveOwnerPrimes M q ∧
    q ≤ u.minFac ∧
    u % u.minFac = 0 ∧
    u.minFac % 2 = 1 ∧
    u % 2 = 1 := by
  rw [pn1RoughCompositeTail, mem_filter, subTwoQBlock, mem_filter] at hu
  obtain ⟨⟨hu_full, _⟩, hu2, hu_rough, hu_comp⟩ := hu
  have hu_props := fullLowerMURUpper_mem_props hu_full
  have hu_lt_2M : u < 2 * M := hu_props.2.2.1
  have hu_odd : u % 2 = 1 := hu_props.2.2.2.1
  have hu_npv2 : 1 ≤ u % 2 := by omega
  have h_mf := minFac_mul_self_le_of_not_isPrimeNat hu2 hu_comp
  have h_mf_isp : IsPrimeNat u.minFac := h_mf.1
  have h_mf_mod0 : u % u.minFac = 0 := h_mf.2.1
  have h_mf_le_u : u.minFac ≤ u := h_mf.2.2.1
  have h_mf_sq_le : u.minFac * u.minFac ≤ u := h_mf.2.2.2
  have h_mf_two : 2 ≤ u.minFac := h_mf_isp.1
  have h_mf_npv2 : 1 ≤ u.minFac % 2 :=
    (nonPVen_divisor_inheritance_native (by omega : 0 < 2) (Nat.minFac_dvd u) hu_npv2).1
  have h_mf_lt_2 : u.minFac % 2 < 2 := Nat.mod_lt u.minFac (by omega : 0 < 2)
  have h_mf_odd : u.minFac % 2 = 1 := by omega
  have h_q_le_mf : q ≤ u.minFac := by
    match Nat.lt_or_ge u.minFac q with
    | Or.inr hge => exact hge
    | Or.inl hlt =>
      have h_pos := hu_rough u.minFac (mem_range.mpr hlt) h_mf_two
      omega
  have h_mf_lt_2M : u.minFac < 2 * M := Nat.lt_of_le_of_lt h_mf_le_u hu_lt_2M
  have h_mf_lt_range : u.minFac < 2 * M + 1 :=
    Nat.lt_trans h_mf_lt_2M (Nat.lt_succ_self (2 * M))
  have h_mf_sq_2M : u.minFac * u.minFac ≤ 2 * M :=
    Nat.le_of_lt (Nat.lt_of_le_of_lt h_mf_sq_le hu_lt_2M)
  refine ⟨?_, h_q_le_mf, h_mf_mod0, h_mf_odd, hu_odd⟩
  rw [sqrtActiveOwnerPrimes, mem_filter, mem_range]
  exact ⟨h_mf_lt_range, h_mf_isp, h_mf_odd, h_q_le_mf, h_mf_sq_2M⟩

/-- **Theorem 2.2 (`subTwoQBlock_roughCompositeTail_card_le_sqrtActiveOwnerPrimes`):**
    Ports `Step209` Theorem 3.1 (`subTwoQBlock_semiprimeTail_card_le_sqrtActiveOwnerPrimes`)
    unconditionally for ALL `M, q, k : ℕ` (without `2 * M < q ^ 3`):
    `Nat.minFac` is injective on `pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) q k) q`
    and maps into `sqrtActiveOwnerPrimes M q`, so:
    `(pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) q k) q).card ≤ (sqrtActiveOwnerPrimes M q).card`. -/
theorem subTwoQBlock_roughCompositeTail_card_le_sqrtActiveOwnerPrimes (M q k : ℕ) :
    (pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) q k) q).card ≤
      (sqrtActiveOwnerPrimes M q).card := by
  have h_sub :
      (pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) q k) q).image Nat.minFac ⊆
        sqrtActiveOwnerPrimes M q := by
    intro p hp
    rw [mem_image] at hp
    obtain ⟨u, hu, rfl⟩ := hp
    exact (roughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes hu).1
  have h_inj :
      Set.InjOn Nat.minFac
        (↑(pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) q k) q) : Set ℕ) := by
    intro a0 ha0 b0 hb0 h_mf_eq
    rw [mem_coe] at ha0 hb0
    have ha_props := roughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes ha0
    have hb_props := roughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes hb0
    have ha_blk : a0 ∈ subTwoQBlock (fullLowerMURUpper M) q k := by
      rw [pn1RoughCompositeTail, mem_filter] at ha0
      exact ha0.1
    have hb_blk : b0 ∈ subTwoQBlock (fullLowerMURUpper M) q k := by
      rw [pn1RoughCompositeTail, mem_filter] at hb0
      exact hb0.1
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
      ((pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) q k) q).image Nat.minFac).card =
        (pn1RoughCompositeTail (subTwoQBlock (fullLowerMURUpper M) q k) q).card :=
    Finset.card_image_of_injOn h_inj
  rw [← h_card_img]
  exact card_le_card h_sub

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.zero_absorber_and_one_neutral_pVen_laws
#print axioms WuPaper.ESZerosBridge.nonPVen_divisor_inheritance_native
#print axioms WuPaper.ESZerosBridge.roughSurvivorSet_subset_nonPVenDomain
#print axioms WuPaper.ESZerosBridge.optimal_M3_plus_1_cutoff_vanishes_composite_tail_and_embeds_goldbach
#print axioms WuPaper.ESZerosBridge.minFac_mul_self_le_of_not_isPrimeNat
#print axioms WuPaper.ESZerosBridge.subTwoQBlock_roughCompositeTail_card_le_sqrtActiveOwnerPrimes
