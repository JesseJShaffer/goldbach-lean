import WR2Step228LiLiuSubTwoQSingleHitAnd51ModuleMasterCapstone

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step230LiLiuOptimalM3Plus1And53ModuleCapstone.lean — Zero-One Neutral/Absorber Laws, Universal Non-`p`-ven Divisor Inheritance, `Step209` Optimal `M_3 + 1` Cutoff, Per-Block `√(2M)` Owner Injection & Master 53-Module `D19 N` Capstone

Ports `Step209` Sections 1–3 onto the Track 2 (`D19 N`) stack using the Zero-One
Neutral/Absorber laws (`zero_absorber_and_one_neutral_pVen_laws_liliu`), universal `p`-ven
divisor inheritance (`nonPVen_divisor_inheritance_liliu`), and explicit square-absorber bounds.
-/

/-!
## Section 1: Zero-One Neutral/Absorber Laws, Non-`p`-ven Divisor Inheritance & Optimal `q_opt := max M 3 + 1` Cutoff
-/

/-- Explicit Zero-Absorber (`0`) and One-Neutral (`1`) laws across all `p`-ven domains (`Step121`). -/
theorem zero_absorber_and_one_neutral_pVen_laws_liliu {p : ℕ} (hp2 : 2 ≤ p) (u : ℕ) :
    0 * u = 0 ∧
    u + 0 = u ∧
    0 % p = 0 ∧
    1 * u = u ∧
    1 % p = 1 ∧
    1 ≤ 1 % p := by
  have h0_mod : 0 % p = 0 := Nat.zero_mod p
  have h1_mod : 1 % p = 1 := Nat.mod_eq_of_lt (by omega : 1 < p)
  exact ⟨Nat.zero_mul u, Nat.add_zero u, h0_mod, Nat.one_mul u, h1_mod, by omega⟩

/-- Universal Non-`p`-ven Divisor Inheritance on Track 2 (`WR2Step212`). -/
theorem nonPVen_divisor_inheritance_liliu
    {p d u : ℕ} (hp_pos : 0 < p) (h_dvd : d ∣ u) (hu_npv : 1 ≤ u % p) :
    1 ≤ d % p ∧ ¬ (p ∣ d) := by
  have hd_npv : 1 ≤ d % p := by
    if hd0 : d % p = 0 then
      have h_p_dvd_d : p ∣ d := by
        have h_div : p * (d / p) + d % p = d := Nat.div_add_mod d p
        exact ⟨d / p, by omega⟩
      have h_p_dvd_u : p ∣ u := Nat.dvd_trans h_p_dvd_d h_dvd
      have h_u_mod0 : u % p = 0 :=
        (mod_eq_zero_and_mul_div_of_dvd_liliu hp_pos h_p_dvd_u).1
      omega
    else
      omega
  refine ⟨hd_npv, ?_⟩
  intro hp_dvd_d
  have hd_mod0 : d % p = 0 := (mod_eq_zero_and_mul_div_of_dvd_liliu hp_pos hp_dvd_d).1
  omega

def liliuRoughSurvivorSet (S : Finset ℕ) (q : ℕ) : Finset ℕ :=
  S.filter (fun u : ℕ => 2 ≤ u ∧ ∀ d ∈ range q, 2 ≤ d → 1 ≤ u % d)

theorem liliuRoughSurvivorSet_subset_nonPVenDomain
    (S : Finset ℕ) {p q : ℕ} (hp2 : 2 ≤ p) (hp_lt : p < q) :
    liliuRoughSurvivorSet S q ⊆ liliuNonPVenDomain S p ∧
    (liliuPVenDomain (liliuRoughSurvivorSet S q) p).card = 0 := by
  have h_sub : liliuRoughSurvivorSet S q ⊆ liliuNonPVenDomain S p := by
    intro u hu
    rw [liliuRoughSurvivorSet, mem_filter] at hu
    rw [liliuNonPVenDomain, mem_filter]
    exact ⟨hu.1, hu.2.2 p (mem_range.mpr hp_lt) hp2⟩
  have h_pv_zero : (liliuPVenDomain (liliuRoughSurvivorSet S q) p).card = 0 := by
    match Nat.eq_zero_or_pos (liliuPVenDomain (liliuRoughSurvivorSet S q) p).card with
    | Or.inl h0 => exact h0
    | Or.inr hpos =>
      obtain ⟨u, hu⟩ := card_pos.mp hpos
      rw [liliuPVenDomain, mem_filter] at hu
      have hu_npv := h_sub hu.1
      rw [liliuNonPVenDomain, mem_filter] at hu_npv
      have h0 : u % p = 0 := hu.2
      have h1 : 1 ≤ u % p := hu_npv.2
      omega
  exact ⟨h_sub, h_pv_zero⟩

def liliuFullLowerMURPrimeRadii (M : ℕ) : Finset ℕ :=
  (range (M - 2)).filter (fun R : ℕ =>
    1 ≤ R ∧ 1 ≤ (M - R) % 2 ∧ IsPrimeNat (M - R))

def liliuFullLowerMURUpper (M : ℕ) : Finset ℕ :=
  (liliuFullLowerMURPrimeRadii M).image (fun R : ℕ => M + R)

theorem liliuFullLowerMURUpper_mem_props {M u : ℕ} (hu : u ∈ liliuFullLowerMURUpper M) :
    M + 1 ≤ u ∧
    u ≤ 2 * M - 3 ∧
    u < 2 * M ∧
    u % 2 = 1 ∧
    IsPrimeNat (2 * M - u) ∧
    (2 * M - u) + u = 2 * M := by
  rw [liliuFullLowerMURUpper, mem_image] at hu
  obtain ⟨R, hR, rfl⟩ := hu
  rw [liliuFullLowerMURPrimeRadii, mem_filter, mem_range] at hR
  obtain ⟨_, _, _, hMR_isp⟩ := hR
  have h_sub : 2 * M - (M + R) = M - R := by omega
  rw [h_sub]
  exact ⟨by omega, by omega, by omega, by omega, hMR_isp, by omega⟩

def liliuOptimalUpperCutoff (M : ℕ) : ℕ :=
  max M 3 + 1

/-- **Theorem 1.1 (`liliu_optimal_M3_plus_1_cutoff_vanishes_composite_tail`):**
    Unconditional `Step209` Optimal `M_3 + 1` Cutoff & Goldbach Embedding on Track 2. -/
theorem liliu_optimal_M3_plus_1_cutoff_vanishes_composite_tail (M : ℕ) :
    let M3 := max M 3
    let q_opt := liliuOptimalUpperCutoff M
    let U_full := liliuFullLowerMURUpper M3
    (∀ u ∈ U_full, q_opt ≤ u ∧ u < 2 * q_opt) ∧
    (liliuPn1RoughCompositeTail U_full q_opt).card = 0 ∧
    (∀ u ∈ liliuRoughSurvivorSet U_full q_opt,
      IsPrimeNat u ∧ Nat.Prime u ∧ Nat.Prime (2 * M3 - u) ∧ (2 * M3 - u) + u = 2 * M3) ∧
    (0 < (liliuRoughSurvivorSet U_full q_opt).card →
      ∃ p q p_next' : ℕ,
        Nat.Prime p ∧ Nat.Prime q ∧ 2 * M3 = p + q ∧
        p < p_next' ∧ IsPrimeNat p_next') := by
  dsimp only
  have hM3_ge3 : 3 ≤ max M 3 := Nat.le_max_right M 3
  have h_bounds :
      ∀ u ∈ liliuFullLowerMURUpper (max M 3),
        liliuOptimalUpperCutoff M ≤ u ∧ u < 2 * liliuOptimalUpperCutoff M := by
    intro u hu
    have hp := liliuFullLowerMURUpper_mem_props hu
    unfold liliuOptimalUpperCutoff
    omega
  have h_tail_zero :
      (liliuPn1RoughCompositeTail (liliuFullLowerMURUpper (max M 3)) (liliuOptimalUpperCutoff M)).card = 0 :=
    liliuPn1RoughCompositeTail_eq_empty_below_two_mul_Pn1 (fun u hu => (h_bounds u hu).2)
  have h_surv :
      ∀ u ∈ liliuRoughSurvivorSet (liliuFullLowerMURUpper (max M 3)) (liliuOptimalUpperCutoff M),
        IsPrimeNat u ∧ Nat.Prime u ∧
        Nat.Prime (2 * max M 3 - u) ∧ (2 * max M 3 - u) + u = 2 * max M 3 := by
    intro u hu
    rw [liliuRoughSurvivorSet, mem_filter] at hu
    obtain ⟨hu_full, hu2, hu_rough⟩ := hu
    have hu_lt : u < 2 * liliuOptimalUpperCutoff M := (h_bounds u hu_full).2
    have hu_p := liliu_rough_below_two_mul_Pn1_isPrimeNat hu2 hu_lt
      (fun d hd2 hd_lt => hu_rough d (mem_range.mpr hd_lt) hd2)
    have hp_props := liliuFullLowerMURUpper_mem_props hu_full
    exact ⟨hu_p.1, hu_p.2, isPrimeNat_to_natPrime_liliu hp_props.2.2.2.2.1, hp_props.2.2.2.2.2⟩
  refine ⟨h_bounds, h_tail_zero, h_surv, ?_⟩
  intro h_pos
  obtain ⟨u, hu⟩ := card_pos.mp h_pos
  have h_all := h_surv u hu
  obtain ⟨p_next', hp_lt, hp_isp⟩ :=
    hasNextPrimeConnection_unconditional (2 * max M 3 - u)
  exact ⟨2 * max M 3 - u, u, p_next', h_all.2.2.1, h_all.2.1, h_all.2.2.2.symm,
    hp_lt, hp_isp⟩

/-!
## Section 2: Square-Absorber `minFac` Bound & Per-Block `√(2M)` Injection (`Step209` §3a)
-/

theorem minFac_mul_self_le_of_not_isPrimeNat_liliu
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
    (mod_eq_zero_and_mul_div_of_dvd_liliu h_mf_pos h_mf_dvd).1
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

/-- Active `√(2M)` LPF Owner Prime Set (`Step209` §3). -/
def liliuSqrtActiveOwnerPrimes (M q : ℕ) : Finset ℕ :=
  (range (2 * M + 1)).filter (fun p : ℕ =>
    IsPrimeNat p ∧ p % 2 = 1 ∧ q ≤ p ∧ p * p ≤ 2 * M)

theorem liliuRoughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes
    {M q k u : ℕ}
    (hu : u ∈ liliuPn1RoughCompositeTail (liliuSubTwoQBlock (liliuFullLowerMURUpper M) q k) q) :
    u.minFac ∈ liliuSqrtActiveOwnerPrimes M q ∧
    q ≤ u.minFac ∧
    u % u.minFac = 0 ∧
    u.minFac % 2 = 1 ∧
    u % 2 = 1 := by
  rw [liliuPn1RoughCompositeTail, mem_filter, liliuSubTwoQBlock, mem_filter] at hu
  obtain ⟨⟨hu_full, _⟩, hu2, hu_rough, hu_comp⟩ := hu
  have hu_props := liliuFullLowerMURUpper_mem_props hu_full
  have hu_lt_2M : u < 2 * M := hu_props.2.2.1
  have hu_odd : u % 2 = 1 := hu_props.2.2.2.1
  have hu_npv2 : 1 ≤ u % 2 := by omega
  have h_mf := minFac_mul_self_le_of_not_isPrimeNat_liliu hu2 hu_comp
  have h_mf_isp : IsPrimeNat u.minFac := h_mf.1
  have h_mf_mod0 : u % u.minFac = 0 := h_mf.2.1
  have h_mf_le_u : u.minFac ≤ u := h_mf.2.2.1
  have h_mf_sq_le : u.minFac * u.minFac ≤ u := h_mf.2.2.2
  have h_mf_two : 2 ≤ u.minFac := h_mf_isp.1
  have h_mf_npv2 : 1 ≤ u.minFac % 2 :=
    (nonPVen_divisor_inheritance_liliu (by omega : 0 < 2) (Nat.minFac_dvd u) hu_npv2).1
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
  rw [liliuSqrtActiveOwnerPrimes, mem_filter, mem_range]
  exact ⟨h_mf_lt_range, h_mf_isp, h_mf_odd, h_q_le_mf, h_mf_sq_2M⟩

/-- **Theorem 2.1 (`liliuSubTwoQBlock_roughCompositeTail_card_le_sqrtActiveOwnerPrimes`):**
    Unconditional Per-Block `√(2M)` `Nat.minFac` Injection (`Step209` §3a):
    For ALL `M, q, k : ℕ`,
    `(liliuPn1RoughCompositeTail (liliuSubTwoQBlock (liliuFullLowerMURUpper M) q k) q).card ≤ (liliuSqrtActiveOwnerPrimes M q).card`. -/
theorem liliuSubTwoQBlock_roughCompositeTail_card_le_sqrtActiveOwnerPrimes (M q k : ℕ) :
    (liliuPn1RoughCompositeTail (liliuSubTwoQBlock (liliuFullLowerMURUpper M) q k) q).card ≤
      (liliuSqrtActiveOwnerPrimes M q).card := by
  have h_sub :
      (liliuPn1RoughCompositeTail (liliuSubTwoQBlock (liliuFullLowerMURUpper M) q k) q).image Nat.minFac ⊆
        liliuSqrtActiveOwnerPrimes M q := by
    intro p hp
    rw [mem_image] at hp
    obtain ⟨u, hu, rfl⟩ := hp
    exact (liliuRoughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes hu).1
  have h_inj :
      Set.InjOn Nat.minFac
        (↑(liliuPn1RoughCompositeTail (liliuSubTwoQBlock (liliuFullLowerMURUpper M) q k) q) : Set ℕ) := by
    intro a0 ha0 b0 hb0 h_mf_eq
    rw [mem_coe] at ha0 hb0
    have ha_props := liliuRoughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes ha0
    have hb_props := liliuRoughCompositeTail_minFac_mem_sqrtActiveOwnerPrimes hb0
    have ha_blk : a0 ∈ liliuSubTwoQBlock (liliuFullLowerMURUpper M) q k := by
      rw [liliuPn1RoughCompositeTail, mem_filter] at ha0
      exact ha0.1
    have hb_blk : b0 ∈ liliuSubTwoQBlock (liliuFullLowerMURUpper M) q k := by
      rw [liliuPn1RoughCompositeTail, mem_filter] at hb0
      exact hb0.1
    have h_diam_fn :=
      (liliuSubTwoQBlock_unconditional_partition_and_diameter (liliuFullLowerMURUpper M) q).2.2.2 k
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
      exact eq_of_sub_lt_two_max_of_odd_of_mod_eq_liliu hp_odd hle h_d_p ha_odd hb_odd h_mod_eq
    | Or.inr hge =>
      have h_d_q : a0 - b0 < 2 * max q 1 := h_diam_fn b0 a0 hb_blk ha_blk hge
      have h_d_p : a0 - b0 < 2 * max a0.minFac 1 := Nat.lt_of_lt_of_le h_d_q h_max_le
      exact (eq_of_sub_lt_two_max_of_odd_of_mod_eq_liliu hp_odd hge h_d_p hb_odd ha_odd h_mod_eq.symm).symm
  have h_card_img :
      ((liliuPn1RoughCompositeTail (liliuSubTwoQBlock (liliuFullLowerMURUpper M) q k) q).image Nat.minFac).card =
        (liliuPn1RoughCompositeTail (liliuSubTwoQBlock (liliuFullLowerMURUpper M) q k) q).card :=
    Finset.card_image_of_injOn h_inj
  rw [← h_card_img]
  exact card_le_card h_sub

/-- **Master Theorem 3.1 (`master_53module_step208_step209_step212_and_goldbach_lean_capstone`):**
    Complete 53-Module Master Synthesis uniting `Goldbach.one_plus_one_nine_count` (`D19 N`),
    Zero-One Neutral/Absorber Laws, Universal Non-`p`-ven Divisor Inheritance,
    `Step209` Optimal `M_3 + 1` Cutoff & `√(2M)` Per-Block `Nat.minFac` Injection,
    `Step208` Sub-`2r` Single-Hit & `2 · P_{n+1}` Filter,
    `Step203`/`Step205` Bilateral Outer Cayley Cone Discharge, and
    `Step212` First-Missing-Prime `q_E` Zero-Sum Collapse. -/
theorem master_53module_step208_step209_step212_and_goldbach_lean_capstone :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (liliuPn1RoughCompositeTail
        (liliuFullLowerMURUpper (max (N / 2) 3))
        (liliuOptimalUpperCutoff (N / 2))).card = 0 ∧
      (∀ q k : ℕ,
        (liliuPn1RoughCompositeTail
          (liliuSubTwoQBlock (liliuFullLowerMURUpper (N / 2)) q k) q).card ≤
          (liliuSqrtActiveOwnerPrimes (N / 2) q).card) ∧
      (∀ q_E : ℕ, IsFirstMissingOddPrimeLiliu N q_E → N < q_E * (q_E + 2) + 2 →
        (∑ r ∈ pinchedOddPrimes919 N, (liliuTargetSieved3PrimeFiber N r q_E).card) = 0 ∧
        (fiveupPinchedQRSubfilter 9 10 N).card ≤ q_E ∧
        (((q_E : ℝ) ≤ liuMainTerm0004 N) →
          ∃ p q p_next' : ℕ,
            Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next' ∧ IsPrimeNat p_next')) := by
  obtain ⟨K, hK4, hCap51⟩ := master_51module_complete_step208_step212_and_goldbach_lean_capstone
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven
  have hM := hCap51 N hNK hEven
  exact ⟨hM.1,
         (liliu_optimal_M3_plus_1_cutoff_vanishes_composite_tail (N / 2)).2.1,
         fun q k => liliuSubTwoQBlock_roughCompositeTail_card_le_sqrtActiveOwnerPrimes (N / 2) q k,
         hM.2.2.2.2⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.zero_absorber_and_one_neutral_pVen_laws_liliu
#print axioms WuPaper.ESZerosBridge.nonPVen_divisor_inheritance_liliu
#print axioms WuPaper.ESZerosBridge.liliuRoughSurvivorSet_subset_nonPVenDomain
#print axioms WuPaper.ESZerosBridge.liliu_optimal_M3_plus_1_cutoff_vanishes_composite_tail
#print axioms WuPaper.ESZerosBridge.minFac_mul_self_le_of_not_isPrimeNat_liliu
#print axioms WuPaper.ESZerosBridge.liliuSubTwoQBlock_roughCompositeTail_card_le_sqrtActiveOwnerPrimes
#print axioms WuPaper.ESZerosBridge.master_53module_step208_step209_step212_and_goldbach_lean_capstone
