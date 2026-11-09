import WR2Step216LiLiuRSCOrthogonalMultiplexorAndGlobalFiberBound

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step218LiLiuRSCInvolutionOrbitPairingAndD19Capstone.lean — Universal Odd-Modulus Square Involution & 5-Channel RSC Orbit Pairing Capstone for `D19 N`

Welds the Universal Subtraction-Free Square Involution Identity, the Universal Odd-Modulus
Square Involution Orbit Theorem (`universal_odd_modulus_sq_mem_liliuQrInvolutionOrbits`),
the Half-Chord Square Involution Orbit Folding (`21` orbits mod 65, `16` orbits mod 63),
and the 5-Channel RSC 2-to-1 Paired Involution Orbit Contraction (`12` mod 65, `9` mod 63,
`108` mod 8190) into the 41-Module `Goldbach.All` (`D19 N`) Master Capstone.
-/

/-!
## Section 1: Universal Subtraction-Free Square Involution & Native Modular Reduction
-/

theorem add_sq_add_sq_eq_liliu (a d : ℕ) :
    (a + d) ^ 2 + d ^ 2 = a ^ 2 + (a + d) * (2 * d) := by
  rw [nat_sq_eq_mul (a + d), nat_sq_eq_mul d, nat_sq_eq_mul a]
  have h1 : (a + d) * (a + d) = a * (a + d) + d * (a + d) :=
    Nat.right_distrib a d (a + d)
  have h2 : a * (a + d) = a * a + a * d := Nat.left_distrib a a d
  have h3 : d * (a + d) = d * a + d * d := Nat.left_distrib d a d
  have h4 : (a + d) * (2 * d) = a * (2 * d) + d * (2 * d) :=
    Nat.right_distrib a d (2 * d)
  have h5 : a * d = d * a := Nat.mul_comm a d
  have h2d : 2 * d = d + d := by omega
  have h6 : a * (2 * d) = a * d + a * d := by
    rw [h2d, Nat.left_distrib a d d]
  have h7 : d * (2 * d) = d * d + d * d := by
    rw [h2d, Nat.left_distrib d d d]
  omega

/-- Universal subtraction-free square involution identity: for all `d ≤ m`,
    `m ^ 2 + d ^ 2 = (m - d) ^ 2 + m * (2 * d)`. -/
theorem sub_sq_add_mul_two_eq_sq_add_sq_liliu {m d : ℕ} (hle : d ≤ m) :
    m ^ 2 + d ^ 2 = (m - d) ^ 2 + m * (2 * d) := by
  have h_id := add_sq_add_sq_eq_liliu (m - d) d
  have h_add : m - d + d = m := Nat.sub_add_cancel hle
  rw [h_add] at h_id
  exact h_id

/-- Pure native proof of `(m * K + A) % m = A % m` for all `m, K, A : ℕ`. -/
theorem mul_add_mod_self_left_liliu (m K A : ℕ) :
    (m * K + A) % m = A % m := by
  if hm0 : m = 0 then
    subst hm0
    rw [Nat.zero_mul, Nat.zero_add]
  else
    have hm_pos : 0 < m := by omega
    have hX_div : m * ((m * K + A) / m) + (m * K + A) % m = m * K + A :=
      Nat.div_add_mod (m * K + A) m
    have hA_div : m * (A / m) + A % m = A := Nat.div_add_mod A m
    have h_dist : m * (K + A / m) = m * K + m * (A / m) := Nat.left_distrib m K (A / m)
    have hX_lt : (m * K + A) % m < m := Nat.mod_lt (m * K + A) hm_pos
    have hA_lt : A % m < m := Nat.mod_lt A hm_pos
    match Nat.lt_or_ge ((m * K + A) % m) (A % m) with
    | Or.inl h_lt =>
      have h_diff_lt : A % m - (m * K + A) % m < m := by omega
      have h_eq : m * (K + A / m) + (A % m - (m * K + A) % m) = m * ((m * K + A) / m) := by omega
      have h_zero := eq_zero_of_mul_add_eq_mul_of_lt_liliu h_diff_lt h_eq
      omega
    | Or.inr h_ge =>
      match Nat.lt_or_ge (A % m) ((m * K + A) % m) with
      | Or.inl h_gt =>
        have h_diff_lt : (m * K + A) % m - A % m < m := by omega
        have h_eq : m * ((m * K + A) / m) + ((m * K + A) % m - A % m) = m * (K + A / m) := by omega
        have h_zero := eq_zero_of_mul_add_eq_mul_of_lt_liliu h_diff_lt h_eq
        omega
      | Or.inr h_le =>
        omega

/-- Pure native proof of `(x * x) % m = ((x % m) * (x % m)) % m` for all `x, m : ℕ`. -/
theorem sq_mod_eq_rem_sq_mod_liliu (x m : ℕ) :
    (x * x) % m = ((x % m) * (x % m)) % m := by
  have h_div : m * (x / m) + x % m = x := Nat.div_add_mod x m
  have h_expand : x * x = m * ((x / m) * x + (x / m) * (x % m)) + (x % m) * (x % m) := by
    calc x * x
      _ = (m * (x / m) + x % m) * x := by rw [h_div]
      _ = (m * (x / m)) * x + (x % m) * x := Nat.right_distrib (m * (x / m)) (x % m) x
      _ = m * ((x / m) * x) + (x % m) * (m * (x / m) + x % m) := by
          rw [Nat.mul_assoc m (x / m) x, h_div]
      _ = m * ((x / m) * x) + ((x % m) * (m * (x / m)) + (x % m) * (x % m)) := by
          rw [Nat.left_distrib (x % m) (m * (x / m)) (x % m)]
      _ = m * ((x / m) * x) + (m * ((x / m) * (x % m)) + (x % m) * (x % m)) := by
          rw [Nat.mul_comm (x % m) (m * (x / m)), Nat.mul_assoc m (x / m) (x % m)]
      _ = (m * ((x / m) * x) + m * ((x / m) * (x % m))) + (x % m) * (x % m) :=
          (Nat.add_assoc _ _ _).symm
      _ = m * ((x / m) * x + (x / m) * (x % m)) + (x % m) * (x % m) := by
          rw [← Nat.left_distrib m ((x / m) * x) ((x / m) * (x % m))]
  rw [h_expand]
  exact mul_add_mod_self_left_liliu m ((x / m) * x + (x / m) * (x % m)) ((x % m) * (x % m))

/-- Connects `sub_sq_add_mul_two_eq_sq_add_sq_liliu` to `mul_add_mod_self_left_liliu`
    to prove `((m - d) * (m - d)) % m = (d * d) % m` for all `d ≤ m`. -/
theorem involution_complement_sq_mod_eq_liliu {m d : ℕ} (hle : d ≤ m) :
    ((m - d) * (m - d)) % m = (d * d) % m := by
  have h_id := sub_sq_add_mul_two_eq_sq_add_sq_liliu hle
  rw [nat_sq_eq_mul m, nat_sq_eq_mul d, nat_sq_eq_mul (m - d)] at h_id
  rw [Nat.add_comm ((m - d) * (m - d)) (m * (2 * d))] at h_id
  have h_mod_eq : (m * m + d * d) % m = (m * (2 * d) + (m - d) * (m - d)) % m := by
    rw [h_id]
  rw [mul_add_mod_self_left_liliu m m (d * d),
      mul_add_mod_self_left_liliu m (2 * d) ((m - d) * (m - d))] at h_mod_eq
  exact h_mod_eq.symm

/-!
## Section 2: Universal Odd-Modulus Square Involution Orbit Theorem & Mod-9 Collapse
-/

/-- Folded Quadratic Residue Involution Orbits for odd modulus `m`. -/
def liliuQrInvolutionOrbits (m : ℕ) : Finset ℕ :=
  (range ((m + 1) / 2)).image (fun x : ℕ => (x * x) % m)

/-- **Theorem 2.1 (`universal_odd_modulus_sq_mem_liliuQrInvolutionOrbits`):**
    For EVERY odd modulus `m` (`m % 2 = 1`) and EVERY `x : ℕ`,
    `(x * x) % m ∈ liliuQrInvolutionOrbits m`. -/
theorem universal_odd_modulus_sq_mem_liliuQrInvolutionOrbits
    {m : ℕ} (hm_odd : m % 2 = 1) (x : ℕ) :
    (x * x) % m ∈ liliuQrInvolutionOrbits m := by
  have hm_pos : 0 < m := by omega
  have hd_lt : x % m < m := Nat.mod_lt x hm_pos
  have hd_le : x % m ≤ m := Nat.le_of_lt hd_lt
  have h_sq_rem := sq_mod_eq_rem_sq_mod_liliu x m
  rw [liliuQrInvolutionOrbits, mem_image]
  match Nat.lt_or_ge (x % m) ((m + 1) / 2) with
  | Or.inl h_lt_half =>
    refine ⟨x % m, mem_range.mpr h_lt_half, h_sq_rem.symm⟩
  | Or.inr h_ge_half =>
    have h_comp_lt : m - x % m < (m + 1) / 2 := by omega
    have h_comp_sq := involution_complement_sq_mod_eq_liliu hd_le
    refine ⟨m - x % m, mem_range.mpr h_comp_lt, ?_⟩
    rw [h_comp_sq, ← h_sq_rem]

def liliuQrMod9Basis (j : ℕ) : ℕ :=
  j + j / 3

/-- Folded Quadratic Residue Involution Orbits on Square-Shell `Mod 9` (`{0, 1, 4, 7}`). -/
def liliuQrMod9Orbits : Finset ℕ :=
  (range 4).image (fun j : ℕ => (liliuQrMod9Basis j * liliuQrMod9Basis j) % 9)

theorem liliuQrInvolutionOrbits_card_bounds (m : ℕ) :
    (liliuQrInvolutionOrbits m).card ≤ (m + 1) / 2 ∧
    liliuQrMod9Orbits.card ≤ 4 := by
  have h1 : (liliuQrInvolutionOrbits m).card ≤ (range ((m + 1) / 2)).card := card_image_le
  rw [card_range] at h1
  have h2 : liliuQrMod9Orbits.card ≤ (range 4).card := card_image_le
  rw [card_range] at h2
  exact ⟨h1, h2⟩

theorem sq_mod9_mem_liliuQrMod9Orbits (x : ℕ) :
    (x * x) % 9 ∈ liliuQrMod9Orbits := by
  have h9 := universal_odd_modulus_sq_mem_liliuQrInvolutionOrbits (m := 9) (by omega : 9 % 2 = 1) x
  rw [liliuQrInvolutionOrbits, mem_image] at h9
  obtain ⟨k, hk_range, hk_eq⟩ := h9
  rw [mem_range] at hk_range
  have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rw [liliuQrMod9Orbits, mem_image]
  rcases hk_cases with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, mem_range.mpr (by omega), hk_eq⟩
  · exact ⟨1, mem_range.mpr (by omega), hk_eq⟩
  · exact ⟨2, mem_range.mpr (by omega), hk_eq⟩
  · exact ⟨0, mem_range.mpr (by omega), hk_eq⟩
  · exact ⟨3, mem_range.mpr (by omega), hk_eq⟩

theorem sq_mod_mem_liliuQrInvolutionOrbits (x : ℕ) :
    (x * x) % 5 ∈ liliuQrInvolutionOrbits 5 ∧
    (x * x) % 7 ∈ liliuQrInvolutionOrbits 7 ∧
    (x * x) % 13 ∈ liliuQrInvolutionOrbits 13 ∧
    (x * x) % 9 ∈ liliuQrMod9Orbits :=
  ⟨universal_odd_modulus_sq_mem_liliuQrInvolutionOrbits (by omega : 5 % 2 = 1) x,
   universal_odd_modulus_sq_mem_liliuQrInvolutionOrbits (by omega : 7 % 2 = 1) x,
   universal_odd_modulus_sq_mem_liliuQrInvolutionOrbits (by omega : 13 % 2 = 1) x,
   sq_mod9_mem_liliuQrMod9Orbits x⟩

/-- **Theorem 2.2 (`liliuFiber_halfChordSq_mod65_and_mod63_orbit_bounds`):**
    On any fiber `S : Finset ℕ`, the half-chord midpoint square map `q ↦ (((q + r) / 2) ^ 2) % m`
    occupies at most `21` orbits modulo `65` (`3 * 7`) and at most `16` orbits modulo `63` (`4 * 4`). -/
theorem liliuFiber_halfChordSq_mod65_and_mod63_orbit_bounds (S : Finset ℕ) (r : ℕ) :
    (S.image (fun q : ℕ => (((q + r) / 2) ^ 2) % 65)).card ≤ 21 ∧
    (S.image (fun q : ℕ => (((q + r) / 2) ^ 2) % 63)).card ≤ 16 := by
  have h_sub65 :
      S.image (fun q : ℕ => (((q + r) / 2) ^ 2) % 65) ⊆
        (liliuQrInvolutionOrbits 5 ×ˢ liliuQrInvolutionOrbits 13).image
          liliuCrtReconstruct65From5And13 := by
    intro c hc
    rw [mem_image] at hc
    obtain ⟨q, _, rfl⟩ := hc
    set A_h := (q + r) / 2
    have h_sq_eq : A_h ^ 2 = A_h * A_h := nat_sq_eq_mul A_h
    have h_orbits := sq_mod_mem_liliuQrInvolutionOrbits A_h
    have hc_lt : (A_h ^ 2) % 65 < 65 := Nat.mod_lt (A_h ^ 2) (by omega : 0 < 65)
    have h_crt := liliuCrtReconstruct65_mod5_mod13_id (A_h ^ 2) ((A_h ^ 2) % 65) hc_lt
    rw [mem_image]
    refine ⟨((A_h * A_h) % 5, (A_h * A_h) % 13), ?_, ?_⟩
    · rw [mem_product]
      exact ⟨h_orbits.1, h_orbits.2.2.1⟩
    · rw [← h_sq_eq, ← h_crt.2.1, ← h_crt.2.2]
      exact h_crt.1
  have h_sub63 :
      S.image (fun q : ℕ => (((q + r) / 2) ^ 2) % 63) ⊆
        (liliuQrMod9Orbits ×ˢ liliuQrInvolutionOrbits 7).image
          liliuCrtReconstruct63From9And7 := by
    intro c hc
    rw [mem_image] at hc
    obtain ⟨q, _, rfl⟩ := hc
    set A_h := (q + r) / 2
    have h_sq_eq : A_h ^ 2 = A_h * A_h := nat_sq_eq_mul A_h
    have h_orbits := sq_mod_mem_liliuQrInvolutionOrbits A_h
    have hc_lt : (A_h ^ 2) % 63 < 63 := Nat.mod_lt (A_h ^ 2) (by omega : 0 < 63)
    have h_crt := liliuCrtReconstruct63_mod9_mod7_id (A_h ^ 2) ((A_h ^ 2) % 63) hc_lt
    rw [mem_image]
    refine ⟨((A_h * A_h) % 9, (A_h * A_h) % 7), ?_, ?_⟩
    · rw [mem_product]
      exact ⟨h_orbits.2.2.2, h_orbits.2.1⟩
    · rw [← h_sq_eq, ← h_crt.2.2.1, ← h_crt.2.2.2]
      exact h_crt.2.1
  have h_card65 :
      (S.image (fun q : ℕ => (((q + r) / 2) ^ 2) % 65)).card ≤
        (liliuQrInvolutionOrbits 5).card * (liliuQrInvolutionOrbits 13).card := by
    have h1 := Nat.le_trans (card_le_card h_sub65) card_image_le
    rw [card_product] at h1
    exact h1
  have h_card63 :
      (S.image (fun q : ℕ => (((q + r) / 2) ^ 2) % 63)).card ≤
        liliuQrMod9Orbits.card * (liliuQrInvolutionOrbits 7).card := by
    have h1 := Nat.le_trans (card_le_card h_sub63) card_image_le
    rw [card_product] at h1
    exact h1
  have hb5 := (liliuQrInvolutionOrbits_card_bounds 5).1
  have hb7 := (liliuQrInvolutionOrbits_card_bounds 7).1
  have hb13 := (liliuQrInvolutionOrbits_card_bounds 13).1
  have hb9 := (liliuQrInvolutionOrbits_card_bounds 9).2
  have h_mul21 := Nat.mul_le_mul hb5 hb13
  have h_mul16 := Nat.mul_le_mul hb9 hb7
  omega

/-!
## Section 3: 2-to-1 RSC Channel Involution Orbit Pairing (`12`, `9`, and `108` Paired Orbits)
-/

def liliuRscPairedOrbitMod65 (q : ℕ) : ℕ × ℕ :=
  ((q % 5 - 1) / 2, (q % 13 - 1) / 2)

def liliuRscPairedOrbitMod63 (q : ℕ) : ℕ × ℕ :=
  ((q % 9 - 1 - (q % 9) / 3) / 2, (q % 7 - 1) / 2)

def liliuRscPairedOrbitMod8190 (q : ℕ) : (ℕ × ℕ) × (ℕ × ℕ) :=
  (liliuRscPairedOrbitMod65 q, liliuRscPairedOrbitMod63 q)

/-- **Theorem 3.1 (`liliuFiber_rsc_paired_orbit_card_bounds`):**
    For every `r ≥ 13`, on `liliuShearContractedFiber N r`, the 2-to-1 paired involution
    orbits satisfy `card ≤ 12` on Mod-65, `card ≤ 9` on Mod-63, and `card ≤ 108` across Mod-8190. -/
theorem liliuFiber_rsc_paired_orbit_card_bounds
    {N r : ℕ} (hr13 : 13 ≤ r) :
    ((liliuShearContractedFiber N r).image liliuRscPairedOrbitMod65).card ≤ 12 ∧
    ((liliuShearContractedFiber N r).image liliuRscPairedOrbitMod63).card ≤ 9 ∧
    ((liliuShearContractedFiber N r).image liliuRscPairedOrbitMod8190).card ≤ 108 := by
  have hr_pos : 0 < r := by omega
  have h_sub65 :
      (liliuShearContractedFiber N r).image liliuRscPairedOrbitMod65 ⊆
        range 2 ×ˢ range 6 := by
    intro pair hp
    rw [mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have h_omc := (liliuShearContractedFiber_lower_pinch_10_9 hr_pos hq).2.2
    have h5_pos : 1 ≤ q % 5 := h_omc 5 (by omega) (by omega)
    have h13_pos : 1 ≤ q % 13 := h_omc 13 (by omega) hr13
    have h5_lt : q % 5 < 5 := Nat.mod_lt q (by omega)
    have h13_lt : q % 13 < 13 := Nat.mod_lt q (by omega)
    rw [mem_product, mem_range, mem_range]
    unfold liliuRscPairedOrbitMod65
    dsimp only
    omega
  have h_sub63 :
      (liliuShearContractedFiber N r).image liliuRscPairedOrbitMod63 ⊆
        range 3 ×ˢ range 3 := by
    intro pair hp
    rw [mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have h_omc := (liliuShearContractedFiber_lower_pinch_10_9 hr_pos hq).2.2
    have h3_pos : 1 ≤ q % 3 := h_omc 3 (by omega) (by omega)
    have h7_pos : 1 ≤ q % 7 := h_omc 7 (by omega) (by omega)
    have h9_lt : q % 9 < 9 := Nat.mod_lt q (by omega)
    have h7_lt : q % 7 < 7 := Nat.mod_lt q (by omega)
    rw [mem_product, mem_range, mem_range]
    unfold liliuRscPairedOrbitMod63
    dsimp only
    omega
  have h_sub8190 :
      (liliuShearContractedFiber N r).image liliuRscPairedOrbitMod8190 ⊆
        (liliuShearContractedFiber N r).image liliuRscPairedOrbitMod65 ×ˢ
        (liliuShearContractedFiber N r).image liliuRscPairedOrbitMod63 := by
    intro quad hquad
    rw [mem_image] at hquad
    obtain ⟨q, hq, rfl⟩ := hquad
    rw [mem_product, mem_image, mem_image]
    exact ⟨⟨q, hq, rfl⟩, ⟨q, hq, rfl⟩⟩
  have h_c65 : ((liliuShearContractedFiber N r).image liliuRscPairedOrbitMod65).card ≤ 12 := by
    have h1 := card_le_card h_sub65
    rw [card_product, card_range, card_range] at h1
    exact h1
  have h_c63 : ((liliuShearContractedFiber N r).image liliuRscPairedOrbitMod63).card ≤ 9 := by
    have h1 := card_le_card h_sub63
    rw [card_product, card_range] at h1
    omega
  have h_c8190 : ((liliuShearContractedFiber N r).image liliuRscPairedOrbitMod8190).card ≤ 108 := by
    have h1 := card_le_card h_sub8190
    rw [card_product] at h1
    have h_mul := Nat.mul_le_mul h_c65 h_c63
    omega
  exact ⟨h_c65, h_c63, h_c8190⟩

/-- **Master 41-Module Capstone (`master_41module_D19_rsc_involution_orbit_pairing_capstone`):**
    Complete 41-Module Capstone uniting `Goldbach.one_plus_one_nine_count` (`liuMainTerm0004 N < (D19 N : ℝ)`),
    the Universal Subtraction-Free Square Involution Identity (`m ^ 2 + d ^ 2 = (m - d) ^ 2 + m * (2 * d)`),
    the Half-Chord Square Involution Orbit Bounds (`21` orbits mod 65, `16` orbits mod 63),
    the 5-Channel RSC 2-to-1 Paired Involution Orbit Bounds (`12` mod 65, `9` mod 63, `108` mod 8190),
    the Constructive Global Per-Fiber Product Contraction (`liliuFloorSubfiber_card_le_admissible_mul_stride`),
    and the Factorial Lighthouse Next-Prime Generator (`hasNextPrimeConnection_unconditional`). -/
theorem master_41module_D19_rsc_involution_orbit_pairing_capstone :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (∀ m d : ℕ, d ≤ m → m ^ 2 + d ^ 2 = (m - d) ^ 2 + m * (2 * d)) ∧
      (∀ r : ℕ,
        ((liliuShearContractedFiber N r).image (fun q : ℕ => (((q + r) / 2) ^ 2) % 65)).card ≤ 21 ∧
        ((liliuShearContractedFiber N r).image (fun q : ℕ => (((q + r) / 2) ^ 2) % 63)).card ≤ 16) ∧
      (∀ r : ℕ, 13 ≤ r →
        ((liliuShearContractedFiber N r).image liliuRscPairedOrbitMod65).card ≤ 12 ∧
        ((liliuShearContractedFiber N r).image liliuRscPairedOrbitMod63).card ≤ 9 ∧
        ((liliuShearContractedFiber N r).image liliuRscPairedOrbitMod8190).card ≤ 108) ∧
      (∀ r L m : ℕ, 0 < m →
        (liliuFloorSubfiber N r L).card ≤
          ((liliuFloorSubfiber N r L).image (fun q : ℕ => q % m)).card *
            (((N / r) / m - L / m) + 1)) ∧
      (fiveupPinchedQRSubfilter 9 10 N).card ≤
        1 + ((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).card ∧
      ((((1 + ((pinchedOddPrimes919 N).biUnion (liliuTight3PrimeFiberPairs N)).card : ℕ) : ℝ) ≤
          liuMainTerm0004 N) →
        ∃ p q p_next' : ℕ,
          Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next' ∧ IsPrimeNat p_next') := by
  obtain ⟨K, hK4, hCap39⟩ := master_39module_D19_rsc_multiplexor_and_global_fiber_product_capstone
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven
  have hM := hCap39 N hNK hEven
  refine ⟨hM.1,
          fun m d hle => sub_sq_add_mul_two_eq_sq_add_sq_liliu hle,
          fun r => liliuFiber_halfChordSq_mod65_and_mod63_orbit_bounds (liliuShearContractedFiber N r) r,
          fun r hr13 => liliuFiber_rsc_paired_orbit_card_bounds hr13,
          hM.2.2.2.1,
          hM.2.2.2.2.1,
          hM.2.2.2.2.2⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.sub_sq_add_mul_two_eq_sq_add_sq_liliu
#print axioms WuPaper.ESZerosBridge.mul_add_mod_self_left_liliu
#print axioms WuPaper.ESZerosBridge.sq_mod_eq_rem_sq_mod_liliu
#print axioms WuPaper.ESZerosBridge.involution_complement_sq_mod_eq_liliu
#print axioms WuPaper.ESZerosBridge.universal_odd_modulus_sq_mem_liliuQrInvolutionOrbits
#print axioms WuPaper.ESZerosBridge.liliuFiber_halfChordSq_mod65_and_mod63_orbit_bounds
#print axioms WuPaper.ESZerosBridge.liliuFiber_rsc_paired_orbit_card_bounds
#print axioms WuPaper.ESZerosBridge.master_41module_D19_rsc_involution_orbit_pairing_capstone
