import WR2Step215WR2RSCOrthogonalMultiplexorAnd8190FiberBound

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step217WR2RSCInvolutionOrbitPairingAndChannelContraction.lean — Universal Odd-Modulus Square Involution & 5-Channel RSC Orbit Pairing

1. **Universal Subtraction-Free Square Involution & Modular Reduction
   (`sub_sq_add_mul_two_eq_sq_add_sq`, `mul_add_mod_self_left_native`,
   `sq_mod_eq_rem_sq_mod_native`, `involution_complement_sq_mod_eq_native`):**
   Proves in pure `Init` arithmetic for all `m, d, x : ℕ` (`d ≤ m`) that:
   - `(m * K + A) % m = A % m`,
   - `(x * x) % m = ((x % m) * (x % m)) % m`, and
   - `((m - d) * (m - d)) % m = (d * d) % m`.
2. **Universal Odd-Modulus Square Involution Orbit Theorem
   (`universal_odd_modulus_sq_mem_qrInvolutionOrbits`,
   `wr2Fiber_halfChordSq_mod65_and_mod63_orbit_bounds`):**
   Proves for EVERY odd modulus `m` (`m % 2 = 1`) that `(x * x) % m ∈ qrInvolutionOrbits m`
   (`card ≤ (m + 1) / 2`), and collapses `Mod 9` (`3^2 ≡ 0^2 mod 9`) to `4` orbits (`{0, 1, 4, 7}`),
   proving that the half-chord square `((q + r) / 2) ^ 2` occupies at most `3 * 7 = 21` orbits
   modulo `65` and at most `4 * 4 = 16` orbits modulo `63`.
3. **2-to-1 RSC Channel Involution Orbit Pairing (`wr2Fiber_rsc_paired_orbit_card_bounds`):**
   Contracts the 5-channel RSC survivor lanes via 2-to-1 orbit pairing to at most `12`
   orbits on Mod-65, `9` orbits on Mod-63, and `108` paired orbits across Mod-8190.
-/

/-!
## Section 1: Universal Subtraction-Free Square Involution & Pure Native Modular Reduction
-/

/-- Pure native subtraction-free polynomial identity:
    `(a + d) ^ 2 + d ^ 2 = a ^ 2 + (a + d) * (2 * d)` for all `a, d : ℕ`. -/
theorem add_sq_add_sq_eq_native (a d : ℕ) :
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

/-- **Theorem 1.1 (`sub_sq_add_mul_two_eq_sq_add_sq`):**
    For every modulus `m` and residue `d ≤ m`, `m ^ 2 + d ^ 2 = (m - d) ^ 2 + m * (2 * d)`. -/
theorem sub_sq_add_mul_two_eq_sq_add_sq {m d : ℕ} (hle : d ≤ m) :
    m ^ 2 + d ^ 2 = (m - d) ^ 2 + m * (2 * d) := by
  have h_id := add_sq_add_sq_eq_native (m - d) d
  have h_add : m - d + d = m := Nat.sub_add_cancel hle
  rw [h_add] at h_id
  exact h_id

/-- Pure native proof of `(m * K + A) % m = A % m` for all `m, K, A : ℕ`,
    connected directly to `eq_zero_of_mul_add_eq_mul_of_lt` (`WR2Step205`). -/
theorem mul_add_mod_self_left_native (m K A : ℕ) :
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
      have h_zero := eq_zero_of_mul_add_eq_mul_of_lt h_diff_lt h_eq
      omega
    | Or.inr h_ge =>
      match Nat.lt_or_ge (A % m) ((m * K + A) % m) with
      | Or.inl h_gt =>
        have h_diff_lt : (m * K + A) % m - A % m < m := by omega
        have h_eq : m * ((m * K + A) / m) + ((m * K + A) % m - A % m) = m * (K + A / m) := by omega
        have h_zero := eq_zero_of_mul_add_eq_mul_of_lt h_diff_lt h_eq
        omega
      | Or.inr h_le =>
        omega

/-- **Theorem 1.2 (`sq_mod_eq_rem_sq_mod_native`):**
    Pure native proof of `(x * x) % m = ((x % m) * (x % m)) % m` for all `x, m : ℕ`. -/
theorem sq_mod_eq_rem_sq_mod_native (x m : ℕ) :
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
  exact mul_add_mod_self_left_native m ((x / m) * x + (x / m) * (x % m)) ((x % m) * (x % m))

/-- **Theorem 1.3 (`involution_complement_sq_mod_eq_native`):**
    Connects `sub_sq_add_mul_two_eq_sq_add_sq` directly to `mul_add_mod_self_left_native`
    to prove `((m - d) * (m - d)) % m = (d * d) % m` for all `d ≤ m`. -/
theorem involution_complement_sq_mod_eq_native {m d : ℕ} (hle : d ≤ m) :
    ((m - d) * (m - d)) % m = (d * d) % m := by
  have h_id := sub_sq_add_mul_two_eq_sq_add_sq hle
  rw [nat_sq_eq_mul m, nat_sq_eq_mul d, nat_sq_eq_mul (m - d)] at h_id
  rw [Nat.add_comm ((m - d) * (m - d)) (m * (2 * d))] at h_id
  have h_mod_eq : (m * m + d * d) % m = (m * (2 * d) + (m - d) * (m - d)) % m := by
    rw [h_id]
  rw [mul_add_mod_self_left_native m m (d * d),
      mul_add_mod_self_left_native m (2 * d) ((m - d) * (m - d))] at h_mod_eq
  exact h_mod_eq.symm

/-!
## Section 2: Universal Odd-Modulus Square Involution Orbit Theorem & Mod-9 Collapse
-/

/-- The folded Quadratic Residue Involution Orbit set for odd modulus `m`:
    projects the lower half-interval `range ((m + 1) / 2)` via `x ↦ (x * x) % m`. -/
def qrInvolutionOrbits (m : ℕ) : Finset ℕ :=
  (range ((m + 1) / 2)).image (fun x : ℕ => (x * x) % m)

/-- **Theorem 2.1 (`universal_odd_modulus_sq_mem_qrInvolutionOrbits`):**
    Universal 5UP Square Involution Orbit Folding: for EVERY odd modulus `m` (`m % 2 = 1`)
    and EVERY `x : ℕ`, `(x * x) % m ∈ qrInvolutionOrbits m`. -/
theorem universal_odd_modulus_sq_mem_qrInvolutionOrbits
    {m : ℕ} (hm_odd : m % 2 = 1) (x : ℕ) :
    (x * x) % m ∈ qrInvolutionOrbits m := by
  have hm_pos : 0 < m := by omega
  have hd_lt : x % m < m := Nat.mod_lt x hm_pos
  have hd_le : x % m ≤ m := Nat.le_of_lt hd_lt
  have h_sq_rem := sq_mod_eq_rem_sq_mod_native x m
  rw [qrInvolutionOrbits, mem_image]
  match Nat.lt_or_ge (x % m) ((m + 1) / 2) with
  | Or.inl h_lt_half =>
    refine ⟨x % m, mem_range.mpr h_lt_half, h_sq_rem.symm⟩
  | Or.inr h_ge_half =>
    have h_comp_lt : m - x % m < (m + 1) / 2 := by omega
    have h_comp_sq := involution_complement_sq_mod_eq_native hd_le
    refine ⟨m - x % m, mem_range.mpr h_comp_lt, ?_⟩
    rw [h_comp_sq, ← h_sq_rem]

/-- Explicit 4-orbit basis `j ↦ j + j / 3` (`{0, 1, 2, 4}`) for Square-Shell `Mod 9`
    (since `3^2 % 9 = 0 = 0^2 % 9`), giving the 4 orbits `{0, 1, 4, 7}`. -/
def qrMod9Basis (j : ℕ) : ℕ :=
  j + j / 3

/-- The 4 Quadratic Residue Involution Orbits on Square-Shell `Mod 9`: `{0, 1, 4, 7}`. -/
def qrMod9Orbits : Finset ℕ :=
  (range 4).image (fun j : ℕ => (qrMod9Basis j * qrMod9Basis j) % 9)

/-- Cardinality bounds on `qrInvolutionOrbits m` and `qrMod9Orbits`. -/
theorem qrInvolutionOrbits_card_bounds (m : ℕ) :
    (qrInvolutionOrbits m).card ≤ (m + 1) / 2 ∧
    qrMod9Orbits.card ≤ 4 := by
  have h1 : (qrInvolutionOrbits m).card ≤ (range ((m + 1) / 2)).card := card_image_le
  rw [card_range] at h1
  have h2 : qrMod9Orbits.card ≤ (range 4).card := card_image_le
  rw [card_range] at h2
  exact ⟨h1, h2⟩

/-- Every integer square `(x * x) % 9` belongs to the 4-element set `qrMod9Orbits`,
    proven by reducing to `qrInvolutionOrbits 9` (`k < 5`) and collapsing `k = 3` to `j = 0`. -/
theorem sq_mod9_mem_qrMod9Orbits (x : ℕ) :
    (x * x) % 9 ∈ qrMod9Orbits := by
  have h9 := universal_odd_modulus_sq_mem_qrInvolutionOrbits (m := 9) (by omega : 9 % 2 = 1) x
  rw [qrInvolutionOrbits, mem_image] at h9
  obtain ⟨k, hk_range, hk_eq⟩ := h9
  rw [mem_range] at hk_range
  have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rw [qrMod9Orbits, mem_image]
  rcases hk_cases with rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, mem_range.mpr (by omega), hk_eq⟩
  · exact ⟨1, mem_range.mpr (by omega), hk_eq⟩
  · exact ⟨2, mem_range.mpr (by omega), hk_eq⟩
  · exact ⟨0, mem_range.mpr (by omega), hk_eq⟩
  · exact ⟨3, mem_range.mpr (by omega), hk_eq⟩

/-- Specialization of `universal_odd_modulus_sq_mem_qrInvolutionOrbits` and `sq_mod9_mem_qrMod9Orbits`
    to the RSC channels `{5, 7, 13, 9}`. -/
theorem sq_mod_mem_qrInvolutionOrbits (x : ℕ) :
    (x * x) % 5 ∈ qrInvolutionOrbits 5 ∧
    (x * x) % 7 ∈ qrInvolutionOrbits 7 ∧
    (x * x) % 13 ∈ qrInvolutionOrbits 13 ∧
    (x * x) % 9 ∈ qrMod9Orbits :=
  ⟨universal_odd_modulus_sq_mem_qrInvolutionOrbits (by omega : 5 % 2 = 1) x,
   universal_odd_modulus_sq_mem_qrInvolutionOrbits (by omega : 7 % 2 = 1) x,
   universal_odd_modulus_sq_mem_qrInvolutionOrbits (by omega : 13 % 2 = 1) x,
   sq_mod9_mem_qrMod9Orbits x⟩

/-- **Theorem 2.2 (`wr2Fiber_halfChordSq_mod65_and_mod63_orbit_bounds`):**
    On any fiber `S : Finset ℕ` (including `wr2ShearContractedFiber N r`), the half-chord
    midpoint square map `q ↦ (((q + r) / 2) ^ 2) % m` is restricted by the 5UP Reciprocal
    Shear Involution to:
    1. At most `3 * 7 = 21` quadratic residue orbits modulo `65`, and
    2. At most `4 * 4 = 16` quadratic residue orbits modulo `63`. -/
theorem wr2Fiber_halfChordSq_mod65_and_mod63_orbit_bounds (S : Finset ℕ) (r : ℕ) :
    (S.image (fun q : ℕ => (((q + r) / 2) ^ 2) % 65)).card ≤ 21 ∧
    (S.image (fun q : ℕ => (((q + r) / 2) ^ 2) % 63)).card ≤ 16 := by
  have h_sub65 :
      S.image (fun q : ℕ => (((q + r) / 2) ^ 2) % 65) ⊆
        (qrInvolutionOrbits 5 ×ˢ qrInvolutionOrbits 13).image crtReconstruct65From5And13 := by
    intro c hc
    rw [mem_image] at hc
    obtain ⟨q, _, rfl⟩ := hc
    set A_h := (q + r) / 2
    have h_sq_eq : A_h ^ 2 = A_h * A_h := nat_sq_eq_mul A_h
    have h_orbits := sq_mod_mem_qrInvolutionOrbits A_h
    have hc_lt : (A_h ^ 2) % 65 < 65 := Nat.mod_lt (A_h ^ 2) (by omega : 0 < 65)
    have h_crt := crtReconstruct65_mod5_mod13_id (A_h ^ 2) ((A_h ^ 2) % 65) hc_lt
    rw [mem_image]
    refine ⟨((A_h * A_h) % 5, (A_h * A_h) % 13), ?_, ?_⟩
    · rw [mem_product]
      exact ⟨h_orbits.1, h_orbits.2.2.1⟩
    · rw [← h_sq_eq, ← h_crt.2.1, ← h_crt.2.2]
      exact h_crt.1
  have h_sub63 :
      S.image (fun q : ℕ => (((q + r) / 2) ^ 2) % 63) ⊆
        (qrMod9Orbits ×ˢ qrInvolutionOrbits 7).image crtReconstruct63From9And7 := by
    intro c hc
    rw [mem_image] at hc
    obtain ⟨q, _, rfl⟩ := hc
    set A_h := (q + r) / 2
    have h_sq_eq : A_h ^ 2 = A_h * A_h := nat_sq_eq_mul A_h
    have h_orbits := sq_mod_mem_qrInvolutionOrbits A_h
    have hc_lt : (A_h ^ 2) % 63 < 63 := Nat.mod_lt (A_h ^ 2) (by omega : 0 < 63)
    have h_crt := crtReconstruct63_mod9_mod7_id (A_h ^ 2) ((A_h ^ 2) % 63) hc_lt
    rw [mem_image]
    refine ⟨((A_h * A_h) % 9, (A_h * A_h) % 7), ?_, ?_⟩
    · rw [mem_product]
      exact ⟨h_orbits.2.2.2, h_orbits.2.1⟩
    · rw [← h_sq_eq, ← h_crt.2.2.1, ← h_crt.2.2.2]
      exact h_crt.2.1
  have h_card65 :
      (S.image (fun q : ℕ => (((q + r) / 2) ^ 2) % 65)).card ≤
        (qrInvolutionOrbits 5).card * (qrInvolutionOrbits 13).card := by
    have h1 := Nat.le_trans (card_le_card h_sub65) card_image_le
    rw [card_product] at h1
    exact h1
  have h_card63 :
      (S.image (fun q : ℕ => (((q + r) / 2) ^ 2) % 63)).card ≤
        qrMod9Orbits.card * (qrInvolutionOrbits 7).card := by
    have h1 := Nat.le_trans (card_le_card h_sub63) card_image_le
    rw [card_product] at h1
    exact h1
  have hb5 := (qrInvolutionOrbits_card_bounds 5).1
  have hb7 := (qrInvolutionOrbits_card_bounds 7).1
  have hb13 := (qrInvolutionOrbits_card_bounds 13).1
  have hb9 := (qrInvolutionOrbits_card_bounds 9).2
  have h_mul21 := Nat.mul_le_mul hb5 hb13
  have h_mul16 := Nat.mul_le_mul hb9 hb7
  omega

/-!
## Section 3: 2-to-1 RSC Channel Involution Orbit Pairing (`12`, `9`, and `108` Paired Orbits)
-/

/-- Branch-free 2-to-1 involution orbit folding on Mod-65 (`2 * 6 = 12` paired orbits). -/
def rscPairedOrbitMod65 (q : ℕ) : ℕ × ℕ :=
  ((q % 5 - 1) / 2, (q % 13 - 1) / 2)

/-- Branch-free 2-to-1 involution orbit folding on Mod-63 (`3 * 3 = 9` paired orbits). -/
def rscPairedOrbitMod63 (q : ℕ) : ℕ × ℕ :=
  ((q % 9 - 1 - (q % 9) / 3) / 2, (q % 7 - 1) / 2)

/-- Full 5-channel RSC Paired Involution Orbit map on Mod-8190 (`12 * 9 = 108` paired orbits). -/
def rscPairedOrbitMod8190 (q : ℕ) : (ℕ × ℕ) × (ℕ × ℕ) :=
  (rscPairedOrbitMod65 q, rscPairedOrbitMod63 q)

/-- **Theorem 3.1 (`wr2Fiber_rsc_paired_orbit_card_bounds`):**
    For every `r ≥ 13`, on `wr2ShearContractedFiber N r`:
    1. The Mod-65 2-to-1 paired involution orbits have cardinality at most `2 * 6 = 12`,
    2. The Mod-63 2-to-1 paired involution orbits have cardinality at most `3 * 3 = 9`, and
    3. The full 5-channel Mod-8190 paired involution orbits have cardinality at most
       `12 * 9 = 108` out of `8190`. -/
theorem wr2Fiber_rsc_paired_orbit_card_bounds
    {N r : ℕ} (hr13 : 13 ≤ r) :
    ((wr2ShearContractedFiber N r).image rscPairedOrbitMod65).card ≤ 12 ∧
    ((wr2ShearContractedFiber N r).image rscPairedOrbitMod63).card ≤ 9 ∧
    ((wr2ShearContractedFiber N r).image rscPairedOrbitMod8190).card ≤ 108 := by
  have hr_pos : 0 < r := by omega
  have h_sub65 :
      (wr2ShearContractedFiber N r).image rscPairedOrbitMod65 ⊆
        range 2 ×ˢ range 6 := by
    intro pair hp
    rw [mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have h_omc := (wr2ShearContractedFiber_lower_pinch_and_bilateral_omc hr_pos hq).2.1
    have h5_pos : 1 ≤ q % 5 := h_omc 5 (by omega) (by omega)
    have h13_pos : 1 ≤ q % 13 := h_omc 13 (by omega) hr13
    have h5_lt : q % 5 < 5 := Nat.mod_lt q (by omega)
    have h13_lt : q % 13 < 13 := Nat.mod_lt q (by omega)
    rw [mem_product, mem_range, mem_range]
    unfold rscPairedOrbitMod65
    dsimp only
    omega
  have h_sub63 :
      (wr2ShearContractedFiber N r).image rscPairedOrbitMod63 ⊆
        range 3 ×ˢ range 3 := by
    intro pair hp
    rw [mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have h_omc := (wr2ShearContractedFiber_lower_pinch_and_bilateral_omc hr_pos hq).2.1
    have h3_pos : 1 ≤ q % 3 := h_omc 3 (by omega) (by omega)
    have h7_pos : 1 ≤ q % 7 := h_omc 7 (by omega) (by omega)
    have h9_lt : q % 9 < 9 := Nat.mod_lt q (by omega)
    have h7_lt : q % 7 < 7 := Nat.mod_lt q (by omega)
    rw [mem_product, mem_range, mem_range]
    unfold rscPairedOrbitMod63
    dsimp only
    omega
  have h_sub8190 :
      (wr2ShearContractedFiber N r).image rscPairedOrbitMod8190 ⊆
        (wr2ShearContractedFiber N r).image rscPairedOrbitMod65 ×ˢ
        (wr2ShearContractedFiber N r).image rscPairedOrbitMod63 := by
    intro quad hquad
    rw [mem_image] at hquad
    obtain ⟨q, hq, rfl⟩ := hquad
    rw [mem_product, mem_image, mem_image]
    exact ⟨⟨q, hq, rfl⟩, ⟨q, hq, rfl⟩⟩
  have h_c65 : ((wr2ShearContractedFiber N r).image rscPairedOrbitMod65).card ≤ 12 := by
    have h1 := card_le_card h_sub65
    rw [card_product, card_range, card_range] at h1
    exact h1
  have h_c63 : ((wr2ShearContractedFiber N r).image rscPairedOrbitMod63).card ≤ 9 := by
    have h1 := card_le_card h_sub63
    rw [card_product, card_range] at h1
    omega
  have h_c8190 : ((wr2ShearContractedFiber N r).image rscPairedOrbitMod8190).card ≤ 108 := by
    have h1 := card_le_card h_sub8190
    rw [card_product] at h1
    have h_mul := Nat.mul_le_mul h_c65 h_c63
    omega
  exact ⟨h_c65, h_c63, h_c8190⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.sub_sq_add_mul_two_eq_sq_add_sq
#print axioms WuPaper.ESZerosBridge.mul_add_mod_self_left_native
#print axioms WuPaper.ESZerosBridge.sq_mod_eq_rem_sq_mod_native
#print axioms WuPaper.ESZerosBridge.involution_complement_sq_mod_eq_native
#print axioms WuPaper.ESZerosBridge.universal_odd_modulus_sq_mem_qrInvolutionOrbits
#print axioms WuPaper.ESZerosBridge.wr2Fiber_halfChordSq_mod65_and_mod63_orbit_bounds
#print axioms WuPaper.ESZerosBridge.wr2Fiber_rsc_paired_orbit_card_bounds
