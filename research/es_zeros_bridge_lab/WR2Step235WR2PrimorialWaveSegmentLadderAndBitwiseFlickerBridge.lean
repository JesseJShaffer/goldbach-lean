import WR2Step233WR2SqrtHorizonCollapseAndStrictLowerMURemb

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open WuPaper.ClassicalSlots

/-!
# WR2Step235WR2PrimorialWaveSegmentLadderAndBitwiseFlickerBridge.lean — `Step211` Primorial/Factorial Wave-Segment Ladder, Bitwise `p`-ven Flicker Filter & `reciprocalSqrtCutoff` Closure (`WR2` Track 1)

Ports Section 1 of `Step211_PrimorialWaveSegmentSteppingAndCosetFlickerBridge_v1.lean`
into the `goldbach-lean` Track 1 (`WR2`) bridge:

1. **Next-Lower Primorial & Factorial Wave-Segment Ladder (`nextLowerPrimorialPeriod`,
   `nextLowerPrimorialOrFactorialPeriod`, `activeWaveSegmentCount`, `waveSyncHorizon`):**
   Selects the largest wave period `W ∈ {6, 24, 30, 36, 210, 2310, 30030, 510510}` fitting
   inside the lower MUR radius horizon `M - 3` without foreknowledge above `2 * M`.
2. **Pairwise Disjoint MUR Wave Segments (`murWaveSegment W s`):**
   Proves that distinct wave segments `s1 ≠ s2` are disjoint and every active segment
   `s < activeWaveSegmentCount M W` lies inside `[1, waveSyncHorizon M W] ⊆ [1, M - 3]`.
3. **Bitwise `p`-ven Flicker Stepping & `reciprocalSqrtCutoff M` Closure:**
   Connects `bitwiseStepFlickerSet U p0 = nonPVenDomain U p0` (`1 ≤ u % p0`) to
   `reciprocalSqrtCutoff M := Nat.sqrt (2 * M) + 1`, proving that at `reciprocalSqrtCutoff M`
   the composite tail on `fullLowerMURUpper M` vanishes identically (`card = 0`).
-/

/-- Selects the largest primorial wave period `W ∈ {6, 30, 210, 2310, 30030, 510510}`
    that fits inside the lower MUR radius horizon `M - 3` (`Step211`). -/
def nextLowerPrimorialPeriod (M : ℕ) : ℕ :=
  let H := M - 3
  if 510510 ≤ H then 510510
  else if 30030 ≤ H then 30030
  else if 2310 ≤ H then 2310
  else if 210 ≤ H then 210
  else if 30 ≤ H then 30
  else if 6 ≤ H then 6
  else 1

/-- Extended lower-anchor period ladder incorporating `6 → 24 (4!) → 30 (5#) → 36 (6^2)`
    before `210 (7#)`, `2310 (11#)`, `30030 (13#)`, and `510510 (17#)` (`Step211`). -/
def nextLowerPrimorialOrFactorialPeriod (M : ℕ) : ℕ :=
  let H := M - 3
  if 510510 ≤ H then 510510
  else if 30030 ≤ H then 30030
  else if 2310 ≤ H then 2310
  else if 210 ≤ H then 210
  else if 36 ≤ H then 36
  else if 30 ≤ H then 30
  else if 24 ≤ H then 24
  else if 6 ≤ H then 6
  else 1

/-- Number of complete wave segments of period `max W 1` inside `M - 3` (`Step211`). -/
def activeWaveSegmentCount (M W : ℕ) : ℕ :=
  (M - 3) / max W 1

/-- Synchronized wave horizon `activeWaveSegmentCount M W * max W 1` (`Step211`). -/
def waveSyncHorizon (M W : ℕ) : ℕ :=
  activeWaveSegmentCount M W * max W 1

/-- The `s`-th MUR wave segment `[s * max W 1 + 1, (s + 1) * max W 1]` (`Step211`). -/
def murWaveSegment (W s : ℕ) : Finset ℕ :=
  (range ((s + 1) * max W 1 + 1)).filter (fun R : ℕ => s * max W 1 + 1 ≤ R)

/-- The Reciprocal Square-Root Cutoff `⌊√(2M)⌋ + 1` (`Step211`). -/
def reciprocalSqrtCutoff (M : ℕ) : ℕ :=
  Nat.sqrt (2 * M) + 1

/-- Single-prime bitwise `p`-ven stepping filter removing multiples of `p0` from `U` (`Step211`). -/
def bitwiseStepFlickerSet (U : Finset ℕ) (p0 : ℕ) : Finset ℕ :=
  nonPVenDomain U p0

/-- **Theorem 1.1 (`next_lower_primorial_wave_segment_and_bitwise_flicker_lock`):**
    Ports `Step211` Section 1 into the Track 1 (`WR2`) bridge in pure native arithmetic:
    1. Exact divisibility chain `6 ∣ 24 ∧ 6 ∣ 30 ∧ 6 ∣ 36 ∧ 30 ∣ 210 ∧ 210 ∣ 2310 ∧ 2310 ∣ 30030 ∧ 30030 ∣ 510510`,
    2. `1 ≤ nextLowerPrimorialPeriod M ∧ 1 ≤ nextLowerPrimorialOrFactorialPeriod M`,
    3. For `9 ≤ M`: `6 ≤ nextLowerPrimorialPeriod M ∧ nextLowerPrimorialPeriod M ≤ M - 3 ∧ 1 ≤ activeWaveSegmentCount M (nextLowerPrimorialPeriod M)`,
    4. `waveSyncHorizon M W ≤ M - 3`,
    5. Distinct wave segments `s1 ≠ s2` are disjoint (`Disjoint (murWaveSegment W s1) (murWaveSegment W s2)`),
    6. Every active segment `s < activeWaveSegmentCount M W` satisfies `∀ R ∈ murWaveSegment W s, 1 ≤ R ∧ R ≤ waveSyncHorizon M W ∧ R ≤ M - 3`, and
    7. At `reciprocalSqrtCutoff M`, `(pn1RoughCompositeTail (fullLowerMURUpper M) (reciprocalSqrtCutoff M)).card = 0`
       and `(roughSurvivorSet (fullLowerMURUpper M) (reciprocalSqrtCutoff M)).card = (primeSurvivorSet (fullLowerMURUpper M) (reciprocalSqrtCutoff M)).card`. -/
theorem next_lower_primorial_wave_segment_and_bitwise_flicker_lock
    (M W s s1 s2 : ℕ) :
    (6 ∣ 24 ∧ 6 ∣ 30 ∧ 6 ∣ 36 ∧ 30 ∣ 210 ∧ 210 ∣ 2310 ∧ 2310 ∣ 30030 ∧ 30030 ∣ 510510) ∧
    1 ≤ nextLowerPrimorialPeriod M ∧
    1 ≤ nextLowerPrimorialOrFactorialPeriod M ∧
    (9 ≤ M →
      6 ≤ nextLowerPrimorialPeriod M ∧
      nextLowerPrimorialPeriod M ≤ M - 3 ∧
      6 ≤ nextLowerPrimorialOrFactorialPeriod M ∧
      nextLowerPrimorialOrFactorialPeriod M ≤ M - 3 ∧
      1 ≤ activeWaveSegmentCount M (nextLowerPrimorialPeriod M)) ∧
    waveSyncHorizon M W ≤ M - 3 ∧
    (s1 ≠ s2 → Disjoint (murWaveSegment W s1) (murWaveSegment W s2)) ∧
    (s < activeWaveSegmentCount M W →
      ∀ R ∈ murWaveSegment W s, 1 ≤ R ∧ R ≤ waveSyncHorizon M W ∧ R ≤ M - 3) ∧
    (pn1RoughCompositeTail (fullLowerMURUpper M) (reciprocalSqrtCutoff M)).card = 0 ∧
    (roughSurvivorSet (fullLowerMURUpper M) (reciprocalSqrtCutoff M)).card =
      (primeSurvivorSet (fullLowerMURUpper M) (reciprocalSqrtCutoff M)).card := by
  have h_ladder :
      6 ∣ 24 ∧ 6 ∣ 30 ∧ 6 ∣ 36 ∧ 30 ∣ 210 ∧ 210 ∣ 2310 ∧ 2310 ∣ 30030 ∧ 30030 ∣ 510510 :=
    ⟨⟨4, rfl⟩, ⟨5, rfl⟩, ⟨6, rfl⟩, ⟨7, rfl⟩, ⟨11, rfl⟩, ⟨13, rfl⟩, ⟨17, rfl⟩⟩
  have h_pos_prim : 1 ≤ nextLowerPrimorialPeriod M := by
    unfold nextLowerPrimorialPeriod
    dsimp only
    split_ifs <;> omega
  have h_pos_fact : 1 ≤ nextLowerPrimorialOrFactorialPeriod M := by
    unfold nextLowerPrimorialOrFactorialPeriod
    dsimp only
    split_ifs <;> omega
  have h_M9 :
      9 ≤ M →
        6 ≤ nextLowerPrimorialPeriod M ∧
        nextLowerPrimorialPeriod M ≤ M - 3 ∧
        6 ≤ nextLowerPrimorialOrFactorialPeriod M ∧
        nextLowerPrimorialOrFactorialPeriod M ≤ M - 3 ∧
        1 ≤ activeWaveSegmentCount M (nextLowerPrimorialPeriod M) := by
    intro h9
    have h_p_bounds :
        6 ≤ nextLowerPrimorialPeriod M ∧ nextLowerPrimorialPeriod M ≤ M - 3 := by
      unfold nextLowerPrimorialPeriod
      dsimp only
      split_ifs <;> omega
    have h_f_bounds :
        6 ≤ nextLowerPrimorialOrFactorialPeriod M ∧
        nextLowerPrimorialOrFactorialPeriod M ≤ M - 3 := by
      unfold nextLowerPrimorialOrFactorialPeriod
      dsimp only
      split_ifs <;> omega
    set P := nextLowerPrimorialPeriod M
    have hP_pos : 0 < max P 1 := by omega
    have h_mul1 : max P 1 * 1 ≤ M - 3 := by
      have h_p1 : 6 ≤ P := h_p_bounds.1
      have h_p2 : P ≤ M - 3 := h_p_bounds.2
      omega
    have h_div_ge1 : 1 ≤ activeWaveSegmentCount M P :=
      le_div_of_mul_le_native hP_pos h_mul1
    exact ⟨h_p_bounds.1, h_p_bounds.2, h_f_bounds.1, h_f_bounds.2, h_div_ge1⟩
  have h_hor_le : waveSyncHorizon M W ≤ M - 3 := by
    unfold waveSyncHorizon activeWaveSegmentCount
    set D := max W 1
    have h_div : D * ((M - 3) / D) + (M - 3) % D = M - 3 := Nat.div_add_mod (M - 3) D
    rw [Nat.mul_comm ((M - 3) / D) D]
    omega
  have h_disj : s1 ≠ s2 → Disjoint (murWaveSegment W s1) (murWaveSegment W s2) := by
    intro hne
    apply Finset.disjoint_left.mpr
    intro R hR1 hR2
    rw [murWaveSegment, mem_filter, mem_range] at hR1 hR2
    set D := max W 1
    match Nat.lt_or_ge s1 s2 with
    | Or.inl hlt =>
      have h_le : s1 + 1 ≤ s2 := hlt
      have h_mul : (s1 + 1) * D ≤ s2 * D := Nat.mul_le_mul_right D h_le
      omega
    | Or.inr _ =>
      have h_gt : s2 + 1 ≤ s1 := by omega
      have h_mul : (s2 + 1) * D ≤ s1 * D := Nat.mul_le_mul_right D h_gt
      omega
  have h_seg_in :
      s < activeWaveSegmentCount M W →
        ∀ R ∈ murWaveSegment W s, 1 ≤ R ∧ R ≤ waveSyncHorizon M W ∧ R ≤ M - 3 := by
    intro hs R hR
    rw [murWaveSegment, mem_filter, mem_range] at hR
    set D := max W 1
    have h_s1_le : s + 1 ≤ activeWaveSegmentCount M W := hs
    have h_mul_le : (s + 1) * D ≤ waveSyncHorizon M W :=
      Nat.mul_le_mul_right D h_s1_le
    have hR1 : 1 ≤ R := by omega
    have hR_hor : R ≤ waveSyncHorizon M W := by omega
    have hR_M3 : R ≤ M - 3 := Nat.le_trans hR_hor h_hor_le
    exact ⟨hR1, hR_hor, hR_M3⟩
  have h_col :=
    sqrt_succ_horizon_collapses_all_blocks_and_composite_tail
      (M := M) (q := reciprocalSqrtCutoff M) (Nat.le_refl _)
  exact ⟨h_ladder, h_pos_prim, h_pos_fact, h_M9, h_hor_le, h_disj, h_seg_in,
    h_col.1, h_col.2.1⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.next_lower_primorial_wave_segment_and_bitwise_flicker_lock
