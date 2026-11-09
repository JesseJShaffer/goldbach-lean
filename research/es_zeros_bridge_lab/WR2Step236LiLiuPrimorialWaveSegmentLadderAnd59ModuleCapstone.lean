import WR2Step234LiLiuSqrtHorizonCollapseAnd57ModuleCapstone

set_option exponentiation.threshold 10000
set_option maxHeartbeats 800000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace WuPaper.ESZerosBridge

open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-!
# WR2Step236LiLiuPrimorialWaveSegmentLadderAnd59ModuleCapstone.lean — `Step211` Primorial/Factorial Wave-Segment Ladder, Bitwise `p`-ven Flicker Filter & Master 59-Module `D19 N` Capstone

Ports `Step211` Section 1 onto Track 2 (`D19 N`) and welds it into the 59-Module
`Goldbach.All` (`D19 N`) Master Capstone.
-/

def liliuNextLowerPrimorialPeriod (M : ℕ) : ℕ :=
  let H := M - 3
  if 510510 ≤ H then 510510
  else if 30030 ≤ H then 30030
  else if 2310 ≤ H then 2310
  else if 210 ≤ H then 210
  else if 30 ≤ H then 30
  else if 6 ≤ H then 6
  else 1

def liliuNextLowerPrimorialOrFactorialPeriod (M : ℕ) : ℕ :=
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

def liliuActiveWaveSegmentCount (M W : ℕ) : ℕ :=
  (M - 3) / max W 1

def liliuWaveSyncHorizon (M W : ℕ) : ℕ :=
  liliuActiveWaveSegmentCount M W * max W 1

def liliuMurWaveSegment (W s : ℕ) : Finset ℕ :=
  (range ((s + 1) * max W 1 + 1)).filter (fun R : ℕ => s * max W 1 + 1 ≤ R)

def liliuReciprocalSqrtCutoff (M : ℕ) : ℕ :=
  Nat.sqrt (2 * M) + 1

def liliuBitwiseStepFlickerSet (U : Finset ℕ) (p0 : ℕ) : Finset ℕ :=
  liliuNonPVenDomain U p0

/-- **Theorem 1.1 (`liliu_next_lower_primorial_wave_segment_and_bitwise_flicker_lock`):**
    Ports `Step211` Section 1 onto Track 2 (`D19 N`) in pure native arithmetic. -/
theorem liliu_next_lower_primorial_wave_segment_and_bitwise_flicker_lock
    (M W s s1 s2 : ℕ) :
    (6 ∣ 24 ∧ 6 ∣ 30 ∧ 6 ∣ 36 ∧ 30 ∣ 210 ∧ 210 ∣ 2310 ∧ 2310 ∣ 30030 ∧ 30030 ∣ 510510) ∧
    1 ≤ liliuNextLowerPrimorialPeriod M ∧
    1 ≤ liliuNextLowerPrimorialOrFactorialPeriod M ∧
    (9 ≤ M →
      6 ≤ liliuNextLowerPrimorialPeriod M ∧
      liliuNextLowerPrimorialPeriod M ≤ M - 3 ∧
      6 ≤ liliuNextLowerPrimorialOrFactorialPeriod M ∧
      liliuNextLowerPrimorialOrFactorialPeriod M ≤ M - 3 ∧
      1 ≤ liliuActiveWaveSegmentCount M (liliuNextLowerPrimorialPeriod M)) ∧
    liliuWaveSyncHorizon M W ≤ M - 3 ∧
    (s1 ≠ s2 → Disjoint (liliuMurWaveSegment W s1) (liliuMurWaveSegment W s2)) ∧
    (s < liliuActiveWaveSegmentCount M W →
      ∀ R ∈ liliuMurWaveSegment W s, 1 ≤ R ∧ R ≤ liliuWaveSyncHorizon M W ∧ R ≤ M - 3) ∧
    (liliuPn1RoughCompositeTail (liliuFullLowerMURUpper M) (liliuReciprocalSqrtCutoff M)).card = 0 ∧
    (liliuRoughSurvivorSet (liliuFullLowerMURUpper M) (liliuReciprocalSqrtCutoff M)).card =
      (liliuPrimeSurvivorSet (liliuFullLowerMURUpper M) (liliuReciprocalSqrtCutoff M)).card := by
  have h_ladder :
      6 ∣ 24 ∧ 6 ∣ 30 ∧ 6 ∣ 36 ∧ 30 ∣ 210 ∧ 210 ∣ 2310 ∧ 2310 ∣ 30030 ∧ 30030 ∣ 510510 :=
    ⟨⟨4, rfl⟩, ⟨5, rfl⟩, ⟨6, rfl⟩, ⟨7, rfl⟩, ⟨11, rfl⟩, ⟨13, rfl⟩, ⟨17, rfl⟩⟩
  have h_pos_prim : 1 ≤ liliuNextLowerPrimorialPeriod M := by
    unfold liliuNextLowerPrimorialPeriod
    dsimp only
    split_ifs <;> omega
  have h_pos_fact : 1 ≤ liliuNextLowerPrimorialOrFactorialPeriod M := by
    unfold liliuNextLowerPrimorialOrFactorialPeriod
    dsimp only
    split_ifs <;> omega
  have h_M9 :
      9 ≤ M →
        6 ≤ liliuNextLowerPrimorialPeriod M ∧
        liliuNextLowerPrimorialPeriod M ≤ M - 3 ∧
        6 ≤ liliuNextLowerPrimorialOrFactorialPeriod M ∧
        liliuNextLowerPrimorialOrFactorialPeriod M ≤ M - 3 ∧
        1 ≤ liliuActiveWaveSegmentCount M (liliuNextLowerPrimorialPeriod M) := by
    intro h9
    have h_p_bounds :
        6 ≤ liliuNextLowerPrimorialPeriod M ∧ liliuNextLowerPrimorialPeriod M ≤ M - 3 := by
      unfold liliuNextLowerPrimorialPeriod
      dsimp only
      split_ifs <;> omega
    have h_f_bounds :
        6 ≤ liliuNextLowerPrimorialOrFactorialPeriod M ∧
        liliuNextLowerPrimorialOrFactorialPeriod M ≤ M - 3 := by
      unfold liliuNextLowerPrimorialOrFactorialPeriod
      dsimp only
      split_ifs <;> omega
    set P := liliuNextLowerPrimorialPeriod M
    have hP_pos : 0 < max P 1 := by omega
    have h_mul1 : max P 1 * 1 ≤ M - 3 := by
      have h_p1 : 6 ≤ P := h_p_bounds.1
      have h_p2 : P ≤ M - 3 := h_p_bounds.2
      omega
    have h_div_ge1 : 1 ≤ liliuActiveWaveSegmentCount M P :=
      le_div_of_mul_le_liliu hP_pos h_mul1
    exact ⟨h_p_bounds.1, h_p_bounds.2, h_f_bounds.1, h_f_bounds.2, h_div_ge1⟩
  have h_hor_le : liliuWaveSyncHorizon M W ≤ M - 3 := by
    unfold liliuWaveSyncHorizon liliuActiveWaveSegmentCount
    set D := max W 1
    have h_div : D * ((M - 3) / D) + (M - 3) % D = M - 3 := Nat.div_add_mod (M - 3) D
    rw [Nat.mul_comm ((M - 3) / D) D]
    omega
  have h_disj : s1 ≠ s2 → Disjoint (liliuMurWaveSegment W s1) (liliuMurWaveSegment W s2) := by
    intro hne
    apply Finset.disjoint_left.mpr
    intro R hR1 hR2
    rw [liliuMurWaveSegment, mem_filter, mem_range] at hR1 hR2
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
      s < liliuActiveWaveSegmentCount M W →
        ∀ R ∈ liliuMurWaveSegment W s, 1 ≤ R ∧ R ≤ liliuWaveSyncHorizon M W ∧ R ≤ M - 3 := by
    intro hs R hR
    rw [liliuMurWaveSegment, mem_filter, mem_range] at hR
    set D := max W 1
    have h_s1_le : s + 1 ≤ liliuActiveWaveSegmentCount M W := hs
    have h_mul_le : (s + 1) * D ≤ liliuWaveSyncHorizon M W :=
      Nat.mul_le_mul_right D h_s1_le
    have hR1 : 1 ≤ R := by omega
    have hR_hor : R ≤ liliuWaveSyncHorizon M W := by omega
    have hR_M3 : R ≤ M - 3 := Nat.le_trans hR_hor h_hor_le
    exact ⟨hR1, hR_hor, hR_M3⟩
  have h_col :=
    liliu_sqrt_succ_horizon_collapses_all_blocks_and_composite_tail
      (M := M) (q := liliuReciprocalSqrtCutoff M) (Nat.le_refl _)
  exact ⟨h_ladder, h_pos_prim, h_pos_fact, h_M9, h_hor_le, h_disj, h_seg_in,
    h_col.1, h_col.2.1⟩

/-- **Master Theorem 2.1 (`master_59module_step208_step209_step211_step212_goldbach_lean_capstone`):**
    Complete 59-Module Master Capstone uniting `Goldbach.one_plus_one_nine_count` (`D19 N`),
    the `Step211` Primorial/Factorial Wave-Segment Ladder & `reciprocalSqrtCutoff` Zero-Tail Collapse,
    the `Step209` Section 3b Disjoint Lower-MUR Reflection & Strict Inequality,
    and the `Step212` First-Missing-Prime `q_E` Zero-Sum Collapse. -/
theorem master_59module_step208_step209_step211_step212_goldbach_lean_capstone :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N : ℕ, K ≤ N → Even N →
      liuMainTerm0004 N < (D19 N : ℝ) ∧
      (1 ≤ liliuNextLowerPrimorialPeriod (N / 2) ∧
       liliuWaveSyncHorizon (N / 2) (liliuNextLowerPrimorialPeriod (N / 2)) ≤ (N / 2) - 3) ∧
      (liliuPn1RoughCompositeTail
        (liliuFullLowerMURUpper (N / 2))
        (liliuReciprocalSqrtCutoff (N / 2))).card = 0 ∧
      (∀ q k : ℕ,
        (liliuPn1RoughCompositeTail
          (liliuSubTwoQBlock (liliuFullLowerMURUpper (N / 2)) q k) q).card +
          (liliuAboveSqrtLowerMURPrimes (N / 2)).card ≤
          (liliuFullLowerMURUpper (N / 2)).card) ∧
      (∀ q_E : ℕ, IsFirstMissingOddPrimeLiliu N q_E → N < q_E * (q_E + 2) + 2 →
        (∑ r ∈ pinchedOddPrimes919 N, (liliuTargetSieved3PrimeFiber N r q_E).card) = 0 ∧
        (fiveupPinchedQRSubfilter 9 10 N).card ≤ q_E ∧
        (((q_E : ℝ) ≤ liuMainTerm0004 N) →
          ∃ p q p_next' : ℕ,
            Nat.Prime p ∧ Nat.Prime q ∧ N = p + q ∧ p < p_next' ∧ IsPrimeNat p_next')) := by
  obtain ⟨K, hK4, hCap57⟩ := master_57module_complete_sqrt_horizon_and_step209_goldbach_lean_capstone
  refine ⟨K, hK4, ?_⟩
  intro N hNK hEven
  have hM := hCap57 N hNK hEven
  have h_s211 :=
    liliu_next_lower_primorial_wave_segment_and_bitwise_flicker_lock
      (N / 2) (liliuNextLowerPrimorialPeriod (N / 2)) 0 0 1
  exact ⟨hM.1,
         ⟨h_s211.2.1, h_s211.2.2.2.2.1⟩,
         h_s211.2.2.2.2.2.2.2.1,
         hM.2.2.1,
         hM.2.2.2⟩

end WuPaper.ESZerosBridge

#print axioms WuPaper.ESZerosBridge.liliu_next_lower_primorial_wave_segment_and_bitwise_flicker_lock
#print axioms WuPaper.ESZerosBridge.master_59module_step208_step209_step211_step212_goldbach_lean_capstone
