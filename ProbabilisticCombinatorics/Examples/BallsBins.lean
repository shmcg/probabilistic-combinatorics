/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

public import ProbabilisticCombinatorics.Method.FirstMoment.Basic
public import ProbabilisticCombinatorics.Method.FirstMoment.Asymptotics
public import Mathlib.Probability.UniformOn
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Coupon collection by the first-moment method

Throw `m` balls independently and uniformly into `n` bins. Count empty bins,
compute its expectation, and apply Markov. The quantitative conclusion is
`Pr(some bin is empty) ≤ n * exp (-m/n)`, hence at most `n ^ (-ε)` once
`m ≥ (1+ε) n log n`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Classical ProbabilityTheory ENNReal Topology

namespace ProbabilisticCombinatorics.Examples.BallsBins

open FirstMoment

/-- The actual product law of independent uniform choices of bins. -/
def allocationMeasure (n m : ℕ) : Measure (Fin m → Fin n) :=
  Measure.pi fun _ : Fin m ↦ uniformOn (Set.univ : Set (Fin n))

instance (n m : ℕ) : IsFiniteMeasure (allocationMeasure n m) := by
  unfold allocationMeasure
  infer_instance

instance (n m : ℕ) [NeZero n] : IsProbabilityMeasure (allocationMeasure n m) := by
  unfold allocationMeasure
  infer_instance

/-- The bad event attached to one bin: no ball chooses it. -/
def emptyBin {n m : ℕ} (b : Fin n) : Set (Fin m → Fin n) :=
  {ω | ∀ i, ω i ≠ b}

/-- The ordinary natural-valued count of empty bins. -/
def emptyCount (n m : ℕ) (ω : Fin m → Fin n) : ℕ :=
  ∑ b : Fin n, (emptyBin b).indicator (1 : (Fin m → Fin n) → ℕ) ω

theorem emptyCount_eq_zero (n m : ℕ) (ω : Fin m → Fin n) :
    emptyCount n m ω = 0 ↔ Function.Surjective ω := by
  rw [emptyCount, sum_indicators_eq_zero]
  simp [emptyBin, Function.Surjective]

/-- A fixed bin is missed by each ball with probability `1 - 1/n`. -/
theorem emptyBin_probability (n m : ℕ) (hn : 0 < n) (b : Fin n) :
    (allocationMeasure n m).real (emptyBin b) = (1 - 1 / (n : ℝ)) ^ m := by
  let : NeZero n := ⟨hn.ne'⟩
  let ν := uniformOn (Set.univ : Set (Fin n))
  have hsingleton : ν.real {b} = 1 / (n : ℝ) := by
    simp [ν, measureReal_def, uniformOn_univ]
  have hmiss : ν.real ({b}ᶜ : Set (Fin n)) = 1 - 1 / (n : ℝ) := by
    rw [measureReal_compl (measurableSet_singleton b), hsingleton, probReal_univ]
  have hrect : emptyBin (m := m) b = Set.univ.pi (fun _ : Fin m ↦ ({b}ᶜ : Set (Fin n))) := by
    ext ω
    simp [emptyBin]
  rw [measureReal_def, hrect, allocationMeasure, Measure.pi_pi]
  simpa [measureReal_def] using congrArg (fun x : ℝ ↦ x ^ m) hmiss

/-- Linearity of expectation: add the `n` identical empty-bin probabilities. -/
theorem expected_emptyCount (n m : ℕ) (hn : 0 < n) :
    (allocationMeasure n m)[emptyCount n m] = (n : ℝ) * (1 - 1 / (n : ℝ)) ^ m := by
  calc
    _ = ∑ b : Fin n, (allocationMeasure n m).real (emptyBin b) :=
      expectation_sum_indicators _ Finset.univ emptyBin
        (fun _ _ ↦ (Set.toFinite _).measurableSet)
    _ = _ := by simp [emptyBin_probability n m hn, nsmul_eq_mul]

/-- First moment: the failure probability is at most the expected empty-bin count. -/
theorem failure_probability_le_exact (n m : ℕ) (hn : 0 < n) :
    (allocationMeasure n m).real {ω | ¬ Function.Surjective ω} ≤
      (n : ℝ) * (1 - 1 / (n : ℝ)) ^ m := by
  have h := measure_ne_zero_le_expectation (allocationMeasure n m) (emptyCount n m)
    Integrable.of_finite
  rw [expected_emptyCount n m hn] at h
  simpa only [ne_eq, emptyCount_eq_zero] using h

/-- The elementary estimate `(1-1/n)^m ≤ exp(-m/n)`. -/
theorem missed_bin_bound (n m : ℕ) (hn : 0 < n) :
    (1 - 1 / (n : ℝ)) ^ m ≤ Real.exp (-(m : ℝ) / n) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hbase : 0 ≤ 1 - 1 / (n : ℝ) :=
    sub_nonneg.mpr ((div_le_one₀ hnpos).mpr hn1)
  calc
    _ ≤ (Real.exp (-(1 / (n : ℝ)))) ^ m :=
      pow_le_pow_left₀ hbase (Real.one_sub_le_exp_neg _) m
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- The useful exponential upper bound on the expected empty-bin count. -/
theorem expected_emptyCount_le_exp (n m : ℕ) (hn : 0 < n) :
    (allocationMeasure n m)[emptyCount n m] ≤ (n : ℝ) * Real.exp (-(m : ℝ) / n) := by
  rw [expected_emptyCount n m hn]
  exact mul_le_mul_of_nonneg_left (missed_bin_bound n m hn) (Nat.cast_nonneg n)

/-- A quantitative coupon-collector bound, valid for every positive `n` and every `m`. -/
theorem failure_probability_le_exp (n m : ℕ) (hn : 0 < n) :
    (allocationMeasure n m).real {ω | ¬ Function.Surjective ω} ≤
      (n : ℝ) * Real.exp (-(m : ℝ) / n) := by
  exact (failure_probability_le_exact n m hn).trans
    (mul_le_mul_of_nonneg_left (missed_bin_bound n m hn) (Nat.cast_nonneg n))

/-- Substitute the coupon-collector cutoff into the exponential estimate. -/
theorem coupon_cutoff_bound (n m : ℕ) (hn : 0 < n) (ε : ℝ)
    (hm : (1 + ε) * (n : ℝ) * Real.log n ≤ m) :
    (n : ℝ) * Real.exp (-(m : ℝ) / n) ≤ (n : ℝ) ^ (-ε) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hdiv : (1 + ε) * Real.log n ≤ (m : ℝ) / n := by
    apply (le_div_iff₀ hnpos).mpr
    nlinarith only [hm]
  calc
    _ ≤ (n : ℝ) * Real.exp (-((1 + ε) * Real.log n)) :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hdiv))
        (Nat.cast_nonneg n)
    _ = _ := by
      rw [Real.rpow_def_of_pos hnpos]
      nth_rw 1 [← Real.exp_log hnpos]
      rw [← Real.exp_add]
      congr 1
      ring

/-- Once `m ≥ (1+ε)n log n`, the expected number of empty bins is at most `n^(-ε)`. -/
theorem expected_emptyCount_le_rpow (n m : ℕ) (hn : 0 < n) (ε : ℝ)
    (hm : (1 + ε) * (n : ℝ) * Real.log n ≤ m) :
    (allocationMeasure n m)[emptyCount n m] ≤ (n : ℝ) ^ (-ε) :=
  (expected_emptyCount_le_exp n m hn).trans (coupon_cutoff_bound n m hn ε hm)

/-- Above the coupon-collector cutoff, the failure probability is at most `n^(-ε)`. -/
theorem failure_probability_le_rpow (n m : ℕ) (hn : 0 < n) (ε : ℝ)
    (hm : (1 + ε) * (n : ℝ) * Real.log n ≤ m) :
    (allocationMeasure n m).real {ω | ¬ Function.Surjective ω} ≤ (n : ℝ) ^ (-ε) :=
  (failure_probability_le_exp n m hn).trans (coupon_cutoff_bound n m hn ε hm)

/-- Equivalently, every bin is occupied with probability at least `1 - n^(-ε)`. -/
theorem success_probability_ge (n m : ℕ) (hn : 0 < n) (ε : ℝ)
    (hm : (1 + ε) * (n : ℝ) * Real.log n ≤ m) :
    1 - (n : ℝ) ^ (-ε) ≤
      (allocationMeasure n m).real {ω | Function.Surjective ω} := by
  let : NeZero n := ⟨hn.ne'⟩
  simpa only [emptyCount_eq_zero] using
    one_sub_le_measure_zero_of_expectation_le (allocationMeasure n m) (emptyCount n m)
      Integrable.of_finite (expected_emptyCount_le_rpow n m hn ε hm)

/-- For any fixed positive `ε`, the coupon-collector cutoff gives high probability.
The number of balls may vary arbitrarily, provided it is eventually above the cutoff. -/
theorem coupon_collection_whp (ε : ℝ) (hε : 0 < ε) (m : ℕ → ℕ)
    (hm : ∀ᶠ n : ℕ in atTop, (1 + ε) * (n : ℝ) * Real.log n ≤ m n) :
    Tendsto (fun n ↦ (allocationMeasure n (m n)).real {ω | Function.Surjective ω})
      atTop (𝓝 1) := by
  have hprob : ∀ᶠ n in atTop, IsProbabilityMeasure (allocationMeasure n (m n)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    let : NeZero n := ⟨hn.ne'⟩
    infer_instance
  have hEX : ∀ᶠ n in atTop,
      ((allocationMeasure n (m n))[emptyCount n (m n)] : ℝ) ≤ (n : ℝ) ^ (-ε) := by
    filter_upwards [hm, eventually_gt_atTop 0] with n hmn hn
    exact expected_emptyCount_le_rpow n (m n) hn ε hmn
  have hδ : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-ε)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hε).comp tendsto_natCast_atTop_atTop
  simpa only [emptyCount_eq_zero] using
    tendsto_measure_zero_of_expectation_le
      (fun n ↦ allocationMeasure n (m n)) (fun n ↦ emptyCount n (m n))
      (fun n ↦ (n : ℝ) ^ (-ε)) hprob
      (Eventually.of_forall fun _ ↦ Integrable.of_finite) hEX hδ

/-- In particular, round `(1+ε)n log n` up to an integer number of balls. -/
theorem coupon_collection_ceil_whp (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦
      (allocationMeasure n ⌈(1 + ε) * (n : ℝ) * Real.log n⌉₊).real
        {ω | Function.Surjective ω}) atTop (𝓝 1) :=
  coupon_collection_whp ε hε (fun n ↦ ⌈(1 + ε) * (n : ℝ) * Real.log n⌉₊)
    (Eventually.of_forall fun _ ↦ Nat.le_ceil _)

end ProbabilisticCombinatorics.Examples.BallsBins
