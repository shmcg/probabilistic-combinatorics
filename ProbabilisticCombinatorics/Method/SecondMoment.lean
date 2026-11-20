/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # The zero-count bound and pairwise contributions to variance -/

public section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory BigOperators Classical

namespace ProbabilisticCombinatorics.SecondMoment

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- If the mean is positive, a zero is at least one mean away from the mean. -/
theorem measure_zero_le_variance_div_sq [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) (hm : 0 < μ[X]) :
    μ.real {ω | X ω = 0} ≤ Var[X; μ] / μ[X] ^ 2 := by
  apply ENNReal.toReal_le_of_le_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))
  refine (measure_mono ?_).trans (meas_ge_le_variance_div_sq hX hm)
  intro ω (hω : X ω = 0)
  simp [hω, abs_of_pos hm]

variable [IsProbabilityMeasure μ]

/-- The ordered-pair expansion. This also handles positively correlated overlapping witnesses. -/
theorem variance_sum_indicators (s : Finset ι) (E : ι → Set Ω)
    (hE : ∀ i ∈ s, MeasurableSet (E i)) :
    Var[fun ω ↦ ∑ i ∈ s, (E i).indicator (1 : Ω → ℝ) ω; μ] =
      ∑ i ∈ s, ∑ j ∈ s, (μ.real (E i ∩ E j) - μ.real (E i) * μ.real (E j)) := by
  have hL i (hi : i ∈ s) : MemLp ((E i).indicator (1 : Ω → ℝ)) 2 μ :=
    (memLp_const (1 : ℝ)).indicator (hE i hi).nullMeasurableSet
  rw [variance_fun_sum' hL]
  refine Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ ?_
  rw [covariance_eq_sub (hL i hi) (hL j hj)]
  have prod : (E i).indicator (1 : Ω → ℝ) * (E j).indicator 1 = (E i ∩ E j).indicator 1 := by
    ext ω
    by_cases h : ω ∈ E i <;> by_cases k : ω ∈ E j <;> simp [h, k]
  rw [prod, integral_indicator_one ((hE i hi).inter (hE j hj)),
    integral_indicator_one (hE i hi), integral_indicator_one (hE j hj)]

/-- Nonpositive off-diagonal covariances force the variance below the expected count. -/
theorem variance_le_sum_of_pairwise (s : Finset ι) (E : ι → Set Ω)
    (hE : ∀ i ∈ s, MeasurableSet (E i))
    (hp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → μ.real (E i ∩ E j) ≤ μ.real (E i) * μ.real (E j)) :
    Var[fun ω ↦ ∑ i ∈ s, (E i).indicator (1 : Ω → ℝ) ω; μ] ≤ ∑ i ∈ s, μ.real (E i) := by
  rw [variance_sum_indicators s E hE]
  apply Finset.sum_le_sum
  intro i hi
  calc
    _ ≤ ∑ j ∈ s, if i = j then μ.real (E i) else 0 := by
      apply Finset.sum_le_sum
      intro j hj
      split_ifs with h
      · subst j
        simp [mul_self_nonneg]
      · exact sub_nonpos.mpr (hp i hi j hj h)
    _ = _ := by simp [hi]

end ProbabilisticCombinatorics.SecondMoment
