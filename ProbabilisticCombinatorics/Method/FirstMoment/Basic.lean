/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Probability.Notation
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The first-moment method

1. Choose a count `X : Ω → ℕ`.
2. Compute or bound its real expectation `μ[X]`.
3. Apply Markov: `μ.real {ω | X ω ≠ 0} ≤ μ[X]`.

Consequently, `1 - μ[X] ≤ μ.real {ω | X ω = 0}`, and `μ[X] < 1`
guarantees an outcome with count zero.

`μ[X]` is Mathlib's expectation notation, here for the real integral of the
natural count cast to `ℝ`. `μ.real E` is the probability of `E` as a real number.
The integrability hypothesis is discharged by `Integrable.of_finite` on finite
spaces with measurable singletons; a probability measure is automatically finite.

The indicator-sum helpers at the end are optional: they use Mathlib's existing
linearity of expectation and expectation-of-an-indicator theorems. The main
method applies to any natural-valued count, however its expectation was bounded.
-/

open MeasureTheory
open scoped BigOperators Classical ProbabilityTheory

namespace ProbabilisticCombinatorics.FirstMoment

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A positive natural count is at least one, so Markov bounds its nonzero probability. -/
theorem measure_ne_zero_le_expectation (μ : Measure Ω) (X : Ω → ℕ)
    (hX : Integrable (fun ω ↦ (X ω : ℝ)) μ) :
    μ.real {ω | X ω ≠ 0} ≤ μ[X] := by
  simpa only [one_mul, Nat.one_le_cast, Nat.one_le_iff_ne_zero] using
    mul_meas_ge_le_integral_of_nonneg
      (ae_of_all μ fun ω ↦ Nat.cast_nonneg (X ω)) hX (1 : ℝ)

/-- The quantitative first-moment conclusion: the probability of zero violations
is at least one minus the expected number of violations. -/
theorem one_sub_expectation_le_measure_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℕ) (hX : Integrable (fun ω ↦ (X ω : ℝ)) μ) :
    1 - μ[X] ≤ μ.real {ω | X ω = 0} := by
  have hcover : {ω | X ω ≠ 0} ∪ {ω | X ω = 0} = Set.univ := by
    ext ω
    by_cases h : X ω = 0 <;> simp [h]
  have htotal := measureReal_union_le (μ := μ) {ω | X ω ≠ 0} {ω | X ω = 0}
  rw [hcover, probReal_univ] at htotal
  linarith [measure_ne_zero_le_expectation μ X hX]

/-- If the expected natural count is below one, some outcome has count zero. -/
theorem exists_zero_of_expectation_lt_one (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℕ) (hX : Integrable (fun ω ↦ (X ω : ℝ)) μ)
    (hEX : (μ[X] : ℝ) < 1) : ∃ ω, X ω = 0 := by
  have hpos : 0 < μ.real {ω | X ω = 0} :=
    (sub_pos.mpr hEX).trans_le (one_sub_expectation_le_measure_zero μ X hX)
  exact nonempty_of_measureReal_ne_zero hpos.ne'

/-- Markov's inequality for a natural-valued count and a positive natural threshold. -/
theorem measure_ge_le_expectation_div (μ : Measure Ω) (X : Ω → ℕ)
    (hX : Integrable (fun ω ↦ (X ω : ℝ)) μ) {k : ℕ} (hk : 0 < k) :
    μ.real {ω | k ≤ X ω} ≤ μ[X] / (k : ℝ) := by
  apply (le_div_iff₀ (show (0 : ℝ) < k from Nat.cast_pos.mpr hk)).mpr
  simpa only [Nat.cast_le, mul_comm] using
    mul_meas_ge_le_integral_of_nonneg
      (ae_of_all μ fun ω ↦ Nat.cast_nonneg (X ω)) hX (k : ℝ)


/-! ## A small tactic frontend -/

/-- Apply the count form of the first-moment method. Integrability is discharged
from a hypothesis or finiteness when possible; otherwise it remains a visible goal. -/
macro "first_moment" " using " μ:term ", " X:term : tactic =>
  `(tactic|
    (refine ProbabilisticCombinatorics.FirstMoment.exists_zero_of_expectation_lt_one
       $μ $X ?_ ?_
     try
       first
       | assumption
       | exact MeasureTheory.Integrable.of_finite))


/-- In a finite discrete probability space, only the expectation estimate remains. -/
example [Finite Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℕ)
    (hEX : (μ[X] : ℝ) ≤ 1 / 2) : ∃ ω, X ω = 0 := by
  first_moment using μ, X
  linarith

/-! ## Optional helpers for counts of bad events -/

variable {ι : Type*}

/-- Linearity of expectation for a finite sum of natural-valued indicators. -/
theorem expectation_sum_indicators (μ : Measure Ω) [IsFiniteMeasure μ]
    (s : Finset ι) (E : ι → Set Ω)
    (hE : ∀ i ∈ s, MeasurableSet (E i)) :
    μ[fun ω ↦ ∑ i ∈ s, (E i).indicator (1 : Ω → ℕ) ω] =
      ∑ i ∈ s, μ.real (E i) := by
  calc
    _ = ∫ ω, ∑ i ∈ s, (E i).indicator (1 : Ω → ℝ) ω ∂μ := by
      congr 1
      ext ω
      simp [Set.indicator_apply]
    _ = ∑ i ∈ s, ∫ ω, (E i).indicator (1 : Ω → ℝ) ω ∂μ :=
      integral_finsetSum s fun i hi ↦ (integrable_const 1).indicator (hE i hi)
    _ = _ := Finset.sum_congr rfl fun i hi ↦ integral_indicator_one (hE i hi)

/-- A finite sum of indicators is integrable under a finite measure. -/
theorem integrable_sum_indicators (μ : Measure Ω) [IsFiniteMeasure μ]
    (s : Finset ι) (E : ι → Set Ω)
    (hE : ∀ i ∈ s, MeasurableSet (E i)) :
    Integrable (fun ω ↦ ((∑ i ∈ s, (E i).indicator (1 : Ω → ℕ) ω : ℕ) : ℝ)) μ := by
  have h := integrable_finsetSum s fun i hi ↦
    (integrable_const (μ := μ) (1 : ℝ)).indicator (hE i hi)
  convert h using 1
  ext ω
  simp [Set.indicator_apply]

/-- Expected number of indices whose events occur, expressed as a filtered cardinality. -/
theorem expectation_card_filter (μ : Measure Ω) [IsFiniteMeasure μ]
    (s : Finset ι) (E : ι → Set Ω) (hE : ∀ i ∈ s, MeasurableSet (E i)) :
    μ[fun ω ↦ (s.filter fun i ↦ ω ∈ E i).card] = ∑ i ∈ s, μ.real (E i) := by
  simpa [Set.indicator_apply] using expectation_sum_indicators μ s E hE

/-- The number of events occurring in a finite family is integrable. -/
theorem integrable_card_filter (μ : Measure Ω) [IsFiniteMeasure μ]
    (s : Finset ι) (E : ι → Set Ω) (hE : ∀ i ∈ s, MeasurableSet (E i)) :
    Integrable (fun ω ↦ ((s.filter fun i ↦ ω ∈ E i).card : ℝ)) μ := by
  simpa [Set.indicator_apply] using integrable_sum_indicators μ s E hE

omit [MeasurableSpace Ω] in
/-- The natural-valued indicator sum is zero exactly when no selected event occurs. -/
theorem sum_indicators_eq_zero (s : Finset ι) (E : ι → Set Ω) (ω : Ω) :
    (∑ i ∈ s, (E i).indicator (1 : Ω → ℕ) ω) = 0 ↔ ∀ i ∈ s, ω ∉ E i := by
  simp [Set.indicator_apply]

end ProbabilisticCombinatorics.FirstMoment
