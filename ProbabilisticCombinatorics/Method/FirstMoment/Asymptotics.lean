/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

public import ProbabilisticCombinatorics.Method.FirstMoment.Basic
public import Mathlib.Topology.Order.Basic

@[expose] public section

/-!
# Quantitative first moments and high probability

Keep an explicit error budget `δ`: an expectation bound gives failure probability
at most `δ` and success probability at least `1 - δ`. If `δ` tends to zero,
success probability tends to one. The spaces, measures, and counts may all vary
with the index. Hypotheses only need to hold eventually, so small boundary cases
such as zero bins do not complicate asymptotic statements.
-/

open MeasureTheory Filter
open scoped ProbabilityTheory Topology

namespace ProbabilisticCombinatorics.FirstMoment

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Retain an explicit upper bound on failure probability. -/
theorem measure_ne_zero_le_of_expectation_le (μ : Measure Ω) (X : Ω → ℕ)
    (hX : Integrable (fun ω ↦ (X ω : ℝ)) μ) {δ : ℝ}
    (hEX : (μ[X] : ℝ) ≤ δ) : μ.real {ω | X ω ≠ 0} ≤ δ :=
  (measure_ne_zero_le_expectation μ X hX).trans hEX

/-- Retain an explicit lower bound on success probability. -/
theorem one_sub_le_measure_zero_of_expectation_le (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℕ)
    (hX : Integrable (fun ω ↦ (X ω : ℝ)) μ) {δ : ℝ}
    (hEX : (μ[X] : ℝ) ≤ δ) : 1 - δ ≤ μ.real {ω | X ω = 0} :=
  (sub_le_sub_left hEX 1).trans (one_sub_expectation_le_measure_zero μ X hX)

section Limits

variable {ι : Type*} {l : Filter ι} {Ω' : ι → Type*}
    [∀ i, MeasurableSpace (Ω' i)]

/-- A vanishing expectation budget gives vanishing failure probability. -/
theorem tendsto_measure_ne_zero_of_expectation_le
    (μ : ∀ i, Measure (Ω' i)) (X : ∀ i, Ω' i → ℕ) (δ : ι → ℝ)
    (hX : ∀ᶠ i in l, Integrable (fun ω ↦ (X i ω : ℝ)) (μ i))
    (hEX : ∀ᶠ i in l, ((μ i)[X i] : ℝ) ≤ δ i)
    (hδ : Tendsto δ l (𝓝 0)) :
    Tendsto (fun i ↦ (μ i).real {ω | X i ω ≠ 0}) l (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hδ (Eventually.of_forall fun _ ↦ measureReal_nonneg) ?_
  filter_upwards [hX, hEX] with i hi hEi
  exact measure_ne_zero_le_of_expectation_le (μ i) (X i) hi hEi

/-- The quantitative first-moment method yields a high-probability conclusion.
The index filter can be `atTop` on natural numbers, and the sample space may
depend on the index. Probability and integrability are only needed eventually. -/
theorem tendsto_measure_zero_of_expectation_le
    (μ : ∀ i, Measure (Ω' i)) (X : ∀ i, Ω' i → ℕ) (δ : ι → ℝ)
    (hprob : ∀ᶠ i in l, IsProbabilityMeasure (μ i))
    (hX : ∀ᶠ i in l, Integrable (fun ω ↦ (X i ω : ℝ)) (μ i))
    (hEX : ∀ᶠ i in l, ((μ i)[X i] : ℝ) ≤ δ i)
    (hδ : Tendsto δ l (𝓝 0)) :
    Tendsto (fun i ↦ (μ i).real {ω | X i ω = 0}) l (𝓝 1) := by
  have hlimit : Tendsto (fun i ↦ 1 - δ i) l (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub hδ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlimit tendsto_const_nhds ?_ ?_
  · filter_upwards [hprob, hX, hEX] with i hpi hi hEi
    let := hpi
    exact one_sub_le_measure_zero_of_expectation_le (μ i) (X i) hi hEi
  · filter_upwards [hprob] with i hpi
    let := hpi
    exact measureReal_le_one

end Limits

/-! Importing this module also lets `first_moment` keep a quantitative goal.
It recognizes failure bounds, success bounds, and the original existence goal.
The expectation estimate remains a visible obligation. -/

macro_rules
  | `(tactic| first_moment using $μ:term, $X:term) =>
    `(tactic|
      (first
       | refine ProbabilisticCombinatorics.FirstMoment.one_sub_le_measure_zero_of_expectation_le
           $μ $X ?_ ?_
       | refine ProbabilisticCombinatorics.FirstMoment.measure_ne_zero_le_of_expectation_le
           $μ $X ?_ ?_
       | refine ProbabilisticCombinatorics.FirstMoment.exists_zero_of_expectation_lt_one
           $μ $X ?_ ?_
       try
         first
         | assumption
         | exact MeasureTheory.Integrable.of_finite))

end ProbabilisticCombinatorics.FirstMoment
