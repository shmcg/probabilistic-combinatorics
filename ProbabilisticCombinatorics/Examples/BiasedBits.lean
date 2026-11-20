/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

public import ProbabilisticCombinatorics.Method.FirstMoment.Basic
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.ProductMeasure

@[expose] public section

/-!
# Counting true bits

For a finite family of Bernoulli bits, choose the number of true bits as `X`.
Compute `E[X] = ∑ i, p i` by linearity, then apply the count form of Markov.
-/

open MeasureTheory ProbabilityTheory unitInterval
open scoped BigOperators Classical ENNReal ProbabilityTheory

namespace ProbabilisticCombinatorics.Examples.BiasedBits

open FirstMoment

/-- The probability of a true bit in a product of Bernoulli laws. -/
theorem biased_bit_probability {J : Type*} (p : J → I) (i : J) :
    (Measure.infinitePi (fun j : J ↦ bernoulliMeasure true false (p j))).real
        {x : J → Bool | x i = true} = (p i : ℝ) := by
  have h : (Measure.infinitePi (fun j : J ↦ bernoulliMeasure true false (p j)))
      {x : J → Bool | x i = true} = (toNNReal (p i) : ℝ≥0∞) := by
    change (Measure.infinitePi (fun j : J ↦ bernoulliMeasure true false (p j)))
      ((fun x : J → Bool ↦ x i) ⁻¹' ({true} : Set Bool)) = _
    rw [← Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton true)]
    rw [Measure.infinitePi_map_eval]
    exact bernoulliMeasure_apply_of_mem_of_notMem (p i)
      (measurableSet_singleton true) (by simp) (by simp)
  simpa [measureReal_def] using congrArg ENNReal.toReal h

/-- Expected number of true bits, with one natural-valued indicator for each coordinate. -/
theorem biased_bits_expectation {J : Type*} [Fintype J] (p : J → I) :
    (Measure.infinitePi (fun j : J ↦ bernoulliMeasure true false (p j)))[
      fun x : J → Bool ↦ ∑ i : J, if x i = true then (1 : ℕ) else 0] =
        ∑ i : J, (p i : ℝ) := by
  let μ := Measure.infinitePi (fun j : J ↦ bernoulliMeasure true false (p j))
  let E : J → Set (J → Bool) := fun i ↦ {x | x i = true}
  have hE (i : J) : MeasurableSet (E i) :=
    (measurableSet_singleton true).preimage (measurable_pi_apply i)
  calc
    _ = ∑ i : J, μ.real (E i) := by
      simpa [E, μ, Set.indicator_apply] using
        expectation_sum_indicators μ Finset.univ E (fun i _ ↦ hE i)
    _ = _ := Finset.sum_congr rfl fun i _ ↦ biased_bit_probability p i

/-- Choose the number of true bits, compute its expectation, and apply Markov. -/
theorem biased_bits_tail {J : Type*} [Fintype J] (p : J → I) {k : ℕ} (hk : 0 < k) :
    (Measure.infinitePi (fun j : J ↦ bernoulliMeasure true false (p j))).real
      {x : J → Bool | k ≤ ∑ i : J, if x i = true then (1 : ℕ) else 0} ≤
        (∑ i : J, (p i : ℝ)) / (k : ℝ) := by
  have h := FirstMoment.measure_ge_le_expectation_div
    (Measure.infinitePi (fun j : J ↦ bernoulliMeasure true false (p j)))
    (fun x : J → Bool ↦ ∑ i : J, if x i = true then (1 : ℕ) else 0)
    (Integrable.of_finite) hk
  simpa only [biased_bits_expectation] using h

end ProbabilisticCombinatorics.Examples.BiasedBits
