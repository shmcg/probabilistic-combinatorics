/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

public import Mathlib.MeasureTheory.Integral.Average

/-! # Averaging after deterministic repair -/

public section

open MeasureTheory
open scoped ProbabilityTheory

namespace ProbabilisticCombinatorics.Alteration

/-- Average a pointwise upper bound on the cost of a feasible repaired object.
Only the upper bound needs to be integrable. -/
theorem exists_feasible_le_expectation {Ω A : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (repair : Ω → A) (feasible : A → Prop)
    (cost : A → ℝ) (budget : Ω → ℝ) (hb : Integrable budget μ)
    (good : ∀ ω, feasible (repair ω)) (bound : ∀ ω, cost (repair ω) ≤ budget ω) :
    ∃ a, feasible a ∧ cost a ≤ ∫ ω, budget ω ∂μ := by
  obtain ⟨ω, hω⟩ := exists_le_integral hb
  exact ⟨repair ω, good ω, (bound ω).trans hω⟩

end ProbabilisticCombinatorics.Alteration
