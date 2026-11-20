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

/-- Average a pointwise lower bound on the value retained by a feasible repair.
Only the lower bound needs to be integrable. -/
theorem exists_feasible_ge_expectation {Ω A : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (repair : Ω → A) (feasible : A → Prop)
    (value : A → ℝ) (gain : Ω → ℝ) (hg : Integrable gain μ)
    (good : ∀ ω, feasible (repair ω)) (bound : ∀ ω, gain ω ≤ value (repair ω)) :
    ∃ a, feasible a ∧ (∫ ω, gain ω ∂μ) ≤ value a := by
  obtain ⟨ω, hω⟩ := exists_integral_le hg
  exact ⟨repair ω, good ω, hω.trans (bound ω)⟩

end ProbabilisticCombinatorics.Alteration
