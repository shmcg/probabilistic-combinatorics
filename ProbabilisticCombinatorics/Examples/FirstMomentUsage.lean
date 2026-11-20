/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

public import ProbabilisticCombinatorics.Method.FirstMoment.Asymptotics

@[expose] public section

open MeasureTheory
open scoped ProbabilityTheory

namespace ProbabilisticCombinatorics.Examples.FirstMomentUsage

variable {Ω : Type*} [MeasurableSpace Ω] [Finite Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℕ) (δ : ℝ)

example (hEX : (μ[X] : ℝ) ≤ δ) : μ.real {ω | X ω ≠ 0} ≤ δ := by
  first_moment using μ, X
  exact hEX

example (hEX : (μ[X] : ℝ) ≤ δ) : 1 - δ ≤ μ.real {ω | X ω = 0} := by
  first_moment using μ, X
  exact hEX

example (hEX : (μ[X] : ℝ) < 1) : ∃ ω, X ω = 0 := by
  first_moment using μ, X
  exact hEX

end ProbabilisticCombinatorics.Examples.FirstMomentUsage
