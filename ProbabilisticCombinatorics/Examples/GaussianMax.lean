/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

public import ProbabilisticCombinatorics.Method.FirstMoment.Basic
public import ProbabilisticCombinatorics.Method.FirstMoment.Asymptotics
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The maximum of standard Gaussian marginals

Count the coordinates exceeding `t`. The expected count is at most
`n * exp (-t^2 / 2)`, by the Gaussian moment-generating function and Chernoff's
inequality. The first-moment method then bounds the chance of any exceedance.

Only the individual standard Gaussian laws are assumed. The coordinates need
not be independent. We state the maximum bound as `∀ i, G i ω ≤ t`, which also
has an unambiguous meaning for an empty index type.
-/

open MeasureTheory ProbabilityTheory Real Filter
open scoped BigOperators Classical ProbabilityTheory Topology

namespace ProbabilisticCombinatorics.GaussianMax

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Number of coordinates strictly above the threshold. -/
noncomputable def exceedanceCount {n : ℕ} (G : Fin n → Ω → ℝ) (t : ℝ) (ω : Ω) : ℕ :=
  ∑ i, ({ω | t < G i ω} : Set Ω).indicator (1 : Ω → ℕ) ω

omit [MeasurableSpace Ω] in
theorem exceedanceCount_eq_zero {n : ℕ} (G : Fin n → Ω → ℝ) (t : ℝ) (ω : Ω) :
    exceedanceCount G t ω = 0 ↔ ∀ i, G i ω ≤ t := by
  simpa only [exceedanceCount, Finset.mem_univ, forall_const, Set.mem_ofPred_eq, not_lt] using
    FirstMoment.sum_indicators_eq_zero Finset.univ (fun i : Fin n ↦ {ω | t < G i ω}) ω

/-- The Gaussian exponential-moment calculation, followed by Mathlib's Chernoff bound. -/
theorem standardGaussian_tail_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    {G : Ω → ℝ} (hG : HasLaw G (gaussianReal 0 1) μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t < G ω} ≤ exp (-t ^ 2 / 2) := by
  have hint : Integrable (fun ω ↦ exp (t * G ω)) μ :=
    hG.integrable_fun_comp (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) t)
  have htail := measure_ge_le_exp_mul_mgf (μ := μ) (X := G) t ht hint
  rw [mgf_gaussianReal hG t] at htail
  simp only [zero_mul, NNReal.coe_one, one_mul, zero_add] at htail
  have hexp : exp (-t * t) * exp (t ^ 2 / 2) = exp (-t ^ 2 / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  exact (measureReal_mono (show {ω | t < G ω} ⊆ {ω | t ≤ G ω} from
    fun ω h ↦ (show t ≤ G ω from le_of_lt h))).trans (htail.trans_eq hexp)

private theorem integrable_exceedanceCount (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (G : Fin n → Ω → ℝ)
    (hG : ∀ i, HasLaw (G i) (gaussianReal 0 1) μ) (t : ℝ) :
    Integrable (fun ω ↦ (exceedanceCount G t ω : ℝ)) μ := by
  have h := integrable_finsetSum Finset.univ fun i _ ↦
    (integrable_const (μ := μ) (1 : ℝ)).indicator₀
      ((hG i).aemeasurable.nullMeasurable
        (show MeasurableSet (Set.Ioi t) from measurableSet_Ioi))
  convert h using 1
  ext ω
  simp [exceedanceCount, Set.indicator_apply]

/-- Linearity of expectation, including almost-everywhere measurable Gaussian coordinates. -/
theorem expectation_exceedanceCount (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (G : Fin n → Ω → ℝ)
    (hG : ∀ i, HasLaw (G i) (gaussianReal 0 1) μ) (t : ℝ) :
    μ[exceedanceCount G t] = ∑ i, μ.real {ω | t < G i ω} := by
  calc
    _ = ∫ ω, ∑ i : Fin n, ({ω | t < G i ω} : Set Ω).indicator (1 : Ω → ℝ) ω ∂μ := by
      congr 1
      ext ω
      simp [exceedanceCount, Set.indicator_apply]
    _ = ∑ i : Fin n, ∫ ω, ({ω | t < G i ω} : Set Ω).indicator (1 : Ω → ℝ) ω ∂μ :=
      integral_finsetSum Finset.univ fun i _ ↦
        (integrable_const (μ := μ) (1 : ℝ)).indicator₀
          ((hG i).aemeasurable.nullMeasurable measurableSet_Ioi)
    _ = _ := Finset.sum_congr rfl fun i _ ↦ by
      have hnull : NullMeasurableSet {ω | t < G i ω} μ :=
        (hG i).aemeasurable.nullMeasurable measurableSet_Ioi
      rw [integral_indicator₀ hnull]
      simp only [Pi.one_apply, setIntegral_const, smul_eq_mul, mul_one]

/-- The expected number of threshold violations is at most `n exp (-t²/2)`. -/
theorem expectation_exceedanceCount_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (G : Fin n → Ω → ℝ)
    (hG : ∀ i, HasLaw (G i) (gaussianReal 0 1) μ) {t : ℝ} (ht : 0 ≤ t) :
    μ[exceedanceCount G t] ≤ (n : ℝ) * exp (-t ^ 2 / 2) := by
  rw [expectation_exceedanceCount μ G hG]
  calc
    _ ≤ ∑ _i : Fin n, exp (-t ^ 2 / 2) :=
      Finset.sum_le_sum fun i _ ↦ standardGaussian_tail_le μ (hG i) ht
    _ = _ := by simp

/-- A first-moment bound for the maximum of arbitrary standard Gaussian marginals. -/
theorem all_le_probability_lower_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (G : Fin n → Ω → ℝ)
    (hG : ∀ i, HasLaw (G i) (gaussianReal 0 1) μ) {t : ℝ} (ht : 0 ≤ t) :
    1 - (n : ℝ) * exp (-t ^ 2 / 2) ≤ μ.real {ω | ∀ i, G i ω ≤ t} := by
  simpa only [exceedanceCount_eq_zero] using
    FirstMoment.one_sub_le_measure_zero_of_expectation_le μ (exceedanceCount G t)
      (integrable_exceedanceCount μ G hG t) (expectation_exceedanceCount_le μ G hG ht)

/-- The usual threshold slightly above `sqrt (2 log n)`. -/
noncomputable def threshold (n : ℕ) (ε : ℝ) : ℝ :=
  (1 + ε) * sqrt (2 * log (n : ℝ))

/-- Substituting the threshold gives an explicit negative power of `n`. -/
theorem threshold_error_eq {n : ℕ} (hn : 1 ≤ n) (ε : ℝ) :
    (n : ℝ) * exp (-(threshold n ε) ^ 2 / 2) =
      (n : ℝ) ^ (-(2 * ε + ε ^ 2)) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hlog : 0 ≤ log (n : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hn)
  have hradicand : 0 ≤ 2 * log (n : ℝ) := mul_nonneg (by norm_num) hlog
  have hsquare : (threshold n ε) ^ 2 = (1 + ε) ^ 2 * (2 * log (n : ℝ)) := by
    simp only [threshold, mul_pow, Real.sq_sqrt hradicand]
  calc
    _ = exp (log (n : ℝ)) * exp (-(threshold n ε) ^ 2 / 2) := by
      rw [Real.exp_log hnpos]
    _ = exp (log (n : ℝ) - (threshold n ε) ^ 2 / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = _ := by
      rw [Real.rpow_def_of_pos hnpos, hsquare]
      congr 1
      ring

/-- Quantitative Gaussian maximum bound. No joint independence hypothesis is needed. -/
theorem threshold_probability_lower_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 1 ≤ n) (G : Fin n → Ω → ℝ)
    (hG : ∀ i, HasLaw (G i) (gaussianReal 0 1) μ) {ε : ℝ} (hε : 0 < ε) :
    1 - (n : ℝ) ^ (-(2 * ε + ε ^ 2)) ≤
      μ.real {ω | ∀ i, G i ω ≤ threshold n ε} := by
  rw [← threshold_error_eq hn ε]
  apply all_le_probability_lower_bound μ G hG
  exact mul_nonneg (by linarith) (Real.sqrt_nonneg _)

/-- The explicit Gaussian error budget tends to zero for every fixed positive `ε`. -/
theorem error_budget_tendsto_zero {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-(2 * ε + ε ^ 2))) atTop (𝓝 0) := by
  have hexponent : 0 < 2 * ε + ε ^ 2 := by nlinarith [sq_nonneg ε]
  exact (tendsto_rpow_neg_atTop hexponent).comp tendsto_natCast_atTop_atTop

/-- The Gaussian maximum bound holds with high probability, even when the probability
spaces vary with `n` and the coordinates on each space are dependent. -/
theorem threshold_whp {Ω' : ℕ → Type*} [∀ n, MeasurableSpace (Ω' n)]
    (μ : ∀ n, Measure (Ω' n)) [∀ n, IsProbabilityMeasure (μ n)]
    (G : ∀ n, Fin n → Ω' n → ℝ)
    (hG : ∀ n i, HasLaw (G n i) (gaussianReal 0 1) (μ n))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (μ n).real {ω | ∀ i, G n i ω ≤ threshold n ε}) atTop (𝓝 1) := by
  have h := FirstMoment.tendsto_measure_zero_of_expectation_le μ
    (fun n ↦ exceedanceCount (G n) (threshold n ε))
    (fun n ↦ (n : ℝ) ^ (-(2 * ε + ε ^ 2)))
    (Eventually.of_forall fun _ ↦ inferInstance)
    (Eventually.of_forall fun n ↦ integrable_exceedanceCount (μ n) (G n) (hG n) (threshold n ε))
    (show ∀ᶠ n in atTop, ((μ n)[exceedanceCount (G n) (threshold n ε)] : ℝ) ≤
        (n : ℝ) ^ (-(2 * ε + ε ^ 2)) from by
      filter_upwards [eventually_ge_atTop 1] with n hn
      rw [← threshold_error_eq hn ε]
      exact expectation_exceedanceCount_le (μ n) (G n) (hG n)
        (mul_nonneg (by linarith) (Real.sqrt_nonneg _)))
    (error_budget_tendsto_zero hε)
  simpa only [exceedanceCount_eq_zero] using h

end ProbabilisticCombinatorics.GaussianMax
