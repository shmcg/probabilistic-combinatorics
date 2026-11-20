/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

public import ProbabilisticCombinatorics.Examples.Ramsey.Basic
public import ProbabilisticCombinatorics.Method.FirstMoment.Asymptotics
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Log
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

/-!
# The first-moment upper bound for homogeneous sets, with high probability

The threshold `Nat.clog 2 (n * n)` is the ceiling of `2 * log₂ n` for positive
`n`. We prove that the probability of a clique or independent set of this size
is at most `4 / n`, and hence tends to zero.

The estimate retains the factorial in `choose(n,k) ≤ n^k / k!`. The elementary
bound `2^(k-1) ≤ k!` is already enough; no epsilon or Stirling estimate is needed.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Classical ProbabilityTheory Topology

namespace ProbabilisticCombinatorics.Examples.Ramsey

private theorem two_mul_choose_succ_two (k : ℕ) :
    2 * (k + 1).choose 2 = k * (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.choose_succ_succ' (k + 1) 1, Nat.choose_one_right]
      nlinarith

private theorem pow_succ_le_two_pow_choose {n k : ℕ} (hsize : n ^ 2 ≤ 2 ^ k) :
    n ^ (k + 1) ≤ 2 ^ ((k + 1).choose 2) := by
  apply (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : 2 ≠ 0)).mp
  calc
    (n ^ (k + 1)) ^ 2 = (n ^ 2) ^ (k + 1) := by
      simp only [← pow_mul, Nat.mul_comm]
    _ ≤ (2 ^ k) ^ (k + 1) := Nat.pow_le_pow_left hsize _
    _ = (2 ^ ((k + 1).choose 2)) ^ 2 := by
      simp only [← pow_mul]
      rw [← two_mul_choose_succ_two]
      congr 1
      omega

private theorem nat_choose_budget {n k : ℕ} (hk : 0 < k)
    (hsize : n ^ 2 ≤ 2 ^ k) :
    n * n.choose k ≤ 2 ^ (k.choose 2 + 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have hfac : 2 ^ j ≤ (j + 1).factorial := by
    simpa [Nat.add_comm] using
      (Nat.factorial_mul_pow_le_factorial (m := 1) (n := j))
  have hchoose : 2 ^ j * n.choose (j + 1) ≤ n ^ (j + 1) := by
    calc
      _ ≤ (j + 1).factorial * n.choose (j + 1) := Nat.mul_le_mul_right _ hfac
      _ = n.descFactorial (j + 1) := (Nat.descFactorial_eq_factorial_mul_choose _ _).symm
      _ ≤ _ := Nat.descFactorial_le_pow _ _
  have hbig : (n * n.choose (j + 1)) * 2 ^ j ≤
      2 ^ ((j + 2).choose 2) := by
    calc
      _ = n * (2 ^ j * n.choose (j + 1)) := by ring
      _ ≤ n * n ^ (j + 1) := Nat.mul_le_mul_left _ hchoose
      _ = n ^ (j + 2) := (pow_succ' n (j + 1)).symm
      _ ≤ _ := pow_succ_le_two_pow_choose hsize
  have hexp : (j + 2).choose 2 = ((j + 1).choose 2 + 1) + j := by
    rw [Nat.choose_succ_succ' (j + 1) 1, Nat.choose_one_right]
    change (j + 1) + (j + 1).choose 2 = ((j + 1).choose 2 + 1) + j
    omega
  rw [hexp, pow_add] at hbig
  apply (mul_le_mul_iff_right₀ (pow_pos (by decide : 0 < (2 : ℕ)) j)).mp
  simpa [Nat.mul_comm] using hbig

/-- If `n² ≤ 2^k`, the exact first-moment budget is at most `4/n`.
The factorial in the binomial coefficient is what gives decay at `2 log₂ n`. -/
theorem ramsey_budget_le_four_div {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hsize : n ^ 2 ≤ 2 ^ k) :
    (2 * (n.choose k : ℝ)) * (1 / 2 : ℝ) ^ (k.choose 2) ≤ 4 / (n : ℝ) := by
  have hnat := nat_choose_budget hk hsize
  have hr : (n : ℝ) * (n.choose k : ℝ) ≤ 2 * (2 : ℝ) ^ (k.choose 2) := by
    exact_mod_cast (show n * n.choose k ≤ 2 * 2 ^ (k.choose 2) by
      simpa [pow_succ, Nat.mul_comm] using hnat)
  rw [div_pow, one_pow, mul_one_div,
    div_le_div_iff₀ (by positivity) (by exact_mod_cast hn)]
  nlinarith

/-- The ceiling of `2 log₂ n`, expressed by the integer upper logarithm. -/
def logarithmicThreshold (n : ℕ) : ℕ := Nat.clog 2 (n * n)

/-- The integer upper logarithm agrees with the usual real logarithmic threshold. -/
theorem logarithmicThreshold_eq (n : ℕ) :
    logarithmicThreshold n = ⌈2 * Real.logb 2 (n : ℝ)⌉₊ := by
  rw [logarithmicThreshold, ← Real.natCeil_logb_natCast]
  congr 1
  simpa only [Nat.cast_mul, Nat.cast_ofNat, pow_two] using
    Real.logb_pow 2 (n : ℝ) 2

/-- The expected number of cliques and independent sets of logarithmic size
is at most `4/n`. -/
theorem expected_badCount_logarithmic_le (n : ℕ) (hn : 2 ≤ n) :
    (SimpleGraph.binomialRandom (Fin n) fairEdgeProbability)[
      badCount n (logarithmicThreshold n)] ≤ 4 / (n : ℝ) := by
  rw [expected_badCount]
  apply ramsey_budget_le_four_div (by omega)
  · exact Nat.clog_pos (by decide) (by nlinarith)
  · simpa [logarithmicThreshold, pow_two] using Nat.le_pow_clog (by decide : 1 < 2) (n * n)

/-- A finite, quantitative bound at the threshold `ceil(2 log₂ n)`. -/
theorem logarithmic_failure_probability_le (n : ℕ) (hn : 2 ≤ n) :
    (SimpleGraph.binomialRandom (Fin n) fairEdgeProbability).real
        {G | ¬(G.CliqueFree (logarithmicThreshold n) ∧
          G.IndepSetFree (logarithmicThreshold n))} ≤ 4 / (n : ℝ) := by
  exact (ramsey_failure_probability_le n (logarithmicThreshold n)).trans
    (by simpa only [expected_badCount] using expected_badCount_logarithmic_le n hn)

/-- With high probability a fair random graph has no clique or independent set
of size `ceil(2 log₂ n)`. The sample space varies with `n`. -/
theorem logarithmic_failure_probability_tendsto_zero :
    Tendsto (fun n : ℕ ↦
      (SimpleGraph.binomialRandom (Fin n) fairEdgeProbability).real
        {G | ¬(G.CliqueFree (logarithmicThreshold n) ∧
          G.IndepSetFree (logarithmicThreshold n))}) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n ↦ measureReal_nonneg)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact logarithmic_failure_probability_le n hn
  · exact tendsto_const_div_atTop_nhds_zero_nat 4

/-- The quantitative success statement keeps its explicit error budget. -/
theorem logarithmic_success_probability_ge (n : ℕ) (hn : 2 ≤ n) :
    1 - 4 / (n : ℝ) ≤
      (SimpleGraph.binomialRandom (Fin n) fairEdgeProbability).real
        {G | G.CliqueFree (logarithmicThreshold n) ∧
          G.IndepSetFree (logarithmicThreshold n)} := by
  simpa only [badCount_eq_zero_iff] using
    FirstMoment.one_sub_le_measure_zero_of_expectation_le
      (SimpleGraph.binomialRandom (Fin n) fairEdgeProbability)
      (badCount n (logarithmicThreshold n)) (integrable_badCount n _ _)
      (expected_badCount_logarithmic_le n hn)

/-- The general first-moment WHP theorem turns the `4/n` expectation budget
into convergence of the desired graph property's probability to one. -/
theorem logarithmic_success_probability_tendsto_one :
    Tendsto (fun n : ℕ ↦
      (SimpleGraph.binomialRandom (Fin n) fairEdgeProbability).real
        {G | G.CliqueFree ⌈2 * Real.logb 2 (n : ℝ)⌉₊ ∧
          G.IndepSetFree ⌈2 * Real.logb 2 (n : ℝ)⌉₊}) atTop (𝓝 1) := by
  simpa only [badCount_eq_zero_iff, logarithmicThreshold_eq] using
    FirstMoment.tendsto_measure_zero_of_expectation_le
      (fun n ↦ SimpleGraph.binomialRandom (Fin n) fairEdgeProbability)
      (fun n ↦ badCount n (logarithmicThreshold n)) (fun n ↦ 4 / (n : ℝ))
      (Eventually.of_forall fun _ ↦ inferInstance)
      (Eventually.of_forall fun n ↦ integrable_badCount n _ _)
      (eventually_atTop.2 ⟨2, fun n hn ↦ expected_badCount_logarithmic_le n hn⟩)
      (tendsto_const_div_atTop_nhds_zero_nat 4)

end ProbabilisticCombinatorics.Examples.Ramsey
