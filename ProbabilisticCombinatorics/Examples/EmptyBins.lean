/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

public import ProbabilisticCombinatorics.Examples.BallsBins
public import ProbabilisticCombinatorics.Method.SecondMoment

/-! # Empty bins below the coupon-collector threshold -/

public section
noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Classical ProbabilityTheory ENNReal Topology

namespace ProbabilisticCombinatorics.Examples.BallsBins

/-- Two distinct bins are missed by every throw. -/
theorem emptyBin_pair_probability {n m : ℕ} (a b : Fin n) (hab : a ≠ b) :
    (allocationMeasure n m).real (emptyBin a ∩ emptyBin b) = (1 - 2 / (n : ℝ)) ^ m := by
  have hn := a.isLt
  let : NeZero n := ⟨by omega⟩
  let ν := uniformOn (Set.univ : Set (Fin n))
  have hsingle (c : Fin n) : ν.real {c} = 1 / (n : ℝ) := by
    simp [ν, measureReal_def, uniformOn_univ]
  have hmiss : ν.real (({a} ∪ {b})ᶜ : Set (Fin n)) = 1 - 2 / (n : ℝ) := by
    rw [measureReal_compl (by measurability), probReal_univ,
      measureReal_union (μ := ν) (Set.disjoint_singleton.mpr hab) (measurableSet_singleton b), hsingle, hsingle]
    ring
  have rect : emptyBin (m := m) a ∩ emptyBin b =
      Set.univ.pi (fun _ : Fin m ↦ (({a} ∪ {b})ᶜ : Set (Fin n))) := by
    ext ω
    simp [emptyBin, forall_and, and_comm]
  rw [measureReal_def, rect, allocationMeasure, Measure.pi_pi]
  simpa [measureReal_def] using congrArg (fun x : ℝ ↦ x ^ m) hmiss

/-- Finite second-moment bound for the probability all bins have been occupied. -/
theorem surjective_probability_le_inv_mean {n m : ℕ} (hn : 2 ≤ n) :
    (allocationMeasure n m).real {ω | Function.Surjective ω} ≤
      ((n : ℝ) * (1 - 1 / (n : ℝ)) ^ m)⁻¹ := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  let : NeZero n := ⟨by omega⟩
  let μ := allocationMeasure n m
  let E := @emptyBin n m
  let X (ω : Fin m → Fin n) := (emptyCount n m ω : ℝ)
  have repr : X = fun ω ↦ ∑ i, (E i).indicator (1 : (Fin m → Fin n) → ℝ) ω := by
    ext ω
    simp [X, emptyCount, E, Set.indicator_apply]
  have hL : MemLp X 2 μ := by
    rw [repr]
    exact memLp_finsetSum _ (fun i _ ↦ (memLp_const (1 : ℝ)).indicator
      (Set.toFinite (E i)).measurableSet.nullMeasurableSet)
  have hmean : μ[X] = (n : ℝ) * (1 - 1 / (n : ℝ)) ^ m :=
    expected_emptyCount n m (by omega)
  have hx : 0 < 1 - 1 / (n : ℝ) := by
    have := (div_lt_one hn0).mpr (show (1 : ℝ) < n by linarith)
    linarith
  have hm : 0 < μ[X] := hmean ▸ mul_pos hn0 (pow_pos hx _)
  have hv : Var[X; μ] ≤ μ[X] := by
    rw [hmean, repr]
    apply (SecondMoment.variance_le_sum_of_pairwise Finset.univ E
      (fun i _ ↦ (Set.toFinite _).measurableSet) ?_).trans_eq
    · simp [μ, E, emptyBin_probability n m (by omega), nsmul_eq_mul]
    · intro i _ j _ hij
      simp only [E, μ, emptyBin_pair_probability i j hij, emptyBin_probability n m (by omega),
        ← mul_pow]
      apply pow_le_pow_left₀ (sub_nonneg.mpr ((div_le_one hn0).mpr hnR))
      nlinarith [sq_nonneg (1 / (n : ℝ)), show (2 : ℝ) / n = 1 / n + 1 / n by ring]
  have h := (SecondMoment.measure_zero_le_variance_div_sq hL hm).trans
    (div_le_div_of_nonneg_right hv (sq_nonneg _))
  rw [hmean] at h
  have cancel (x : ℝ) (hpos : 0 < x) : x / x ^ 2 = x⁻¹ := by field_simp
  rw [cancel _ (mul_pos hn0 (pow_pos hx m))] at h
  simpa [X, μ, emptyCount_eq_zero] using h

/-- Below the cutoff, the probability of complete occupancy is at most
`exp(1) * n^(-ε)`. The extra constant accounts for using `n` in the cutoff. -/
theorem below_cutoff_bound {n m : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 ≤ ε)
    (hballs : (m : ℝ) ≤ (1 - ε) * n * Real.log n) :
    (allocationMeasure n m).real {ω | Function.Surjective ω} ≤ Real.exp 1 * (n : ℝ) ^ (-ε) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hpred : 0 < (n : ℝ) - 1 := by linarith
  have hx : 0 < 1 - 1 / (n : ℝ) := sub_pos.mpr ((div_lt_one hn0).mpr (by linarith))
  have hlog : -(1 / ((n : ℝ) - 1)) ≤ Real.log (1 - 1 / (n : ℝ)) := by
    apply le_trans _ (Real.one_sub_inv_le_log_of_pos hx)
    apply le_of_eq
    field_simp
    ring
  have hl := Real.log_le_sub_one_of_pos hn0
  have hln := Real.log_nonneg (show 1 ≤ (n : ℝ) by linarith)
  have hdiv : (m : ℝ) / (n - 1 : ℝ) ≤ (1 - ε) * Real.log n + 1 := by
    apply (div_le_iff₀ hpred).mpr
    nlinarith only [hballs, hl, mul_nonneg hε hln]
  have hexp : -((n : ℝ).log + m * Real.log (1 - 1 / (n : ℝ))) ≤ 1 + Real.log n * (-ε) := by
    have hh := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg m)
    rw [mul_neg, mul_one_div] at hh
    linarith
  apply (surjective_probability_le_inv_mean hn).trans
  rw [Real.rpow_def_of_pos hn0, ← Real.exp_add, ← Real.exp_log hx, ← Real.exp_nat_mul]
  nth_rw 1 [← Real.exp_log hn0]
  rw [← Real.exp_add, ← Real.exp_neg]
  simpa only [Real.exp_log hx] using Real.exp_le_exp.mpr hexp

/-- Lower side of the coupon-collector threshold for independent uniform throws. -/
theorem below_cutoff_surjective_tendsto_zero {ε : ℝ} (hε : 0 < ε)
    (m : ℕ → ℕ) (hm : ∀ᶠ n : ℕ in atTop, (m n : ℝ) ≤ (1 - ε) * n * Real.log n) :
    Tendsto (fun n ↦ (allocationMeasure n (m n)).real {ω | Function.Surjective ω})
      atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ ↦ Real.exp 1 * (n : ℝ) ^ (-ε)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hε).comp tendsto_natCast_atTop_atTop).const_mul (Real.exp 1)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall fun _ ↦ measureReal_nonneg)
  filter_upwards [hm, eventually_ge_atTop 2] with n h hn
  exact below_cutoff_bound hn hε.le h

end ProbabilisticCombinatorics.Examples.BallsBins
