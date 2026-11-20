/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

public import ProbabilisticCombinatorics.Examples.Clique
public import ProbabilisticCombinatorics.Method.SecondMoment
public import ProbabilisticCombinatorics.Estimates.IntersectionMoment
public import ProbabilisticCombinatorics.Examples.Ramsey.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Lower bounds on clique number by the second moment -/

public section
noncomputable section

open MeasureTheory ProbabilityTheory SimpleGraph unitInterval Finset
open scoped BigOperators Classical ProbabilityTheory ENNReal

namespace ProbabilisticCombinatorics.Examples.Clique

open RamseyProbabilityHelpers

/-- A shared vertex contributes at most `2^(k/2)` to the normalized joint probability. -/
private theorem choose_two_le_half_mul {r k : ℕ} (h : r ≤ k) : r.choose 2 ≤ (k / 2) * r := by
  rw [Nat.choose_two_right]
  have h1 : r - 1 ≤ 2 * (k / 2) := by omega
  have h2 := Nat.mul_le_mul_left r h1
  rw [show r * (2 * (k / 2)) = 2 * ((k / 2) * r) by ring] at h2
  omega

/-- A finite bound on the lower tail. Its right side tends to zero whenever
`k² * 2^(k/2) / n` tends to zero. -/
theorem cliqueFree_probability_le {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    (binomialRandom (Fin n) Ramsey.fairEdgeProbability).real {G | G.CliqueFree k} ≤
      (1 + (2 : ℝ) ^ (k / 2) * k / n) ^ k - 1 := by
  let μ := binomialRandom (Fin n) Ramsey.fairEdgeProbability
  let F := vertexSets n k
  let C : ℝ := n.choose k
  let K := k.choose 2
  let q : ℝ := (1 / 2) ^ K
  let a : ℝ := 2 ^ (k / 2)
  let B : ℝ := (1 + a * k / n) ^ k
  let X (G : SimpleGraph (Fin n)) : ℝ := cliqueCount n k G
  have hC : 0 < C := by dsimp [C]; exact_mod_cast Nat.choose_pos hk
  have hq : 0 < q := by dsimp [q]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have cardF : F.card = n.choose k := by simp [F, vertexSets]
  have size (s : Finset (Fin n)) (hs : s ∈ F) : s.card = k := by simpa [F, vertexSets] using hs
  have hX : X = fun G ↦ ∑ s ∈ F, (cliqueEvent s).indicator (1 : SimpleGraph (Fin n) → ℝ) G := by
    ext G
    simp [X, cliqueCount, F, Set.indicator_apply]
  have hL : MemLp X 2 μ := by
    rw [hX]
    exact memLp_finsetSum _ fun s _ ↦ (memLp_const (1 : ℝ)).indicator
      (measurableSet_clique s).nullMeasurableSet
  have mean : μ[X] = C * q := expected_cliqueCount n k _
  have single (s : Finset (Fin n)) (hs : s ∈ F) : μ.real (cliqueEvent s) = q := by
    simpa [μ, q, K, cliqueEvent, measureReal_def, size s hs, Ramsey.fairEdgeProbability]
      using congrArg ENNReal.toReal (clique_probability Ramsey.fairEdgeProbability s)
  have pair (s t : Finset (Fin n)) (hs : s ∈ F) (ht : t ∈ F) :
      μ.real (cliqueEvent s ∩ cliqueEvent t) ≤ q ^ 2 * (1 + a) ^ (s ∩ t).card := by
    let r := (s ∩ t).card
    have hr : r ≤ k := (card_le_card inter_subset_left).trans_eq (size s hs)
    have hK : r.choose 2 ≤ K := Nat.choose_le_choose 2 hr
    have he := congrArg ENNReal.toReal (clique_pair_probability Ramsey.fairEdgeProbability s t)
    have eqn : μ.real (cliqueEvent s ∩ cliqueEvent t) = (1 / 2 : ℝ) ^ (K + K - r.choose 2) := by
      simpa [μ, cliqueEvent, K, r, measureReal_def, size s hs, size t ht, Ramsey.fairEdgeProbability] using he
    rw [eqn]
    calc
      _ = q ^ 2 * (2 : ℝ) ^ r.choose 2 := by
        have h : K + K = (K + K - r.choose 2) + r.choose 2 := by omega
        simp only [q, one_div, inv_pow, ← pow_mul, Nat.mul_two]
        rw [h, pow_add]
        field_simp
        simp
      _ ≤ q ^ 2 * a ^ r := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        dsimp [a]
        rw [← pow_mul]
        exact pow_le_pow_right₀ (by norm_num) (choose_two_le_half_mul hr)
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha (by linarith) r) (sq_nonneg _)
  have hv : Var[X; μ] ≤ (C * q) ^ 2 * (B - 1) := by
    rw [hX, SecondMoment.variance_sum_indicators F cliqueEvent (fun s _ ↦ measurableSet_clique s)]
    have row (s : Finset (Fin n)) (hs : s ∈ F) :
        (∑ t ∈ F, (μ.real (cliqueEvent s ∩ cliqueEvent t) - μ.real (cliqueEvent s) * μ.real (cliqueEvent t))) ≤
        q ^ 2 * (C * B - C) := by
      have hg := sum_pow_inter_le s (k := k) (le_of_eq (size s hs)) (by simpa using hk)
        (by simpa using hn) ha
      have hg' : (∑ t ∈ F, (1 + a) ^ (s ∩ t).card) ≤ C * B := by
        simpa [B, C, F, vertexSets, size s hs] using hg
      calc
        _ ≤ ∑ t ∈ F, (q ^ 2 * (1 + a) ^ (s ∩ t).card - q ^ 2) := by
          apply sum_le_sum
          intro t ht
          rw [single s hs, single t ht, ← sq]
          exact sub_le_sub_right (pair s t hs ht) _
        _ = q ^ 2 * ((∑ t ∈ F, (1 + a) ^ (s ∩ t).card) - C) := by
          rw [sum_sub_distrib, ← mul_sum]
          simp [cardF, C, mul_sub, nsmul_eq_mul, mul_comm]
        _ ≤ _ := mul_le_mul_of_nonneg_left (sub_le_sub_right hg' _) (sq_nonneg _)
    apply (sum_le_sum row).trans_eq
    simp [cardF, C, nsmul_eq_mul]; ring
  have h := SecondMoment.measure_zero_le_variance_div_sq hL (mean ▸ mul_pos hC hq)
  rw [mean] at h
  have h' : μ.real {ω | X ω = 0} ≤ B - 1 := h.trans <|
    (div_le_iff₀ (sq_pos_of_pos (mul_pos hC hq))).mpr (by rw [mul_comm]; exact hv)
  simpa [X, μ, B, a, cliqueCount_eq_zero] using h'

open Filter
open scoped Topology

/-- A fair random graph contains a clique of size `⌊(2-ε) log₂ n⌋` with high probability.
The failure event is expressed using Mathlib's `CliqueFree`. -/
theorem logarithmic_cliqueFree_tendsto_zero {ε : ℝ} (he : 0 < ε) (he2 : ε ≤ 2) :
    Tendsto (fun n : ℕ ↦ (binomialRandom (Fin n) Ramsey.fairEdgeProbability).real
      {G | G.CliqueFree ⌊(2 - ε) * Real.logb 2 n⌋₊}) atTop (𝓝 0) := by
  let L := Real.log 2
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hsmall : ∀ᶠ n : ℕ in atTop, ‖Real.log (n : ℝ)‖ ≤ (L / 2) * ‖(n : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually (Real.isLittleO_log_id_atTop.def (half_pos hL))
  let rate (n : ℕ) := (2 / L) ^ 2 * ((Real.log n) ^ 2 / (n : ℝ) ^ (ε / 2))
  have hr : Tendsto rate atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop 2 (half_pos he)).tendsto_div_nhds_zero
    simpa [rate, Real.rpow_two] using
      (h.comp tendsto_natCast_atTop_atTop).const_mul ((2 / L)^2)
  have hb : Tendsto (fun n ↦ Real.exp (rate n) - 1) atTop (𝓝 0) := by
    simpa using ((Real.continuous_exp.tendsto 0).comp hr).sub_const 1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
    (Eventually.of_forall fun _ ↦ measureReal_nonneg)
  filter_upwards [eventually_ge_atTop 1, hsmall] with n hn hlog
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hl := Real.log_nonneg hn1
  simp only [Real.norm_eq_abs, abs_of_nonneg hl, abs_of_pos hn0] at hlog
  let k := ⌊(2 - ε) * Real.logb 2 n⌋₊
  have hk : (k : ℝ) ≤ (2 - ε) * Real.log n / L := by
    have hf := Nat.floor_le (mul_nonneg (sub_nonneg.mpr he2) (div_nonneg hl hL.le))
    simpa [k, Real.logb, L, mul_div_assoc] using hf
  have hk' : (k : ℝ) ≤ 2 / L * Real.log n := by
    apply hk.trans
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hl) hL.le
  have hkn : k ≤ n := by
    apply (Nat.cast_le (α := ℝ)).mp
    apply hk'.trans
    rw [div_mul_eq_mul_div, div_le_iff₀ hL]
    linarith only [hlog, mul_comm L (n : ℝ)]
  have hhalf : ((k / 2 : ℕ) : ℝ) * 2 ≤ (k : ℝ) := by exact_mod_cast Nat.div_mul_le_self k 2
  have ha : (2 : ℝ) ^ (k / 2) ≤ (n : ℝ) ^ (1 - ε / 2) := by
    rw [Real.rpow_def_of_pos hn0]
    have hexp := Real.exp_nat_mul L (k / 2)
    rw [show Real.exp L = 2 from Real.exp_log (by norm_num)] at hexp
    rw [← hexp, Real.exp_le_exp]
    have hkL := (le_div_iff₀ hL).mp hk
    nlinarith only [hkL, mul_le_mul_of_nonneg_right hhalf hL.le]
  have hrate : (k : ℝ) * ((2 : ℝ) ^ (k / 2) * k / n) ≤ rate n := by
    have hs := pow_le_pow_left₀ (Nat.cast_nonneg k) hk' 2
    calc
      _ = (2 : ℝ) ^ (k / 2) * (k : ℝ)^2 / n := by ring
      _ ≤ (n : ℝ) ^ (1 - ε / 2) * (2 / L * Real.log n)^2 / n := by gcongr
      _ = _ := by rw [Real.rpow_sub hn0, Real.rpow_one]; dsimp [rate]; field_simp
  apply (cliqueFree_probability_le (by omega : 0 < n) hkn).trans
  apply sub_le_sub_right
  calc
    _ ≤ (Real.exp ((2 : ℝ) ^ (k / 2) * k / n)) ^ k :=
      pow_le_pow_left₀ (by positivity) (by simpa [add_comm] using Real.add_one_le_exp ((2 : ℝ) ^ (k / 2) * k / n)) _
    _ ≤ _ := by rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.mpr hrate

end ProbabilisticCombinatorics.Examples.Clique
