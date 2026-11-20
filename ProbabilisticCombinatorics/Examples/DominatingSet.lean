/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

public import ProbabilisticCombinatorics.Method.Alteration
public import ProbabilisticCombinatorics.RandomSet.Pattern
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Dominating sets by sampling and repair -/

public section
noncomputable section

open MeasureTheory ProbabilityTheory unitInterval Finset
open scoped Classical ENNReal BigOperators

namespace ProbabilisticCombinatorics.DominatingSet

/-- The degree-sequence form of the alteration bound. -/
theorem exists_dominatingSet {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : I) :
    ∃ D : Finset V, (∀ v, v ∈ D ∨ ∃ w ∈ D, G.Adj v w) ∧
      (D.card : ℝ) ≤ Fintype.card V * (p : ℝ) + ∑ v, (1 - (p : ℝ)) ^ (G.degree v + 1) := by
  classical
  let μ := setBernoulli (Set.univ : Set V) p
  let N (v : V) := insert v (G.neighborFinset v)
  let picked (v : V) : Set (Set V) := {S | v ∈ S}
  let missed (v : V) : Set (Set V) := {S | (N v : Set V) ⊆ Sᶜ}
  let repair (S : Set V) := univ.filter fun v ↦ S ∈ picked v ∨ S ∈ missed v
  let charge (v : V) (S : Set V) : ℝ :=
    (picked v).indicator 1 S + (missed v).indicator 1 S
  have hgood S v : v ∈ repair S ∨ ∃ w ∈ repair S, G.Adj v w := by
    by_cases h : ∃ w ∈ N v, w ∈ S
    · obtain ⟨w, hw, hwS⟩ := h
      have hwD : w ∈ repair S := by
        exact mem_filter.mpr ⟨mem_univ _, Or.inl hwS⟩
      rcases mem_insert.mp hw with hv | hn
      · exact Or.inl (hv ▸ hwD)
      · exact Or.inr ⟨w, hwD, (G.mem_neighborFinset _ _).mp hn⟩
    · left
      simp only [repair, mem_filter, mem_univ, true_and]
      exact Or.inr fun w hw hwS ↦ h ⟨w, hw, hwS⟩
  have hcost S : ((repair S).card : ℝ) ≤ ∑ v, charge v S := by
    simp only [repair, ← Finset.sum_boole]
    apply sum_le_sum
    intro v _
    by_cases h : S ∈ picked v <;> by_cases k : S ∈ missed v <;> simp [charge, h, k]
  obtain ⟨D, hD, hc⟩ := Alteration.exists_feasible_le_expectation μ repair
    (fun D ↦ ∀ v, v ∈ D ∨ ∃ w ∈ D, G.Adj v w) (fun D ↦ (D.card : ℝ))
    (fun S ↦ ∑ v, charge v S) Integrable.of_finite hgood hcost
  have hP (v : V) : μ.real (picked v) = (p : ℝ) := by
    have h := setBernoulli_pattern (u := Set.univ) p {v} ∅ (by simp) (by simp) (by simp)
    simpa [μ, picked, measureReal_def] using congrArg ENNReal.toReal h
  have hM (v : V) : μ.real (missed v) = (1 - (p : ℝ)) ^ (G.degree v + 1) := by
    have h := setBernoulli_pattern (u := Set.univ) p ∅ (N v) (by simp) (by simp) (by simp)
    simpa [μ, missed, N, measureReal_def, card_insert_of_notMem, coe_symm_eq,
      G.card_neighborFinset_eq_degree] using congrArg ENNReal.toReal h
  refine ⟨D, hD, hc.trans_eq ?_⟩
  rw [integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)]
  simp only [charge, integral_add Integrable.of_finite Integrable.of_finite,
    integral_indicator_one (Set.toFinite _).measurableSet, hP, hM, sum_add_distrib,
    sum_const, card_univ, nsmul_eq_mul]

/-- The standard logarithmic bound from a lower bound on every degree, including `d = 0`. -/
theorem exists_dominatingSet_of_degree_ge {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (d : ℕ) (hd : ∀ v, d ≤ G.degree v) :
    ∃ D : Finset V, (∀ v, v ∈ D ∨ ∃ w ∈ D, G.Adj v w) ∧
      (D.card : ℝ) ≤ Fintype.card V * (1 + Real.log (d + 1)) / (d + 1) := by
  let z : ℝ := d + 1
  have hz : 0 < z := by dsimp [z]; positivity
  have hz1 : 1 ≤ z := by dsimp [z]; linarith [Nat.cast_nonneg (α := ℝ) d]
  let p : I := ⟨Real.log z / z, div_nonneg (Real.log_nonneg hz1) hz.le,
    (div_le_one hz).mpr ((Real.log_le_sub_one_of_pos hz).trans (by linarith))⟩
  obtain ⟨D, hD, hc⟩ := exists_dominatingSet G p
  have hpow (v : V) : (1 - (p : ℝ)) ^ (G.degree v + 1) ≤ 1 / z := by
    calc
      _ ≤ (1 - (p : ℝ)) ^ (d + 1) := pow_le_pow_of_le_one (by linarith [p.2.2])
        (by linarith [p.2.1]) (by lia [hd v])
      _ ≤ (Real.exp (-(p : ℝ))) ^ (d + 1) := pow_le_pow_left₀
        (by linarith [p.2.2]) (Real.one_sub_le_exp_neg _) _
      _ = 1 / z := by
        rw [← Real.exp_nat_mul]
        change Real.exp ((↑(d + 1 : ℕ) : ℝ) * -(Real.log z / z)) = _
        have hcast : ((d + 1 : ℕ) : ℝ) = z := by simp [z]
        rw [hcast, show z * -(Real.log z / z) = -Real.log z by field_simp,
          Real.exp_neg, Real.exp_log hz, one_div]
  refine ⟨D, hD, hc.trans ?_⟩
  calc
    _ ≤ Fintype.card V * (p : ℝ) + ∑ _v : V, 1 / z :=
      add_le_add_right (Finset.sum_le_sum fun v _ ↦ hpow v) _
    _ = _ := by simp [p, z, nsmul_eq_mul]; ring

end ProbabilisticCombinatorics.DominatingSet
