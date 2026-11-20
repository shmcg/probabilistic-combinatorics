/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

public import ProbabilisticCombinatorics.Method.FirstMoment.Basic
public import ProbabilisticCombinatorics.RandomGraph.HomogeneousProbability

@[expose] public section

/-!
# Ramsey's first-moment argument, with an explicit random variable

For each `k`-element vertex set there are two indicators: one for being a clique
and one for being an independent set. Their sum `badCount` is a natural number.
Its real expectation is `2 * choose(n,k) * (1/2)^(choose(k,2))`.

The main proof has three steps: choose this count, bound its expectation, and
apply Markov through `exists_zero_of_expectation_lt_one`. The fixed-set
probabilities are proved for Mathlib's actual binomial random graph law in
`RamseyProbabilityHelpers`; they are not assumptions of the result.
-/

open MeasureTheory ProbabilityTheory SimpleGraph unitInterval
open scoped BigOperators Classical ENNReal ProbabilityTheory

namespace ProbabilisticCombinatorics.Examples.Ramsey

open FirstMoment RamseyProbabilityHelpers

/-- A tag records whether a `k`-element vertex set should be a clique or independent. -/
def witnesses (n k : ℕ) : Finset (Bool × Finset (Fin n)) :=
  (Finset.univ : Finset Bool) ×ˢ (Finset.univ : Finset (Fin n)).powersetCard k

def badEvent {n : ℕ} (i : Bool × Finset (Fin n)) : Set (SimpleGraph (Fin n)) :=
  if i.1 then {G | G.IsClique i.2} else {G | G.IsIndepSet i.2}

/-- The indicator random variable for one tagged vertex set. -/
noncomputable def Xi {n : ℕ} (i : Bool × Finset (Fin n)) :
    SimpleGraph (Fin n) → ℕ :=
  (badEvent i).indicator 1

/-- `X = ∑ i, Xᵢ`: the number of `k`-cliques plus `k`-vertex independent sets. -/
noncomputable def badCount (n k : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  ∑ i ∈ witnesses n k, Xi i G

/-- Count zero says exactly that the graph has the desired property. -/
theorem badCount_eq_zero_iff (n k : ℕ) (G : SimpleGraph (Fin n)) :
    badCount n k G = 0 ↔ G.CliqueFree k ∧ G.IndepSetFree k := by
  have hzero : badCount n k G = 0 ↔
      ∀ i ∈ witnesses n k, G ∉ badEvent i := by
    simp [badCount, Xi, Set.indicator_apply]
  rw [hzero]
  constructor
  · intro hnone
    constructor
    · intro S hS
      exact hnone (true, S) (by simp [witnesses, hS.card_eq])
        (by simpa [badEvent] using hS.isClique)
    · intro S hS
      exact hnone (false, S) (by simp [witnesses, hS.card_eq])
        (by simpa [badEvent] using hS.isIndepSet)
  · rintro ⟨hclique, hindep⟩ i hi hG
    have hcard : i.2.card = k := by simpa [witnesses] using hi
    rcases i with ⟨b, S⟩
    cases b
    · exact hindep S ⟨by simpa [badEvent] using hG, hcard⟩
    · exact hclique S ⟨by simpa [badEvent] using hG, hcard⟩

private theorem measurableSet_badEvent {n : ℕ} (i : Bool × Finset (Fin n)) :
    MeasurableSet (badEvent i) := by
  rcases i with ⟨b, S⟩
  cases b
  · simpa [badEvent] using measurableSet_independent S
  · simpa [badEvent] using measurableSet_clique S

theorem integrable_badCount (n k : ℕ)
    (μ : Measure (SimpleGraph (Fin n))) [IsFiniteMeasure μ] :
    Integrable (fun G ↦ (badCount n k G : ℝ)) μ :=
  integrable_sum_indicators μ (witnesses n k) badEvent
    (fun i _ ↦ measurableSet_badEvent i)

/-- The edge probability `1/2`, as an element of the unit interval. -/
noncomputable def fairEdgeProbability : I := ⟨1 / 2, by constructor <;> norm_num⟩

@[simp] private theorem symm_fairEdgeProbability :
    σ fairEdgeProbability = fairEdgeProbability := by
  apply Subtype.ext
  norm_num [coe_symm_eq, fairEdgeProbability]

private theorem fixed_clique_probability (n k : ℕ)
    (S : Finset (Fin n)) (hS : S.card = k) :
    (SimpleGraph.binomialRandom (Fin n) fairEdgeProbability).real
        {G | G.IsClique S} =
      (1 / 2 : ℝ) ^ (k.choose 2) := by
  simpa [measureReal_def, hS, fairEdgeProbability] using
    congrArg ENNReal.toReal (clique_probability fairEdgeProbability S)

private theorem fixed_independent_probability (n k : ℕ)
    (S : Finset (Fin n)) (hS : S.card = k) :
    (SimpleGraph.binomialRandom (Fin n) fairEdgeProbability).real
        {G | G.IsIndepSet S} =
      (1 / 2 : ℝ) ^ (k.choose 2) := by
  have h := independent_probability fairEdgeProbability S
  rw [symm_fairEdgeProbability] at h
  simpa [measureReal_def, hS, fairEdgeProbability] using congrArg ENNReal.toReal h

private theorem fixed_event_probability (n k : ℕ)
    (i : Bool × Finset (Fin n)) (hi : i ∈ witnesses n k) :
    (SimpleGraph.binomialRandom (Fin n) fairEdgeProbability).real (badEvent i) =
      (1 / 2 : ℝ) ^ (k.choose 2) := by
  have hcard : i.2.card = k := by simpa [witnesses] using hi
  rcases i with ⟨b, S⟩
  cases b
  · simpa [badEvent] using fixed_independent_probability n k S hcard
  · simpa [badEvent] using fixed_clique_probability n k S hcard

/-- Linearity gives `E[X] = ∑ E[Xᵢ] = 2 * choose(n,k) * 2^(-choose(k,2))`.
The events indexed by different vertex sets need not be independent. -/
theorem expected_badCount (n k : ℕ) :
    (SimpleGraph.binomialRandom (Fin n) fairEdgeProbability)[badCount n k] =
      (2 * (n.choose k : ℝ)) * (1 / 2 : ℝ) ^ (k.choose 2) := by
  calc
    _ = ∑ i ∈ witnesses n k,
        (SimpleGraph.binomialRandom (Fin n) fairEdgeProbability).real (badEvent i) :=
      expectation_sum_indicators _ (witnesses n k) badEvent
        (fun i _ ↦ measurableSet_badEvent i)
    _ = ∑ _i ∈ witnesses n k, (1 / 2 : ℝ) ^ (k.choose 2) :=
      Finset.sum_congr rfl fun i hi ↦ fixed_event_probability n k i hi
    _ = _ := by simp [witnesses, Finset.card_powersetCard, nsmul_eq_mul]

/-- The same first moment bounds the probability that the desired property fails. -/
theorem ramsey_failure_probability_le (n k : ℕ) :
    (SimpleGraph.binomialRandom (Fin n) fairEdgeProbability).real
        {G | ¬(G.CliqueFree k ∧ G.IndepSetFree k)} ≤
      (2 * (n.choose k : ℝ)) * (1 / 2 : ℝ) ^ (k.choose 2) := by
  have hbad : {G : SimpleGraph (Fin n) | ¬(G.CliqueFree k ∧ G.IndepSetFree k)} =
      {G | badCount n k G ≠ 0} := by
    ext G
    exact not_congr (badCount_eq_zero_iff n k G).symm
  rw [hbad, ← expected_badCount]
  exact measure_ne_zero_le_expectation _ _ (integrable_badCount n k _)

private theorem expectation_lt_one_of_integer_budget {n k : ℕ}
    (h : 2 * n.choose k < 2 ^ (k.choose 2)) :
    (2 * (n.choose k : ℝ)) * (1 / 2 : ℝ) ^ (k.choose 2) < 1 := by
  rw [div_pow, one_pow, mul_one_div, div_lt_one (by positivity)]
  exact_mod_cast h

/-- The exact integer Ramsey criterion, proved by the first moment of `badCount`. -/
theorem ramsey_lower_bound (n k : ℕ)
    (budget : 2 * n.choose k < 2 ^ (k.choose 2)) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ G.IndepSetFree k := by
  -- 1. Choose the random graph and the number of bad configurations.
  let μ := SimpleGraph.binomialRandom (Fin n) fairEdgeProbability
  let X := badCount n k
  -- 2. Compute the expectation by linearity and show it is below one.
  have hEX : (μ[X] : ℝ) < 1 :=
    (expected_badCount n k).trans_lt (expectation_lt_one_of_integer_budget budget)
  -- 3. Markov gives an outcome with no bad configurations.
  obtain ⟨G, hG⟩ := exists_zero_of_expectation_lt_one μ X (integrable_badCount n k μ) hEX
  exact ⟨G, (badCount_eq_zero_iff n k G).mp hG⟩

/-- Sixteen vertices can avoid both six-cliques and independent sets of size six. -/
theorem sixteen_without_homogeneous_six :
    ∃ G : SimpleGraph (Fin 16), G.CliqueFree 6 ∧ G.IndepSetFree 6 := by
  apply ramsey_lower_bound
  norm_num [Nat.choose_eq_factorial_div_factorial]

end ProbabilisticCombinatorics.Examples.Ramsey
