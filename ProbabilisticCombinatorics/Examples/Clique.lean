/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

public import ProbabilisticCombinatorics.Method.FirstMoment.Basic
public import ProbabilisticCombinatorics.RandomGraph.HomogeneousProbability

@[expose] public section

open MeasureTheory SimpleGraph unitInterval
open scoped BigOperators Classical ProbabilityTheory ENNReal

namespace ProbabilisticCombinatorics.Examples.Clique

open FirstMoment RamseyProbabilityHelpers

/-- The candidate vertex sets for a clique of size `k`. -/
def vertexSets (n k : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powersetCard k

/-- The event that a fixed vertex set spans a clique. -/
def cliqueEvent {n : ℕ} (S : Finset (Fin n)) : Set (SimpleGraph (Fin n)) :=
  {G | G.IsClique S}

/-- Count the `k`-cliques by summing their natural-valued indicators. -/
noncomputable def cliqueCount (n k : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  ∑ S ∈ vertexSets n k, (cliqueEvent S).indicator (1 : SimpleGraph (Fin n) → ℕ) G

/-- Zero counted cliques is exactly the usual graph predicate. -/
theorem cliqueCount_eq_zero (n k : ℕ) (G : SimpleGraph (Fin n)) :
    cliqueCount n k G = 0 ↔ G.CliqueFree k := by
  rw [cliqueCount, sum_indicators_eq_zero]
  constructor
  · intro h S hS
    exact h S (by simp [vertexSets, hS.card_eq]) hS.isClique
  · intro h S hS hClique
    have hcard : S.card = k := by simpa [vertexSets] using hS
    exact h S ⟨hClique, hcard⟩

/-- Linearity and the fixed-set probability compute the real expected clique count. -/
theorem expected_cliqueCount (n k : ℕ) (p : I) :
    (SimpleGraph.binomialRandom (Fin n) p)[cliqueCount n k] =
      (n.choose k : ℝ) * (p : ℝ) ^ (k.choose 2) := by
  let μ := SimpleGraph.binomialRandom (Fin n) p
  calc
    _ = ∑ S ∈ vertexSets n k, μ.real (cliqueEvent S) :=
      expectation_sum_indicators μ (vertexSets n k) cliqueEvent
        (fun S _ ↦ measurableSet_clique S)
    _ = ∑ _S ∈ vertexSets n k, (p : ℝ) ^ (k.choose 2) := by
      refine Finset.sum_congr rfl fun S hS ↦ ?_
      have hcard : S.card = k := by simpa [vertexSets] using hS
      simpa [μ, cliqueEvent, measureReal_def, hcard] using
        congrArg ENNReal.toReal (clique_probability p S)
    _ = _ := by simp [vertexSets, Finset.card_powersetCard, nsmul_eq_mul]

/-- Apply the first-moment inequality to the clique count in `G(n,p)`. -/
theorem clique_failure_probability_le (n k : ℕ) (p : I) :
    (SimpleGraph.binomialRandom (Fin n) p).real {G | ¬G.CliqueFree k} ≤
      (n.choose k : ℝ) * (p : ℝ) ^ (k.choose 2) := by
  let μ := SimpleGraph.binomialRandom (Fin n) p
  have hX : Integrable (fun G ↦ (cliqueCount n k G : ℝ)) μ :=
    integrable_sum_indicators μ (vertexSets n k) cliqueEvent
      (fun S _ ↦ measurableSet_clique S)
  have hEX : (μ[cliqueCount n k] : ℝ) =
      (n.choose k : ℝ) * (p : ℝ) ^ (k.choose 2) := expected_cliqueCount n k p
  calc
    _ = μ.real {G | cliqueCount n k G ≠ 0} := by
      congr 1
      ext G
      exact (not_congr (cliqueCount_eq_zero n k G)).symm
    _ ≤ μ[cliqueCount n k] :=
      FirstMoment.measure_ne_zero_le_expectation μ (cliqueCount n k) hX
    _ = _ := hEX

end ProbabilisticCombinatorics.Examples.Clique
