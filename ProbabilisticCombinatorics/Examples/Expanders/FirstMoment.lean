/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

public import ProbabilisticCombinatorics.Method.FirstMoment.Asymptotics
public import ProbabilisticCombinatorics.Probability.UniformPermutation
public import ProbabilisticCombinatorics.Examples.Expanders.Model
public import ProbabilisticCombinatorics.Examples.Expanders.Graph
public import ProbabilisticCombinatorics.Examples.Expanders.Estimates
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# Expanders by the first-moment method

Choose eight independent uniform permutations of `Fin n`. They give eight
perfect matchings between two copies of `Fin n`. Count certificates consisting
of a side, a nonempty source set `S` of size at most `n / 8`, and a target set
`T` of size `2 * S.card` containing the whole neighborhood of `S`.

The expected certificate count is at most `27 / (28 * n)`. Hence the graph
has the two-sided small-set expansion property with probability at least
`1 - 27 / (28 * n)`. This proves existence for every `n` and convergence of the
success probability to one, using the existing quantitative first-moment API.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Classical ProbabilityTheory ENNReal Topology

namespace ProbabilisticCombinatorics.Expanders

open FirstMoment

/-- The actual product law of eight independent uniform perfect matchings. -/
def matchingMeasure (n : ℕ) : Measure (Matchings n) :=
  Measure.pi fun _ : Fin 8 ↦ UniformPermutation.measure n

instance (n : ℕ) : IsProbabilityMeasure (matchingMeasure n) := by
  unfold matchingMeasure
  infer_instance

/-- The eight matchings are independent. A fixed certificate has the eighth
power of the corresponding one-permutation containment probability. -/
theorem badEvent_probability {n : ℕ} (c : Certificate n) :
    (matchingMeasure n).real (badEvent c) =
      ((c.2.2.card.choose c.2.1.card : ℝ) / (n.choose c.2.1.card : ℝ)) ^ 8 := by
  let E : Set (Equiv.Perm (Fin n)) :=
    {τ | ∀ v ∈ c.2.1, (if c.1 then τ else τ.symm) v ∈ c.2.2}
  have hrect : badEvent c = Set.univ.pi (fun _ : Fin 8 ↦ E) := by
    ext π
    simp [badEvent, neighbors_subset_iff, Set.mem_pi, E, oriented]
  have hsingle : (UniformPermutation.measure n).real E =
      (c.2.2.card.choose c.2.1.card : ℝ) / (n.choose c.2.1.card : ℝ) := by
    cases hside : c.1 with
    | false => simpa [E, hside] using
        UniformPermutation.inverse_containment_probability c.2.1 c.2.2
    | true => simpa [E, hside] using
        UniformPermutation.containment_probability c.2.1 c.2.2
  rw [measureReal_def, hrect, matchingMeasure, Measure.pi_pi]
  simpa [measureReal_def] using congrArg (fun x : ℝ ↦ x ^ 8) hsingle

/-- Sampling without replacement only improves the elementary containment bound. -/
theorem badEvent_probability_le {n : ℕ} (hn : 0 < n) (c : Certificate n) :
    (matchingMeasure n).real (badEvent c) ≤
      ((c.2.2.card : ℝ) / n) ^ (8 * c.2.1.card) := by
  rw [badEvent_probability]
  have hsingle := UniformPermutation.containment_probability_le hn c.2.1 c.2.2
  rw [UniformPermutation.containment_probability] at hsingle
  have hnonneg : 0 ≤
      (c.2.2.card.choose c.2.1.card : ℝ) / (n.choose c.2.1.card : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc
    _ ≤ (((c.2.2.card : ℝ) / n) ^ c.2.1.card) ^ 8 :=
      pow_le_pow_left₀ hnonneg hsingle 8
    _ = _ := by rw [← pow_mul, Nat.mul_comm]

/-- Linearity of expectation at one source-set size. -/
theorem expected_badCountAt (n s : ℕ) :
    (matchingMeasure n)[badCountAt n s] =
      2 * (n.choose s : ℝ) * (n.choose (2 * s) : ℝ) *
        ((Nat.choose (2 * s) s : ℝ) / (n.choose s : ℝ)) ^ 8 := by
  calc
    _ = ∑ c ∈ certificates n s, (matchingMeasure n).real (badEvent c) :=
      expectation_sum_indicators _ _ badEvent
        (fun _ _ ↦ (Set.toFinite _).measurableSet)
    _ = ∑ _c ∈ certificates n s,
        ((Nat.choose (2 * s) s : ℝ) / (n.choose s : ℝ)) ^ 8 := by
      apply Finset.sum_congr rfl
      intro c hc
      rcases (mem_certificates s c).mp hc with ⟨hS, hT⟩
      rw [badEvent_probability, hS, hT]
    _ = _ := by simp [card_certificates, nsmul_eq_mul]

/-- The contribution of one source-set size, after the containment estimate. -/
theorem expected_badCountAt_le (n s : ℕ) (hn : 0 < n) :
    (matchingMeasure n)[badCountAt n s] ≤
      2 * (n.choose s : ℝ) * (n.choose (2 * s) : ℝ) *
        ((2 * (s : ℝ)) / n) ^ (8 * s) := by
  calc
    _ = ∑ c ∈ certificates n s, (matchingMeasure n).real (badEvent c) :=
      expectation_sum_indicators _ _ badEvent
        (fun _ _ ↦ (Set.toFinite _).measurableSet)
    _ ≤ ∑ _c ∈ certificates n s, ((2 * (s : ℝ)) / n) ^ (8 * s) := by
      apply Finset.sum_le_sum
      intro c hc
      rcases (mem_certificates s c).mp hc with ⟨hS, hT⟩
      simpa only [hS, hT, Nat.cast_mul, Nat.cast_ofNat] using
        badEvent_probability_le hn c
    _ = _ := by simp [card_certificates, nsmul_eq_mul]

/-- Add the contributions of all source-set sizes. -/
theorem expectation_badCount_sum (n : ℕ) :
    ((matchingMeasure n)[badCount n] : ℝ) =
      ∑ s ∈ Finset.Icc 1 (n / 8), (matchingMeasure n)[badCountAt n s] := by
  simp only [badCount, Nat.cast_sum]
  exact integral_finsetSum _ fun _ _ ↦ Integrable.of_finite

/-- The exact expectation, before replacing sampling without replacement by
the simpler power bound. -/
theorem expected_badCount (n : ℕ) :
    (matchingMeasure n)[badCount n] =
      2 * (∑ s ∈ Finset.Icc 1 (n / 8),
        (n.choose s : ℝ) * (n.choose (2 * s) : ℝ) *
          ((Nat.choose (2 * s) s : ℝ) / (n.choose s : ℝ)) ^ 8) := by
  rw [expectation_badCount_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [expected_badCountAt]
  ring

/-- The first-moment budget before its purely numerical estimate. -/
theorem expected_badCount_le_sum (n : ℕ) (hn : 0 < n) :
    (matchingMeasure n)[badCount n] ≤
      2 * (∑ s ∈ Finset.Icc 1 (n / 8),
        (n.choose s : ℝ) * (n.choose (2 * s) : ℝ) *
          ((2 * (s : ℝ)) / n) ^ (8 * s)) := by
  rw [expectation_badCount_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  simpa only [mul_assoc] using expected_badCountAt_le n s hn

/-- The explicit, vanishing expectation budget for bad expansion certificates. -/
theorem expected_badCount_le (n : ℕ) (hn : 0 < n) :
    (matchingMeasure n)[badCount n] ≤ 27 / (28 * (n : ℝ)) :=
  (expected_badCount_le_sum n hn).trans (expander_budget_le n hn)

/-- A quantitative failure bound from Markov at threshold one. -/
theorem expansion_failure_probability_le (n : ℕ) (hn : 0 < n) :
    (matchingMeasure n).real {π | ¬ Expands π} ≤ 27 / (28 * (n : ℝ)) := by
  simpa only [ne_eq, badCount_eq_zero_iff_expands] using
    measure_ne_zero_le_of_expectation_le (matchingMeasure n) (badCount n)
      Integrable.of_finite (expected_badCount_le n hn)

/-- Keep the quantitative success probability, rather than just existence. -/
theorem expansion_success_probability_ge (n : ℕ) (hn : 0 < n) :
    1 - 27 / (28 * (n : ℝ)) ≤ (matchingMeasure n).real {π | Expands π} := by
  simpa only [badCount_eq_zero_iff_expands] using
    one_sub_le_measure_zero_of_expectation_le (matchingMeasure n) (badCount n)
      Integrable.of_finite (expected_badCount_le n hn)

/-- The explicit budget is strictly below one for every positive `n`. -/
theorem expander_error_lt_one (n : ℕ) (hn : 0 < n) :
    27 / (28 * (n : ℝ)) < 1 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  apply (div_lt_one₀ (by positivity : (0 : ℝ) < 28 * n)).mpr
  linarith

/-- Eight matchings with the two-sided small-set expansion property exist
for every `n`. The empty graph is handled by its vacuous expansion condition. -/
theorem exists_expanding_matchings (n : ℕ) : ∃ π : Matchings n, Expands π := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨fun _ ↦ Equiv.refl _, ?_⟩
    intro side S hS hsmall
    omega
  · obtain ⟨π, hπ⟩ := exists_zero_of_expectation_lt_one (matchingMeasure n)
      (badCount n) Integrable.of_finite
      ((expected_badCount_le n hn).trans_lt (expander_error_lt_one n hn))
    exact ⟨π, (badCount_eq_zero_iff_expands π).mp hπ⟩

/-- A simple bipartite graph of maximum degree eight with the stated two-sided
small-set vertex expansion exists for every size of the two vertex classes. -/
theorem exists_bipartite_expander (n : ℕ) :
    ∃ G : SimpleGraph (Fin n ⊕ Fin n),
      (∀ v, G.degree v ≤ 8) ∧
      (∀ u v : Fin n, ¬ G.Adj (Sum.inl u) (Sum.inl v)) ∧
      (∀ u v : Fin n, ¬ G.Adj (Sum.inr u) (Sum.inr v)) ∧
      (∀ S : Finset (Fin n), 1 ≤ S.card → 8 * S.card ≤ n →
        2 * S.card < ((S.image Sum.inl).biUnion (fun v ↦ G.neighborFinset v)).card) ∧
      (∀ S : Finset (Fin n), 1 ≤ S.card → 8 * S.card ≤ n →
        2 * S.card < ((S.image Sum.inr).biUnion (fun v ↦ G.neighborFinset v)).card) :=
  exists_graph_of_expands (exists_expanding_matchings n)

/-- The finite error budget tends to zero. -/
theorem expander_error_tendsto_zero :
    Tendsto (fun n : ℕ ↦ 27 / (28 * (n : ℝ))) atTop (𝓝 0) := by
  simpa only [div_div] using tendsto_const_div_atTop_nhds_zero_nat (27 / 28 : ℝ)

/-- The expansion property holds with high probability as `n` tends to infinity.
Only the existing generic first-moment limit theorem is needed here. -/
theorem expansion_whp :
    Tendsto (fun n : ℕ ↦ (matchingMeasure n).real {π | Expands π}) atTop (𝓝 1) := by
  simpa only [badCount_eq_zero_iff_expands] using
    tendsto_measure_zero_of_expectation_le matchingMeasure badCount
      (fun n ↦ 27 / (28 * (n : ℝ)))
      (Eventually.of_forall fun _ ↦ inferInstance)
      (Eventually.of_forall fun _ ↦ Integrable.of_finite)
      (eventually_atTop.2 ⟨1, fun n hn ↦ expected_badCount_le n hn⟩)
      expander_error_tendsto_zero

end ProbabilisticCombinatorics.Expanders
