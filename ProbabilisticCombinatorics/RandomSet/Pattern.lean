/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

public import Mathlib.Probability.Distributions.SetBernoulli

/-!
# Finite patterns in a Bernoulli random set

Within the ground set, a prescription on finitely many coordinates has the product of its
one-coordinate probabilities. The ground set and ambient type may both be infinite.
-/

public section

open MeasureTheory Measure unitInterval
open scoped BigOperators ENNReal

namespace ProbabilityTheory

/-- Probability that every element of `present` is selected and every element of
`absent` is omitted. The other coordinates are unrestricted. -/
theorem setBernoulli_pattern {ι : Type*} {u : Set ι} (p : I)
    (present absent : Finset ι) (hd : Disjoint present absent)
    (hp : (present : Set ι) ⊆ u) (ha : (absent : Set ι) ⊆ u) :
    setBer(u, p) {s | (present : Set ι) ⊆ s ∧ (absent : Set ι) ⊆ sᶜ} =
      (toNNReal p : ℝ≥0∞) ^ present.card * (toNNReal (σ p) : ℝ≥0∞) ^ absent.card := by
  classical
  rw [setBernoulli_apply']
  let value (i : ι) : Set Prop := {i ∈ present}
  have cylinder_eq : (fun x : ι → Prop ↦ {i | x i}) ⁻¹'
      {s | (present : Set ι) ⊆ s ∧ (absent : Set ι) ⊆ sᶜ} =
      Set.pi (↑(present ∪ absent) : Set ι) value := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.subset_def, Finset.mem_coe,
      Set.mem_compl_iff, Set.mem_pi, Finset.mem_union, value, Set.mem_singleton_iff, eq_iff_iff]
    grind [Finset.disjoint_left]
  rw [cylinder_eq, infinitePi_pi _ (fun _ _ ↦ measurableSet_singleton _), Finset.prod_union hd]
  congr 1
  · calc
      _ = ∏ _i ∈ present, (toNNReal p : ℝ≥0∞) := by
        refine Finset.prod_congr rfl fun i hi ↦ ?_
        simp [hi, hp hi]
      _ = _ := by simp
  · calc
      _ = ∏ _i ∈ absent, (toNNReal (σ p) : ℝ≥0∞) := by
        refine Finset.prod_congr rfl fun i hi ↦ ?_
        have hn : i ∉ present := fun h ↦ Finset.disjoint_left.mp hd h hi
        simp [hn, ha hi]
      _ = _ := by simp

/-- Inclusion probability of a finite subset of the ground set, as a real number. -/
theorem setBernoulli_real_subset {ι : Type*} {u e : Set ι} (p : I) (he : e.Finite)
    (heu : e ⊆ u) : setBer(u, p).real {s | e ⊆ s} = (p : ℝ) ^ e.ncard := by
  classical
  have h := setBernoulli_pattern (u := u) p he.toFinset ∅ (by simp) (by simpa) (by simp)
  simpa [measureReal_def, Set.ncard_eq_toFinset_card e he] using congrArg ENNReal.toReal h

end ProbabilityTheory
