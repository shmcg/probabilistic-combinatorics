/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

public import ProbabilisticCombinatorics.Hypergraph.IndependentSet
public import ProbabilisticCombinatorics.Method.Alteration
public import ProbabilisticCombinatorics.Method.FirstMoment.Basic
public import ProbabilisticCombinatorics.RandomSet.Pattern
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Independent sets in finite hypergraphs by alteration

Sample vertices independently with probability `p`. The deterministic deletion lemma
charges at most one lost vertex for each fully sampled edge. An edge of size `k` is fully
sampled with probability `p ^ k`, even when it overlaps other edges.
-/

public section
noncomputable section

open MeasureTheory ProbabilityTheory unitInterval ProbabilisticCombinatorics
open scoped Classical BigOperators

namespace Hypergraph

variable {α : Type*} (H : Hypergraph α)

/-- With independent vertex sampling, some independent set retains at least the expected
number of sampled vertices minus the expected number of fully sampled edges. -/
theorem exists_isIndepSet_of_sampling (hV : H.vertexSet.Finite) (hne : ∅ ∉ H.edgeSet) (p : I) :
    ∃ t, H.IsIndepSet t ∧
      (p : ℝ) * H.vertexSet.ncard - (∑ᶠ e ∈ H.edgeSet, (p : ℝ) ^ e.ncard) ≤ t.ncard := by
  classical
  have hE := hV.powerset.subset H.edgeSet_subset_powerset_vertexSet
  let μ := setBernoulli H.vertexSet p
  let picked (v : α) : Set (Set α) := {S | v ∈ S}
  let contained (e : Set α) : Set (Set α) := {S | e ⊆ S}
  let sample (S : Set α) := hV.toFinset.filter fun v ↦ S ∈ picked v
  let bad (S : Set α) := hE.toFinset.filter fun e ↦ S ∈ contained e
  have hsample S : (sample S : Set α) = H.vertexSet ∩ S := by ext; simp [sample, picked]
  have hbad S : (bad S : Set (Set α)) = {e ∈ H.edgeSet | e ⊆ ↑(sample S)} := by
    ext e
    simp only [bad, contained, Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset,
      Set.mem_ofPred_eq, hsample, Set.subset_inter_iff]
    exact ⟨fun h ↦ ⟨h.1, H.subset_vertexSet_of_mem_edgeSet h.1, h.2⟩,
      fun h ↦ ⟨h.1, h.2.2⟩⟩
  have hsampleV S : (sample S : Set α) ⊆ H.vertexSet := (hsample S) ▸ Set.inter_subset_left
  choose repair _ hgood hsize using fun S ↦
    H.exists_isIndepSet_subset hne (sample S).finite_toSet (hsampleV S)
  have hgain S : ((sample S).card : ℝ) - (bad S).card ≤ (repair S).ncard := by
    apply sub_le_iff_le_add.mpr
    exact_mod_cast (by simpa only [← hbad S, Set.ncard_coe_finset] using hsize S :
      (sample S).card ≤ (repair S).ncard + (bad S).card)
  have hpick v (_ : v ∈ hV.toFinset) : MeasurableSet (picked v) := measurableSet_mem v
  have hcont e (he : e ∈ hE.toFinset) : MeasurableSet (contained e) := by
    have hfin := hV.subset (H.subset_vertexSet_of_mem_edgeSet (hE.mem_toFinset.mp he))
    have h : contained e = ⋂ v ∈ e, picked v := by ext; simp [contained, picked, Set.subset_def]
    rw [h]
    exact hfin.measurableSet_biInter fun v _ ↦ measurableSet_mem v
  have hX := FirstMoment.integrable_card_filter μ _ picked hpick
  have hY := FirstMoment.integrable_card_filter μ _ contained hcont
  obtain ⟨t, ht, h⟩ := Alteration.exists_feasible_ge_expectation μ repair H.IsIndepSet
    (fun t ↦ (t.ncard : ℝ)) (fun S ↦ ((sample S).card : ℝ) - (bad S).card)
    (hX.sub hY) hgood hgain
  have hvertex v (hv : v ∈ hV.toFinset) : μ.real (picked v) = (p : ℝ) := by
    have hsub := Set.singleton_subset_iff.mpr (hV.mem_toFinset.mp hv)
    simpa [μ, picked] using setBernoulli_real_subset p (Set.finite_singleton v) hsub
  have hedge e (he : e ∈ hE.toFinset) : μ.real (contained e) = (p : ℝ) ^ e.ncard := by
    have hsub := H.subset_vertexSet_of_mem_edgeSet (hE.mem_toFinset.mp he)
    exact setBernoulli_real_subset p (hV.subset hsub) hsub
  refine ⟨t, ht, ?_⟩
  rw [integral_sub hX hY, FirstMoment.expectation_card_filter μ _ _ hpick,
    FirstMoment.expectation_card_filter μ _ _ hcont, Finset.sum_congr rfl hvertex,
    Finset.sum_congr rfl hedge] at h
  simpa [finsum_mem_eq_finite_toFinset_sum _ hE, Set.ncard_eq_toFinset_card _ hV,
    nsmul_eq_mul, mul_comm] using h

/-- For an `r`-uniform hypergraph, the expected number of fully sampled edges is `m * p^r`. -/
theorem exists_isIndepSet_of_uniform (hV : H.vertexSet.Finite) {r : ℕ} (hr : 0 < r)
    (huniform : ∀ e ∈ H.edgeSet, e.ncard = r) (p : I) :
    ∃ t, H.IsIndepSet t ∧
      (p : ℝ) * H.vertexSet.ncard - H.edgeSet.ncard * (p : ℝ) ^ r ≤ t.ncard := by
  have hne : ∅ ∉ H.edgeSet := by
    intro h
    have hzero := huniform ∅ h
    simp only [Set.ncard_empty] at hzero
    omega
  obtain ⟨t, ht, h⟩ := H.exists_isIndepSet_of_sampling hV hne p
  have hE := hV.powerset.subset H.edgeSet_subset_powerset_vertexSet
  rw [finsum_mem_eq_finite_toFinset_sum _ hE, Finset.sum_congr rfl
    (fun e he ↦ congrArg (fun k : ℕ ↦ (p : ℝ) ^ k) (huniform e (hE.mem_toFinset.mp he)))] at h
  exact ⟨t, ht, by simpa [Set.ncard_eq_toFinset_card _ hE, nsmul_eq_mul] using h⟩

/-- If `d ≥ 1` bounds the average degree of an `r`-uniform hypergraph, choose
`p = d ^ (-1 / (r - 1))`. The incidence bound `r * m ≤ d * n` also covers empty ground sets. -/
theorem exists_isIndepSet_of_averageDegree_le (hV : H.vertexSet.Finite) {r : ℕ} (hr : 2 ≤ r)
    (huniform : ∀ e ∈ H.edgeSet, e.ncard = r) {d : ℝ} (hd : 1 ≤ d)
    (hdeg : (r : ℝ) * H.edgeSet.ncard ≤ d * H.vertexSet.ncard) :
    ∃ t, H.IsIndepSet t ∧
      (1 - 1 / (r : ℝ)) * H.vertexSet.ncard * d ^ (-1 / ((r : ℝ) - 1)) ≤ t.ncard := by
  have hr' : (1 : ℝ) < r := by exact_mod_cast (show 1 < r by omega)
  have hd' : 0 < d := by linarith
  let p : I := ⟨d ^ (-1 / ((r : ℝ) - 1)), Real.rpow_nonneg hd'.le _,
    Real.rpow_le_one_of_one_le_of_nonpos hd (div_nonpos_of_nonpos_of_nonneg (by norm_num)
      (sub_nonneg.mpr hr'.le))⟩
  have hpow : (p : ℝ) ^ r = (p : ℝ) / d := by
    have hexp : (r : ℝ) - 1 ≠ 0 := (sub_pos.mpr hr').ne'
    have hpred : (p : ℝ) ^ (r - 1) = d⁻¹ := by
      change (d ^ (-1 / ((r : ℝ) - 1))) ^ (r - 1 : ℕ) = d⁻¹
      rw [← Real.rpow_natCast, ← Real.rpow_mul hd'.le, Nat.cast_sub (by omega : 1 ≤ r),
        Nat.cast_one, div_mul_cancel₀ _ hexp, Real.rpow_neg_one]
    calc
      (p : ℝ) ^ r = (p : ℝ) ^ (r - 1) * (p : ℝ) := by rw [← pow_succ]; congr 1; omega
      _ = (p : ℝ) / d := by rw [hpred, div_eq_mul_inv, mul_comm]
  obtain ⟨t, ht, h⟩ := H.exists_isIndepSet_of_uniform hV (by omega) huniform p
  have hcharge : H.edgeSet.ncard * ((p : ℝ) / d) ≤ H.vertexSet.ncard * (p : ℝ) / r := by
    apply (le_div_iff₀ (by linarith : (0 : ℝ) < r)).mpr
    rw [mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ hd']
    nlinarith [mul_le_mul_of_nonneg_right hdeg p.2.1]
  refine ⟨t, ht, le_trans ?_ h⟩
  rw [hpow]
  calc
    (1 - 1 / (r : ℝ)) * H.vertexSet.ncard * (p : ℝ) =
        (p : ℝ) * H.vertexSet.ncard - H.vertexSet.ncard * (p : ℝ) / r := by ring
    _ ≤ _ := sub_le_sub_left hcharge _

/-- In a 3-uniform hypergraph with average degree at most `d ≥ 1`, some independent set
has size at least `2n / (3√d)`. -/
theorem exists_isIndepSet_of_three_uniform (hV : H.vertexSet.Finite)
    (hthree : ∀ e ∈ H.edgeSet, e.ncard = 3) {d : ℝ} (hd : 1 ≤ d)
    (hdeg : 3 * (H.edgeSet.ncard : ℝ) ≤ d * H.vertexSet.ncard) :
    ∃ t, H.IsIndepSet t ∧ 2 * H.vertexSet.ncard / (3 * Real.sqrt d) ≤ t.ncard := by
  obtain ⟨t, ht, h⟩ := H.exists_isIndepSet_of_averageDegree_le hV (r := 3) (by decide) hthree hd
    (by simpa using hdeg)
  refine ⟨t, ht, le_trans ?_ h⟩
  norm_num
  rw [Real.rpow_neg (by linarith : 0 ≤ d), ← Real.sqrt_eq_rpow]
  exact le_of_eq (by ring)

end Hypergraph
