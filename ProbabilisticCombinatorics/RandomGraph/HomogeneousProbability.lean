/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Sym.Card
public import ProbabilisticCombinatorics.RandomSet.Pattern

@[expose] public section

open MeasureTheory ProbabilityTheory SimpleGraph unitInterval Finset
open scoped ENNReal BigOperators

namespace ProbabilisticCombinatorics.RamseyProbabilityHelpers

variable {V : Type*}

/-- The unordered pairs of distinct vertices from a finite vertex set. -/
private def pairs [DecidableEq V] (s : Finset V) : Finset (Sym2 V) :=
  s.offDiag.image Sym2.mk.uncurry

private theorem mem_pairs [DecidableEq V] {s : Finset V} {a b : V} :
    s(a, b) ∈ pairs s ↔ a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  simp only [pairs, mem_image, mem_offDiag, Prod.exists, Function.uncurry_apply_pair]
  constructor
  · rintro ⟨x, y, ⟨hx, hy, hxy⟩, h⟩
    rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hx, hy, hxy⟩
    · exact ⟨hy, hx, Ne.symm hxy⟩
  · rintro ⟨ha, hb, hab⟩
    exact ⟨a, b, ⟨ha, hb, hab⟩, rfl⟩

private theorem card_pairs [DecidableEq V] (s : Finset V) :
    (pairs s).card = s.card.choose 2 :=
  Sym2.card_image_offDiag s

private theorem pairs_nondiagonal [DecidableEq V] {s : Finset V} {e : Sym2 V}
    (he : e ∈ pairs s) : ¬ e.IsDiag := by
  induction e using Sym2.ind with
  | _ a b => exact fun h ↦ (mem_pairs.1 he).2.2 (Sym2.mk_isDiag_iff.1 h)

/-- A finite family of distinct, nonloop edges all have a specified status. -/
private theorem edge_pattern_probability [Countable V] (p : I) (t : Finset (Sym2 V))
    (ht : ∀ e ∈ t, ¬ e.IsDiag) (b : Bool) :
    (SimpleGraph.binomialRandom V p) {G | ∀ e ∈ t, (e ∈ G.edgeSet ↔ b = true)} =
      (if b then (toNNReal p : ℝ≥0∞) else (toNNReal (σ p) : ℝ≥0∞)) ^ t.card := by
  classical
  have hm : MeasurableSet {G : SimpleGraph V | ∀ e ∈ t, (e ∈ G.edgeSet ↔ b = true)} := by
    simp only [measurableSet_setOfPred]
    fun_prop
  rw [SimpleGraph.binomialRandom_eq_map, Measure.map_apply SimpleGraph.measurable_fromEdgeSet hm]
  have hsub : (t : Set (Sym2 V)) ⊆ Sym2.diagSetᶜ := fun e he ↦ ht e he
  have hmem (S : Set (Sym2 V)) (e : Sym2 V) (he : e ∈ t) :
      e ∈ (fromEdgeSet S).edgeSet ↔ e ∈ S := by
    simp [edgeSet_fromEdgeSet, show e ∉ Sym2.diagSet from ht e he]
  have pre : fromEdgeSet ⁻¹' {G : SimpleGraph V | ∀ e ∈ t, (e ∈ G.edgeSet ↔ b = true)} =
      {S | ∀ e ∈ t, (e ∈ S ↔ b = true)} := by
    ext S
    change (∀ e ∈ t, e ∈ (fromEdgeSet S).edgeSet ↔ b = true) ↔ _
    exact forall₂_congr fun e he ↦ by rw [hmem S e he]
  rw [pre]
  cases b
  · simpa [Set.subset_def] using setBernoulli_pattern p ∅ t disjoint_bot_left (by simp) hsub
  · simpa [Set.subset_def] using setBernoulli_pattern p t ∅ disjoint_bot_right hsub (by simp)

private theorem clique_iff_pairs [DecidableEq V] (G : SimpleGraph V) (s : Finset V) :
    G.IsClique (s : Set V) ↔ ∀ e ∈ pairs s, e ∈ G.edgeSet := by
  constructor
  · intro h e he
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨ha, hb, hab⟩ := mem_pairs.1 he
      exact h ha hb hab
  · intro h a ha b hb hab
    exact h _ (mem_pairs.2 ⟨ha, hb, hab⟩)

private theorem independent_iff_pairs [DecidableEq V] (G : SimpleGraph V) (s : Finset V) :
    G.IsIndepSet (s : Set V) ↔ ∀ e ∈ pairs s, e ∉ G.edgeSet := by
  constructor
  · intro h e he
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨ha, hb, hab⟩ := mem_pairs.1 he
      exact h ha hb hab
  · intro h a ha b hb hab
    exact h _ (mem_pairs.2 ⟨ha, hb, hab⟩)

/-- A fixed finite clique event is measurable. -/
theorem measurableSet_clique [Countable V] (s : Finset V) :
    MeasurableSet {G : SimpleGraph V | G.IsClique (s : Set V)} := by
  classical
  simp only [clique_iff_pairs, measurableSet_setOfPred]
  fun_prop

/-- A fixed finite independent-set event is measurable. -/
theorem measurableSet_independent [Countable V] (s : Finset V) :
    MeasurableSet {G : SimpleGraph V | G.IsIndepSet (s : Set V)} := by
  classical
  simp only [independent_iff_pairs, measurableSet_setOfPred]
  fun_prop

/-- Exact probability that a fixed finite vertex set spans a clique. -/
theorem clique_probability [Countable V] (p : I) (s : Finset V) :
    (SimpleGraph.binomialRandom V p) {G | G.IsClique (s : Set V)} =
      (toNNReal p : ℝ≥0∞) ^ s.card.choose 2 := by
  classical
  simpa only [clique_iff_pairs, iff_true, Bool.true_eq, ite_true, card_pairs] using
    edge_pattern_probability p (pairs s) (fun _ he ↦ pairs_nondiagonal he) true

/-- Exact probability that a fixed finite vertex set is independent. -/
theorem independent_probability [Countable V] (p : I) (s : Finset V) :
    (SimpleGraph.binomialRandom V p) {G | G.IsIndepSet (s : Set V)} =
      (toNNReal (σ p) : ℝ≥0∞) ^ s.card.choose 2 := by
  classical
  simpa only [independent_iff_pairs, Bool.false_eq_true, iff_false, ite_false, card_pairs] using
    edge_pattern_probability p (pairs s) (fun _ he ↦ pairs_nondiagonal he) false

/-- Two prescribed cliques share exactly the edges internal to the intersection. -/
theorem clique_pair_probability [Countable V] [DecidableEq V] (p : I) (s t : Finset V) :
    (SimpleGraph.binomialRandom V p) ({G | G.IsClique (s : Set V)} ∩
      {G | G.IsClique (t : Set V)}) =
      (toNNReal p : ℝ≥0∞) ^
        (s.card.choose 2 + t.card.choose 2 - (s ∩ t).card.choose 2) := by
  have pairs_inter : pairs s ∩ pairs t = pairs (s ∩ t) := by
    ext e
    induction e using Sym2.ind with
    | _ a b => simp only [mem_inter, mem_pairs]; tauto
  have hc := card_union_add_card_inter (pairs s) (pairs t)
  rw [pairs_inter, card_pairs, card_pairs, card_pairs] at hc
  have h := edge_pattern_probability p (pairs s ∪ pairs t)
    (fun e he ↦ (mem_union.mp he).elim (fun h ↦ pairs_nondiagonal h)
      (fun h ↦ pairs_nondiagonal h)) true
  rw [show (pairs s ∪ pairs t).card = _ from Nat.eq_sub_of_add_eq hc] at h
  simp only [ite_true] at h
  convert h using 2
  ext G
  simp [clique_iff_pairs]
  grind

#print axioms clique_probability
#print axioms independent_probability

end ProbabilisticCombinatorics.RamseyProbabilityHelpers
