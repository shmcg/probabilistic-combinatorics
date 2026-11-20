/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

public import ProbabilisticCombinatorics.Examples.Expanders.Model
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-!
# From eight matchings to a simple bipartite graph

The two summands of `Fin n ⊕ Fin n` are the two vertex classes. The graph records
an edge whenever any of the eight matchings supplies that edge. Thus repeated
edges disappear, the degree is at most eight, and the model's neighborhoods are
exactly the graph's neighborhoods after embedding the appropriate vertex class.
-/

open scoped Classical

namespace ProbabilisticCombinatorics.Expanders

variable {n : ℕ}

/-- The underlying simple bipartite graph of eight perfect matchings. -/
def graph (π : Matchings n) : SimpleGraph (Fin n ⊕ Fin n) where
  Adj u v := match u, v with
    | Sum.inl a, Sum.inr b => ∃ i : Fin 8, π i a = b
    | Sum.inr b, Sum.inl a => ∃ i : Fin 8, π i a = b
    | _, _ => False
  symm := ⟨by intro u v; cases u <;> cases v <;> exact id⟩
  loopless := ⟨by intro u; cases u <;> exact id⟩

instance graphAdjDecidable (π : Matchings n) : DecidableRel (graph π).Adj := by
  intro u v
  cases u <;> cases v <;> dsimp [graph] <;> infer_instance

@[simp]
theorem graph_adj_inl_inr (π : Matchings n) (u v : Fin n) :
    (graph π).Adj (Sum.inl u) (Sum.inr v) ↔ ∃ i : Fin 8, π i u = v := Iff.rfl

@[simp]
theorem graph_adj_inr_inl (π : Matchings n) (u v : Fin n) :
    (graph π).Adj (Sum.inr u) (Sum.inl v) ↔ ∃ i : Fin 8, π i v = u := Iff.rfl

@[simp]
theorem graph_not_adj_inl_inl (π : Matchings n) (u v : Fin n) :
    ¬ (graph π).Adj (Sum.inl u) (Sum.inl v) := id

@[simp]
theorem graph_not_adj_inr_inr (π : Matchings n) (u v : Fin n) :
    ¬ (graph π).Adj (Sum.inr u) (Sum.inr v) := id

/-- The graph neighborhood of a left vertex is the embedded forward neighborhood. -/
theorem neighborFinset_inl (π : Matchings n) (v : Fin n) :
    (graph π).neighborFinset (Sum.inl v) =
      (neighbors π true {v}).image Sum.inr := by
  ext w
  cases w <;> simp [neighbors, oriented, eq_comm]

/-- The graph neighborhood of a right vertex is the embedded inverse neighborhood. -/
theorem neighborFinset_inr (π : Matchings n) (v : Fin n) :
    (graph π).neighborFinset (Sum.inr v) =
      (neighbors π false {v}).image Sum.inl := by
  ext w
  cases w <;> simp [neighbors, oriented, Equiv.eq_symm_apply, eq_comm]

/-- Every vertex of the underlying simple graph has degree at most eight. -/
theorem degree_graph_le (π : Matchings n) (v : Fin n ⊕ Fin n) :
    (graph π).degree v ≤ 8 := by
  cases v with
  | inl v =>
    rw [SimpleGraph.degree, neighborFinset_inl,
      Finset.card_image_of_injective _ Sum.inr_injective]
    exact card_neighbors_singleton_le π true v
  | inr v =>
    rw [SimpleGraph.degree, neighborFinset_inr,
      Finset.card_image_of_injective _ Sum.inl_injective]
    exact card_neighbors_singleton_le π false v

/-- Neighborhood correspondence for arbitrary subsets of the left vertex class. -/
theorem graphNeighbors_inl (π : Matchings n) (S : Finset (Fin n)) :
    (S.image Sum.inl).biUnion (fun v ↦ (graph π).neighborFinset v) =
      (neighbors π true S).image Sum.inr := by
  ext w
  cases w <;> simp [neighbors, oriented, Finset.mem_biUnion, exists_and_left, exists_comm]

/-- Neighborhood correspondence for arbitrary subsets of the right vertex class. -/
theorem graphNeighbors_inr (π : Matchings n) (S : Finset (Fin n)) :
    (S.image Sum.inr).biUnion (fun v ↦ (graph π).neighborFinset v) =
      (neighbors π false S).image Sum.inl := by
  ext w
  cases w <;> simp [neighbors, oriented, Finset.mem_biUnion, Equiv.eq_symm_apply, eq_comm]

/-- The permutation model's expansion property is ordinary graph-neighborhood
expansion on each of the two vertex classes. -/
theorem expands_iff_graph_expansion (π : Matchings n) :
    Expands π ↔
      (∀ S : Finset (Fin n), 1 ≤ S.card → 8 * S.card ≤ n →
        2 * S.card < ((S.image Sum.inl).biUnion (fun v ↦ (graph π).neighborFinset v)).card) ∧
      (∀ S : Finset (Fin n), 1 ≤ S.card → 8 * S.card ≤ n →
        2 * S.card < ((S.image Sum.inr).biUnion (fun v ↦ (graph π).neighborFinset v)).card) := by
  simp only [graphNeighbors_inl, graphNeighbors_inr,
    Finset.card_image_of_injective _ Sum.inl_injective,
    Finset.card_image_of_injective _ Sum.inr_injective, Expands]
  constructor
  · intro h
    exact ⟨h true, h false⟩
  · rintro ⟨hl, hr⟩ side
    cases side
    · exact hr
    · exact hl

/-- An expanding family of matchings yields an actual simple bipartite graph
with maximum degree eight and the same two-sided small-set expansion. -/
theorem exists_graph_of_expands (hex : ∃ π : Matchings n, Expands π) :
    ∃ G : SimpleGraph (Fin n ⊕ Fin n),
      (∀ v, G.degree v ≤ 8) ∧
      (∀ u v : Fin n, ¬ G.Adj (Sum.inl u) (Sum.inl v)) ∧
      (∀ u v : Fin n, ¬ G.Adj (Sum.inr u) (Sum.inr v)) ∧
      (∀ S : Finset (Fin n), 1 ≤ S.card → 8 * S.card ≤ n →
        2 * S.card < ((S.image Sum.inl).biUnion (fun v ↦ G.neighborFinset v)).card) ∧
      (∀ S : Finset (Fin n), 1 ≤ S.card → 8 * S.card ≤ n →
        2 * S.card < ((S.image Sum.inr).biUnion (fun v ↦ G.neighborFinset v)).card) := by
  obtain ⟨π, hπ⟩ := hex
  refine ⟨graph π, ?_, graph_not_adj_inl_inl π, graph_not_adj_inr_inr π, ?_⟩
  · simpa only [← SimpleGraph.ncard_neighborSet] using degree_graph_le π
  · convert (expands_iff_graph_expansion π).mp hπ using 1 <;>
      simp only [SimpleGraph.neighborFinset_def, ← Set.toFinite_toFinset]

end ProbabilisticCombinatorics.Expanders
