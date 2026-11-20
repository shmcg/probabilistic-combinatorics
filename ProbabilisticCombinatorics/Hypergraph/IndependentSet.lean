/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

public import Mathlib.Combinatorics.Hypergraph.Basic
public import Mathlib.Data.Set.Finite.Powerset

/-! # Independent sets by vertex deletion -/

public section

namespace Hypergraph

variable {α : Type*} (H : Hypergraph α)

/-- An independent vertex set contains no entire hyperedge. -/
@[expose] def IsIndepSet (s : Set α) : Prop :=
  s ⊆ H.vertexSet ∧ ∀ e ∈ H.edgeSet, ¬ e ⊆ s

/-- A finite vertex set can be made independent by deleting at most one vertex per
contained edge. Only the sampled set needs to be finite. -/
theorem exists_isIndepSet_subset (hne : ∅ ∉ H.edgeSet) {s : Set α} (hs : s.Finite)
    (hsV : s ⊆ H.vertexSet) :
    ∃ t ⊆ s, H.IsIndepSet t ∧ s.ncard ≤ t.ncard + {e ∈ H.edgeSet | e ⊆ s}.ncard := by
  classical
  let bad := {e ∈ H.edgeSet | e ⊆ s}
  have hbad : bad.Finite := hs.powerset.subset fun _ he ↦ he.2
  have : Finite bad := hbad.to_subtype
  have nonempty (e : bad) : (e : Set α).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr fun h ↦ hne (h ▸ e.property.1)
  let rep (e : bad) := (nonempty e).choose
  have hrep (e : bad) : rep e ∈ (e : Set α) := (nonempty e).choose_spec
  let removed := Set.range rep
  have hsub : removed ⊆ s := by
    rintro _ ⟨e, rfl⟩
    exact e.property.2 (hrep e)
  have hremoved : removed.ncard ≤ bad.ncard := by
    simpa [removed] using Set.ncard_image_le (s := Set.univ) (f := rep) Set.finite_univ
  refine ⟨s \ removed, Set.sdiff_subset, ⟨Set.sdiff_subset.trans hsV, ?_⟩, ?_⟩
  · intro e he hsub
    let i : bad := ⟨e, he, hsub.trans Set.sdiff_subset⟩
    exact (hsub (hrep i)).2 ⟨i, rfl⟩
  · exact (Set.ncard_sdiff_add_ncard_of_subset hsub hs).symm.le.trans
      (Nat.add_le_add_left hremoved _)

end Hypergraph
