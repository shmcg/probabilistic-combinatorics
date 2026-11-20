/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

public import ProbabilisticCombinatorics.Method.FirstMoment.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Order.Interval.Finset.Nat
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# A bounded-degree bipartite expander model

Eight permutations give eight perfect matchings between two copies of `Fin n`.
Repeated edges are harmless: `neighbors` records the neighborhood in the
underlying simple bipartite graph, so every vertex has degree at most eight.

`Expands π` asks that a nonempty set of at most `n / 8` vertices on either side
have strictly more than twice as many neighbors. A bad certificate records the
side, the source set `S` of size `s`, and a target set `T` of size `2 * s`
containing every neighbor of `S`. The natural-valued certificate count is zero
exactly when the desired expansion property holds.
-/

open scoped BigOperators Classical

namespace ProbabilisticCombinatorics.Expanders

/-- A bipartite graph presented as the union of eight perfect matchings. -/
abbrev Matchings (n : ℕ) := Fin 8 → Equiv.Perm (Fin n)

variable {n : ℕ}

/-- `true` follows a matching from left to right; `false` follows it backwards. -/
def oriented (π : Matchings n) (side : Bool) (i : Fin 8) : Equiv.Perm (Fin n) :=
  if side then π i else (π i).symm

/-- The neighborhood of `S`, using the chosen side of the bipartite graph. -/
def neighbors (π : Matchings n) (side : Bool) (S : Finset (Fin n)) :
    Finset (Fin n) :=
  Finset.univ.biUnion fun i ↦ S.image (oriented π side i)

/-- Two-sided vertex expansion for nonempty sets of size at most `n / 8`. -/
def Expands (π : Matchings n) : Prop :=
  ∀ (side : Bool) (S : Finset (Fin n)),
    1 ≤ S.card → 8 * S.card ≤ n → 2 * S.card < (neighbors π side S).card

theorem neighbors_subset_iff (π : Matchings n) (side : Bool)
    (S T : Finset (Fin n)) :
    neighbors π side S ⊆ T ↔ ∀ i : Fin 8, ∀ v ∈ S, oriented π side i v ∈ T := by
  constructor
  · intro h i v hv
    apply h
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
      Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
  · intro h v hv
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
    exact h i u hu

/-- Every vertex has at most eight neighbors, on either side. -/
theorem card_neighbors_singleton_le (π : Matchings n) (side : Bool) (v : Fin n) :
    (neighbors π side {v}).card ≤ 8 := by
  simpa [neighbors, Finset.biUnion_singleton] using
    (Finset.card_image_le (s := (Finset.univ : Finset (Fin 8)))
      (f := fun i ↦ oriented π side i v))

/-- A candidate certificate consists of a side, a source set, and a target set. -/
abbrev Certificate (n : ℕ) := Bool × Finset (Fin n) × Finset (Fin n)

/-- Candidate certificates for source-set size `s`. -/
def certificates (n s : ℕ) : Finset (Certificate n) :=
  Finset.univ ×ˢ ((Finset.univ : Finset (Fin n)).powersetCard s ×ˢ
    (Finset.univ : Finset (Fin n)).powersetCard (2 * s))

@[simp]
theorem mem_certificates (s : ℕ) (c : Certificate n) :
    c ∈ certificates n s ↔ c.2.1.card = s ∧ c.2.2.card = 2 * s := by
  simp [certificates]

/-- There are two choices of side and independent choices of the two vertex sets. -/
theorem card_certificates (n s : ℕ) :
    (certificates n s).card = 2 * n.choose s * n.choose (2 * s) := by
  simp [certificates, Finset.card_powersetCard, mul_assoc]

/-- A certificate is bad when its target set contains the whole neighborhood. -/
def badEvent (c : Certificate n) : Set (Matchings n) :=
  {π | neighbors π c.1 c.2.1 ⊆ c.2.2}

/-- The number of bad certificates of a fixed source-set size. -/
noncomputable def badCountAt (n s : ℕ) (π : Matchings n) : ℕ :=
  ∑ c ∈ certificates n s, (badEvent c).indicator (1 : Matchings n → ℕ) π

/-- The count used by the first-moment method. -/
noncomputable def badCount (n : ℕ) (π : Matchings n) : ℕ :=
  ∑ s ∈ Finset.Icc 1 (n / 8), badCountAt n s π

theorem badCountAt_eq_zero_iff (s : ℕ) (π : Matchings n) :
    badCountAt n s π = 0 ↔
      ∀ (side : Bool) (S T : Finset (Fin n)),
        S.card = s → T.card = 2 * s → ¬ neighbors π side S ⊆ T := by
  rw [badCountAt, FirstMoment.sum_indicators_eq_zero]
  simp only [mem_certificates, badEvent, Set.mem_ofPred_eq]
  constructor
  · intro h side S T hS hT
    exact h (side, S, T) ⟨hS, hT⟩
  · rintro h ⟨side, S, T⟩ ⟨hS, hT⟩
    exact h side S T hS hT

/-- The certificate count detects exactly the failure of the expansion property. -/
theorem badCount_eq_zero_iff_expands (π : Matchings n) :
    badCount n π = 0 ↔ Expands π := by
  simp only [badCount, Finset.sum_eq_zero_iff, badCountAt_eq_zero_iff,
    Finset.mem_Icc, Expands]
  constructor
  · intro h side S hS hsmall
    by_contra hnot
    have hN : (neighbors π side S).card ≤ 2 * S.card := Nat.le_of_not_gt hnot
    have h2S : 2 * S.card ≤ (Finset.univ : Finset (Fin n)).card := by
      simpa using (show 2 * S.card ≤ n by omega)
    obtain ⟨T, hNT, _, hT⟩ :=
      Finset.exists_subsuperset_card_eq (Finset.subset_univ (neighbors π side S)) hN h2S
    have hdiv : S.card ≤ n / 8 := (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
    exact h S.card ⟨hS, hdiv⟩ side S T rfl hT hNT
  · intro h s hs side S T hS hT hNT
    have hsmall : 8 * S.card ≤ n := by
      have := (Nat.le_div_iff_mul_le (by decide : 0 < 8)).mp hs.2
      omega
    have hlarge := h side S (by omega) hsmall
    have hcard := Finset.card_le_card hNT
    omega

end ProbabilisticCombinatorics.Expanders
