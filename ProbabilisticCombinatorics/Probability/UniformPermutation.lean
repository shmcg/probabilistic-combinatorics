/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

public import Mathlib.Probability.UniformOn
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Basic
public import ProbabilisticCombinatorics.Estimates.ChooseRatio

@[expose] public section

/-!
# Uniform permutations and sampling without replacement

A uniform permutation sends a fixed `s`-element subset to a uniform `s`-element
subset. In particular the chance that its image lies in a fixed `t`-element set
is `choose t s / choose n s`, and is at most `(t / n)^s`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical ENNReal

namespace ProbabilisticCombinatorics.UniformPermutation

instance measurableSpace (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

instance measurableSingletonClass (n : ℕ) :
    MeasurableSingletonClass (Equiv.Perm (Fin n)) := ⟨fun _ ↦ trivial⟩

/-- The uniform probability law on all permutations, including the unique
permutation of the empty set. -/
def measure (n : ℕ) : Measure (Equiv.Perm (Fin n)) := uniformOn Set.univ

instance (n : ℕ) : IsProbabilityMeasure (measure n) := by
  unfold measure
  infer_instance

private theorem uniformOn_real {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : α → Prop) :
    (uniformOn (Set.univ : Set α)).real {a | p a} =
      (Nat.card {a // p a} : ℝ) / Nat.card α := by
  rw [measureReal_def, uniformOn_univ,
    Measure.count_apply (Set.toFinite _).measurableSet,
    ← Set.coe_fintypeCard]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENat.toENNReal_coe,
    Nat.card_eq_fintype_card]
  exact congrArg (fun k : ℕ ↦ (k : ℝ) / Fintype.card α)
    (Fintype.card_congr (Equiv.refl _))

/-- A finite map with equally sized fibers sends the uniform law to the uniform law. -/
private theorem uniformOn_real_preimage {α β : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [MeasurableSpace α] [MeasurableSingletonClass α]
    (f : α → β) (c : ℕ) (hc : ∀ b, Nat.card {a // f a = b} = c)
    (p : β → Prop) :
    (uniformOn (Set.univ : Set α)).real {a | p (f a)} =
      (Nat.card {b // p b} : ℝ) / Nat.card β := by
  have htotal : Nat.card α = Nat.card β * c := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
    simp_rw [hc]
    simp [Nat.card_eq_fintype_card]
  have hpart : Nat.card {a // p (f a)} = Nat.card {b // p b} * c := by
    rw [← Nat.card_congr (Equiv.sigmaSubtypeFiberEquivSubtype f (fun _ ↦ Iff.rfl)),
      Nat.card_sigma]
    simp_rw [hc]
    simp [Nat.card_eq_fintype_card]
  have hcpos : 0 < c := by
    have : 0 < Nat.card α := by simp [Nat.card_eq_fintype_card, Fintype.card_pos]
    rw [htotal] at this
    by_contra h
    have : c = 0 := by omega
    simp_all
  rw [uniformOn_real, hpart, htotal, Nat.cast_mul, Nat.cast_mul]
  exact mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr hcpos.ne')

private abbrev Subsets (n s : ℕ) :=
  {U : Finset (Fin n) // U ∈ Finset.univ.powersetCard s}

private def imageSubset {n : ℕ} (S : Finset (Fin n)) (π : Equiv.Perm (Fin n)) :
    Subsets n S.card :=
  ⟨S.map π.toEmbedding, by simp⟩

private theorem map_trans {n : ℕ} (S : Finset (Fin n)) (π τ : Equiv.Perm (Fin n)) :
    S.map (π.trans τ).toEmbedding = (S.map π.toEmbedding).map τ.toEmbedding := by
  rw [Finset.map_map]
  rfl

private def fiberEquiv {n : ℕ} (S : Finset (Fin n)) (U V : Subsets n S.card)
    (τ : Equiv.Perm (Fin n)) (hτ : U.val.map τ.toEmbedding = V.val) :
    {π // imageSubset S π = U} ≃ {π // imageSubset S π = V} where
  toFun π := ⟨π.val.trans τ, by
    have hπ : S.map π.val.toEmbedding = U.val := congrArg Subtype.val π.property
    apply Subtype.ext
    change S.map (π.val.trans τ).toEmbedding = V.val
    rw [map_trans, hπ, hτ]⟩
  invFun π := ⟨π.val.trans τ.symm, by
    have hπ : S.map π.val.toEmbedding = V.val := congrArg Subtype.val π.property
    apply Subtype.ext
    change S.map (π.val.trans τ.symm).toEmbedding = U.val
    rw [map_trans, hπ, ← hτ,
      Finset.map_map]
    simp⟩
  left_inv π := by
    apply Subtype.ext
    ext v
    simp
  right_inv π := by
    apply Subtype.ext
    ext v
    simp

private theorem fiber_card_eq {n : ℕ} (S : Finset (Fin n)) (U V : Subsets n S.card) :
    Nat.card {π // imageSubset S π = U} = Nat.card {π // imageSubset S π = V} := by
  have hcard : U.val.card = V.val.card := by
    have hu := (Finset.mem_powersetCard.mp U.property).2
    have hv := (Finset.mem_powersetCard.mp V.property).2
    omega
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq U.val V.val hcard
  exact Nat.card_congr (fiberEquiv S U V τ hτ)

private def containedSubsetsEquiv {n s : ℕ} (T : Finset (Fin n)) :
    {U : Subsets n s // U.val ⊆ T} ≃ {U : Finset (Fin n) // U ∈ T.powersetCard s} where
  toFun U := ⟨U.val.val, Finset.mem_powersetCard.mpr
    ⟨U.property, (Finset.mem_powersetCard.mp U.val.property).2⟩⟩
  invFun U := ⟨⟨U.val, Finset.mem_powersetCard.mpr
    ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp U.property).2⟩⟩,
    (Finset.mem_powersetCard.mp U.property).1⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The exact sampling-without-replacement probability. No independence between
the images of different vertices is assumed. -/
theorem containment_probability {n : ℕ} (S T : Finset (Fin n)) :
    (measure n).real {π | ∀ v ∈ S, π v ∈ T} =
      (T.card.choose S.card : ℝ) / (n.choose S.card : ℝ) := by
  have hevent : {π : Equiv.Perm (Fin n) | ∀ v ∈ S, π v ∈ T} =
      {π | (imageSubset S π).val ⊆ T} := by
    ext π
    change (∀ v ∈ S, π v ∈ T) ↔ S.map π.toEmbedding ⊆ T
    constructor
    · intro h v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
      exact h w hw
    · intro h v hv
      exact h (Finset.mem_map.mpr ⟨v, hv, rfl⟩)
  have hcount : Nat.card {U : Subsets n S.card // U.val ⊆ T} =
      T.card.choose S.card := by
    rw [Nat.card_congr (containedSubsetsEquiv T)]
    rw [Nat.card_eq_finsetCard, Finset.card_powersetCard]
  have htotal : Nat.card (Subsets n S.card) = n.choose S.card := by
    rw [Nat.card_eq_finsetCard, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [measure, hevent, uniformOn_real_preimage (imageSubset S)
    (Nat.card {π // imageSubset S π = imageSubset S (Equiv.refl _)})
    (fun U ↦ fiber_card_eq S U _) (fun U ↦ U.val ⊆ T), hcount, htotal]

/-- Uniform permutations are invariant under inversion. -/
theorem measure_symm_preimage (n : ℕ) (E : Set (Equiv.Perm (Fin n))) :
    (measure n).real {π | π.symm ∈ E} = (measure n).real E := by
  let e : {π : Equiv.Perm (Fin n) // π.symm ∈ E} ≃ {π : Equiv.Perm (Fin n) // π ∈ E} :=
    { toFun := fun π ↦ ⟨π.val.symm, π.property⟩
      invFun := fun π ↦ ⟨π.val.symm, by simp⟩
      left_inv := fun π ↦ by apply Subtype.ext; simp
      right_inv := fun π ↦ by apply Subtype.ext; simp }
  change (uniformOn Set.univ).real {π : Equiv.Perm (Fin n) | π.symm ∈ E} =
    (uniformOn Set.univ).real {π : Equiv.Perm (Fin n) | π ∈ E}
  rw [uniformOn_real, uniformOn_real, Nat.card_congr e]

/-- The same exact formula for inverse permutations, used for the other side
of a union of perfect matchings. -/
theorem inverse_containment_probability {n : ℕ} (S T : Finset (Fin n)) :
    (measure n).real {π | ∀ v ∈ S, π.symm v ∈ T} =
      (T.card.choose S.card : ℝ) / (n.choose S.card : ℝ) := by
  exact (measure_symm_preimage n {π | ∀ v ∈ S, π v ∈ T}).trans
    (containment_probability S T)

/-- Sampling without replacement only decreases this containment probability
relative to independent uniform samples. -/
theorem containment_probability_le {n : ℕ} (hn : 0 < n) (S T : Finset (Fin n)) :
    (measure n).real {π | ∀ v ∈ S, π v ∈ T} ≤ ((T.card : ℝ) / n) ^ S.card := by
  rw [containment_probability]
  exact Expanders.choose_ratio_le_pow n T.card S.card hn
    (by simpa using Finset.card_le_univ T) (by simpa using Finset.card_le_univ S)

/-- The containment upper bound for inverse permutations. -/
theorem inverse_containment_probability_le {n : ℕ} (hn : 0 < n)
    (S T : Finset (Fin n)) :
    (measure n).real {π | ∀ v ∈ S, π.symm v ∈ T} ≤ ((T.card : ℝ) / n) ^ S.card := by
  rw [inverse_containment_probability]
  exact Expanders.choose_ratio_le_pow n T.card S.card hn
    (by simpa using Finset.card_le_univ T) (by simpa using Finset.card_le_univ S)

end ProbabilisticCombinatorics.UniformPermutation
