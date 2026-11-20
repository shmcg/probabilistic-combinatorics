/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

public import ProbabilisticCombinatorics.Estimates.ChooseRatio
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # An exponential moment for the overlap with a uniform subset -/

public section
open Finset
open scoped BigOperators Classical

namespace ProbabilisticCombinatorics

/-- Sampling a uniform `k`-subset without replacement. Expand over subsets of the marked set
and bound the probability that all elements of each such subset were drawn. -/
theorem sum_pow_inter_le {V : Type*} [Fintype V] [DecidableEq V] (s : Finset V)
    {k : ℕ} (hs : s.card ≤ k) (hk : k ≤ Fintype.card V) (hn : 0 < Fintype.card V)
    {a : ℝ} (ha : 0 ≤ a) :
    (∑ t ∈ (univ : Finset V).powersetCard k, (1 + a) ^ (s ∩ t).card) ≤
      (Fintype.card V).choose k * (1 + a * k / Fintype.card V) ^ s.card := by
  let n := Fintype.card V
  let F := (univ : Finset V).powersetCard k
  have expand (t : Finset V) :
      (1 + a) ^ (s ∩ t).card = ∑ u ∈ s.powerset, if u ⊆ t then a ^ u.card else 0 := by
    have hset : (s ∩ t).powerset = s.powerset.filter (· ⊆ t) := by ext; simp [Finset.subset_inter_iff]
    have e := Finset.prod_one_add (f := fun _ : V ↦ a) (s ∩ t)
    simpa [hset, Finset.sum_filter] using e
  have count (u : Finset V) (hu : u ∈ s.powerset) :
      ((F.filter (u ⊆ ·)).card : ℝ) ≤ n.choose k * ((k : ℝ) / n) ^ u.card := by
    have h := (card_le_card (mem_powerset.mp hu)).trans hs
    rw [show (F.filter (u ⊆ ·)).card = (n - u.card).choose (k - u.card) by
      simpa [F, n] using card_filter_powersetCard_subset u univ k (subset_univ _) h]
    have hc : (0 : ℝ) < n.choose u.card := by exact_mod_cast Nat.choose_pos (h.trans hk)
    have eqn : (n.choose k : ℝ) * k.choose u.card =
        n.choose u.card * ((n - u.card).choose (k - u.card) : ℝ) := by
      exact_mod_cast Nat.choose_mul (n := n) h
    have rat := Expanders.choose_ratio_le_pow n k u.card hn hk (h.trans hk)
    calc
      _ = (n.choose k : ℝ) * (k.choose u.card / (n.choose u.card : ℝ)) := by
        field_simp; linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left rat (Nat.cast_nonneg _)
  change (∑ t ∈ F, _) ≤ _
  simp_rw [expand]
  rw [Finset.sum_comm]
  calc
    _ = ∑ u ∈ s.powerset, ((F.filter (u ⊆ ·)).card : ℝ) * a ^ u.card := by
      apply sum_congr rfl
      intro u _
      rw [← Finset.sum_filter]
      simp
    _ ≤ ∑ u ∈ s.powerset, (n.choose k : ℝ) * (a * k / n) ^ u.card := by
      apply sum_le_sum
      intro u hu
      have h := mul_le_mul_of_nonneg_right (count u hu) (pow_nonneg ha u.card)
      apply h.trans_eq
      rw [mul_div_assoc, mul_pow]
      ring
    _ = _ := by
      rw [← Finset.mul_sum]
      have e := Finset.prod_one_add (f := fun _ : V ↦ a * k / n) s
      simp only [Finset.prod_const] at e
      rw [← e]
end ProbabilisticCombinatorics
