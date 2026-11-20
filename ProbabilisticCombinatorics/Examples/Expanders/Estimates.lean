/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The numerical first-moment budget for eight matching expanders

The two-sided union bound for a union of eight random perfect matchings has
budget `2 * ∑ s, choose n s * choose n (2*s) * (2*s/n)^(8*s)`.
This file proves that the budget over `1 ≤ s ≤ n/8` is at most `27/(28*n)`.
The estimates are independent of the probability space and graph model.
-/

open scoped BigOperators

namespace ProbabilisticCombinatorics.Expanders

/-- A convenient rational version of the usual `(e*n/k)^k` binomial bound. -/
theorem choose_le_three_mul_div_pow (n k : ℕ) (hk : 0 < k) :
    (n.choose k : ℝ) ≤ (3 * (n : ℝ) / k) ^ k := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hf0 : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hfac : (k : ℝ) ^ k / k.factorial ≤ (3 : ℝ) ^ k := by
    calc
      (k : ℝ) ^ k / k.factorial ≤ Real.exp k :=
        Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg k) k
      _ = Real.exp 1 ^ k := by simpa only [mul_one] using Real.exp_nat_mul 1 k
      _ ≤ (3 : ℝ) ^ k := by gcongr; exact Real.exp_one_lt_three.le
  calc
    (n.choose k : ℝ) ≤ (n : ℝ) ^ k / k.factorial := Nat.choose_le_pow_div k n
    _ = ((n : ℝ) / k) ^ k * ((k : ℝ) ^ k / k.factorial) := by
      rw [div_pow]
      field_simp
    _ ≤ ((n : ℝ) / k) ^ k * (3 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_left hfac (by positivity)
    _ = (3 * (n : ℝ) / k) ^ k := by rw [← mul_pow]; congr 1; ring

/-- The contribution from witnesses of one fixed size. -/
theorem expander_summand_le_base_pow (n s : ℕ) (hn : 0 < n) (hs : 0 < s) :
    (n.choose s : ℝ) * (n.choose (2 * s) : ℝ) *
        ((2 * (s : ℝ)) / n) ^ (8 * s) ≤
      (1728 * ((s : ℝ) / n) ^ 5) ^ s := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  have h₁ := choose_le_three_mul_div_pow n s hs
  have h₂ := choose_le_three_mul_div_pow n (2 * s) (by omega)
  push_cast at h₂
  calc
    (n.choose s : ℝ) * (n.choose (2 * s) : ℝ) *
        ((2 * (s : ℝ)) / n) ^ (8 * s) ≤
      (3 * (n : ℝ) / s) ^ s * (3 * (n : ℝ) / (2 * s)) ^ (2 * s) *
        ((2 * (s : ℝ)) / n) ^ (8 * s) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul h₁ h₂ (by positivity) (by positivity)
          · positivity
    _ = (1728 * ((s : ℝ) / n) ^ 5) ^ s := by
      rw [pow_mul (3 * (n : ℝ) / (2 * s)) 2 s,
        pow_mul ((2 * (s : ℝ)) / n) 8 s, ← mul_pow, ← mul_pow]
      congr 1
      field_simp
      ring

/-- On the permitted range of set sizes, the exponential base is linear in `s/n`. -/
theorem expander_base_le_linear (n s : ℕ) (hn : 0 < n) (hsn : 8 * s ≤ n) :
    1728 * ((s : ℝ) / n) ^ 5 ≤ 27 * (s : ℝ) / (64 * n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn' : (8 : ℝ) * s ≤ n := by exact_mod_cast hsn
  have hfrac : (s : ℝ) / n ≤ 1 / 8 := by
    rw [div_le_iff₀ hn']
    linarith
  have hpow : ((s : ℝ) / n) ^ 4 ≤ (1 / 8 : ℝ) ^ 4 := by
    gcongr
  calc
    1728 * ((s : ℝ) / n) ^ 5 =
      (1728 * ((s : ℝ) / n)) * ((s : ℝ) / n) ^ 4 := by ring
    _ ≤ (1728 * ((s : ℝ) / n)) * (1 / 8 : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = 27 * (s : ℝ) / (64 * n) := by ring

/-- The same base is uniformly at most `1/16`. -/
theorem expander_base_le_sixteenth (n s : ℕ) (hn : 0 < n) (hsn : 8 * s ≤ n) :
    1728 * ((s : ℝ) / n) ^ 5 ≤ (1 / 16 : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn' : (8 : ℝ) * s ≤ n := by exact_mod_cast hsn
  calc
    1728 * ((s : ℝ) / n) ^ 5 ≤ 27 * (s : ℝ) / (64 * n) :=
      expander_base_le_linear n s hn hsn
    _ ≤ 1 / 16 := by rw [div_le_iff₀ (by positivity)]; nlinarith

/-- Each size contributes at most a term of a geometric series with ratio `1/8`. -/
theorem expander_summand_le_geometric (n s : ℕ) (hn : 0 < n)
    (hs : 0 < s) (hsn : 8 * s ≤ n) :
    (n.choose s : ℝ) * (n.choose (2 * s) : ℝ) *
        ((2 * (s : ℝ)) / n) ^ (8 * s) ≤
      (27 / (64 * (n : ℝ))) * (1 / 8 : ℝ) ^ (s - 1) := by
  have hs' : s - 1 + 1 = s := by omega
  have hsize : (s : ℝ) ≤ (2 : ℝ) ^ (s - 1) := by
    exact_mod_cast (show s ≤ 2 ^ (s - 1) by
      have : s - 1 < 2 ^ (s - 1) := Nat.lt_two_pow_self
      omega)
  calc
    (n.choose s : ℝ) * (n.choose (2 * s) : ℝ) *
        ((2 * (s : ℝ)) / n) ^ (8 * s) ≤
      (1728 * ((s : ℝ) / n) ^ 5) ^ s := expander_summand_le_base_pow n s hn hs
    _ = (1728 * ((s : ℝ) / n) ^ 5) *
        (1728 * ((s : ℝ) / n) ^ 5) ^ (s - 1) := by
      rw [← pow_succ', hs']
    _ ≤ (27 * (s : ℝ) / (64 * n)) * (1 / 16 : ℝ) ^ (s - 1) := by
      apply mul_le_mul (expander_base_le_linear n s hn hsn)
      · gcongr
        exact expander_base_le_sixteenth n s hn hsn
      · positivity
      · positivity
    _ = (27 / (64 * (n : ℝ))) * ((s : ℝ) * (1 / 16 : ℝ) ^ (s - 1)) := by ring
    _ ≤ (27 / (64 * (n : ℝ))) *
        ((2 : ℝ) ^ (s - 1) * (1 / 16 : ℝ) ^ (s - 1)) := by gcongr
    _ = (27 / (64 * (n : ℝ))) * (1 / 8 : ℝ) ^ (s - 1) := by
      rw [← mul_pow]
      norm_num

/-- The geometric majorant sums to at most `8/7`, including an empty size range. -/
theorem expander_geometric_sum_le (N : ℕ) :
    (∑ s ∈ Finset.Icc 1 N, (1 / 8 : ℝ) ^ (s - 1)) ≤ 8 / 7 := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_left]
  have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := N)
    (show (0 : ℝ) ≤ 1 / 8 by norm_num) (show (1 / 8 : ℝ) < 1 by norm_num)
  norm_num at h
  exact h

/-- The quantitative first-moment budget for eight random perfect matchings. -/
theorem expander_budget_le (n : ℕ) (hn : 0 < n) :
    2 * (∑ s ∈ Finset.Icc 1 (n / 8),
      (n.choose s : ℝ) * (n.choose (2 * s) : ℝ) *
        ((2 * (s : ℝ)) / n) ^ (8 * s)) ≤ 27 / (28 * (n : ℝ)) := by
  calc
    2 * (∑ s ∈ Finset.Icc 1 (n / 8),
        (n.choose s : ℝ) * (n.choose (2 * s) : ℝ) *
          ((2 * (s : ℝ)) / n) ^ (8 * s)) ≤
      2 * (∑ s ∈ Finset.Icc 1 (n / 8),
        (27 / (64 * (n : ℝ))) * (1 / 8 : ℝ) ^ (s - 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro s hs
      have hs' := Finset.mem_Icc.mp hs
      exact expander_summand_le_geometric n s hn (by omega) (by omega)
    _ = (2 * (27 / (64 * (n : ℝ)))) *
        (∑ s ∈ Finset.Icc 1 (n / 8), (1 / 8 : ℝ) ^ (s - 1)) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (2 * (27 / (64 * (n : ℝ)))) * (8 / 7 : ℝ) :=
      mul_le_mul_of_nonneg_left (expander_geometric_sum_le (n / 8)) (by positivity)
    _ = 27 / (28 * (n : ℝ)) := by ring

end ProbabilisticCombinatorics.Expanders
