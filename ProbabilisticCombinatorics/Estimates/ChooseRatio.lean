/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/
module

public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Sampling without replacement: a binomial-ratio bound

The probability that a uniform `s`-subset of an `n`-element set lies in a
fixed `t`-subset is `choose t s / choose n s`. It is at most `(t/n)^s`.
We prove the estimate by first cross-multiplying over the natural numbers.
-/

namespace ProbabilisticCombinatorics.Expanders

/-- Cross-multiplied comparison of descending factorials with powers. -/
theorem descFactorial_mul_pow_le (n t s : ℕ) (htn : t ≤ n) :
    t.descFactorial s * n ^ s ≤ n.descFactorial s * t ^ s := by
  have hfactor (i : ℕ) : (t - i) * n ≤ (n - i) * t := by
    by_cases hit : i ≤ t
    · have hin : i ≤ n := hit.trans htn
      have ht := Nat.sub_add_cancel hit
      have hn := Nat.sub_add_cancel hin
      nlinarith
    · simp [Nat.sub_eq_zero_of_le (by omega : t ≤ i)]
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
    calc
      (t - s) * t.descFactorial s * (n ^ s * n) =
          ((t - s) * n) * (t.descFactorial s * n ^ s) := by ring
      _ ≤ ((n - s) * t) * (n.descFactorial s * t ^ s) := Nat.mul_le_mul (hfactor s) ih
      _ = (n - s) * n.descFactorial s * (t ^ s * t) := by ring

/-- Cross-multiplied form of the binomial-ratio estimate; no division assumptions needed. -/
theorem choose_mul_pow_le (n t s : ℕ) (htn : t ≤ n) :
    t.choose s * n ^ s ≤ n.choose s * t ^ s := by
  have h := descFactorial_mul_pow_le n t s htn
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose] at h
  have hf := Nat.factorial_pos s
  nlinarith

/-- The containment probability for sampling without replacement is at most `(t/n)^s`. -/
theorem choose_ratio_le_pow (n t s : ℕ) (hn : 0 < n) (htn : t ≤ n) (hsn : s ≤ n) :
    (t.choose s : ℝ) / (n.choose s : ℝ) ≤ ((t : ℝ) / n) ^ s := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : (0 : ℝ) < n.choose s := by exact_mod_cast Nat.choose_pos hsn
  have h : (t.choose s : ℝ) * (n : ℝ) ^ s ≤ (n.choose s : ℝ) * (t : ℝ) ^ s := by
    exact_mod_cast choose_mul_pow_le n t s htn
  rw [div_pow]
  apply (div_le_div_iff₀ hc (pow_pos hn' s)).mpr
  nlinarith

end ProbabilisticCombinatorics.Expanders
