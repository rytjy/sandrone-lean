import Mathlib

/-!
# Sandrone.Wilson

Wilson score interval for a binomial proportion, the interval used in our
small-sample notes (9 of 13, 95% interval 0.42–0.87).

Mathlib has no `confidence interval` and no `wilson score` (GitHub code search
on `leanprover-community/mathlib4`, 2026-11-12: 0 hits each). This file starts
that gap with the two definitions and the basic containment fact.
-/

namespace Sandrone

/-- Wilson score interval centre for `x` successes in `n` trials, critical value `z`. -/
noncomputable def wilsonCenter (n x : ℕ) (z : ℝ) : ℝ :=
  ((x : ℝ) + z ^ 2 / 2) / ((n : ℝ) + z ^ 2)

/-- Wilson score interval half-width. -/
noncomputable def wilsonHalf (n x : ℕ) (z : ℝ) : ℝ :=
  z * Real.sqrt ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4) /
    ((n : ℝ) + z ^ 2)

/-- The Wilson centre lies in `[0, 1]` whenever `x ≤ n`. -/
theorem wilsonCenter_mem_Icc (n x : ℕ) (z : ℝ) (hx : x ≤ n) (hn : 0 < n) :
    0 ≤ wilsonCenter n x z ∧ wilsonCenter n x z ≤ 1 := by
  have hx' : (x : ℝ) ≤ (n : ℝ) := by exact_mod_cast hx
  have hz2 : (0 : ℝ) ≤ z ^ 2 := sq_nonneg z
  constructor
  · exact div_nonneg (by positivity) (by positivity)
  · have hden : (0 : ℝ) < (n : ℝ) + z ^ 2 := by positivity
    rw [wilsonCenter, div_le_one hden]
    nlinarith

/-- The Wilson half-width is nonnegative for a nonnegative critical value. -/
theorem wilsonHalf_nonneg (n x : ℕ) (z : ℝ) (hz : 0 ≤ z) (hx : x ≤ n) (hn : 0 < n) :
    0 ≤ wilsonHalf n x z := by
  have hx' : (x : ℝ) ≤ (n : ℝ) := by exact_mod_cast hx
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hxn : (0 : ℝ) ≤ (n : ℝ) - (x : ℝ) := by linarith
  have hxz : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hprod : (0 : ℝ) ≤ (x : ℝ) * ((n : ℝ) - (x : ℝ)) := mul_nonneg hxz hxn
  have hdiv : (0 : ℝ) ≤ (x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) :=
    div_nonneg hprod (le_of_lt hn')
  have hz4 : (0 : ℝ) ≤ z ^ 2 / 4 := by positivity
  have hrad : (0 : ℝ) ≤
      (x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4 := add_nonneg hdiv hz4
  have hsqrt : (0 : ℝ) ≤ Real.sqrt
      ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4) := Real.sqrt_nonneg _
  have hmul : (0 : ℝ) ≤ z * Real.sqrt
      ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4) := mul_nonneg hz hsqrt
  exact div_nonneg hmul (by positivity)

end Sandrone
