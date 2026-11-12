import Mathlib

/-!
# Sandrone.Stats

First batch after reopening the formalization line in CI-only mode.
Small statements on purpose: the point is the loop (write -> push -> CI),
not difficulty. Every proof is checked by `lake build` in CI.
-/

namespace Sandrone

/-- Twice the sum of `0..n` is `n * (n + 1)`. -/
theorem two_mul_sum_range (n : ℕ) :
    2 * (∑ i in Finset.range (n + 1), i) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, Nat.mul_add, ih]
      ring

/-- A finite set has `2 ^ card` subsets. -/
theorem card_finset {α : Type*} [Fintype α] :
    Fintype.card (Finset α) = 2 ^ Fintype.card α := by
  simp

/-- Squares are nonnegative, so `-x^2 <= x^2`. -/
theorem neg_sq_le_sq (x : ℤ) : -x ^ 2 ≤ x ^ 2 := by
  nlinarith [sq_nonneg x]

/-- Sum of squares of integers is nonnegative. -/
theorem sq_add_nonneg (a b : ℤ) : 0 ≤ a ^ 2 + b ^ 2 := by
  positivity

/-- Twice the sum `0..n-1` is `n * (n - 1)`; stated over `ℤ` to avoid truncated subtraction. -/
theorem two_mul_sum_range_int (n : ℕ) :
    2 * (∑ i in Finset.range n, (i : ℤ)) = (n : ℤ) * ((n : ℤ) - 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      push_cast
      ring

/-- Difference of squares factors over the integers. -/
theorem sq_sub_sq_int (a b : ℤ) : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by
  ring

/-- A sum of squares over `range n` is nonnegative. -/
theorem sum_range_sq_nonneg (n : ℕ) :
    0 ≤ ∑ i in Finset.range n, (i : ℤ) ^ 2 := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg i)

end Sandrone
