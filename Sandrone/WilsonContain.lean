import Mathlib
import Sandrone.Wilson

/-!
# Sandrone.WilsonContain

The sample proportion `x / n` lies inside the Wilson score interval.
-/

namespace Sandrone

/-- Squared gap between the sample proportion and the Wilson centre is at most
the squared half-width. -/
theorem wilson_sq_gap (n x : ℕ) (z : ℝ) (hx : x ≤ n) (hn : 0 < n) :
    ((x : ℝ) / (n : ℝ) - wilsonCenter n x z) ^ 2 ≤ (wilsonHalf n x z) ^ 2 := by
  have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hk : (0 : ℝ) < (n : ℝ) + z ^ 2 := by positivity
  have hx' : (x : ℝ) ≤ (n : ℝ) := by exact_mod_cast hx
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hNp : (0 : ℝ) ≤ (n : ℝ) - (x : ℝ) := by linarith
  have hprod : (0 : ℝ) ≤ (x : ℝ) * ((n : ℝ) - (x : ℝ)) := mul_nonneg hx0 hNp
  have hΔ : (0 : ℝ) ≤ (x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4 := by
    have h1 : (0 : ℝ) ≤ (x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) := div_nonneg hprod hN.le
    nlinarith [sq_nonneg z]
  have hleft : ((x : ℝ) / (n : ℝ) - wilsonCenter n x z) ^ 2
      = (z ^ 2 * ((x : ℝ) - (n : ℝ) / 2)) ^ 2 /
        ((n : ℝ) ^ 2 * ((n : ℝ) + z ^ 2) ^ 2) := by
    unfold wilsonCenter
    field_simp
    ring
  have hright : (wilsonHalf n x z) ^ 2
      = z ^ 2 * ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4) /
        ((n : ℝ) + z ^ 2) ^ 2 := by
    unfold wilsonHalf
    rw [div_pow, mul_pow, Real.sq_sqrt hΔ]
  rw [hleft, hright]
  have hkey : (0 : ℝ) ≤ (x : ℝ) * ((n : ℝ) - (x : ℝ)) * ((n : ℝ) + z ^ 2) :=
    mul_nonneg hprod hk.le
  field_simp
  nlinarith [hkey, hprod, sq_nonneg z]

/-- The sample proportion lies inside the Wilson score interval. -/
theorem wilson_contains (n x : ℕ) (z : ℝ) (hz : 0 ≤ z) (hx : x ≤ n) (hn : 0 < n) :
    wilsonLo n x z ≤ (x : ℝ) / (n : ℝ) ∧ (x : ℝ) / (n : ℝ) ≤ wilsonHi n x z := by
  have hsq := wilson_sq_gap n x z hx hn
  have hh := wilsonHalf_nonneg n x z hz hx hn
  have habs : |(x : ℝ) / (n : ℝ) - wilsonCenter n x z| ≤ wilsonHalf n x z :=
    abs_le_of_sq_le_sq hsq hh
  have hb := abs_le.mp habs
  constructor
  · unfold wilsonLo
    linarith [hb.1]
  · unfold wilsonHi
    linarith [hb.2]


/-- With `z = 1.96` the formal centre for 9 of 13 is the rational `13651/21052`
(≈ 0.648442), matching the published interval `[0.42, 0.87]`. -/
theorem wilsonCenter_thirteen_nine :
    wilsonCenter 13 9 (49 / 25 : ℝ) = 13651 / 21052 := by
  norm_num [wilsonCenter]


/-- The lower Wilson endpoint is nonnegative: the interval never leaves `[0, 1]` below. -/
theorem wilsonLo_nonneg (n x : ℕ) (z : ℝ) (hx : x ≤ n) (hn : 0 < n) :
    0 ≤ wilsonLo n x z := by
  have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hk : (0 : ℝ) < (n : ℝ) + z ^ 2 := by positivity
  have hx' : (x : ℝ) ≤ (n : ℝ) := by exact_mod_cast hx
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hNp : (0 : ℝ) ≤ (n : ℝ) - (x : ℝ) := by linarith
  have hprod : (0 : ℝ) ≤ (x : ℝ) * ((n : ℝ) - (x : ℝ)) := mul_nonneg hx0 hNp
  have hΔ : (0 : ℝ) ≤ (x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4 := by
    have h1 : (0 : ℝ) ≤ (x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) := div_nonneg hprod hN.le
    nlinarith [sq_nonneg z]
  have hlo : wilsonLo n x z
      = ((x : ℝ) + z ^ 2 / 2 -
          z * Real.sqrt ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4)) /
        ((n : ℝ) + z ^ 2) := by
    unfold wilsonLo wilsonCenter wilsonHalf
    field_simp
  rw [hlo]
  rcases le_total 0 z with hz | hz
  · have hsqrt : (0 : ℝ) ≤
        Real.sqrt ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4) := Real.sqrt_nonneg _
    have h1 : (0 : ℝ) ≤ z * Real.sqrt
        ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4) := mul_nonneg hz hsqrt
    have h2 : (0 : ℝ) ≤ (x : ℝ) + z ^ 2 / 2 := by positivity
    have hsq : z ^ 2 * ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4)
        ≤ ((x : ℝ) + z ^ 2 / 2) ^ 2 := by
      have hkey : (0 : ℝ) ≤ (x : ℝ) ^ 2 * ((n : ℝ) + z ^ 2) :=
        mul_nonneg (sq_nonneg _) hk.le
      field_simp
      nlinarith [hkey]
    have hs : (z * Real.sqrt
        ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4)) ^ 2
        ≤ ((x : ℝ) + z ^ 2 / 2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hΔ]
      exact hsq
    have habs := (sq_le_sq).mp hs
    rw [abs_of_nonneg h1, abs_of_nonneg h2] at habs
    exact div_nonneg (by linarith) hk.le
  · have hsqrt : (0 : ℝ) ≤
        Real.sqrt ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4) := Real.sqrt_nonneg _
    have hzle : z * Real.sqrt
        ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hz hsqrt
    exact div_nonneg (by nlinarith [sq_nonneg z]) hk.le

/-- The upper Wilson endpoint is at most one. -/
theorem wilsonHi_le_one (n x : ℕ) (z : ℝ) (hx : x ≤ n) (hn : 0 < n) :
    wilsonHi n x z ≤ 1 := by
  have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hk : (0 : ℝ) < (n : ℝ) + z ^ 2 := by positivity
  have hx' : (x : ℝ) ≤ (n : ℝ) := by exact_mod_cast hx
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hNp : (0 : ℝ) ≤ (n : ℝ) - (x : ℝ) := by linarith
  have hΔ : (0 : ℝ) ≤ (x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4 := by
    have h1 : (0 : ℝ) ≤ (x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) :=
      div_nonneg (mul_nonneg hx0 hNp) hN.le
    nlinarith [sq_nonneg z]
  have hhi : wilsonHi n x z
      = ((x : ℝ) + z ^ 2 / 2 +
          z * Real.sqrt ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4)) /
        ((n : ℝ) + z ^ 2) := by
    unfold wilsonHi wilsonCenter wilsonHalf
    field_simp
  rw [hhi, div_le_one hk]
  rcases le_total 0 z with hz | hz
  · have hsqrt : (0 : ℝ) ≤
        Real.sqrt ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4) := Real.sqrt_nonneg _
    have h1 : (0 : ℝ) ≤ z * Real.sqrt
        ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4) := mul_nonneg hz hsqrt
    have h2 : (0 : ℝ) ≤ ((n : ℝ) - (x : ℝ)) + z ^ 2 / 2 := by
      nlinarith [sq_nonneg z]
    have hsq : z ^ 2 * ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4)
        ≤ (((n : ℝ) - (x : ℝ)) + z ^ 2 / 2) ^ 2 := by
      have hkey : (0 : ℝ) ≤ ((n : ℝ) - (x : ℝ)) ^ 2 * ((n : ℝ) + z ^ 2) :=
        mul_nonneg (sq_nonneg _) hk.le
      field_simp
      nlinarith [hkey]
    have hs : (z * Real.sqrt
        ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4)) ^ 2
        ≤ (((n : ℝ) - (x : ℝ)) + z ^ 2 / 2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hΔ]
      exact hsq
    have habs := (sq_le_sq).mp hs
    rw [abs_of_nonneg h1, abs_of_nonneg h2] at habs
    linarith
  · have hsqrt : (0 : ℝ) ≤
        Real.sqrt ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4) := Real.sqrt_nonneg _
    have hzle : z * Real.sqrt
        ((x : ℝ) * ((n : ℝ) - (x : ℝ)) / (n : ℝ) + z ^ 2 / 4) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hz hsqrt
    nlinarith [sq_nonneg z]

end Sandrone
