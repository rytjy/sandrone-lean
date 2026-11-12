import Mathlib

/-!
# Sandrone — first formalization

Three lemmas proved by hand (not aliases), used to establish that the
toolchain, the Mathlib cache, and CI all work end to end.
-/

namespace Sandrone

theorem sq_add (a b : Nat) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

theorem dvd_mul_right' (a b c : Nat) (h : a ∣ b) : a ∣ b * c := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k * c, by ring⟩

theorem reverse_reverse {α : Type*} (l : List α) : l.reverse.reverse = l := by
  simp

end Sandrone
