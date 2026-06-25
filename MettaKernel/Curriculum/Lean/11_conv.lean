/- Lean 11 — the `conv` tactic: navigate to a sub-term and rewrite *there*.
   (Source: TPiL4 Conv.) Vanilla Lean 4 (core `conv`, not the Mathlib conv_lhs macro). -/
namespace L11

-- rewrite inside a hypothesis, at a chosen position
theorem conv_in_hyp (a b : Nat) (h : a + 0 = b) : a = b := by
  conv at h => lhs; rw [Nat.add_zero]
  exact h

theorem conv_in_hyp2 (a b : Nat) (h : a * 1 = b) : a = b := by
  conv at h => lhs; rw [Nat.mul_one]
  exact h

-- rewrite only the left-hand side of the goal
theorem conv_goal (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  conv => lhs; rw [h]

end L11
