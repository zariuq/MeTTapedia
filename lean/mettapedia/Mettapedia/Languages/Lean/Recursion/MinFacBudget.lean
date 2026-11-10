import Mathlib.Data.Nat.Sqrt

/-! A coarse computational budget that does not evaluate the proof's square root. -/

namespace Mettapedia.Languages.Lean.Recursion.MinFacBudget

theorem bound (n k : Nat) : n.sqrt + 2 - k < n + 3 := by
  have smaller := Nat.sqrt_le_self n
  omega

end Mettapedia.Languages.Lean.Recursion.MinFacBudget
