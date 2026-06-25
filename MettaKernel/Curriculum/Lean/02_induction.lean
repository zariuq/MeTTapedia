/- ============================================================================
   Lean ladder 02 — Induction on Nat (prove the arithmetic laws by induction)
   (MeTTaKernel curriculum, DTT ladder, Lean 4 — vanilla)
   Style after the "Natural Number Game".  Check: `lean 02_induction.lean`.
   Note: Lean's `Nat.add` recurses on its SECOND argument, so `n + 0 = n` and
   `n + (k+1) = (n+k)+1` hold by computation; `0 + n` and `(n+1)+m` need induction.
   ========================================================================== -/
namespace ICL02

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]

-- `omega` is Lean's decision procedure for linear arithmetic over Nat/Int —
-- the idiomatic way to discharge these once the shape is understood.
theorem succ_add (n m : Nat) : (n + 1) + m = (n + m) + 1 := by omega

-- but the laws are equally provable by hand, by induction:
theorem add_comm (n m : Nat) : n + m = m + n := by
  induction m with
  | zero => rw [Nat.add_zero, Nat.zero_add]
  | succ k ih => rw [Nat.add_succ, ih, succ_add]

theorem add_assoc (n m p : Nat) : (n + m) + p = n + (m + p) := by omega

end ICL02
