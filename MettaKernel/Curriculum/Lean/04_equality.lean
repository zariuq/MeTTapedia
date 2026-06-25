/- ============================================================================
   Lean ladder 04 — Equality (Eq, rfl, symm, trans, congr, substitution)
   (MeTTaKernel curriculum, DTT ladder, Lean 4 — vanilla)
   Style after "Theorem Proving in Lean 4", ch. Quantifiers and Equality.
   ========================================================================== -/
namespace ICL04

theorem eq_compute : (2 + 2 : Nat) = 4 := rfl

theorem eq_symm (a b : Nat) (h : a = b) : b = a := h.symm

theorem eq_trans (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := h1.trans h2

theorem congr_succ (a b : Nat) (h : a = b) : a + 1 = b + 1 := congrArg (· + 1) h

-- substitution of equals (the `▸` rewrite operator)
theorem subst_pred (a b : Nat) (p : Nat → Prop) (h : a = b) (pa : p a) : p b := h ▸ pa

end ICL04
