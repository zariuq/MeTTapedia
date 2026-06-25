/- ============================================================================
   Lean ladder 03 — Propositions and Proofs (propositions-as-types)
   (MeTTaKernel curriculum, DTT ladder, Lean 4 — vanilla)
   Style after "Theorem Proving in Lean 4", ch. Propositions and Proofs.
   A proof of `p` is a term of type `p`; implication/∀ are functions.
   ========================================================================== -/
namespace ICL03

-- implication & ∀ as functions (term-mode proofs)
theorem imp_self (p : Prop) : p → p := fun hp => hp

theorem imp_trans (p q r : Prop) : (p → q) → (q → r) → (p → r) :=
  fun hpq hqr hp => hqr (hpq hp)

-- conjunction: anonymous constructor + projections
theorem and_comm (p q : Prop) : p ∧ q → q ∧ p :=
  fun h => ⟨h.right, h.left⟩

-- disjunction: case analysis
theorem or_comm (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

-- negation and falsity
theorem not_not_intro (p : Prop) : p → ¬¬p := fun hp hnp => hnp hp

theorem false_elim (p : Prop) : False → p := fun h => h.elim

-- existential: witness intro, `obtain` elim
theorem exists_zero : ∃ n : Nat, n = 0 := ⟨0, rfl⟩

theorem exists_elim (p : Nat → Prop) (q : Prop)
    (h : ∃ n, p n) (hpq : ∀ n, p n → q) : q := by
  obtain ⟨n, hn⟩ := h
  exact hpq n hn

end ICL03
