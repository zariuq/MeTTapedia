/- Lean 10 — tactic-mode proving (source: TPiL4 Tactics). Vanilla Lean 4.
   The interactive layer real proofs are written in. -/
namespace L10

-- intro / apply / exact
theorem imp_trans (P Q R : Prop) (h1 : P → Q) (h2 : Q → R) : P → R := by
  intro p; apply h2; apply h1; exact p

-- cases / anonymous constructor on conjunction and disjunction
theorem and_comm' (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h; cases h with | intro hp hq => exact ⟨hq, hp⟩

theorem or_comm' (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h; cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

-- induction + rw
theorem zero_add' (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]

-- simp / omega decision procedures
theorem add_zero' (n : Nat) : n + 0 = n := by simp
theorem lt_succ (n : Nat) : n < n + 1 := by omega

-- constructor for an existential
theorem exists_three : ∃ n : Nat, n = 3 := by exact ⟨3, rfl⟩

-- calc-style reasoning
theorem calc_cong (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  calc a + 1 = b + 1 := by rw [h]

end L10
