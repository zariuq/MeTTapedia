-- NEGATIVE: a tactic proof that supplies the wrong term is rejected.
theorem bad (P Q : Prop) (h : P) : Q := by exact h
