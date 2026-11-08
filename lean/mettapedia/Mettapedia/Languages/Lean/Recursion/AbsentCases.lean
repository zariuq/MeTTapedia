/-!
# Equations at refuted constructor cases

Lean states the equations of `Nat.div.go` and `Nat.modCore.go` only at
`fuel + 1`: at `fuel = 0` the hypothesis `x < fuel` is impossible, so the
equation compiler emits no equation there. A reading of these functions by
structural recursion on the fuel needs one equation per constructor. The
theorems below are the missing ones: vacuous, since their hypothesis is
refuted, and proved here, so every equation the reading uses is a Lean
theorem. Their right sides are the result type's first constructor.

The export reads `F.eq_absent` beside the equation theorems of `F`.
-/

theorem Nat.div.go.eq_absent (y : Nat) (hy : 0 < y) (x : Nat) (h : x < 0) :
    Nat.div.go y hy 0 x h = 0 :=
  absurd h (Nat.not_lt_zero x)

theorem Nat.modCore.go.eq_absent (y : Nat) (hy : 0 < y) (x : Nat) (h : x < 0) :
    Nat.modCore.go y hy 0 x h = 0 :=
  absurd h (Nat.not_lt_zero x)

/-! Positive and negative examples: the equation at `fuel + 1` computes, and
no proof of the impossible hypothesis exists. -/

example : Nat.div.go 7 (by decide) 24 23 (by decide) = 3 := by decide

example : ¬ ∃ x : Nat, x < 0 := fun ⟨x, h⟩ => Nat.not_lt_zero x h
