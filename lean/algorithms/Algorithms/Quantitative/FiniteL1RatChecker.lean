/-
# Finite L1 Rational Checkers (Init-only)

Pure executable checker kernel for finite quantitative obligations.
No Mathlib imports.
-/

namespace Algorithms.Quantitative

universe u

/-- Canonical Boolean checker for a decidable proposition. -/
def propChecker (p : Prop) [Decidable p] : Bool := decide p

theorem prop_of_checker_true {p : Prop} [Decidable p]
    (h : propChecker p = true) : p := by
  by_cases hp : p
  · exact hp
  · simp [propChecker, hp] at h

theorem not_prop_of_checker_false {p : Prop} [Decidable p]
    (h : propChecker p = false) : ¬ p := by
  by_cases hp : p
  · simp [propChecker, hp] at h
  · exact hp

theorem checker_true_of_prop {p : Prop} [Decidable p]
    (hp : p) : propChecker p = true := by
  by_cases h : p
  · simp [propChecker, h]
  · exact (h hp).elim

theorem checker_false_of_not_prop {p : Prop} [Decidable p]
    (hp : ¬ p) : propChecker p = false := by
  by_cases h : p
  · exact (hp h).elim
  · simp [propChecker, h]

/-- Finite `L1` discrepancy over rationals on a list support. -/
def ratAbs (q : Rat) : Rat := if q < 0 then -q else q

/-- Finite `L1` discrepancy over rationals on a list support. -/
def finiteL1RatList {α : Type u} (xs : List α) (f g : α → Rat) : Rat :=
  (xs.map fun x => ratAbs (f x - g x)).sum

/-- Checker for `finiteL1RatList xs f g ≤ C`. -/
def finiteL1LeCheckerList {α : Type u} (xs : List α) (f g : α → Rat) (C : Rat) : Bool :=
  propChecker (finiteL1RatList xs f g ≤ C)

theorem finiteL1LeList_of_checker_true {α : Type u}
    {xs : List α} {f g : α → Rat} {C : Rat}
    (h : finiteL1LeCheckerList xs f g C = true) :
    finiteL1RatList xs f g ≤ C := by
  exact prop_of_checker_true (p := finiteL1RatList xs f g ≤ C) h

theorem not_finiteL1LeList_of_checker_false {α : Type u}
    {xs : List α} {f g : α → Rat} {C : Rat}
    (h : finiteL1LeCheckerList xs f g C = false) :
    ¬ finiteL1RatList xs f g ≤ C := by
  exact not_prop_of_checker_false (p := finiteL1RatList xs f g ≤ C) h

/-- Checker for a rate-style bound `finiteL1RatList xs f g ≤ C / R` with `R > 0`. -/
def finiteL1RateCheckerList {α : Type u}
    (xs : List α) (f g : α → Rat) (C R : Rat) : Bool :=
  propChecker (0 < R ∧ finiteL1RatList xs f g ≤ C / R)

theorem finiteL1RateList_of_checker_true {α : Type u}
    {xs : List α} {f g : α → Rat} {C R : Rat}
    (h : finiteL1RateCheckerList xs f g C R = true) :
    0 < R ∧ finiteL1RatList xs f g ≤ C / R := by
  exact prop_of_checker_true (p := 0 < R ∧ finiteL1RatList xs f g ≤ C / R) h

theorem not_finiteL1RateList_of_checker_false {α : Type u}
    {xs : List α} {f g : α → Rat} {C R : Rat}
    (h : finiteL1RateCheckerList xs f g C R = false) :
    ¬ (0 < R ∧ finiteL1RatList xs f g ≤ C / R) := by
  exact not_prop_of_checker_false (p := 0 < R ∧ finiteL1RatList xs f g ≤ C / R) h

end Algorithms.Quantitative
