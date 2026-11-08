import Mathlib.Tactic.Ring

/-!
# The cost of element-wise checks

A structural element check, such as a list of numbers, accepts a list exactly
when every element passes. Costs count element checks.

When a list becomes known one element at a time, re-checking every known
element after each arrival costs `n (n + 1) / 2` checks for `n` elements, while
checking only the new element costs `n`. Both report the same verdict after every
arrival, so an early failure is found at the same element.

A recursive walk that checks its argument on every call checks each suffix:
again `n (n + 1) / 2` element checks. When the check is a fixed predicate of the
value, passing the entry check implies that every suffix passes, so the inner
checks can be skipped without changing any answer. A check whose meaning can
change between calls, such as one that reads declarations a body may edit, is not
covered by this law.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ConstraintTypes.CheckCost

variable {α : Type} (check : α → Bool)

/-- Verdicts after each arrival when every arrival re-checks the whole known list. -/
def revalidate : List α → List α → List Bool
  | _, [] => []
  | known, x :: rest => (known ++ [x]).all check :: revalidate (known ++ [x]) rest

/-- Element checks spent by `revalidate`. -/
def revalidateCost : List α → List α → Nat
  | _, [] => 0
  | known, x :: rest => (known.length + 1) + revalidateCost (known ++ [x]) rest

/-- Verdicts after each arrival when only the new element is checked. -/
def accumulate : Bool → List α → List Bool
  | _, [] => []
  | sofar, x :: rest => (sofar && check x) :: accumulate (sofar && check x) rest

/-- Element checks spent by `accumulate`: one per arrival. -/
def accumulateCost (arrivals : List α) : Nat := arrivals.length

theorem revalidate_eq_accumulate (known arrivals : List α) :
    revalidate check known arrivals = accumulate check (known.all check) arrivals := by
  induction arrivals generalizing known with
  | nil => rfl
  | cons x rest ih =>
      simp only [revalidate, accumulate, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
      rw [ih]
      simp [List.all_append]

/-- Same verdict after every arrival, starting from an empty list. -/
theorem incremental_exact (arrivals : List α) :
    revalidate check [] arrivals = accumulate check true arrivals := by
  simpa using revalidate_eq_accumulate check [] arrivals

/-- After the last arrival, both report whether the whole list passes. -/
theorem accumulate_last (sofar : Bool) (arrivals : List α) (nonempty : arrivals ≠ []) :
    (accumulate check sofar arrivals).getLast? = some (sofar && arrivals.all check) := by
  induction arrivals generalizing sofar with
  | nil => exact absurd rfl nonempty
  | cons x rest ih =>
      cases rest with
      | nil => simp [accumulate]
      | cons y more =>
          have step := ih (sofar && check x) (List.cons_ne_nil y more)
          simp only [accumulate] at step ⊢
          rw [List.getLast?_cons_cons, step]
          simp [Bool.and_assoc]

theorem revalidateCost_closed (known arrivals : List α) :
    2 * revalidateCost known arrivals =
      arrivals.length * (2 * known.length + arrivals.length + 1) := by
  induction arrivals generalizing known with
  | nil => simp [revalidateCost]
  | cons x rest ih =>
      simp only [revalidateCost, List.length_cons]
      have step := ih (known ++ [x])
      rw [List.length_append, List.length_singleton] at step
      rw [Nat.mul_add, step]
      ring

/-- Re-checking costs `n (n + 1) / 2` element checks for `n` arrivals. -/
theorem revalidation_quadratic (arrivals : List α) :
    2 * revalidateCost [] arrivals = arrivals.length * (arrivals.length + 1) := by
  simpa using revalidateCost_closed [] arrivals

/-- Checking each arrival once costs `n`. -/
theorem incremental_linear (arrivals : List α) : accumulateCost arrivals = arrivals.length := rfl

/-- Element checks spent by a recursive walk that checks its argument on every call. -/
def walkCost : List α → Nat
  | [] => 0
  | x :: rest => (x :: rest).length + walkCost rest

theorem walk_quadratic (xs : List α) : 2 * walkCost xs = xs.length * (xs.length + 1) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      simp only [walkCost, List.length_cons]
      rw [Nat.mul_add, ih]
      ring

/-- A fixed check that accepts a list accepts each of its suffixes, so a walk's
inner checks on those suffixes always pass and can be skipped. -/
theorem entry_check_covers_suffixes (xs : List α) (passed : xs.all check = true) (k : Nat) :
    (xs.drop k).all check = true := by
  rw [List.all_eq_true] at passed ⊢
  intro x member
  exact passed x (List.mem_of_mem_drop member)

/-- With the inner checks skipped, the walk spends one check per element. -/
theorem skipped_walk_linear (xs : List α) : accumulateCost xs = xs.length := rfl

end Mettapedia.Logic.ConstraintTypes.CheckCost
