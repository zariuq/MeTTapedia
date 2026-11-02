import Mathlib.Data.List.MinMax
import Mathlib.Tactic

/-!
# Progress of an arbitrary finite rotating cursor family

Each productive operation strictly shortens the first cursor and moves it to
the end. Exhaustion of any cursor ends intersection. The positional bound
charges even an incomplete final round; it does not assume the shortest
cursor is first. Seeking and output costs are separate from these advances.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.CyclicProgress

inductive Execution : List Nat → Nat → Prop where
  | exhausted (sizes : List Nat) (empty : 0 ∈ sizes) : Execution sizes 0
  | step {first after work : Nat} {rest : List Nat}
      (positive : ∀ size ∈ first :: rest, 0 < size)
      (progress : after < first)
      (next : Execution (rest ++ [after]) work) :
      Execution (first :: rest) (work + 1)

theorem stops_at_empty {sizes : List Nat} {work : Nat}
    (execution : Execution sizes work) (empty : 0 ∈ sizes) : work = 0 := by
  cases execution with
  | exhausted => rfl
  | step positive progress next => exact False.elim (Nat.lt_irrefl 0 (positive 0 empty))

/-- A cursor at position `before.length` must be advanced once per complete
rotation. The extra position term is the unfinished rotation. -/
theorem positional_bound {sizes : List Nat} {work : Nat}
    (execution : Execution sizes work) :
    ∀ before value after, sizes = before ++ value :: after →
      work ≤ sizes.length * value + before.length := by
  induction execution with
  | exhausted sizes empty => intros; omega
  | @step first after work rest positive progress next ih =>
      intro before value suffix shape
      cases before with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at shape
          rcases shape with ⟨rfl, rfl⟩
          have bound := ih rest after [] (by simp)
          simp only [List.length_append, List.length_cons,
            List.length_nil, Nat.add_zero] at bound ⊢
          nlinarith
      | cons head before =>
          simp only [List.cons_append, List.cons.injEq] at shape
          rcases shape with ⟨rfl, rfl⟩
          have bound := ih before value (suffix ++ [after]) (by simp [List.append_assoc])
          simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at bound ⊢
          omega

theorem bound_by_any_cursor {sizes : List Nat} {work value : Nat}
    (execution : Execution sizes work) (member : value ∈ sizes) :
    work < sizes.length * (value + 1) := by
  obtain ⟨before, after, shape⟩ := List.mem_iff_append.mp member
  have bound := positional_bound execution before value after shape
  have position : before.length < sizes.length := by simp [shape]
  rw [Nat.mul_add, Nat.mul_one]
  omega

theorem total_bound {sizes : List Nat} {work : Nat}
    (execution : Execution sizes work) : work ≤ sizes.sum := by
  induction execution with
  | exhausted => omega
  | step positive progress next ih =>
      simp only [List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero] at ih ⊢
      omega

theorem positive_minimum_bound {sizes : List Nat} {work : Nat}
    (execution : Execution sizes work) {minimum : Nat}
    (chosen : sizes.min? = some minimum) :
    work ≤ sizes.length * (minimum + 1) := by
  exact Nat.le_of_lt (bound_by_any_cursor execution (List.min?_mem chosen))

namespace Controls

theorem three_cursors : Execution [3, 1, 5] 2 := by
  apply Execution.step (by simp) (show 2 < 3 by decide)
  apply Execution.step (by simp) (show 0 < 1 by decide)
  exact Execution.exhausted [5, 2, 0] (by simp)

theorem empty_middle_stops : ∀ work, Execution [5, 0, 8] work → work = 0 := by
  intro work execution
  exact stops_at_empty execution (by simp)

/-- Four successive advances of only the first side cannot borrow the
cyclic certificate, even though that side has four keys to discard. -/
theorem ignoring_rotation_is_not_admitted : ¬Execution [4, 1] 4 := by
  intro execution
  have bound := positional_bound execution [4] 1 [] rfl
  norm_num at bound

end Controls

end Mettapedia.Machines.Cursor.CyclicProgress
