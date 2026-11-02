import Mathlib.Tactic

/-!
# First-occurrence numbering under a retained caller context

The numbered stream is extracted from a term traversal. Previously seen
cells keep their ordinal; new cells extend the single shared context. A
streaming validator checks whether an already stored key has exactly those
ordinals, without constructing a replacement term. Its success is equivalent
to the independent numbered-stream result, including the outgoing context.

This proves the variable-numbering boundary, not the runtime traversal's
coverage, cell/frame identity construction, or the full term alpha codec.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ContextualAlphaNumbering

variable {Cell : Type} [DecidableEq Cell]

def next (seen : List Cell) (cell : Cell) : Nat × List Cell :=
  if cell ∈ seen then (seen.idxOf cell, seen) else (seen.length, seen ++ [cell])

def number : List Cell → List Cell → List Nat × List Cell
  | seen, [] => ([], seen)
  | seen, cell :: rest =>
      let first := next seen cell
      let later := number first.2 rest
      (first.1 :: later.1, later.2)

/-- This validator consumes stored ordinals and publishes only the context,
whereas `number` constructs the complete numbered output independently. -/
def check : List Cell → List (Cell × Nat) → Option (List Cell)
  | seen, [] => some seen
  | seen, (cell, ordinal) :: rest =>
      if cell ∈ seen then
        if ordinal = seen.idxOf cell then check seen rest else none
      else if ordinal = seen.length then check (seen ++ [cell]) rest else none

theorem check_next (seen : List Cell) (cell : Cell) (ordinal : Nat) (rest : List (Cell × Nat)) :
    check seen ((cell, ordinal) :: rest) =
      if ordinal = (next seen cell).1 then check (next seen cell).2 rest else none := by
  by_cases member : cell ∈ seen <;> simp [check, next, member]

theorem check_exact (seen : List Cell) (input : List (Cell × Nat)) (after : List Cell) :
    check seen input = some after ↔
      number seen (input.map Prod.fst) = (input.map Prod.snd, after) := by
  induction input generalizing seen with
  | nil => simp [check, number]
  | cons entry rest ih =>
      rcases entry with ⟨cell, ordinal⟩
      rw [check_next]
      by_cases same : ordinal = (next seen cell).1
      · simp only [if_pos same, ih, List.map_cons, number, Prod.mk.injEq, List.cons.injEq]
        simp [same, Prod.ext_iff]
      · simp only [if_neg same, reduceCtorEq, List.map_cons, number, Prod.mk.injEq, List.cons.injEq]
        exact iff_of_false (by simp) (by rintro ⟨⟨wrong, _⟩, _⟩; exact same wrong.symm)

/-- Numbering parts in sequence shares precisely one incoming/outgoing context. -/
theorem number_append (seen first second : List Cell) :
    number seen (first ++ second) =
      ((number seen first).1 ++ (number (number seen first).2 second).1,
        (number (number seen first).2 second).2) := by
  induction first generalizing seen with
  | nil => simp [number]
  | cons cell rest ih => simp [number, ih]

theorem next_keeps_known (seen : List Cell) (cell : Cell) (known : cell ∈ seen) :
    next seen cell = (seen.idxOf cell, seen) := by simp [next, known]

theorem next_preserves_prefix (seen : List Cell) (cell : Cell) :
    seen.IsPrefix (next seen cell).2 := by
  by_cases known : cell ∈ seen
  · simp [next, known]
  · exact ⟨[cell], by simp [next, known]⟩

theorem known_number_survives_extension (seen : List Cell) (known : Cell) (extra : List Cell)
    (present : known ∈ seen) : (seen ++ extra).idxOf known = seen.idxOf known :=
  List.idxOf_append_of_mem present

namespace Controls

theorem reset_changes_shared_variables :
    number ([] : List Nat) [10, 20, 20, 10] = ([0, 1, 1, 0], [10, 20]) ∧
    (number ([] : List Nat) [20, 10]).1 = [0, 1] := by decide

theorem repeated_part_keeps_ordinals :
    number ([] : List Nat) [10, 20, 10, 20] = ([0, 1, 0, 1], [10, 20]) := by decide

theorem standalone_key_can_fail_in_context :
    check ([] : List Nat) [(20, 0), (10, 1)] = some [20, 10] ∧
    check [10, 20] [(20, 0), (10, 1)] = none ∧
    check [10, 20] [(20, 1), (10, 0)] = some [10, 20] := by decide

end Controls

#print axioms check_exact
#print axioms number_append
#print axioms known_number_survives_extension

end Mettapedia.Machines.ContextualAlphaNumbering
