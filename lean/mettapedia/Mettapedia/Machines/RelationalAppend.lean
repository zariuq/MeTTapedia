import Mettapedia.Machines.Cursor.ListCells

/-!
# Relational append as two resumable alternatives

The first input has a finite proper spine; the second input may be any
reference term, including an open or improper tail. `prepend` independently
specifies the result. `Derives` gives the empty-prefix alternative and the
one-cell continuation used by a relational implementation. A consumer may
suspend after either alternative without materializing every prefix.

This proves the structural step law. Native substitution and list-carrier
matching remain governed by `Cursor.ListCells`, rather than being assumed to
be ordinary expression equality.
-/
set_option autoImplicit false
namespace Mettapedia.Machines.RelationalAppend
open Cursor.ListCells

def prepend : List PT → PT → PT
  | [], tail => tail
  | head :: rest, tail => .cons head (prepend rest tail)

inductive Derives : List PT → PT → PT → Prop
  | empty (tail : PT) : Derives [] tail tail
  | step {head : PT} {rest : List PT} {tail result : PT} :
      Derives rest tail result → Derives (head :: rest) tail (.cons head result)

theorem derives_sound {front : List PT} {tail result : PT}
    (run : Derives front tail result) : prepend front tail = result := by
  induction run with
  | empty => rfl
  | step _ ih => exact congrArg _ ih

theorem derives_complete (front : List PT) (tail : PT) :
    Derives front tail (prepend front tail) := by
  induction front with
  | nil => exact .empty tail
  | cons head rest ih => exact .step ih

theorem derives_iff (front : List PT) (tail result : PT) :
    Derives front tail result ↔ prepend front tail = result := by
  constructor
  · exact derives_sound
  · intro equality
    rw [← equality]
    exact derives_complete front tail

/-- The empty-prefix witness is valid even when the result has no known spine. -/
theorem empty_witness (tail : PT) : Derives [] tail tail := .empty tail

/-- Decomposing a nonempty prefix neither loses nor invents a solution. -/
theorem nonempty_iff (head : PT) (rest : List PT) (tail result : PT) :
    Derives (head :: rest) tail result ↔
      ∃ next, result = .cons head next ∧ Derives rest tail next := by
  constructor
  · intro run
    cases run with
    | step previous => exact ⟨_, rfl, previous⟩
  · rintro ⟨next, rfl, previous⟩
    exact .step previous

namespace Controls

theorem open_tail :
    Derives [.atom 1, .atom 2] (.var 0)
      (.cons (.atom 1) (.cons (.atom 2) (.var 0))) :=
  .step (.step (.empty _))

theorem improper_tail :
    Derives [.atom 1] (.atom 7) (.cons (.atom 1) (.atom 7)) :=
  .step (.empty _)

/-- Rejecting all unbound-prefix calls loses the valid empty-prefix answer. -/
theorem rejecting_open_query_loses_witness :
    ∃ front, Derives front (.var 0) (.var 0) := ⟨[], .empty _⟩

/-- The recursive alternative must share its head with the output cell. -/
theorem wrong_head_rejected :
    ¬ Derives [.atom 1] .nil (.cons (.atom 2) .nil) := by
  intro run
  have wrong := derives_sound run
  simp [prepend] at wrong

/-- Treating an open tail as an empty list changes the relation. -/
theorem dropping_tail_rejected :
    ¬ Derives [.atom 1] (.var 0) (.cons (.atom 1) .nil) := by
  intro run
  have wrong := derives_sound run
  simp [prepend] at wrong
end Controls
end Mettapedia.Machines.RelationalAppend
