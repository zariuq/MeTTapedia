import Mettapedia.Languages.MeTTa.PeTTa.LibTransformReadsAtTheCall

/-!
# Resuming transform from prepared proposals

A run keeps the entry proposals and performs each requested firing against the
store left by the previous continuation. The trace law applies to routing
callbacks that themselves change the store.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.LibTransform

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)

/-- Consume a prepared frontier, executing one firing when its branch
is reached. The route of one firing finishes before the remaining guides
are used. -/
def resumeGuides {α : Type} (route : Answers → Search Store α)
    (source : Sources) (emit : Subst → Answers) :
    List Footprint → Search Store α
  | [], store => .done store
  | guide :: rest, store =>
      match fire store guide source emit with
      | none => resumeGuides route source emit rest store
      | some (after, publications) =>
          (route publications after).append (resumeGuides route source emit rest)

theorem resumeGuides_eq_bind {α : Type} (route : Answers → Search Store α)
    (source : Sources) (emit : Subst → Answers) (guides : List Footprint) :
    resumeGuides route source emit guides =
      (Search.superpose guides).bind (fun guide => (firing source emit guide).bind route) := by
  induction guides with
  | nil => rfl
  | cons guide rest ih =>
      funext store
      simp only [resumeGuides, Search.bind, Search.superpose, Trace.bind, firing]
      cases decision : fire store guide source emit with
      | none =>
          simp only [Trace.bind, Trace.append]
          exact congrFun ih store
      | some admission =>
          obtain ⟨after, publications⟩ := admission
          simp only [Trace.bind, LibTransformStep.append_done]
          congr 1

/-- The prepared and authored runs agree on the whole trace, including the
store after each result and all resumptions under a subsequent write. -/
theorem resumeGuides_eq_transformWith {α : Type} (route : Answers → Search Store α)
    (source : Sources) (emit : Subst → Answers) (store : Store) :
    resumeGuides route source emit (proposals store source) store =
      transformWith route source emit store :=
  congrFun (resumeGuides_eq_bind route source emit (proposals store source)) store

namespace Controls

open LibTransformStep.Controls (one two anyN dropTwo)

/-- A continuation which removes a later row distinguishes branch-per-match
execution from a single all-read firing. -/
theorem resume_after_write :
    let source := readSources [anyN] none
    let emit := instances (.var "x")
    let entry := [one, two]
    (LibTransformStep.under dropTwo
      (resumeGuides toCaller source emit (proposals entry source) entry)).1 = [.symbol "one"] := by
  dsimp only
  rw [resumeGuides_eq_transformWith]
  exact LibTransformStep.Controls.branch_per_match_misses_a_removed_row

theorem retain_all_read_after_write :
    let source := LibTransformStep.allRead anyN
    let emit := instances (.var "x")
    let entry := [one, two]
    (LibTransformStep.under dropTwo
      (resumeGuides toCaller source emit (proposals entry source) entry)).1 =
      [.symbol "one", .symbol "two"] := by
  dsimp only
  rw [resumeGuides_eq_transformWith]
  exact LibTransformStep.Controls.all_read_answers_a_removed_row

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.LibTransform
