import Mettapedia.Languages.MeTTa.PeTTa.Unifying

/-!
# Scoped selection for all-match removal

The selection layer uses the existing scoped PeTTa unifier, including open stored
rows and exhaustion. Each row is tested independently after renaming. No shared
unifier across the selected rows is assumed. The return-value policy of the older
`Unifying.removeRows` model is not imported as a contract for current CeTTa.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.StoreAndDemand.PeTTaSelection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Unifying
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)

/-- An independent per-occurrence specification, retaining the selected count. -/
inductive Selection (pattern : Atom) : Nat → List Atom → List Atom → Nat → Prop
  | nil (use : Nat) : Selection pattern use [] [] 0
  | take {use : Nat} {row : Atom} {rest kept : List Atom} {count : Nat} {bindings : Subst}
      (matched : unify [] pattern (rename use row) = .ok bindings)
      (tail : Selection pattern (use + 1) rest kept count) :
      Selection pattern use (row :: rest) kept (count + 1)
  | keep {use : Nat} {row : Atom} {rest kept : List Atom} {count : Nat}
      (clashed : unify [] pattern (rename use row) = .clash)
      (tail : Selection pattern (use + 1) rest kept count) :
      Selection pattern use (row :: rest) (row :: kept) count

/-- The existing evaluator's selector realizes the per-row relation. -/
theorem selection_survivors {pattern : Atom} {use : Nat} {rows kept : List Atom} {count : Nat}
    (selected : Selection pattern use rows kept count) : survivors pattern use rows = some kept := by
  induction selected with
  | nil => rfl
  | take matched tail ih => simp [survivors, ih, matched]
  | keep clashed tail ih => simp [survivors, ih, clashed]

/-- Every successful evaluator selection has independent match evidence for every removed row. -/
theorem survivors_selection {pattern : Atom} {use : Nat} {rows kept : List Atom}
    (completed : survivors pattern use rows = some kept) :
    ∃ count, Selection pattern use rows kept count := by
  induction rows generalizing use kept with
  | nil =>
      simp only [survivors, Option.some.injEq] at completed
      subst kept
      exact ⟨0, .nil _⟩
  | cons row rest ih =>
      cases tail : survivors pattern (use + 1) rest with
      | none => simp [survivors, tail] at completed
      | some remaining =>
          obtain ⟨count, selected⟩ := ih tail
          cases matched : unify [] pattern (rename use row) with
          | ok bindings =>
              simp [survivors, tail, matched] at completed
              subst kept
              exact ⟨count + 1, .take matched selected⟩
          | clash =>
              simp [survivors, tail, matched] at completed
              subst kept
              exact ⟨count, .keep matched selected⟩
          | exhausted => simp [survivors, tail, matched] at completed

theorem selection_length {pattern : Atom} {use : Nat} {rows kept : List Atom} {count : Nat}
    (selected : Selection pattern use rows kept count) : kept.length + count = rows.length := by
  induction selected with
  | nil => rfl
  | take matched tail ih => simp only [List.length_cons]; omega
  | keep clashed tail ih => simp only [List.length_cons]; omega

theorem selection_preserves_order {pattern : Atom} {use : Nat} {rows kept : List Atom} {count : Nat}
    (selected : Selection pattern use rows kept count) : kept.Sublist rows := by
  induction selected with
  | nil => exact .slnil
  | take matched tail ih => exact ih.cons _
  | keep clashed tail ih => exact ih.cons_cons _

/-- A Boolean change report is equivalent to a nonzero selected-occurrence count. -/
theorem change_iff_selected {pattern : Atom} {use : Nat} {rows kept : List Atom} {count : Nat}
    (selected : Selection pattern use rows kept count) :
    decide (kept.length < rows.length) = true ↔ 0 < count := by
  have sizes := selection_length selected
  simp only [decide_eq_true_eq]
  omega

/-- Unifier exhaustion cannot certify a completed empty or negative selection. -/
theorem exhaustion_prevents_selection (pattern row : Atom) (use : Nat) (rest : List Atom)
    (exhausted : unify [] pattern (rename use row) = .exhausted) :
    survivors pattern use (row :: rest) = none := by
  cases tail : survivors pattern (use + 1) rest <;> simp [survivors, tail, exhausted]

namespace Controls

def item (atom : Atom) : Atom := .expression [.symbol "item", atom]

theorem independent_bindings_remove_both :
    survivors (item (.var "x")) 0 [item (.symbol "a"), item (.symbol "b")] = some [] := by
  decide

theorem open_stored_row_can_match :
    survivors (item (.symbol "a")) 0 [item (.var "stored")] = some [] := by decide

theorem nonmatching_row_survives :
    survivors (item (.symbol "a")) 0 [item (.symbol "b")] = some [item (.symbol "b")] := by
  decide

end Controls
end Mettapedia.Languages.MeTTa.StoreAndDemand.PeTTaSelection
