import Mettapedia.Languages.MeTTa.PeTTa.LibTransform
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingTransform

/-!
# Reads alone, against PeTTa's `match`

`SpaceSemantics.query` is the PeTTa folder's `match` of one pattern over the rows of a
space: the template under every matching row, in row order and with every duplicate. Its
matcher has PeTTa's list view, under which a `(cons h t)` pattern reads an expression by
head and tail; without it, the matcher is the structural one (`matchValue_eq_matchAtom`).
For such a pattern, a transform that reads it on a ground store gives exactly `query`'s
answers and leaves the store unchanged (`transform_read_eq_query`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.LibTransform

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (matchAtom applySubst isGroundAtom)

/-- `match` on one pattern without the list view is PeTTa's `query`. -/
theorem matchAnswers_single_eq_query (s : Store) (p template : Atom)
    (clear : UnifyingTransform.noListView p = true) :
    matchAnswers s [p] template = SpaceSemantics.query s p template := by
  have same : ∀ row, SpaceSemantics.matchValue [] p row = matchAtom [] p row := fun row =>
    UnifyingTransform.matchValue_eq_matchAtom _ [] p row le_rfl clear
  induction s with
  | nil => rfl
  | cons b s ih =>
      simp only [matchAnswers, matchConj, SpaceSemantics.query, same] at ih ⊢
      cases h : matchAtom [] p b <;> simp_all [matchesIn]

/-- **Law 1 against PeTTa's `match`.** On a ground store, reading one pattern without the
list view, into a template that is not a `,` conjunction, a transform answers exactly what
PeTTa's `query` answers, duplicates and order included, and leaves the store unchanged. -/
theorem transform_read_eq_query (s : Store) (ground : ∀ a ∈ s, isGroundAtom a = true)
    (p template : Atom) (clear : UnifyingTransform.noListView p = true)
    (plain : ¬ IsComma template) :
    (transform (readSources [p] none) template s).drain =
      (SpaceSemantics.query s p template, s) := by
  rw [transform_reads_eq_match s ground [p] none template plain]
  simp [matchAnswers_single_eq_query s p template clear]

end Mettapedia.Languages.MeTTa.PeTTa.LibTransform
