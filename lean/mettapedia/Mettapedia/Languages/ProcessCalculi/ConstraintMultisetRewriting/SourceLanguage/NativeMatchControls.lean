import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.NativeMatchKernel
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.AnswerCollection

/-!
# Binding-aware native matching, and an invalid match that is refused

The matched datum is an intrinsically scoped lambda, not an encoded flat
token. Its body retains its bound variable. A numeric pattern cannot match
the same lambda, even though admission is expressed by semantic solvability.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.NativeQuery.MatchControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration Toolkit MatchKernel

def identity : MData := lamAt bv
def closedIdentity : MClosed := .op .lam (.cons (.var .zero) .nil)
def pattern : MData := mvar [60] 0
def row : Row mkeys [] () := ⟨identity, []⟩
abbrev D : Discipline MSig [] () := ⟨MTy, fun _ _ => True⟩
def duplicateRow : Row mkeys [] () := ⟨num 1, []⟩
def duplicateWorld : World mkeys [] () := ⟨0, 0, fun _ => {duplicateRow, duplicateRow}⟩

theorem binding_match_live : Solvable ([] ++ rowUse 0 row pattern) :=
  ⟨Empty, noNames, closeNames [(([], [60], 0), closedIdentity)] (cnum 0), fun equation member => by
    obtain rfl := List.mem_singleton.mp member
    rfl⟩

theorem binding_match_fires :
    (firing 0 [] pattern pattern row).Admits MatchKernel.X (initial 0 [] pattern pattern row) :=
  admitted_of_source 0 [] pattern pattern row binding_match_live

theorem invalid_match_dead : ¬ Solvable ([] ++ rowUse 0 row (num 1)) := by
  rintro ⟨Names, declaration, point, known⟩
  have impossible := known _ (List.mem_singleton_self _)
  change (Term.op (Sum.inl (MOp.num 1)) .nil : Term (signature MSig declaration) [] ()) =
    Term.op (Sum.inl MOp.lam) (.cons (.var .zero) .nil) at impossible
  cases impossible

theorem invalid_match_refused :
    ¬ (firing 0 [] (num 1) pattern row).Admits MatchKernel.X (initial 0 [] (num 1) pattern row) :=
  fun admitted => invalid_match_dead ((admitted_iff_source 0 [] (num 1) pattern row).mp admitted)

/-- The source duplicate-row example really has an admitted native match,
independent of the collector's later treatment of its answer occurrences. -/
theorem duplicate_example_match_fires :
    (firing 0 [] (num 1) (num 7) duplicateRow).Admits MatchKernel.X
      (initial 0 [] (num 1) (num 7) duplicateRow) :=
  admitted_of_source 0 [] (num 1) (num 7) duplicateRow
    ⟨Empty, noNames, closeNames [] (cnum 0), fun equation inside => by
      simp only [rowUse, duplicateRow, copyStore, List.map_nil, List.nil_append,
        List.mem_singleton] at inside
      subst equation
      rfl⟩

def bound (value : Int) : Branch mkeys [] () MTy :=
  ⟨[(foD [] [9] 0, num value)], .value (num 7), [], []⟩

theorem bound_live (value : Int) : Solvable (bound value).store :=
  ⟨Empty, noNames, closeNames [(([], [9], 0), cnum value)] (cnum 0), fun equation inside => by
    obtain rfl := List.mem_singleton.mp inside
    rw [instantiate_foD]
    simp [closeNames]
    rfl⟩

theorem captured_reopening_rejects_conflicting_caller :
    ¬ Solvable (AnswerCollection.resume (D := D) (bound 1) (bound 0)).store := by
  rintro ⟨Names, declaration, point, known⟩
  obtain ⟨one, zero⟩ := (AnswerCollection.resume_models point _ _).mp known
  have readsOne := one _ (List.mem_singleton_self _)
  have readsZero := zero _ (List.mem_singleton_self _)
  have impossible : (Term.op (Sum.inl (MOp.num 1)) .nil : Term (signature MSig declaration) [] ()) =
      Term.op (Sum.inl (MOp.num 0)) .nil := readsOne.symm.trans readsZero
  cases impossible

def copiedPoint : Assignment (fam mkeys) noNames :=
  closeNames [(([], [9], 0), cnum 1), (([4], [9], 0), cnum 0)] (cnum 0)

/-- Generative row copying and captured-answer reopening have different
binding policies: copying freshens the row name, while reopening preserves
the captured caller identity. -/
theorem copying_captured_names_changes_sharing :
    Solvable ((bound 1).store ++ rowUse 4 ⟨num 7, (bound 0).store⟩ (num 7)) ∧
      ¬ Solvable (AnswerCollection.resume (D := D) (bound 1) (bound 0)).store :=
  ⟨⟨Empty, noNames, copiedPoint, by decide⟩, captured_reopening_rejects_conflicting_caller⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.NativeQuery.MatchControls
