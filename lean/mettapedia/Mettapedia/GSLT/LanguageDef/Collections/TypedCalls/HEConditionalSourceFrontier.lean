import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEConditionalEquationFrames

/-!
# Complete conditional equation frontier in the range source space

The source space contains both conditional clauses and the recursive range
equation. Completeness plus their actual heads and Boolean tests determines
exactly one physical conditional occurrence. The selected contextual frame
then exposes the whole held branch, including its nested evaluation marks.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEConditionalSourceFrontier

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps
open Spec.Type.Presentation Spec.Type.RuntimeRefinement
open HEConditionalEquationFrames (query pattern body)
open HEIfSourceSelection.Range (space)

private def headName : Atom → Option String
  | .expression (.symbol name :: _) => some name
  | _ => none

private def boolTest : Atom → Option Bool
  | .expression (_ :: .grounded (.bool value) :: _) => some value
  | _ => none

theorem reached_row (live : List Atom) (before : Frame) (condition : Bool) (yes no : Entry.Value)
    (works : List EquationWork) (work : EquationWork)
    (frontier : EquationFrontierRel space live (query condition yes no).erase before.bindings works)
    (member : work ∈ works) :
    work.position = (if condition then 4 else 5) ∧ work.left = pattern condition ∧ work.right = body condition := by
  obtain ⟨_, occurrence⟩ := frontier.occurrence member
  obtain ⟨valuation, model⟩ := occurrence.result.1.2
  have equation := ((occurrence.solutions valuation).mp model).1
  obtain ⟨rename, _, renamedPattern, _, _⟩ := occurrence.selected.1
  have patternEq := EquationFreshening.alphaRename_eq renamedPattern
  have stored := occurrence.stored
  have bound : work.position < 6 := by
    simpa [space, Space.ofList] using (List.getElem?_eq_some_iff.mp stored).1
  have positions : work.position = 0 ∨ work.position = 1 ∨ work.position = 2 ∨
      work.position = 3 ∨ work.position = 4 ∨ work.position = 5 := by omega
  rcases positions with zero | one | two | three | four | five
  · simp [space, Space.ofList, zero] at stored
  · simp [space, Space.ofList, one] at stored
  · simp [space, Space.ofList, two] at stored
  · have raw : work.left = HEFreshEquationFrames.Range.pattern ∧ work.right = HEFreshEquationFrames.Range.body := by
      simpa [space, Space.ofList, three] using stored.symm
    rw [patternEq, raw.1] at equation
    have heads := congrArg headName equation
    simp [query, Entry.Value.erase, HEFreshEquationFrames.Range.pattern, applyTypeValuation, renameTypeVars, headName] at heads
  · have raw : work.left = pattern true ∧ work.right = body true := by
      simpa [space, Space.ofList, four, pattern, body] using stored.symm
    rw [patternEq, raw.1] at equation
    have tests := congrArg boolTest equation
    have same : condition = true := by
      simpa [query, Entry.Value.erase, pattern, applyTypeValuation, renameTypeVars, boolTest] using tests
    subst condition
    exact ⟨four, raw⟩
  · have raw : work.left = pattern false ∧ work.right = body false := by
      simpa [space, Space.ofList, five, pattern, body] using stored.symm
    rw [patternEq, raw.1] at equation
    have tests := congrArg boolTest equation
    have same : condition = false := by
      simpa [query, Entry.Value.erase, pattern, applyTypeValuation, renameTypeVars, boolTest] using tests
    subst condition
    exact ⟨five, raw⟩

theorem complete_singleton (policy : Policy) (live : List Atom) (before : Frame)
    (condition : Bool) (yes no : Entry.Value)
    (yesClosed : TypeSubst.typeVars yes.erase = []) (noClosed : TypeSubst.typeVars no.erase = []) :
    ∃ (work : EquationWork) (after : Frame),
      EquationFrontierRel space live (query condition yes no).erase before.bindings [work] ∧
      after.bindings = work.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding before.environment (query condition yes no)
        (Entry.Value.ofAtom work.pattern) after.environment ∧
      after.read policy (Entry.Value.ofAtom work.body) = if condition then yes else no := by
  have stored : space.atoms[if condition then 4 else 5]? =
      some (.expression [.symbol "=", pattern condition, body condition]) := by cases condition <;> rfl
  obtain ⟨works, work, after, frontier, member, _, bound, unified, read⟩ :=
    HEConditionalEquationFrames.source_frame space policy live before condition yes no yesClosed noClosed _ stored
  cases works with
  | nil => cases member
  | cons first rest =>
      have firstPosition := (reached_row live before condition yes no _ first frontier (by simp)).1
      have restNil : rest = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro other present
        have otherPosition := (reached_row live before condition yes no _ other frontier (List.mem_cons_of_mem _ present)).1
        have distinct := (List.nodup_cons.mp frontier.positions_nodup).1
        exact distinct (List.mem_map.mpr ⟨other, present, otherPosition.trans firstPosition.symm⟩)
      subst rest
      have same := List.mem_singleton.mp member
      subst work
      exact ⟨first, after, frontier, bound, unified, read⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEConditionalSourceFrontier
