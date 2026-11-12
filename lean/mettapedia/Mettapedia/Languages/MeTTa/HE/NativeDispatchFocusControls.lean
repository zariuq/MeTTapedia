import Mettapedia.Languages.MeTTa.HE.NativeDispatchFocus
import Mettapedia.Languages.MeTTa.HE.RetainedNativeDispatchControls

/-!
# A native call under two context callers, including a repeated identity

The active leaf refers to the root's context identity through another
context. Updating that leaf changes the root's view, not the intervening
context's store. All three caller levels retain the shared reached world.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.NativeDispatchFocusControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open RecursiveTasks.Contextual RecursiveMachine.Contextual
open RetainedNativeDispatchControls NativeDispatchFocus

def path : CallPath Bool := .under false inner (.under true inner .here)
def initial : WorldConfiguration Bool Store :=
  {before with control := path.fill (.work (.call [] [] call Atom.atomType activation))}
def reached (fails : Bool) : WorldConfiguration Bool Store :=
  resumeAt dispatch path initial [] [] call Atom.atomType (.symbol "touch") [.grounded (.int 7)]
    (advance world true) (plan fails world true)
def raw (fails : Bool) : List Result := if fails then errorRows else rows world true
def onceInside (fails : Bool) : List Result := (raw fails).map (tuplePrepend (.symbol "inside"))
def twiceInside (fails : Bool) : List Result := (onceInside fails).map (tuplePrepend (.symbol "inside"))
def allAnswers (fails : Bool) : List Result := emitted ++ (outerRows ++ twiceInside fails)

theorem active_context_uses_the_complete_path : path.active true = true := rfl

theorem actual_two_level_step (fails : Bool) :
    WorldStep (environment fails).view (environment fails).services dispatch Completed.scopedLookup Policy.unmarked
      initial (reached fails) :=
  focused_step (environment fails) Policy.unmarked path initial [] [] call Atom.atomType activation
    (.symbol "touch") [.grounded (.int 7)] (outcome fails world true) (advance world true) (plan fails world true)
    rfl (by simp [call, Entry.Value.erase]) rfl (by simp [call, Entry.Value.erase, IsErrorRel])
    (produced fails world true) (prepared fails world true)

theorem reached_two_level_source (fails : Bool) :
    (reached fails).SourceRel (environment fails) Policy.unmarked (allAnswers fails) (advance world true) := by
  have first : WorldStackRel (environment fails) Policy.unmarked true (advance world true)
      inner (raw fails) (onceInside fails) (advance world true) := .cons (.tupleTail _ _) (.nil _)
  have second : WorldStackRel (environment fails) Policy.unmarked false (advance world true)
      inner (onceInside fails) (twiceInside fails) (advance world true) := .cons (.tupleTail _ _) (.nil _)
  have outer : WorldStackRel (environment fails) Policy.unmarked true (advance world true)
      stack (twiceInside fails) (outerRows ++ twiceInside fails) (advance world true) := .cons (.prepend _ _) (.nil _)
  refine ⟨twiceInside fails, outerRows ++ twiceInside fails, advance world true, ?_, outer, rfl⟩
  cases fails with
  | true => exact .context (.context (.returning errorRows) first) second
  | false => exact .context (.context (.work (completed_rows world true)) first) second

theorem complete_two_level_source (fails : Bool) :
    initial.SourceRel (environment fails) Policy.unmarked (allAnswers fails) (advance world true) := by
  apply (focused_source_iff (environment fails) Policy.unmarked path initial [] [] call Atom.atomType activation
    (.symbol "touch") [.grounded (.int 7)] (allAnswers fails) (advance world true) rfl
    (by simp [call, Entry.Value.erase]) rfl (by simp [call, Entry.Value.erase, IsErrorRel])).mpr
  exact ⟨outcome fails world true, advance world true, plan fails world true, produced fails world true,
    prepared fails world true, reached_two_level_source fails⟩

theorem actual_two_level_completion (fails : Bool) :
    WorldSteps (environment fails).view (environment fails).services dispatch Completed.scopedLookup Policy.unmarked
      initial ⟨advance world true, true, .returning [], [], allAnswers fails⟩ :=
  RecursiveExecution.Contextual.Stateful.source_to_finished (complete_two_level_source fails)

theorem the_repeated_context_identity_observes_its_own_write (fails : Bool) :
    (reached fails).world true = 41 ∧ (reached fails).world false = 5 := by
  cases fails <;> exact ⟨rfl, rfl⟩

theorem using_the_intervening_context_writes_the_wrong_store :
    (advance world false) true = 40 ∧ (advance world false) false = 6 ∧
      (advance world false) true ≠ (advance world true) true := by decide

theorem both_successful_copies_survive_both_callers :
    (twiceInside false).map (fun item => item.1.erase) =
      [.expression [.symbol "inside", .symbol "inside", .grounded (.int 40)],
       .expression [.symbol "inside", .symbol "inside", .grounded (.int 40)]] := by cbv

end Mettapedia.Languages.MeTTa.HE.NativeDispatchFocusControls
