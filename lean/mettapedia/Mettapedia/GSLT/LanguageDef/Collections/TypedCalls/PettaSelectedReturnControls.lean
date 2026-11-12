import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnSources
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnOperations
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnBoundary
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaArgumentControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnScopes

/-!
# Physical-position controls for selective return obligations

The synthetic stacks isolate occurrence identity and saved-continuation
mutations; they are not advertised as source-reachable complete calls. The
named source fixture's initial-state proof and actual argument controls remain
separate from these small stack countermodels.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay PettaCallerReturnFrames
open PettaSelectedReturnWork
open PettaCheckpointFixtures (num text call)

private def argument : Atom := .var "input"
private def wrong : Atom := text "intermediate"
private def world : EagerDFS.World := {state := Effects.loaded {equations := [], declarations := []}}
private def row : Row := ⟨[.sym "Atom"], .sym "Atom"⟩
private def saved : CallFrame :=
  ⟨"keep", row, [], [argument], 1, [], [], argument, 0, .var "callee", 1, .body⟩
private def active : DControl := ⟨[], [], wrong, ∅, 0⟩
private def duplicateContext : Context Unit := ⟨(), [saved, saved]⟩
private def duplicateWork : Work Unit := (active, duplicateContext, [3])

private theorem observed_alias (control : DControl) (recipe : Atom)
    (held : Bridges.ScopedReturnLocal.AliasHolds recipe control) (terminal : control.goals = []) :
    (resolve control.bindings).map (fun environment => read environment control.destination) =
      (resolve control.bindings).map (fun environment => read environment recipe) := by
  cases resolved : resolve control.bindings with
  | none => rfl
  | some environment =>
      simp only [Option.map_some]
      exact congrArg some (Bridges.ScopedReturnLocal.terminal_alias_observation recipe
        (⟨world, control, ()⟩ : Cursor Unit) held terminal environment resolved)

private theorem identity_caller (control : DControl) : CallerHolds argument control saved :=
  ⟨"input", fun _ _ => rfl, .inl (fun _ _ => rfl)⟩

theorem equal_frame_values_occur_at_both_positions :
    duplicateWork.2.1.calls[0]? = some saved ∧ duplicateWork.2.1.calls[1]? = some saved := ⟨rfl, rfl⟩

theorem the_second_occurrence_retains_the_return : Holds saved argument 1 duplicateWork := by
  exact ⟨[saved], [], rfl, rfl, .caller saved (identity_caller active)⟩

theorem the_first_occurrence_does_not_have_that_return : ¬ Holds saved argument 0 duplicateWork := by
  intro held
  have unequal :
      (resolve active.bindings).map (fun environment => read environment active.destination) ≠
        (resolve active.bindings).map (fun environment => read environment argument) := by
    cbv
    intro impossible
    cases impossible
  exact unequal (observed_alias active argument (head_alias held) rfl)

theorem frame_value_alone_cannot_select_the_return :
    duplicateWork.2.1.calls[0]? = duplicateWork.2.1.calls[1]? ∧
      Holds saved argument 1 duplicateWork ∧ ¬ Holds saved argument 0 duplicateWork := by
  exact ⟨rfl, the_second_occurrence_retains_the_return, the_first_occurrence_does_not_have_that_return⟩

theorem popping_an_owned_call_restores_position_zero :
    Holds saved argument 0 (resumeCaller active saved, (⟨(), [saved]⟩ : Context Unit), [3]) := by
  exact pop_inner active duplicateContext [3] saved [saved] the_second_occurrence_retains_the_return rfl

private def prefixControl : DControl := {active with goals := [.evaluate (call "helper" []) (.var "temporary")]}

theorem a_new_typed_prefix_call_moves_the_mark :
    Holds saved argument 2
      (rowWork prefixControl duplicateContext [3] 1 "helper" [] (.var "temporary") [] ⟨[], .sym "Atom"⟩ 0) := by
  have held : Holds saved argument 1 (prefixControl, duplicateContext, [3]) :=
    ⟨[saved], [], rfl, rfl, .caller saved (identity_caller prefixControl)⟩
  exact row_work prefixControl duplicateContext [3] held 1 "helper" [] (.var "temporary") []
    ⟨[], .sym "Atom"⟩ 0 rfl (by decide)

private def changedCaller : CallFrame := {saved with callerDestination := wrong}
private def changedWork : Work Unit := (active, (⟨(), [changedCaller, saved]⟩ : Context Unit), [3])

theorem correct_position_does_not_certify_changed_caller_fields :
    changedWork.2.1.calls[1]? = some saved ∧ ¬ Holds saved argument 1 changedWork := by
  refine ⟨rfl, ?_⟩
  intro held
  obtain ⟨above, outside, length, _stack, returning⟩ := active_prefix held rfl
  have empty : above = [] := List.eq_nil_of_length_eq_zero length
  subst above
  have unequal :
      (resolve (resumeCaller active changedCaller).bindings).map
          (fun environment => read environment (resumeCaller active changedCaller).destination) ≠
        (resolve (resumeCaller active changedCaller).bindings).map
          (fun environment => read environment argument) := by
    cbv
    intro impossible
    cases impossible
  exact unequal (observed_alias _ argument returning.resume_top.no_calls rfl)

private def outer : CallFrame := {saved with head := "outside", row := ⟨[], .sym "String"⟩, callerDestination := wrong}
private def ownControl : DControl := {active with destination := argument}
private def ownWork : Work Unit := (ownControl, (⟨(), [saved, outer]⟩ : Context Unit), [5])

theorem inherited_unrelated_return_is_not_a_precondition : Holds saved argument 0 ownWork := by
  exact at_head saved argument ownWork [outer] rfl ⟨"input", fun _ _ => rfl, .inl (fun _ _ => rfl)⟩

theorem imposing_the_old_whole_stack_obligation_would_reject_it :
    ¬ Frames argument ownControl ownWork.2.1.calls := by
  intro held
  have unequal :
      (resolve (viewControl ownControl ownWork.2.1.calls).bindings).map
          (fun environment => read environment (viewControl ownControl ownWork.2.1.calls).destination) ≠
        (resolve (viewControl ownControl ownWork.2.1.calls).bindings).map
          (fun environment => read environment argument) := by
    cbv
    intro impossible
    cases impossible
  exact unequal (observed_alias _ argument held.view rfl)

theorem named_source_fixture_starts_without_preinstalled_frames :
    PettaArgumentProgress.Safe PettaArgumentControls.initial := by
  exact PettaArgumentProgress.root_safe _ _ _ () []

private def collectingControl : DControl :=
  {ownControl with goals := [.evaluate (call "collapse" [wrong]) (.var "items")]}
private def collectingWork : Work Unit := (collectingControl, ownWork.2)
private def collectingScope : Scope Unit := ⟨[collectingWork], [], none⟩
private def collectingMarks : PettaSelectedReturnScopes.Marks := ⟨[some 0], none⟩
private def collectionChild : Scope Unit :=
  ⟨[duplicateWork], [], some ({collectingControl with goals := []}, .var "items", ownWork.2.1, ownWork.2.2)⟩
private def suspendedParent : Scope Unit := {collectingScope with frontier := []}

private theorem collecting_scope_held :
    PettaSelectedReturnScopes.ScopeHolds saved argument collectingMarks collectingScope := by
  refine ⟨.cons ?_ .nil, ?_⟩
  · intro index same
    cases Option.some.inj same
    exact at_head saved argument collectingWork [outer] rfl ⟨"input", fun _ _ => rfl, .inl (fun _ _ => rfl)⟩
  · intro index impossible
    cases impossible

theorem entering_collection_saves_the_mark_without_constraining_child_results :
    PettaSelectedReturnScopes.Stack saved argument
      [⟨[none], some 0⟩, ⟨[], none⟩] [collectionChild, suspendedParent] := by
  exact PettaSelectedReturnScopes.collection_push collectingScope [] [] collectingControl ownWork.2.1 ownWork.2.2 []
    (some 0) [] none (.cons collecting_scope_held .nil) rfl wrong (.var "items") [] rfl collectionChild rfl

theorem the_collection_child_need_not_return_the_outer_input :
    ¬ Holds saved argument 0 duplicateWork := the_first_occurrence_does_not_have_that_return

theorem completing_collection_restores_the_same_mark (copies : List (Atom × List Atom)) :
    PettaSelectedReturnScopes.Stack saved argument [⟨[some 0], none⟩]
      [{suspendedParent with frontier := [Source.resumeCopies copies
        ({collectingControl with goals := []}, .var "items", ownWork.2.1, ownWork.2.2)]}] := by
  exact PettaSelectedReturnScopes.collection_resume collectionChild suspendedParent [] ⟨[none], some 0⟩ ⟨[], none⟩ []
    entering_collection_saves_the_mark_without_constraining_child_results _ rfl copies

theorem a_saved_caller_mark_requires_an_actual_caller :
    ¬ PettaSelectedReturnScopes.ScopeHolds saved argument ⟨[some 0], some 0⟩ collectingScope := by
  intro held
  obtain ⟨_caller, impossible, _returning⟩ := held.2 0 rfl
  cases impossible

theorem frontier_annotations_cannot_silently_omit_a_position :
    ¬ PettaSelectedReturnScopes.Frontier saved argument [] [ownWork] := by
  intro held
  have length := PettaSelectedReturnScopes.Frontier.length held
  norm_num at length

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnControls
