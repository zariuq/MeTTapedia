import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnScopes
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundSelectedControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkDepth

/-!
# Actual collapse entry and retained compound-caller controls

The fixture begins at a typed body boundary, not an asserted complete native
call. Its collapse entry is executed by the existing host. The actual mark
update saves the selected obligation on the caller, not the arbitrary child
answers. Erasing it is not an allowed alternative annotation.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundScopeControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks)
open PettaCompoundReturnControls (program recipe argument num text call services)
open PettaCompoundSelectedControls (saved context)

def expression : Atom := call "superpose" [.expression [num 7, num 7]]
def bodyControl : DControl :=
  ⟨[(.var "number", num 4)], [.evaluate (call "collapse" [expression]) (.var "collected"),
    .evaluate recipe (.var "out")], .var "out", ∅, 0⟩
def current : Scope Unit := ⟨[(bodyControl, context, [7])], [], none⟩
def before : State Unit :=
  (Allocator.empty 8 64, ⟨{state := Effects.loaded (program false false), output := [text "before"]}, [current]⟩)
def caller : CollectionCaller (Context Unit) :=
  ({bodyControl with goals := [.evaluate recipe (.var "out")]}, .var "collected", context, [7])
def child : Scope Unit :=
  ⟨[(collapseChild bodyControl (collectionSupport before.2) expression, context, [7])], [], some caller⟩
def entered : State Unit := (before.1, ⟨before.2.world, [child, {current with frontier := []}]⟩)
def initialMarks : List Marks := [⟨[some 0], none⟩]
def enteredMarks : List Marks := [⟨[none], some 0⟩, ⟨[], none⟩]

private theorem body_alias : Bridges.DestinationDataReturnState.AliasHolds (program false false) recipe bodyControl := by
  refine ⟨recipe, Bridges.DestinationDataReturnFunction.checksData_sound _ _ (by cbv), fun _ _ => rfl, .inr (.inl ?_)⟩
  exact (Bridges.ScopedReturnObligation.Pending.evaluation recipe [] .leaf).prepend_evaluation
    (call "collapse" [expression]) (.var "collected")

theorem initial_selected_obligation_is_earned :
    PettaCompoundReturnScopes.Stack (program false false) saved recipe initialMarks before.2.scopes := by
  refine .cons ⟨.cons ?_ .nil, ?_⟩ .nil
  · intro index selected
    cases Option.some.inj selected
    exact PettaCompoundSelectedWork.at_head _ _ _ _ [] rfl body_alias
  · intro index impossible; cases impossible

theorem the_actual_host_enters_the_child :
    PettaOccurrenceOverlay.step services .eagerValue (program false false) before = .silent entered := by cbv

theorem the_actual_update_saves_the_caller_not_the_child :
    PettaReturnMarkUpdate.advance initialMarks before entered = some enteredMarks := by cbv

theorem compound_scope_obligation_survives_the_actual_entry :
    PettaCompoundReturnScopes.Stack (program false false) saved recipe enteredMarks entered.2.scopes :=
  PettaCompoundReturnScopes.collection_push current [] [] bodyControl context [7] [] (some 0) [] none
    initial_selected_obligation_is_earned rfl expression (.var "collected") [.evaluate recipe (.var "out")] rfl child rfl

theorem a_child_mark_is_not_the_computed_layout :
    PettaReturnMarkUpdate.advance initialMarks before entered ≠ some [⟨[some 0], none⟩, ⟨[], none⟩] := by
  rw [the_actual_update_saves_the_caller_not_the_child]
  intro impossible
  cases impossible

theorem dropping_the_saved_caller_mark_is_not_the_computed_layout :
    PettaReturnMarkUpdate.advance initialMarks before entered ≠ some [⟨[none], none⟩, ⟨[], none⟩] := by
  rw [the_actual_update_saves_the_caller_not_the_child]
  intro impossible
  cases impossible

theorem a_child_cannot_claim_the_selected_parent_depth :
    ¬ PettaReturnMarkDepth.Depths 1 [⟨[some 0], none⟩, ⟨[], none⟩] := by
  intro held
  have wrong := PettaReturnMarkDepth.frontier_owner held 0 List.mem_cons_self
  norm_num at wrong

theorem arbitrary_copied_answers_restore_the_actual_caller (copies : List (Atom × List Atom)) :
    PettaCompoundReturnScopes.Stack (program false false) saved recipe [⟨[some 0], none⟩]
      [{current with frontier := [Source.resumeCopies copies caller]}] :=
  PettaCompoundReturnScopes.collection_resume child {current with frontier := []} [] ⟨[none], some 0⟩ ⟨[], none⟩ []
    compound_scope_obligation_survives_the_actual_entry caller rfl copies

def observation : Option (List Atom × List Atom × List Atom) :=
  match (PettaOccurrenceOverlay.machine services .eagerValue (program false false)).run 80 before with
  | (packets, .finished final) => do
      let collected ← packets.mapM fun packet => do
        let environment ← resolve packet.bindings
        pure (read environment (.var "collected"))
      pure (packets.map CollectedAnswer.value, collected, final.2.world.output)
  | _ => none

theorem duplicate_child_answers_do_not_replace_the_compound_body_result :
    observation = some ([argument], [.expression [num 7, num 7]], [text "before"]) := by cbv

theorem dropping_a_collected_duplicate_changes_the_observation :
    observation ≠ some ([argument], [.expression [num 7]], [text "before"]) := by
  rw [duplicate_child_answers_do_not_replace_the_compound_body_result]
  intro impossible
  cases impossible

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundScopeControls
