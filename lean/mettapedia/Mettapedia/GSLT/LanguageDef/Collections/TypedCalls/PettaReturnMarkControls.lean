import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkEntry
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypedReturnControls

/-!
# Controls for computed return lineage and actual guard outcomes

The guard controls execute the existing typed overlay and its live source
typing service. The cut and depth controls isolate metadata geometry; they
are not presented as complete source-originated call proofs.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks)
open PettaReturnMarkUpdate
open PettaTypedReturnControls (num text services unavailable program boundary)

def selected : List Marks := [⟨[some 0], none⟩]

theorem pushing_an_owned_call_changes_the_position :
    shift 3 4 (some 2) = some 3 ∧ shift 3 4 (some 2) ≠ some 2 := by decide

theorem popping_an_owned_call_restores_the_position :
    shift 4 3 (some 3) = some 2 ∧ shift 4 3 (some 0) = none := by decide

theorem argument_progress_is_not_a_frame_push :
    shift 3 3 (some 2) = some 2 ∧ shift 3 3 (some 2) ≠ some 3 := by decide

theorem no_selected_frame_can_be_invented (oldCount newCount : Nat) :
    shift oldCount newCount none = none := shift_none oldCount newCount

theorem zero_fuel_preserves_the_supplied_layout :
    runMarks services program 0 (boundary (.sym "Number") (num 4)) selected = some selected := rfl

theorem served_selected_guard_retires_its_mark :
    runMarks services program 1 (boundary (.sym "Number") (num 4)) selected =
      some [⟨[none], none⟩] := by cbv

theorem refused_selected_guard_has_no_generated_mark :
    runMarks services program 1 (boundary (.sym "Number") (text "wrong")) selected =
      some [⟨[], none⟩] := by cbv

theorem duplicate_guard_answers_are_two_physical_continuations :
    runMarks services program 1 (boundary (.var "a") (.symbol "dual")) selected =
      some [⟨[none, none], none⟩] := by cbv

theorem an_unserved_guard_retains_its_exact_mark :
    runMarks unavailable program 1 (boundary (.sym "Number") (num 4)) selected = some selected := by cbv

theorem replacing_an_unserved_mark_with_none_changes_the_update :
    runMarks unavailable program 1 (boundary (.sym "Number") (num 4)) selected ≠
      some [⟨[none], none⟩] := by
  rw [an_unserved_guard_retains_its_exact_mark]
  intro impossible
  cases impossible

def publications : Step Unit → List Atom
  | .publish answers _ => answers.map (·.value)
  | _ => []

theorem the_actual_typed_dispatcher_does_not_publish_a_refused_result :
    publications (PettaOccurrenceOverlay.step services .eagerValue program
      (boundary (.sym "Number") (text "wrong"))) = [] := by cbv

/-- Dropping the typed dispatcher is a genuine wrong-answer mutation, not
merely a different internal marker layout. -/
theorem bypassing_typed_dispatch_publishes_the_refused_result :
    publications (liftSource (Bridges.ScopedQuerySource.ownedStep .eagerValue program
      (boundary (.sym "Number") (text "wrong")))) = [text "wrong"] := by cbv

theorem a_child_scope_cannot_claim_the_parent_depth :
    ¬ PettaReturnMarkDepth.Depths 1 [⟨[some 0], none⟩, ⟨[], none⟩] := by
  intro held
  have wrong := PettaReturnMarkDepth.frontier_owner held 0 List.mem_cons_self
  norm_num at wrong

theorem a_mark_at_its_actual_child_depth_is_allowed :
    PettaReturnMarkDepth.Depths 2 [⟨[some 0], none⟩, ⟨[], none⟩] := by
  refine .cons ⟨?_, ?_⟩ (.cons ⟨?_, ?_⟩ .nil)
  · intro mark member index marked
    rfl
  · intro index impossible
    cases impossible
  · intro mark impossible
    cases impossible
  · intro index impossible
    cases impossible

private def shallow : CallFrame := PettaTypedReturnControls.frame (.sym "Number") (num 4)
private def deep : CallFrame := {shallow with head := "outer", scopeDepth := 2}
private def outOfOrder : Context Unit := ⟨(), [shallow, deep]⟩

theorem bounded_depths_alone_allow_the_wrong_top_depth :
    PettaFrameScopes.CallsAt 2 outOfOrder := by
  intro frame member
  change frame ∈ [shallow, deep] at member
  rcases List.mem_cons.mp member with rfl | later
  · norm_num [shallow, PettaTypedReturnControls.frame]
  · cases List.mem_singleton.mp later
    norm_num [deep]

theorem that_bounded_stack_is_not_ordered : ¬ PettaCallOrder.Ordered outOfOrder := by
  unfold PettaCallOrder.Ordered
  decide

theorem the_correct_depth_order_is_admitted :
    PettaCallOrder.Ordered (⟨(), [deep, shallow]⟩ : Context Unit) := by
  unfold PettaCallOrder.Ordered
  decide

private def cutControl : DControl :=
  {PettaTypedReturnControls.caller (num 4) with goals := [.commit], cutBoundary := 1}
private def cutContext : Context Unit := ⟨(), [PettaTypedReturnControls.frame (.sym "Number") (num 4)]⟩
private def cutWork : Work Unit := (cutControl, cutContext, [])
private def youngerWork : Work Unit := (cutControl, cutContext, [1])
private def olderWork : Work Unit := (cutControl, cutContext, [2])
private def cutScope : Scope Unit := ⟨[cutWork, youngerWork, olderWork], [], none⟩
private def beforeCut : State Unit :=
  (Allocator.empty 8 64, ⟨PettaTypedReturnControls.world, [cutScope]⟩)
private def afterCut : State Unit :=
  (beforeCut.1, ⟨beforeCut.2.world,
    [{cutScope with frontier := [({cutControl with goals := []}, cutContext, []), olderWork]}]⟩)

theorem cut_drops_only_the_matching_younger_annotation :
    advance [⟨[some 0, some 3, none], none⟩] beforeCut afterCut =
      some [⟨[some 0, none], none⟩] := by cbv

theorem an_active_return_is_not_mistaken_for_cut_filtering :
    frameActive (boundary (.sym "Number") (num 4)) = true ∧ frameActive beforeCut = false := by cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkControls
