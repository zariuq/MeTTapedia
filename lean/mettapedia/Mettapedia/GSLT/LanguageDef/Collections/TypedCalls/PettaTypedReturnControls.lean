import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypedReturnDelivery
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSourceTypeServices

/-!
# Return-boundary controls with live source type queries

These execute the actual typed overlay at its return boundary. They distinguish
refusal, unserved queries, multiple typing alternatives and range erasure.
The completed prefix's output is part of the retained world throughout.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypedReturnControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay PettaTypedReturnDelivery

def num (value : Int) : Atom := .grounded (.int value)
def text (value : String) : Atom := .grounded (.string value)

def program : SpaceSemantics.Program where
  equations := []
  declarations :=
    [PettaSourceTypeRows.declaration "dual" (.sym "Number"),
     PettaSourceTypeRows.declaration "dual" (.sym "Bool")]
  layout := [.declaration, .declaration]

def world : EagerDFS.World := {state := Effects.loaded program, output := [num 7]}
def services : Services Unit := PettaSourceTypeServices.services []

def frame (range : Ty String) (value : Atom) : CallFrame :=
  ⟨"closed", ⟨[], range⟩, [], [], 0, [], [], value, 3, value, 1, .body⟩

def caller (value : Atom) : DControl := ⟨[], [], value, ∅, 9⟩
def context : Context Unit := ⟨(), []⟩
def emptyScope : Scope Unit := ⟨[], [], none⟩
def seed : State Unit := (Allocator.empty 8 64, ⟨world, [emptyScope]⟩)

def boundary (range : Ty String) (value : Atom) : State Unit :=
  attach seed emptyScope [] (caller value) context [11] [] (frame range value) []

def nextFrontier (operations : Services Unit) (range : Ty String) (value : Atom) : Option (List (Work Unit)) :=
  match PettaOccurrenceOverlay.step operations .eagerValue program (boundary range value) with
  | .silent next => next.2.scopes.head?.map (·.frontier)
  | _ => none

theorem number_return_has_one_continuation :
    (nextFrontier services (.sym "Number") (num 4)).map List.length = some 1 := by cbv

theorem wrong_range_has_no_continuation :
    (nextFrontier services (.sym "Number") (text "wrong")).map List.length = some 0 := by cbv

theorem erasing_the_range_admits_the_wrong_result :
    (nextFrontier services (.sym "%Undefined%") (text "wrong")).map List.length = some 1 := by cbv

theorem distinct_source_typings_remain_two_continuations :
    (nextFrontier services (.var "a") (.symbol "dual")).map List.length = some 2 := by cbv

def unavailable : Services Unit := { services with
  orderedGuard := fun _ _ _ _ _ => none
  guard_exact := by intro _ _ _ _ _ _ served; cases served }

theorem unserved_return_keeps_the_complete_boundary :
    PettaOccurrenceOverlay.step unavailable .eagerValue program (boundary (.sym "Number") (num 4)) =
      .call (.guard "closed" 0 (.sym "Number") (num 4)) (boundary (.sym "Number") (num 4)) := by cbv

def returnedWorld (range : Ty String) (value : Atom) : Option EagerDFS.World :=
  match PettaOccurrenceOverlay.step services .eagerValue program (boundary range value) with
  | .silent next => some next.2.world
  | _ => none

theorem refusal_preserves_the_completed_effect_prefix :
    returnedWorld (.sym "Number") (text "wrong") = some world := by cbv

theorem multiple_returns_do_not_replay_the_body_effect :
    returnedWorld (.var "a") (.symbol "dual") = some world := by cbv

theorem successful_return_restores_only_the_saved_continuation :
    (nextFrontier services (.sym "Number") (num 4)).map
      (List.map fun item => (item.1.bindings, item.1.goals, item.1.cutBoundary, item.2.1.calls, item.2.2)) =
      some [([], [], 3, [], [11, 0])] := by cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypedReturnControls
