import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnSource
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnBoundary
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundScopeControls

/-!
# Nonvacuous complete-source and arbitrary-destination boundary controls

The source preservation theorem is instantiated at the actual collapse-entry
fixture with derived call order and physical depths. Separate terminal-body
fixtures use a compound output destination, not a variable proxy. They check
the real guard, its refusal, solver suspension and an untyped-publication
mutation. These are body-boundary controls, not native call adequacy claims.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 24000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundSourceControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks)
open PettaCompoundReturnControls (program recipe argument services num text)

theorem collapse_fixture_has_actual_call_order : PettaCallOrder.Invariant PettaCompoundScopeControls.before := by
  constructor
  · apply PettaContextFacts.root_frontier_safe
    intro item member
    cases List.mem_singleton.mp member
    simp [PettaCallOrder.Ordered, PettaCompoundSelectedControls.context]
  · apply PettaFrameScopes.Scoped.root
    intro item member
    cases List.mem_singleton.mp member
    intro frame present
    cases List.mem_singleton.mp present
    exact ⟨by decide, by decide⟩

theorem collapse_fixture_has_earned_mark_depths :
    PettaReturnMarkDepth.Depths PettaCompoundSelectedControls.saved.scopeDepth PettaCompoundScopeControls.initialMarks :=
  PettaReturnMarkDepth.initial_depths (User := Unit) PettaCompoundSelectedControls.saved [] 1 0 rfl

theorem complete_owned_source_preservation_has_a_real_instance :
    PettaCompoundReturnScopes.Preserves (program false false) PettaCompoundSelectedControls.saved recipe
      PettaCompoundScopeControls.initialMarks PettaCompoundScopeControls.before
      (liftSource (Bridges.ScopedQuerySource.ownedStep .eagerValue (program false false) PettaCompoundScopeControls.before)) :=
  PettaCompoundReturnScopes.owned_step_keeps (program false false) PettaCompoundScopeControls.before
    PettaCompoundScopeControls.initialMarks PettaCompoundScopeControls.initial_selected_obligation_is_earned
    collapse_fixture_has_earned_mark_depths collapse_fixture_has_actual_call_order (by cbv)

def frame (bad : Bool) : CallFrame :=
  {PettaCompoundSelectedControls.saved with
    row := ⟨[.sym "Atom"], .sym (if bad then "Other" else "Box")⟩,
    ready := [argument], callDestination := argument, callerDestination := argument}
def control : DControl := ⟨[], [], argument, ∅, 0⟩
def context (bad : Bool) : Context Unit := ⟨(), [frame bad]⟩
def current (bad : Bool) : Scope Unit := ⟨[(control, context bad, [3])], [], none⟩
def boundary (bad : Bool) : State Unit :=
  (Allocator.empty 8 64, ⟨{state := Effects.loaded (program false bad), output := [text "before"]}, [current bad]⟩)
def marks : List Marks := [⟨[some 0], none⟩]

theorem the_actual_destination_is_not_a_variable : ¬∃ name, control.destination = .var name := by
  rintro ⟨name, impossible⟩
  cases impossible

private theorem terminal_alias (bad : Bool) : Bridges.DestinationDataReturnState.AliasHolds (program false bad) argument control := by
  refine ⟨argument, Bridges.DestinationDataReturnFunction.checksData_sound _ _ ?_, fun _ _ => rfl, .inl ?_⟩
  · cases bad <;> cbv
  · exact fun _ _ => rfl

theorem compound_terminal_is_actually_marked (bad : Bool) :
    PettaCompoundReturnScopes.Stack (program false bad) (frame bad) argument marks (boundary bad).2.scopes := by
  refine .cons ⟨.cons ?_ .nil, ?_⟩ .nil
  · intro index same
    cases Option.some.inj same
    exact PettaCompoundSelectedWork.at_head _ _ _ _ [] rfl (terminal_alias bad)
  · intro index impossible; cases impossible

theorem marked_guard_needs_no_variable_output (bad : Bool) :
    ∃ outside, (context bad).calls = frame bad :: outside ∧
      PettaOccurrenceOverlay.step services .eagerValue (program false bad) (boundary bad) =
        match resolve control.bindings with
        | none => .call (.source (.branch .invalidEnvironment)) (boundary bad)
        | some environment => consumeBody services (boundary bad) (current bad) [] control (context bad) [3] []
            (frame bad) outside (read environment argument) :=
  PettaCompoundReturnBoundary.marked_dispatch (program false bad) (frame bad) argument services (boundary bad)
    (current bad) [] control (context bad) [3] [] [] none [] (compound_terminal_is_actually_marked bad)
    (PettaReturnMarkDepth.initial_depths (User := Unit) (frame bad) [] 1 0 rfl) rfl rfl rfl rfl

def observe (bad : Bool) : Option (List Atom × List Atom) :=
  match (PettaOccurrenceOverlay.machine services .eagerValue (program false bad)).run 5 (boundary bad) with
  | (packets, .finished final) => some (packets.map CollectedAnswer.value, final.2.world.output)
  | _ => none

theorem the_compound_destination_returns_through_its_actual_guard : observe false = some ([argument], [text "before"]) := by cbv
theorem a_refused_compound_destination_does_not_publish : observe true = some ([], [text "before"]) := by cbv

def publications : Step Unit → List Atom
  | .publish packets _ => packets.map CollectedAnswer.value
  | _ => []

theorem bypassing_the_typed_boundary_publishes_the_refused_compound_value :
    publications (liftSource (Bridges.ScopedQuerySource.ownedStep .eagerValue (program false true) (boundary true))) = [argument] := by cbv

def broken : State Unit :=
  let source := boundary false
  (source.1, {source.2 with scopes :=
    [⟨[({control with bindings := [(num 1, num 2)]}, context false, [3])], [], none⟩]})

theorem an_invalid_resolver_retains_the_original_request_state :
    PettaOccurrenceOverlay.step services .eagerValue (program false false) broken =
      .call (.source (.branch .invalidEnvironment)) broken := by cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundSourceControls
