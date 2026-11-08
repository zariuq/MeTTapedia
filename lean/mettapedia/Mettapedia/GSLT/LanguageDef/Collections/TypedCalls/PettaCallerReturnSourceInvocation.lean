import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnSourceChoices

/-! Actual source invocation preserves the typed caller return view. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnSourceInvocation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open PettaOccurrenceOverlay PettaCallerReturnFrames

def Preserves {User : Type} (inputs : User → Atom)
    (action : Source.ScopeAction Allocator (Context User)) : Prop :=
  ∀ source ∈ RefinementTransport.actionStates action, PettaCallerReturnView.Holds inputs source

theorem silent_preserves {User : Type} {inputs : User → Atom} (source : State User)
    (held : PettaCallerReturnView.Holds inputs source) : Preserves inputs (.silent source) := by
  simpa only [Preserves, RefinementTransport.actionStates, List.mem_singleton, forall_eq] using held

theorem call_preserves {User : Type} {inputs : User → Atom} (source : State User) (request : ScopeBoundary)
    (held : PettaCallerReturnView.Holds inputs source) : Preserves inputs (.call request source) := by
  simpa only [Preserves, RefinementTransport.actionStates, List.mem_singleton, forall_eq] using held

theorem invocation_preserves {User : Type} (inputs : User → Atom) {program : SpaceSemantics.Program}
    {allocator : Allocator} {world : EagerDFS.World} {current : Scope User} {parents : List (Scope User)}
    {control : DControl} {context : Context User} {origins : List Nat} {pending : List (Work User)}
    {head : String} {arguments : List Atom} {destination : Atom} {older : List EagerDFS.Destination.Goal}
    {environment : Environment} {action : Source.ScopeAction Allocator (Context User)}
    (source : Source.Invocation Source.FreshOperations.owned program allocator world current parents control context
      origins pending head arguments destination older environment action)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke head arguments destination :: older)
    (resolved : resolve control.bindings = some environment)
    (noQuery : Bridges.ScopedQuerySource.queryStep (allocator, ⟨world, current :: parents⟩) = none)
    (noCase : Bridges.ScopedCaseSource.readyStep Bridges.ScopedQuerySource.plainQueryPattern
      (allocator, ⟨world, current :: parents⟩) = none)
    (held : PettaCallerReturnView.Holds inputs (allocator, ⟨world, current :: parents⟩)) : Preserves inputs action := by
  have tail (name : String) : Bridges.ScopedReturnObligation.Pending (.var name) control.destination control.goals →
      Bridges.ScopedReturnObligation.Pending (.var name) control.destination older := by
    intro returning
    exact Bridges.ScopedReturnRawEntry.pending_raw_invocation_tail name control.destination
      (allocator, ⟨world, current :: parents⟩) current parents control context origins pending head arguments destination
      older environment rfl frontier atCall resolved returning noQuery noCase
  cases source with
  | parsed text value after parseHead input returned =>
      apply silent_preserves
      apply PettaCallerReturnView.replace_active inputs _ current parents control context origins pending _ current.collected
        after world held rfl frontier
      intro captured
      exact PettaCallerReturnSourceChoices.primitive_choices inputs control context origins destination older [value] captured tail
  | primitive state values ordinary known returned =>
      apply silent_preserves
      apply PettaCallerReturnView.replace_active inputs _ current parents control context origins pending _ current.collected
        allocator {world with state} held rfl frontier
      intro captured
      exact PettaCallerReturnSourceChoices.primitive_choices inputs control context origins destination older values captured tail
  | equations selected ordinary known notIO declared selectedRows =>
      apply silent_preserves
      apply PettaCallerReturnView.replace_active inputs _ current parents control context origins pending _ current.collected
        allocator world held rfl frontier
      intro captured work member
      obtain ⟨choice, present, rfl⟩ := List.mem_map.mp member
      exact PettaCallerReturnSourceChoices.equation_frontier inputs
        (protectControl control (collectionSupport ⟨world, current :: parents⟩)) context head
        (arguments.map (read environment)) destination older _ selected pending.length
        (captured.protect_control _) tail selectedRows choice present
  | parseFault | parseAllocation | parseArity | primitiveFault | unserved => exact call_preserves _ _ held

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnSourceInvocation
