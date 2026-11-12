import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundSelectedWork
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnRaw

/-!
# Real source choice frontiers retain the selected compound return

Each generated work item keeps its actual context and reached constraints.
With an owned typed prefix, record extension protects its saved caller;
without one, the source's compound-return laws apply. Scalar query fusion
uses the actual primitive answers rather than a blanket tail-only premise.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundSelectedWork

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay
open Bridges.ScopedReturnObligation (Pending)

theorem protect_control {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame}
    {argument : Atom} {index : Nat} (control : DControl) (context : Context User) (origins : List Nat)
    (boundary : Finset String) (held : Holds program saved argument index (control, context, origins)) :
    Holds program saved argument index (protectControl control boundary, context, origins) := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  refine ⟨above, outside, length, calls, ?_⟩
  apply returning.source_step (after := protectControl control boundary) (.refl _)
  exact fun keptAlias => keptAlias.refinement (.refl _) rfl rfl

theorem primitive_choices {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame}
    {argument : Atom} {index : Nat} (control : DControl) (context : Context User) (origins : List Nat)
    (head : String) (destination : Atom) (older : List EagerDFS.Destination.Goal) (values : List Atom)
    (held : Holds program saved argument index (control, context, origins))
    (atCall : ∃ arguments, control.goals = .invoke head arguments destination :: older)
    (tail : ∀ recipe, Pending recipe control.destination control.goals → Pending recipe control.destination older) :
    ∀ work ∈ primitiveWork control context origins destination older values, Holds program saved argument index work := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  obtain ⟨arguments, atCall⟩ := atCall
  intro work member
  have sameContext : work.2.1 = context := by obtain ⟨row, present, rfl⟩ := List.mem_map.mp member; rfl
  have sameBindings : work.1.bindings = control.bindings := by obtain ⟨row, present, rfl⟩ := List.mem_map.mp member; rfl
  refine ⟨above, outside, length, (congrArg Context.calls sameContext).trans calls, ?_⟩
  apply returning.source_step (after := work.1)
  · rw [sameBindings]; exact .refl _
  · rintro ⟨recipe, data, obligation⟩
    exact ⟨recipe, data, Bridges.DestinationDataReturnDispatch.primitive_choices_with_tail control context origins head
      arguments destination older values obligation atCall (tail recipe) work member⟩

/-- Actual scalar-query answers may discharge the return at this head.
They must not be excluded by requiring the return to be in the suffix. -/
theorem primitive_answers {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame}
    {argument : Atom} {index : Nat} (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List EagerDFS.Destination.Goal)
    (environment : Environment) (state : Effects.State) (values : List Atom)
    (scopes : source.2.scopes = current :: parents) (front : current.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke head arguments destination :: older) (resolved : resolve control.bindings = some environment)
    (noQuery : Bridges.ScopedQuerySource.queryStep source = none)
    (noCase : Bridges.ScopedCaseSource.readyStep Bridges.ScopedQuerySource.plainQueryPattern source = none)
    (returned : StdLib.apply source.2.world.state head (arguments.map (read environment)) = .ok (state, values))
    (held : Holds program saved argument index (control, context, origins)) :
    ∀ work ∈ primitiveWork control context origins destination older values, Holds program saved argument index work := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  intro work member
  obtain ⟨⟨value, occurrence⟩, present, rfl⟩ := List.mem_map.mp member
  refine ⟨above, outside, length, calls, ?_⟩
  apply returning.source_step (after := {control with goals := .equate value destination :: older}) (.refl _)
  rintro ⟨recipe, data, obligation⟩
  refine ⟨recipe, data, ?_⟩
  apply Bridges.DestinationDataReturnDispatch.nondata_transition
    (after := {control with goals := .equate value destination :: older}) obligation atCall
    (by intro impossible; cases impossible) (fun _ solved => solved) rfl
  intro pendingReturn
  exact Bridges.DestinationDataReturnRaw.primitive_return_pending recipe control.destination source current parents control
    context origins pending head arguments destination older environment state values scopes front atCall resolved pendingReturn
    noQuery noCase returned value (List.fst_mem_of_mem_zipIdx present)

theorem equation_choices {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame}
    {argument : Atom} {index : Nat} (control : DControl) (context : Context User) (origins : List Nat)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List EagerDFS.Destination.Goal)
    (positions : List Nat) (selected : List (Nat × DControl)) (retained : Nat)
    (held : Holds program saved argument index (control, context, origins))
    (atCall : ∃ sourceArguments, control.goals = .invoke head sourceArguments destination :: older)
    (tail : ∀ recipe, Pending recipe control.destination control.goals → Pending recipe control.destination older)
    (frontier : ClauseChoice.Frontier program control head arguments destination older positions selected) :
    ∀ choice ∈ selected, Holds program saved argument index (predicateEntry retained choice.2, context, origins ++ [choice.1]) := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  induction frontier with
  | nil => simp
  | skip decision rest ih => exact ih
  | @keep occurrence remaining next answers decision rest ih =>
      intro choice member
      rcases List.mem_cons.mp member with rfl | later
      · refine ⟨above, outside, length, calls, ?_⟩
        apply returning.source_step (after := predicateEntry retained next)
        · cases decision with
          | selected equation bindings row sameHead matched => exact RefinementTransport.accepted_extends matched
        · rintro ⟨recipe, data, obligation⟩
          exact ⟨recipe, data, Bridges.DestinationDataReturnDispatch.equation_choice_with_tail control head arguments
            destination older occurrence retained next obligation atCall (tail recipe) decision⟩
      · exact ih choice later

theorem query_choices {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame}
    {argument : Atom} {index : Nat} (control : DControl) (context : Context User) (origins : List Nat)
    (space pattern body destination : Atom) (older : List EagerDFS.Destination.Goal) (rows : List Atom)
    (start : Nat) (selected : List (Nat × DControl))
    (held : Holds program saved argument index (control, context, origins))
    (atQuery : control.goals = .query space pattern body destination :: older)
    (frontier : QueryFrontier control pattern body destination older start rows selected) :
    ∀ choice ∈ selected, Holds program saved argument index (choice.2, context, origins ++ [choice.1]) := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  intro choice member
  refine ⟨above, outside, length, calls, ?_⟩
  apply returning.source_step (after := choice.2) (RefinementTransport.query_frontier_good frontier choice member)
  rintro ⟨recipe, data, obligation⟩
  exact ⟨recipe, data, Bridges.DestinationDataReturnDispatch.query_selected_return control space pattern body destination older
    rows start selected obligation atQuery frontier choice member⟩

theorem captured_choices {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame}
    {argument : Atom} {index : Nat} (control : DControl) (context : Context User) (origins : List Nat)
    (space pattern readPattern body destination : Atom) (older : List EagerDFS.Destination.Goal)
    (offset : Nat) (rows : List Atom) (selected : List (Nat × DControl))
    (held : Holds program saved argument index (control, context, origins))
    (atQuery : control.goals = .invoke "match" [space, pattern, body] destination :: older)
    (frontier : Bridges.ScopedQuerySource.Choices control readPattern body destination older offset rows selected) :
    ∀ choice ∈ selected, Holds program saved argument index (choice.2, context, origins ++ [choice.1]) := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  intro choice member
  refine ⟨above, outside, length, calls, ?_⟩
  apply returning.source_step (after := choice.2)
  · obtain ⟨suffix, record⟩ := (frontier.frames choice member).2.2.2.2.2.2.1
    rw [record]; exact RefinementTransport.append_extends _ _
  · rintro ⟨recipe, data, obligation⟩
    exact ⟨recipe, data, Bridges.DestinationDataReturnDispatch.captured_query_return control space pattern readPattern body
      destination older offset rows selected obligation atQuery frontier choice member⟩

theorem superpose_choices {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame}
    {argument : Atom} {index : Nat} (control : DControl) (context : Context User) (origins : List Nat)
    (alternatives : List Atom) (destination : Atom) (older : List EagerDFS.Destination.Goal)
    (held : Holds program saved argument index (control, context, origins))
    (atGoal : control.goals = .evaluate (.expression [.symbol "superpose", .expression alternatives]) destination :: older) :
    ∀ work ∈ superposeWork control context origins alternatives destination older, Holds program saved argument index work := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  intro work member
  have sameContext : work.2.1 = context := by obtain ⟨row, present, rfl⟩ := List.mem_map.mp member; rfl
  have sameBindings : work.1.bindings = control.bindings := by obtain ⟨row, present, rfl⟩ := List.mem_map.mp member; rfl
  refine ⟨above, outside, length, (congrArg Context.calls sameContext).trans calls, ?_⟩
  apply returning.source_step (after := work.1)
  · rw [sameBindings]; exact .refl _
  · rintro ⟨recipe, data, obligation⟩
    exact ⟨recipe, data, Bridges.DestinationDataReturnDispatch.superpose_choices_return data control context origins
      alternatives destination older obligation atGoal work member⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundSelectedWork
