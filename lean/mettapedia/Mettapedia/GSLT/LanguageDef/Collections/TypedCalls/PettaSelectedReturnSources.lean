import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnWork

/-!
# Source operations preserve the selected frame's return continuation

The source operations keep their actual controls, bindings and opaque
contexts. Only the proof's owned prefix is used by the existing return laws.
The inherited frame suffix is not asked to satisfy the body's contract.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnWork

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay PettaCallerReturnFrames

theorem local_source {User : Type} {saved : CallFrame} {argument : Atom} {index : Nat}
    {program : SpaceSemantics.Program} {before after : Cursor (Context User)} (origins : List Nat)
    (source : Source.Step .eagerValue program before (.silent after))
    (held : Holds saved argument index (before.control, before.context, origins))
    (noSequence : ∀ pairs body destination older,
      before.control.goals ≠ .evaluate (.expression [.symbol "let*", .expression pairs, body]) destination :: older) :
    Holds saved argument index (after.control, after.context, origins) := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  refine ⟨above, outside, length, ?_, ?_⟩
  · simpa only [RefinementTransport.silent_context_preserved source] using calls
  · apply returning.source_step
    · exact RefinementTransport.local_step_extends source _ (by simp [RefinementTransport.localRecords])
    · intro ordinary
      exact Bridges.ScopedReturnLocal.alias_silent_preserves argument ordinary noSequence source

theorem opening {User : Type} {saved : CallFrame} {argument : Atom} {index : Nat}
    (control : DControl) (context : Context User) (origins : List Nat)
    (held : Holds saved argument index (control, context, origins))
    (older : List EagerDFS.Destination.Goal) (boundary : Nat)
    (atGoal : control.goals = .openCommit :: older) :
    Holds saved argument index ({control with goals := older, cutBoundary := boundary}, context, origins) := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  exact ⟨above, outside, length, calls, PettaCallerReturnSourceChoices.opening returning older boundary atGoal⟩

theorem committing {User : Type} {saved : CallFrame} {argument : Atom} {index : Nat}
    (control : DControl) (context : Context User) (origins : List Nat)
    (held : Holds saved argument index (control, context, origins))
    (older : List EagerDFS.Destination.Goal) (atGoal : control.goals = .commit :: older) :
    Holds saved argument index ({control with goals := older}, context, origins) := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  exact ⟨above, outside, length, calls, PettaCallerReturnSourceChoices.committing returning older atGoal⟩

theorem collapse_caller {User : Type} {saved : CallFrame} {argument : Atom} {index : Nat}
    (control : DControl) (context : Context User) (origins : List Nat)
    (held : Holds saved argument index (control, context, origins))
    (child destination : Atom) (older : List EagerDFS.Destination.Goal)
    (atGoal : control.goals = .evaluate (.expression [.symbol "collapse", child]) destination :: older) :
    Holds saved argument index ({control with goals := older}, context, origins) := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  exact ⟨above, outside, length, calls, PettaCallerReturnSourceChoices.collapse_caller returning child destination older atGoal⟩

theorem primitive_choices {User : Type} {saved : CallFrame} {argument : Atom} {index : Nat}
    (control : DControl) (context : Context User) (origins : List Nat)
    (destination : Atom) (older : List EagerDFS.Destination.Goal) (values : List Atom)
    (held : Holds saved argument index (control, context, origins))
    (tail : ∀ name, Bridges.ScopedReturnObligation.Pending (.var name) control.destination control.goals →
      Bridges.ScopedReturnObligation.Pending (.var name) control.destination older) :
    ∀ item ∈ primitiveWork control context origins destination older values, Holds saved argument index item := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  intro item member
  obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
  refine ⟨above, outside, length, calls, ?_⟩
  exact PettaCallerReturnSourceChoices.primitive_choices (fun _ : User => argument) control
    {context with calls := above} origins destination older values returning tail _ (List.mem_map.mpr ⟨entry, present, rfl⟩)

theorem equation_choices {User : Type} {saved : CallFrame} {argument : Atom} {index : Nat}
    (program : SpaceSemantics.Program) (control : DControl) (context : Context User) (origins : List Nat)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List EagerDFS.Destination.Goal)
    (positions : List Nat) (selected : List (Nat × DControl)) (retained : Nat)
    (held : Holds saved argument index (control, context, origins))
    (tail : ∀ name, Bridges.ScopedReturnObligation.Pending (.var name) control.destination control.goals →
      Bridges.ScopedReturnObligation.Pending (.var name) control.destination older)
    (frontier : ClauseChoice.Frontier program control head arguments destination older positions selected) :
    ∀ choice ∈ selected,
      Holds saved argument index (predicateEntry retained choice.2, context, origins ++ [choice.1]) := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  intro choice member
  refine ⟨above, outside, length, calls, ?_⟩
  exact PettaCallerReturnSourceChoices.equation_frontier (fun _ : User => argument) control
    {context with calls := above} head arguments destination older positions selected retained returning tail frontier choice member

theorem query_choices {User : Type} {saved : CallFrame} {argument : Atom} {index : Nat}
    (control : DControl) (context : Context User) (origins : List Nat)
    (space pattern body destination : Atom) (older : List EagerDFS.Destination.Goal)
    (rows : List Atom) (start : Nat) (selected : List (Nat × DControl))
    (held : Holds saved argument index (control, context, origins))
    (atQuery : control.goals = .query space pattern body destination :: older)
    (frontier : QueryFrontier control pattern body destination older start rows selected) :
    ∀ choice ∈ selected, Holds saved argument index (choice.2, context, origins ++ [choice.1]) := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  intro choice member
  refine ⟨above, outside, length, calls, ?_⟩
  exact PettaCallerReturnSourceChoices.query_frontier (fun _ : User => argument) control
    {context with calls := above} space pattern body destination older rows start selected returning atQuery frontier choice member

theorem captured_choices {User : Type} {saved : CallFrame} {argument : Atom} {index : Nat}
    (control : DControl) (context : Context User) (origins : List Nat)
    (space pattern readPattern body destination : Atom) (older : List EagerDFS.Destination.Goal)
    (offset : Nat) (rows : List Atom) (selected : List (Nat × DControl))
    (held : Holds saved argument index (control, context, origins))
    (atQuery : control.goals = .invoke "match" [space, pattern, body] destination :: older)
    (frontier : Bridges.ScopedQuerySource.Choices control readPattern body destination older offset rows selected) :
    ∀ choice ∈ selected, Holds saved argument index (choice.2, context, origins ++ [choice.1]) := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  intro choice member
  refine ⟨above, outside, length, calls, ?_⟩
  exact PettaCallerReturnSourceChoices.captured_frontier (fun _ : User => argument) control
    {context with calls := above} space pattern readPattern body destination older offset rows selected
    returning atQuery frontier choice member

theorem superpose_choices {User : Type} {saved : CallFrame} {argument : Atom} {index : Nat}
    (control : DControl) (context : Context User) (origins : List Nat) (alternatives : List Atom)
    (destination : Atom) (older : List EagerDFS.Destination.Goal)
    (held : Holds saved argument index (control, context, origins))
    (atGoal : control.goals = .evaluate (.expression [.symbol "superpose", .expression alternatives]) destination :: older) :
    ∀ item ∈ superposeWork control context origins alternatives destination older, Holds saved argument index item := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  intro item member
  obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
  refine ⟨above, outside, length, calls, ?_⟩
  exact PettaCallerReturnSourceChoices.superpose_frontier (fun _ : User => argument) control
    {context with calls := above} origins alternatives destination older returning atGoal _ (List.mem_map.mpr ⟨entry, present, rfl⟩)

theorem collection_copies {User : Type} {saved : CallFrame} {argument : Atom} {index : Nat}
    (copies : List (Atom × List Atom)) (caller : CollectionCaller (Context User))
    (held : Holds saved argument index (caller.1, caller.2.2.1, caller.2.2.2)) :
    Holds saved argument index (Source.resumeCopies copies caller) := by
  obtain ⟨above, outside, length, calls, returning⟩ := held
  refine ⟨above, outside, length, calls, ?_⟩
  exact PettaCallerReturnSourceChoices.collection_copies (fun _ : User => argument) copies
    (caller.1, caller.2.1, {caller.2.2.1 with calls := above}, caller.2.2.2) returning

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedReturnWork
