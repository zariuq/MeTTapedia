import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnView
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnRawEntry

/-!
# Source choices while typed callers retain the outer return

With an empty typed stack the earned source recipe theorem applies. With a
saved typed caller, actual logical record refinement transports its unchanged
continuation. This distinction covers arbitrary intermediate callee values.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnSourceChoices

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay PettaCallerReturnFrames

theorem local_step {User : Type} (inputs : User → Atom) {program : SpaceSemantics.Program}
    {before after : Cursor (Context User)}
    (source : Source.Step .eagerValue program before (.silent after))
    (held : Frames (inputs before.context.user) before.control before.context.calls)
    (noSequence : ∀ pairs body destination older,
      before.control.goals ≠ .evaluate (.expression [.symbol "let*", .expression pairs, body]) destination :: older) :
    Frames (inputs after.context.user) after.control after.context.calls := by
  rw [RefinementTransport.silent_context_preserved source]
  apply held.source_step
  · exact RefinementTransport.local_step_extends source _ (by simp [RefinementTransport.localRecords])
  · intro returning
    exact Bridges.ScopedReturnLocal.alias_silent_preserves _ returning noSequence source

theorem primitive_choices {User : Type} (inputs : User → Atom) (control : DControl)
    (context : Context User) (origins : List Nat) (destination : Atom) (older : List EagerDFS.Destination.Goal)
    (values : List Atom) (held : Frames (inputs context.user) control context.calls)
    (tail : ∀ name, Bridges.ScopedReturnObligation.Pending (.var name) control.destination control.goals →
      Bridges.ScopedReturnObligation.Pending (.var name) control.destination older) :
    ∀ work ∈ primitiveWork control context origins destination older values, PettaCallerReturnPhases.WorkHolds inputs work := by
  intro work member
  have sameContext : work.2.1 = context := by obtain ⟨row, _present, rfl⟩ := List.mem_map.mp member; rfl
  have sameBindings : work.1.bindings = control.bindings := by obtain ⟨row, _present, rfl⟩ := List.mem_map.mp member; rfl
  change Frames (inputs work.2.1.user) work.1 work.2.1.calls
  rw [sameContext]
  apply held.source_step
  · rw [sameBindings]
    exact .refl _
  · rintro ⟨name, returning⟩
    exact ⟨name, Bridges.ScopedReturnDispatch.primitive_choices_with_tail name _ control context origins destination older values
      returning (tail name) work member⟩

theorem equation_frontier {User : Type} (inputs : User → Atom) {program : SpaceSemantics.Program}
    (control : DControl) (context : Context User) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List EagerDFS.Destination.Goal) (positions : List Nat)
    (selected : List (Nat × Control)) (retained : Nat)
    (held : Frames (inputs context.user) control context.calls)
    (tail : ∀ name, Bridges.ScopedReturnObligation.Pending (.var name) control.destination control.goals →
      Bridges.ScopedReturnObligation.Pending (.var name) control.destination older)
    (frontier : ClauseChoice.Frontier program control head arguments destination older positions selected) :
    ∀ choice ∈ selected, Frames (inputs context.user) (predicateEntry retained choice.2) context.calls := by
  induction frontier with
  | nil => simp
  | skip decision rest ih => exact ih
  | @keep occurrence remaining next answers decision rest ih =>
      intro choice member
      rcases List.mem_cons.mp member with rfl | later
      · apply held.source_step
        · cases decision with
          | selected equation bindings row sameHead matched => exact RefinementTransport.accepted_extends matched
        · rintro ⟨name, returning⟩
          exact ⟨name, Bridges.ScopedReturnDispatch.equation_choice_with_tail name _ control head arguments destination older
            occurrence retained next returning (tail name) decision⟩
      · exact ih choice later

theorem query_frontier {User : Type} (inputs : User → Atom) (control : DControl) (context : Context User)
    (space pattern body destination : Atom) (older : List EagerDFS.Destination.Goal) (rows : List Atom)
    (start : Nat) (selected : List (Nat × Control))
    (held : Frames (inputs context.user) control context.calls)
    (atQuery : control.goals = .query space pattern body destination :: older)
    (frontier : QueryFrontier control pattern body destination older start rows selected) :
    ∀ choice ∈ selected, Frames (inputs context.user) choice.2 context.calls := by
  intro choice member
  apply held.source_step
  · exact RefinementTransport.query_frontier_good frontier choice member
  · rintro ⟨name, returning⟩
    exact ⟨name, Bridges.ScopedReturnDispatch.query_selected_return name _ control space pattern body destination older
      rows start selected returning atQuery frontier choice member⟩

theorem captured_frontier {User : Type} (inputs : User → Atom) (control : DControl) (context : Context User)
    (space pattern readPattern body destination : Atom) (older : List EagerDFS.Destination.Goal)
    (offset : Nat) (rows : List Atom) (selected : List (Nat × Control))
    (held : Frames (inputs context.user) control context.calls)
    (atQuery : control.goals = .invoke "match" [space, pattern, body] destination :: older)
    (frontier : Bridges.ScopedQuerySource.Choices control readPattern body destination older offset rows selected) :
    ∀ choice ∈ selected, Frames (inputs context.user) choice.2 context.calls := by
  intro choice member
  apply held.source_step
  · obtain ⟨suffix, record⟩ := (frontier.frames choice member).2.2.2.2.2.2.1
    rw [record]
    exact RefinementTransport.append_extends _ _
  · rintro ⟨name, returning⟩
    exact ⟨name, Bridges.ScopedReturnDispatch.captured_query_return name _ control space pattern readPattern body destination older
      offset rows selected returning atQuery frontier choice member⟩

theorem opening {argument : Atom} {control : DControl} {frames : List CallFrame}
    (held : Frames argument control frames) (older : List EagerDFS.Destination.Goal) (boundary : Nat)
    (atGoal : control.goals = .openCommit :: older) :
    Frames argument {control with goals := older, cutBoundary := boundary} frames := by
  apply held.source_step (after := {control with goals := older, cutBoundary := boundary}) (.refl _)
  rintro ⟨name, returning⟩
  exact ⟨name, Bridges.ScopedReturnDispatch.open_commit_keeps_return name _ control older boundary returning atGoal⟩

theorem committing {argument : Atom} {control : DControl} {frames : List CallFrame}
    (held : Frames argument control frames) (older : List EagerDFS.Destination.Goal)
    (atGoal : control.goals = .commit :: older) :
    Frames argument {control with goals := older} frames := by
  apply held.source_step (after := {control with goals := older}) (.refl _)
  rintro ⟨name, returning⟩
  exact ⟨name, Bridges.ScopedReturnDispatch.commit_keeps_return name _ control older returning atGoal⟩

theorem collapse_caller {argument : Atom} {control : DControl} {frames : List CallFrame}
    (held : Frames argument control frames) (child destination : Atom) (older : List EagerDFS.Destination.Goal)
    (atGoal : control.goals = .evaluate (.expression [.symbol "collapse", child]) destination :: older) :
    Frames argument {control with goals := older} frames := by
  apply held.source_step (after := {control with goals := older}) (.refl _)
  rintro ⟨name, returning⟩
  exact ⟨name, Bridges.ScopedReturnDispatch.collapse_saved_return name _ control child destination older returning atGoal⟩

theorem superpose_frontier {User : Type} (inputs : User → Atom) (control : DControl) (context : Context User)
    (origins : List Nat) (alternatives : List Atom) (destination : Atom) (older : List EagerDFS.Destination.Goal)
    (held : Frames (inputs context.user) control context.calls)
    (atGoal : control.goals = .evaluate (.expression [.symbol "superpose", .expression alternatives]) destination :: older) :
    ∀ item ∈ superposeWork control context origins alternatives destination older,
      PettaCallerReturnPhases.WorkHolds inputs item := by
  intro item present
  have sameContext : item.2.1 = context := by obtain ⟨row, _member, rfl⟩ := List.mem_map.mp present; rfl
  have sameBindings : item.1.bindings = control.bindings := by obtain ⟨row, _member, rfl⟩ := List.mem_map.mp present; rfl
  change Frames (inputs item.2.1.user) item.1 item.2.1.calls
  rw [sameContext]
  apply held.source_step
  · rw [sameBindings]
    exact .refl _
  · rintro ⟨name, returning⟩
    exact ⟨name, Bridges.ScopedReturnDispatch.superpose_choices_return name _ control context origins alternatives destination older
      returning atGoal item present⟩

theorem collection_copies {User : Type} (inputs : User → Atom) (copies : List (Atom × List Atom))
    (caller : CollectionCaller (Context User))
    (held : Frames (inputs caller.2.2.1.user) caller.1 caller.2.2.1.calls) :
    PettaCallerReturnPhases.WorkHolds inputs (Source.resumeCopies copies caller) := by
  apply held.source_step (after := (Source.resumeCopies copies caller).1) (.refl _)
  rintro ⟨name, protectedRead, returning⟩
  refine ⟨name, protectedRead, ?_⟩
  rcases returning with realized | pending
  · exact .inl realized
  · exact .inr (pending.prepend_equation _ _)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnSourceChoices
