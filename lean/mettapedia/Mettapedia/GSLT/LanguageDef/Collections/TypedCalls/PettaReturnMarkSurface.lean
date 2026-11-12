import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkContracts
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnOwned

/-!
# Actual owned surface handlers preserve deterministic return marks

This uses the existing source handlers and their return-recipe laws. Marks
come from the computed update on the real reached state. Allocation, world
and collected-answer data are retained, not replayed from an entry snapshot.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkUpdate

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks WorkMarked Stack)
open PettaCallerReturnFrames

theorem evaluate_not_commit {control : DControl} {expression destination : Atom} {older : List EagerDFS.Destination.Goal}
    (scheduled : control.goals = .evaluate expression destination :: older) :
    ∀ tail, control.goals ≠ .commit :: tail := PettaMarkedTransitions.evaluate_not_commit scheduled

theorem invoke_not_commit {control : DControl} {head : String} {arguments : List Atom} {destination : Atom}
    {older : List EagerDFS.Destination.Goal} (scheduled : control.goals = .invoke head arguments destination :: older) :
    ∀ tail, control.goals ≠ .commit :: tail := PettaMarkedTransitions.invoke_not_commit scheduled

theorem constrained_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    (marks : List Marks) (source : State User) (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedQuerySource.constrainedCall source = some action)
    (held : Stack saved argument marks source.2.scopes) :
    Preserves saved argument marks source (liftSource action) := PettaMarkedTransitions.constrained_keeps marks source action computed held

theorem mutation_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    (marks : List Marks) (source : State User) (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedQuerySource.mutationCall source = some action)
    (held : Stack saved argument marks source.2.scopes) :
    Preserves saved argument marks source (liftSource action) := PettaMarkedTransitions.mutation_keeps marks source action computed held

theorem ownership_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    (marks : List Marks) (source : State User) (program : SpaceSemantics.Program)
    (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedQuerySource.ownershipStep program source = some action)
    (held : Stack saved argument marks source.2.scopes) :
    Preserves saved argument marks source (liftSource action) := PettaMarkedTransitions.ownership_keeps marks source program action computed held

theorem syntax_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedQuerySource.syntaxStep source = some action)
    (held : Stack saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents)
    (front : current.frontier = (control, context, origins) :: pending) :
    Preserves saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source (liftSource action) := by
  simp only [Bridges.ScopedQuerySource.syntaxStep, scopes, front] at computed
  repeat' first
    | (cases Option.some.inj computed; exact call_keeps _ source _ held)
    | (cases Option.some.inj computed
       apply installed_scope_keeps source current parents (control, context, origins) pending [(_, context, origins)]
         mark pendingMarks callerMark parentMarks held scopes front
         (.inr (evaluate_not_commit (by assumption))) _ _ _
       intro active
       apply same_count_generated (control, context, origins) _ mark
       · intro item member
         cases List.mem_singleton.mp member
         rfl
       · intro index marked item member
         cases List.mem_singleton.mp member
         obtain ⟨above, outside, length, calls, returning⟩ := active index marked
         refine ⟨above, outside, length, calls, ?_⟩
         apply returning.source_step
         · exact .refl _
         · rintro ⟨name, localReturn⟩
           exact ⟨name, Bridges.ScopedReturnDispatch.sequence_return name _ control _ _ _ _ _ localReturn
             (by assumption) (by assumption)⟩)
    | contradiction
    | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem case_entry_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedCaseSource.entryStep source = some action)
    (held : Stack saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents)
    (front : current.frontier = (control, context, origins) :: pending) :
    Preserves saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source (liftSource action) := by
  simp only [Bridges.ScopedCaseSource.entryStep, scopes, front] at computed
  repeat' first
    | (cases Option.some.inj computed; exact call_keeps _ source _ held)
    | (cases Option.some.inj computed
       apply installed_scope_keeps source current parents (control, context, origins) pending [(_, context, origins)]
         mark pendingMarks callerMark parentMarks held scopes front
         (.inr (evaluate_not_commit (by assumption))) _ _ _
       intro active
       apply same_count_generated (control, context, origins) _ mark
       · intro item member
         cases List.mem_singleton.mp member
         rfl
       · intro index marked item member
         cases List.mem_singleton.mp member
         obtain ⟨above, outside, length, calls, returning⟩ := active index marked
         refine ⟨above, outside, length, calls, ?_⟩
         apply returning.source_step
         · exact .refl _
         · rintro ⟨name, localReturn⟩
           exact ⟨name, Bridges.ScopedReturnDispatch.case_key_return name _ control _ _ _ _ localReturn (by assumption)⟩)
    | contradiction
    | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem case_ready_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedCaseSource.readyStep Bridges.ScopedQuerySource.plainQueryPattern source = some action)
    (held : Stack saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents)
    (front : current.frontier = (control, context, origins) :: pending) :
    Preserves saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source (liftSource action) := by
  simp only [Bridges.ScopedCaseSource.readyStep, scopes, front] at computed
  repeat' first
    | (cases Option.some.inj computed; exact call_keeps _ source _ held)
    | (cases Option.some.inj computed
       apply installed_scope_keeps source current parents (control, context, origins) pending []
         mark pendingMarks callerMark parentMarks held scopes front
         (.inr (invoke_not_commit (by assumption))) _ _ _
       intro _active item member
       cases member)
    | (cases Option.some.inj computed
       apply installed_scope_keeps source current parents (control, context, origins) pending [(_, context, _)]
         mark pendingMarks callerMark parentMarks held scopes front
         (.inr (invoke_not_commit (by assumption))) _ _ _
       intro active
       apply same_count_generated (control, context, origins) _ mark
       · intro item member
         cases List.mem_singleton.mp member
         rfl
       · intro index marked item member
         cases List.mem_singleton.mp member
         have selected := (Bridges.ScopedCaseSelection.select_iff_source _ _ _ _ _).mp (by assumption)
         obtain ⟨above, outside, length, calls, returning⟩ := active index marked
         refine ⟨above, outside, length, calls, ?_⟩
         apply returning.source_step
         · exact (Bridges.ScopedCaseSelection.selected_record selected).1
         · rintro ⟨name, localReturn⟩
           exact ⟨name, Bridges.ScopedReturnDispatch.case_body_return name _ control _ _ _ _ _ _ localReturn
             (by assumption) (by assumption) selected⟩)
    | contradiction
    | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem captured_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedQuerySource.queryStep source = some action)
    (held : Stack saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents)
    (front : current.frontier = (control, context, origins) :: pending) :
    Preserves saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source (liftSource action) := by
  simp only [Bridges.ScopedQuerySource.queryStep, scopes, front] at computed
  repeat' first
    | (cases Option.some.inj computed; exact call_keeps _ source _ held)
    | (cases Option.some.inj computed
       apply installed_scope_keeps source current parents (control, context, origins) pending
         (Bridges.ScopedQuerySource.work context origins _) mark pendingMarks callerMark parentMarks held scopes front
         (.inr (invoke_not_commit (by assumption))) _ _ _
       intro active
       apply same_count_generated (control, context, origins) _ mark
       · intro item member
         obtain ⟨choice, _present, rfl⟩ := List.mem_map.mp member
         rfl
       · intro index marked item member
         obtain ⟨choice, present, rfl⟩ := List.mem_map.mp member
         exact PettaSelectedReturnWork.captured_choices control context origins _ _ _ _ _ _ _ _ _
           (active index marked) (by assumption)
           (Bridges.ScopedQuerySource.capture_has_source _ _ _ _ _ _ _ _ (by assumption)) choice present)
    | contradiction
    | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem unifying_keeps {User : Type} {saved : CallFrame} {argument : Atom}
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedQuerySource.unifyingQueryStep source = some action)
    (held : Stack saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents)
    (front : current.frontier = (control, context, origins) :: pending) :
    Preserves saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source (liftSource action) := by
  simp only [Bridges.ScopedQuerySource.unifyingQueryStep, scopes, front] at computed
  repeat' first
    | (cases Option.some.inj computed
       apply installed_scope_keeps source current parents (control, context, origins) pending [(_, context, origins)]
         mark pendingMarks callerMark parentMarks held scopes front
         (.inr (invoke_not_commit (by assumption))) _ _ _
       intro active
       apply same_count_generated (control, context, origins) _ mark
       · intro item member
         cases List.mem_singleton.mp member
         rfl
       · intro index marked item member
         cases List.mem_singleton.mp member
         obtain ⟨above, outside, length, calls, returning⟩ := active index marked
         refine ⟨above, outside, length, calls, ?_⟩
         apply returning.source_step
         · exact .refl _
         · rintro ⟨name, localReturn⟩
           exact ⟨name, Bridges.ScopedReturnDispatch.query_ready_to_owned name _ control _ _ _ _ _ localReturn
             (by assumption)⟩)
    | contradiction
    | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReturnMarkUpdate
