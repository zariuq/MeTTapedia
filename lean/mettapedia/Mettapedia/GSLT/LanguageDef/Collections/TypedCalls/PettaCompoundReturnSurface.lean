import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnInvocation

/-!
# Owned surface handlers preserve computed compound-return marks

The real sequence, case and query handlers provide their reached controls,
records and frontiers. Local source compound laws and frame refinement earn
the obligations on those controls; the mark update remains the shared one.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnScopes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open PettaOccurrenceOverlay
open PettaSelectedReturnScopes (Marks)

theorem constrained_keeps {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame} {argument : Atom}
    (marks : List Marks) (source : State User) (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedQuerySource.constrainedCall source = some action)
    (held : Stack program saved argument marks source.2.scopes) : Preserves program saved argument marks source (liftSource action) :=
  PettaMarkedTransitions.constrained_keeps marks source action computed held

theorem mutation_keeps {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame} {argument : Atom}
    (marks : List Marks) (source : State User) (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedQuerySource.mutationCall source = some action)
    (held : Stack program saved argument marks source.2.scopes) : Preserves program saved argument marks source (liftSource action) :=
  PettaMarkedTransitions.mutation_keeps marks source action computed held

theorem ownership_keeps {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame} {argument : Atom}
    (marks : List Marks) (source : State User) (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedQuerySource.ownershipStep program source = some action)
    (held : Stack program saved argument marks source.2.scopes) : Preserves program saved argument marks source (liftSource action) :=
  PettaMarkedTransitions.ownership_keeps marks source program action computed held

theorem syntax_keeps {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame} {argument : Atom}
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedQuerySource.syntaxStep source = some action)
    (held : Stack program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents) (front : current.frontier = (control, context, origins) :: pending) :
    Preserves program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source (liftSource action) := by
  simp only [Bridges.ScopedQuerySource.syntaxStep, scopes, front] at computed
  repeat' first
    | (cases Option.some.inj computed; exact call_keeps _ source _ held)
    | (cases Option.some.inj computed
       apply PettaMarkedTransitions.installed_scope_keeps (Held := PettaCompoundSelectedWork.Holds program saved argument)
         source current parents (control, context, origins) pending [(_, context, origins)] mark pendingMarks callerMark
         parentMarks held scopes front (.inr (PettaMarkedTransitions.evaluate_not_commit (by assumption))) _ _ _
       intro active
       apply PettaMarkedTransitions.same_count_generated (Held := PettaCompoundSelectedWork.Holds program saved argument)
         (control, context, origins) [(_, context, origins)] mark
       · intro item member; cases List.mem_singleton.mp member; rfl
       · intro index marked item member
         cases List.mem_singleton.mp member
         obtain ⟨above, outside, length, calls, returning⟩ := active index marked
         refine ⟨above, outside, length, calls, ?_⟩
         apply returning.source_step
         · exact .refl _
         · rintro ⟨recipe, data, obligation⟩
           exact ⟨recipe, data, Bridges.DestinationDataReturnDispatch.sequence_return data control _ _ _ _ _ obligation
             (by assumption) (by assumption)⟩)
    | contradiction
    | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem case_entry_keeps {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame} {argument : Atom}
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedCaseSource.entryStep source = some action)
    (held : Stack program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents) (front : current.frontier = (control, context, origins) :: pending) :
    Preserves program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source (liftSource action) := by
  simp only [Bridges.ScopedCaseSource.entryStep, scopes, front] at computed
  repeat' first
    | (cases Option.some.inj computed; exact call_keeps _ source _ held)
    | (cases Option.some.inj computed
       apply PettaMarkedTransitions.installed_scope_keeps (Held := PettaCompoundSelectedWork.Holds program saved argument)
         source current parents (control, context, origins) pending [(_, context, origins)] mark pendingMarks callerMark
         parentMarks held scopes front (.inr (PettaMarkedTransitions.evaluate_not_commit (by assumption))) _ _ _
       intro active
       apply PettaMarkedTransitions.same_count_generated (Held := PettaCompoundSelectedWork.Holds program saved argument)
         (control, context, origins) [(_, context, origins)] mark
       · intro item member; cases List.mem_singleton.mp member; rfl
       · intro index marked item member
         cases List.mem_singleton.mp member
         obtain ⟨above, outside, length, calls, returning⟩ := active index marked
         refine ⟨above, outside, length, calls, ?_⟩
         apply returning.source_step
         · exact .refl _
         · rintro ⟨recipe, data, obligation⟩
           exact ⟨recipe, data, Bridges.DestinationDataReturnDispatch.case_key_return data control _ _ _ _ obligation (by assumption)⟩)
    | contradiction
    | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem case_ready_keeps {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame} {argument : Atom}
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedCaseSource.readyStep Bridges.ScopedQuerySource.plainQueryPattern source = some action)
    (held : Stack program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents) (front : current.frontier = (control, context, origins) :: pending) :
    Preserves program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source (liftSource action) := by
  simp only [Bridges.ScopedCaseSource.readyStep, scopes, front] at computed
  repeat' first
    | (cases Option.some.inj computed; exact call_keeps _ source _ held)
    | (cases Option.some.inj computed
       apply PettaMarkedTransitions.installed_scope_keeps (Held := PettaCompoundSelectedWork.Holds program saved argument)
         source current parents (control, context, origins) pending [] mark pendingMarks callerMark parentMarks held scopes front
         (.inr (PettaMarkedTransitions.invoke_not_commit (by assumption))) _ _ _
       intro _active item member; cases member)
    | (cases Option.some.inj computed
       apply PettaMarkedTransitions.installed_scope_keeps (Held := PettaCompoundSelectedWork.Holds program saved argument)
         source current parents (control, context, origins) pending [(_, context, _)] mark pendingMarks callerMark parentMarks
         held scopes front (.inr (PettaMarkedTransitions.invoke_not_commit (by assumption))) _ _ _
       intro active
       apply PettaMarkedTransitions.same_count_generated (Held := PettaCompoundSelectedWork.Holds program saved argument)
         (control, context, origins) [(_, context, _)] mark
       · intro item member; cases List.mem_singleton.mp member; rfl
       · intro index marked item member
         cases List.mem_singleton.mp member
         have selected := (Bridges.ScopedCaseSelection.select_iff_source _ _ _ _ _).mp (by assumption)
         obtain ⟨above, outside, length, calls, returning⟩ := active index marked
         refine ⟨above, outside, length, calls, ?_⟩
         apply returning.source_step
         · exact (Bridges.ScopedCaseSelection.selected_record selected).1
         · rintro ⟨recipe, data, obligation⟩
           exact ⟨recipe, data, Bridges.DestinationDataReturnDispatch.case_body_return control _ _ _ _ _ _ obligation
             (by assumption) (by assumption) selected⟩)
    | contradiction
    | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem captured_keeps {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame} {argument : Atom}
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedQuerySource.queryStep source = some action)
    (held : Stack program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents) (front : current.frontier = (control, context, origins) :: pending) :
    Preserves program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source (liftSource action) := by
  simp only [Bridges.ScopedQuerySource.queryStep, scopes, front] at computed
  repeat' first
    | (cases Option.some.inj computed; exact call_keeps _ source _ held)
    | (cases Option.some.inj computed
       apply PettaMarkedTransitions.installed_scope_keeps (Held := PettaCompoundSelectedWork.Holds program saved argument)
         source current parents (control, context, origins) pending (Bridges.ScopedQuerySource.work context origins _) mark
         pendingMarks callerMark parentMarks held scopes front (.inr (PettaMarkedTransitions.invoke_not_commit (by assumption))) _ _ _
       intro active
       apply PettaMarkedTransitions.same_count_generated (Held := PettaCompoundSelectedWork.Holds program saved argument)
         (control, context, origins) (Bridges.ScopedQuerySource.work context origins _) mark
       · intro item member; obtain ⟨choice, present, rfl⟩ := List.mem_map.mp member; rfl
       · intro index marked item member
         obtain ⟨choice, present, rfl⟩ := List.mem_map.mp member
         exact PettaCompoundSelectedWork.captured_choices control context origins _ _ _ _ _ _ _ _ _
           (active index marked) (by assumption)
           (Bridges.ScopedQuerySource.capture_has_source _ _ _ _ _ _ _ _ (by assumption)) choice present)
    | contradiction
    | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

theorem unifying_keeps {User : Type} {program : SpaceSemantics.Program} {saved : CallFrame} {argument : Atom}
    (source : State User) (current : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (mark : Option Nat) (pendingMarks : List (Option Nat)) (callerMark : Option Nat) (parentMarks : List Marks)
    (action : Bridges.ScopedQuerySource.Action (Context User))
    (computed : Bridges.ScopedQuerySource.unifyingQueryStep source = some action)
    (held : Stack program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source.2.scopes)
    (scopes : source.2.scopes = current :: parents) (front : current.frontier = (control, context, origins) :: pending) :
    Preserves program saved argument (⟨mark :: pendingMarks, callerMark⟩ :: parentMarks) source (liftSource action) := by
  simp only [Bridges.ScopedQuerySource.unifyingQueryStep, scopes, front] at computed
  repeat' first
    | (cases Option.some.inj computed
       apply PettaMarkedTransitions.installed_scope_keeps (Held := PettaCompoundSelectedWork.Holds program saved argument)
         source current parents (control, context, origins) pending [(_, context, origins)] mark pendingMarks callerMark
         parentMarks held scopes front (.inr (PettaMarkedTransitions.invoke_not_commit (by assumption))) _ _ _
       intro active
       apply PettaMarkedTransitions.same_count_generated (Held := PettaCompoundSelectedWork.Holds program saved argument)
         (control, context, origins) [(_, context, origins)] mark
       · intro item member; cases List.mem_singleton.mp member; rfl
       · intro index marked item member
         cases List.mem_singleton.mp member
         obtain ⟨above, outside, length, calls, returning⟩ := active index marked
         refine ⟨above, outside, length, calls, ?_⟩
         apply returning.source_step
         · exact .refl _
         · rintro ⟨recipe, data, obligation⟩
           exact ⟨recipe, data, Bridges.DestinationDataReturnDispatch.query_ready_to_owned control _ _ _ _ _ obligation (by assumption)⟩)
    | contradiction
    | (split at computed <;> try dsimp only [bind, Option.bind] at computed)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCompoundReturnScopes
