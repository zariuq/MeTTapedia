import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaFrameScopes

/-!
# Existing source execution preserves indexed typed-frame scope bounds

Ordinary source steps retain their opaque typed context. Entering a collection
weakens active bounds by one while saving the caller at the parent depth;
collection return restores that saved context. Surface macro handlers use their
existing local-context evidence rather than a second body semantics.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaFrameScopeSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open PettaOccurrenceOverlay PettaFrameScopes

def Kept {User : Type} (action : Source.ScopeAction Allocator (Context User)) : Prop :=
  ∀ next ∈ RefinementTransport.actionStates action, Bounded next

private theorem silent_kept {User : Type} (source : State User) (bounded : Bounded source) :
    Kept (.silent source) := by
  simpa only [Kept, RefinementTransport.actionStates, List.mem_singleton, forall_eq] using bounded

private theorem call_kept {User : Type} (source : State User) (request : ScopeBoundary) (bounded : Bounded source) :
    Kept (.call request source) := by
  simpa only [Kept, RefinementTransport.actionStates, List.mem_singleton, forall_eq] using bounded

theorem local_kept {User : Type} {source : State User} {action : Bridges.ScopedQuerySource.Action (Context User)}
    (localAction : Bridges.ScopedQueryBinding.Local source action) (bounded : Bounded source) : Kept action := by
  cases localAction with
  | retained => exact call_kept _ _ bounded
  | scheduled current parents control context origins pending generated scopes frontier records =>
      apply silent_kept
      apply Scoped.replace_active (scopes ▸ bounded) control context origins pending generated current.collected frontier
      intro held item member
      simpa only [(records item member).1] using held

theorem invocation_kept {User : Type} {program : SpaceSemantics.Program}
    {allocator : Allocator} {world : EagerDFS.World} {current : Scope User} {parents : List (Scope User)}
    {control : DControl} {context : Context User} {origins : List Nat} {pending : List (Work User)}
    {head : String} {arguments : List Atom} {destination : Atom} {older : List EagerDFS.Destination.Goal}
    {environment : Environment} {action : Source.ScopeAction Allocator (Context User)}
    (source : Source.Invocation Source.FreshOperations.owned program allocator world current parents control context
      origins pending head arguments destination older environment action)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (bounded : Bounded (allocator, ⟨world, current :: parents⟩)) : Kept action := by
  cases source with
  | parsed text value after parseHead input returned =>
      apply silent_kept
      apply Scoped.replace_active bounded control context origins pending _ current.collected frontier
      intro held item member
      obtain ⟨row, _present, rfl⟩ := List.mem_map.mp member
      exact held
  | primitive state values ordinary known returned =>
      apply silent_kept
      apply Scoped.replace_active bounded control context origins pending _ current.collected frontier
      intro held item member
      obtain ⟨row, _present, rfl⟩ := List.mem_map.mp member
      exact held
  | equations selected ordinary known notIO declared selectedRows =>
      apply silent_kept
      apply Scoped.replace_active bounded control context origins pending _ current.collected frontier
      intro held item member
      obtain ⟨row, _present, rfl⟩ := List.mem_map.mp member
      exact held
  | parseFault | parseAllocation | parseArity | primitiveFault | unserved => exact call_kept _ _ bounded

theorem active_kept {User : Type} {program : SpaceSemantics.Program}
    {allocator : Allocator} {world : EagerDFS.World} {current : Scope User} {parents : List (Scope User)}
    {control : DControl} {context : Context User} {origins : List Nat} {pending : List (Work User)}
    {action : Source.ScopeAction Allocator (Context User)}
    (source : Source.ActiveStep Source.FreshOperations.owned .eagerValue program allocator world current parents
      control context origins pending action)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (bounded : Bounded (allocator, ⟨world, current :: parents⟩)) : Kept action := by
  cases source with
  | opening older atGoal =>
      apply silent_kept
      apply Scoped.replace_active bounded control context origins pending [(_, context, origins)] current.collected frontier
      intro held item member
      cases List.mem_singleton.mp member
      exact held
  | committing older younger retained atGoal partition boundary =>
      apply silent_kept
      apply Scoped.replace_head bounded
      intro item member
      rcases List.mem_cons.mp member with rfl | previous
      · exact bounded.head (control, context, origins) (frontier ▸ List.mem_cons_self)
      · exact bounded.head item (frontier ▸ List.mem_cons_of_mem _ (partition ▸ List.mem_append_right _ previous))
  | invalidCommit => exact call_kept _ _ bounded
  | next reached localStep =>
      apply silent_kept
      apply Scoped.replace_active bounded control context origins pending [(_, reached.context, origins)] current.collected frontier
      intro held item member
      cases List.mem_singleton.mp member
      simpa only [RefinementTransport.silent_context_preserved localStep] using held
  | refused bindings reached localStep =>
      apply silent_kept
      apply Scoped.replace_active bounded control context origins pending [] current.collected frontier
      intro held item impossible
      cases impossible
  | answered value bindings reached localStep =>
      have after : Scoped (EagerDFS.Scope.record current pending ⟨value, bindings, origins, []⟩ :: parents) :=
        bounded.replace_head pending _ (fun item member => bounded.head item (frontier ▸ List.mem_cons_of_mem _ member))
      split <;> simpa only [Kept, Bounded, RefinementTransport.actionStates, List.mem_singleton, forall_eq] using after
  | boundary => exact call_kept _ _ bounded
  | invocation head arguments destination older environment action atCall resolved notPrint served =>
      exact invocation_kept served frontier bounded
  | queried space pattern body destination older environment rows selected atQuery resolved readRows selectedRows =>
      apply silent_kept
      apply Scoped.replace_active bounded control context origins pending _ current.collected frontier
      intro held item member
      obtain ⟨row, _present, rfl⟩ := List.mem_map.mp member
      exact held
  | queryFault => exact call_kept _ _ bounded
  | collapsed expression destination older atGoal =>
      apply silent_kept
      apply Scoped.push bounded _ _ pending rfl
      · intro item member
        exact bounded.head item (frontier ▸ List.mem_cons_of_mem _ member)
      · intro item member
        cases List.mem_singleton.mp member
        exact (bounded.head (control, context, origins) (frontier ▸ List.mem_cons_self)).weaken (by omega)
      · exact bounded.head (control, context, origins) (frontier ▸ List.mem_cons_self)
  | choice alternatives destination older atGoal =>
      apply silent_kept
      apply Scoped.replace_active bounded control context origins pending _ current.collected frontier
      intro held item member
      obtain ⟨row, _present, rfl⟩ := List.mem_map.mp member
      exact held
  | empty destination older atGoal =>
      apply silent_kept
      apply Scoped.replace_active bounded control context origins pending [] current.collected frontier
      intro held item impossible
      cases impossible

theorem collection_kept {User : Type} {before after : State User}
    (source : Source.CollectionReturn Source.FreshOperations.owned before after)
    (bounded : Bounded before) : Bounded after := by
  cases source with
  | complete supply after world answers caller parent parents copied ready returned copies =>
      exact bounded.resume caller rfl _ (fun held => held)

theorem scoped_kept {User : Type} {program : SpaceSemantics.Program}
    {before : State User} {action : Source.ScopeAction Allocator (Context User)}
    (source : Source.ScopedStep Source.FreshOperations.owned .eagerValue program before action)
    (bounded : Bounded before) : Kept action := by
  cases source with
  | active allocator world current parents control context origins pending action frontier source =>
      exact active_kept source frontier bounded
  | finished => simpa only [Kept, RefinementTransport.actionStates, List.mem_singleton, forall_eq] using bounded
  | collected source => exact silent_kept _ (collection_kept source bounded)
  | associated | allocation => exact call_kept _ _ bounded

theorem base_kept {User : Type} (program : SpaceSemantics.Program) (source : State User) (bounded : Bounded source) :
    Kept (Bridges.ScopedQuerySource.step .eagerValue program source) := by
  unfold Bridges.ScopedQuerySource.step
  repeat' first
    | exact local_kept (Bridges.ScopedQueryBinding.syntax_local source _ (by assumption)) bounded
    | exact local_kept (Bridges.ScopedQueryBinding.constrained_local source _ (by assumption)) bounded
    | exact local_kept (Bridges.ScopedQueryBinding.mutation_local source _ (by assumption)) bounded
    | exact local_kept (Bridges.ScopedQueryBinding.query_local source _ (by assumption)) bounded
    | exact scoped_kept ((Source.scoped_step_iff_source .eagerValue program source bounded.valid _).mp rfl) bounded
    | split

theorem owned_kept {User : Type} (program : SpaceSemantics.Program) (source : State User) (bounded : Bounded source) :
    Kept (Bridges.ScopedQuerySource.ownedStep .eagerValue program source) := by
  unfold Bridges.ScopedQuerySource.ownedStep
  split
  · exact local_kept (Bridges.ScopedQueryBinding.case_entry_local source _ (by assumption)) bounded
  · split
    · exact local_kept (Bridges.ScopedQueryBinding.case_ready_local _ source _ (by assumption)) bounded
    · have base := base_kept program source bounded
      split
      · exact local_kept (Bridges.ScopedQueryBinding.ownership_local program source _ (by assumption)) bounded
      · dsimp only
        split
        · cases extended : Bridges.ScopedQuerySource.unifyingQueryStep source with
          | none => simpa only [extended, Option.getD_none] using base
          | some action =>
              simpa only [extended, Option.getD_some] using
                (local_kept (Bridges.ScopedQueryBinding.unifying_local source action extended) bounded)
        · exact base

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaFrameScopeSource
