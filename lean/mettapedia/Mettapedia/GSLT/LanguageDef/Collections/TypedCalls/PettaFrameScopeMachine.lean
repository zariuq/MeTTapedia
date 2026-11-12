import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaFrameScopeSource

/-!
# All typed overlay phases preserve scope-owned call frames

Source steps use the existing source preservation theorem. Typed row entry
creates frames at the actual current depth; argument preparation and guards
retain that depth, and body return pops only its own frame. No invariant of
arbitrary caller-supplied frames is assumed at initialization.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaFrameScopeMachine

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open PettaOccurrenceOverlay PettaFrameScopes

def Keeps {User : Type} (action : Step User) : Prop :=
  ∀ next ∈ PettaOccurrenceBinding.retained action, Bounded next

private theorem silent_keeps {User : Type} (source : State User) (bounded : Bounded source) :
    Keeps (.silent source) := by
  simpa only [Keeps, PettaOccurrenceBinding.retained, List.mem_singleton, forall_eq] using bounded

private theorem call_keeps {User : Type} (source : State User) (request : Request) (bounded : Bounded source) :
    Keeps (.call request source) := by
  simpa only [Keeps, PettaOccurrenceBinding.retained, List.mem_singleton, forall_eq] using bounded

theorem source_keeps {User : Type} (program : SpaceSemantics.Program) (source : State User) (bounded : Bounded source) :
    Keeps (liftSource (Bridges.ScopedQuerySource.ownedStep .eagerValue program source)) := by
  have kept := PettaFrameScopeSource.owned_kept program source bounded
  generalize actionEq : Bridges.ScopedQuerySource.ownedStep .eagerValue program source = action at kept ⊢
  cases action <;> simpa only [Keeps, PettaOccurrenceBinding.retained, liftSource,
    PettaFrameScopeSource.Kept, RefinementTransport.actionStates] using kept

theorem enter_rows_keeps {User : Type} (services : Services User) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List EagerDFS.Destination.Goal)
    (bounded : Bounded source) (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending) :
    Keeps (enterRows services source current parents control context origins pending head arguments destination older) := by
  unfold enterRows
  split
  · exact call_keeps _ _ bounded
  · exact call_keeps _ _ bounded
  · dsimp only
    split
    · apply silent_keeps
      apply Scoped.replace_active (scopes ▸ bounded) control context origins pending _ current.collected frontier
      intro held item member
      obtain ⟨⟨row, occurrence⟩, _present, rfl⟩ := List.mem_map.mp member
      have depth : source.2.scopes.length = parents.length + 1 := by simp [scopes]
      simpa only [depth] using row_work_bound source.2.scopes.length control context origins head arguments
        destination older row occurrence (by simp [depth]) (by simpa only [depth] using held)
    · exact call_keeps _ _ bounded

theorem next_argument_keeps {User : Type} (services : Services User) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame)
    (bounded : Bounded source) (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside) :
    Keeps (nextArgument services source current parents control context origins pending frame outside) := by
  unfold nextArgument
  split
  · apply silent_keeps
    apply Scoped.replace_active (scopes ▸ bounded) control context origins pending _ current.collected frontier
    intro held item member
    cases List.mem_singleton.mp member
    exact held.update_top calls _ rfl
  · split
    all_goals
      apply silent_keeps
      apply Scoped.replace_active (scopes ▸ bounded) control context origins pending _ current.collected frontier
      intro held item member
      cases List.mem_singleton.mp member
      exact held.update_top calls _ rfl

theorem argument_guard_keeps {User : Type} (services : Services User) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (formal : Ty String) (slot value : Atom)
    (bounded : Bounded source) (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside) :
    Keeps (consumeArgument services source current parents control context origins pending frame outside formal slot value) := by
  unfold consumeArgument
  split
  · exact call_keeps _ _ bounded
  · apply silent_keeps
    apply Scoped.replace_active (scopes ▸ bounded) control context origins pending _ current.collected frontier
    intro held item member
    obtain ⟨row, _present, rfl⟩ := List.mem_map.mp member
    exact held.update_top calls _ rfl

theorem result_guard_keeps {User : Type} (services : Services User) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (value : Atom)
    (bounded : Bounded source) (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside) :
    Keeps (consumeBody services source current parents control context origins pending frame outside value) := by
  unfold consumeBody
  split
  · exact call_keeps _ _ bounded
  · apply silent_keeps
    apply Scoped.replace_active (scopes ▸ bounded) control context origins pending _ current.collected frontier
    intro held item member
    obtain ⟨row, _present, rfl⟩ := List.mem_map.mp member
    exact held.pop calls

theorem delegate_keeps {User : Type} (services : Services User) (program : SpaceSemantics.Program)
    (source : State User) (current : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (bounded : Bounded source) (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending) :
    Keeps (delegate services .eagerValue program source current parents control context origins pending) := by
  unfold delegate
  repeat' first
    | exact source_keeps program source bounded
    | exact enter_rows_keeps services source current parents control context origins pending _ _ _ _ bounded scopes frontier
    | split

theorem step_keeps {User : Type} (services : Services User) (program : SpaceSemantics.Program)
    (source : State User) (bounded : Bounded source) :
    Keeps (PettaOccurrenceOverlay.step services .eagerValue program source) := by
  unfold PettaOccurrenceOverlay.step
  split
  · exact source_keeps program source bounded
  · rename_i current parents scopes
    split
    · exact source_keeps program source bounded
    · rename_i control context origins pending frontier
      repeat' first
        | exact delegate_keeps services program source current parents control context origins pending bounded scopes frontier
        | exact next_argument_keeps services source current parents control context origins pending _ _ bounded scopes frontier (by assumption)
        | exact argument_guard_keeps services source current parents control context origins pending _ _ _ _ _ bounded scopes frontier (by assumption)
        | exact result_guard_keeps services source current parents control context origins pending _ _ _ bounded scopes frontier (by assumption)
        | exact call_keeps _ _ bounded
        | split

theorem path_keeps {User : Type} (services : Services User) (program : SpaceSemantics.Program)
    {before after : State User}
    (path : Relation.ReflTransGen (PettaOccurrenceBinding.Continues services .eagerValue program) before after)
    (bounded : Bounded before) : Bounded after := by
  induction path with
  | refl => exact bounded
  | @tail current after previous advanced ih =>
      have kept := step_keeps services program current ih
      rcases advanced with silent | ⟨events, published⟩
      · rw [silent] at kept
        exact kept after (by simp [PettaOccurrenceBinding.retained])
      · rw [published] at kept
        exact kept after (by simp [PettaOccurrenceBinding.retained])

theorem lifted_no_failure {User : Type} (program : SpaceSemantics.Program) (source : State User)
    (bounded : Bounded source) (events : List CollectedAnswer) :
    liftSource (Bridges.ScopedQuerySource.ownedStep .eagerValue program source) ≠ .fail events := by
  have noFailure := Bridges.ScopedReturnPublication.owned_has_no_failure_packets program source bounded.valid events
  generalize actionEq : Bridges.ScopedQuerySource.ownedStep .eagerValue program source = action at noFailure ⊢
  cases action <;> simp_all [liftSource]

theorem step_no_failure {User : Type} (services : Services User) (program : SpaceSemantics.Program)
    (source : State User) (bounded : Bounded source) (events : List CollectedAnswer) :
    PettaOccurrenceOverlay.step services .eagerValue program source ≠ .fail events := by
  intro failed
  unfold PettaOccurrenceOverlay.step at failed
  repeat' first
    | exact lifted_no_failure program source bounded events failed
    | (unfold delegate at failed)
    | (unfold enterRows at failed)
    | (unfold nextArgument at failed)
    | (unfold consumeArgument at failed)
    | (unfold consumeBody at failed)
    | (cases failed)
    | (split at failed <;> try dsimp only at failed)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaFrameScopeMachine
