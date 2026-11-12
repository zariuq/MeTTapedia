import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnOwned
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnTransitions

/-!
# All-phase retained return invariants for the actual typed source overlay

The machine is the existing occurrence-wise overlay, not a replacement body
evaluator. Its source handlers and typed argument/body continuations preserve
the return-obligation view and ordinary scope validity. Every finite run keeps
that invariant in each retained state, including suspension and exhaustion.

This is not yet a theorem about every emitted packet: typed-frame scope bounds
and the outer call-frame embedding remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnMachine

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open PettaOccurrenceOverlay

def ScopeSafe {User : Type} (action : Step User) : Prop :=
  ∀ next ∈ PettaOccurrenceBinding.retained action, EagerDFS.ScopesValid next.2.scopes

private theorem silent_scopes {User : Type} (source : State User)
    (valid : EagerDFS.ScopesValid source.2.scopes) : ScopeSafe (.silent source) := by
  simpa only [ScopeSafe, PettaOccurrenceBinding.retained, List.mem_singleton, forall_eq] using valid

private theorem call_scopes {User : Type} (source : State User) (request : Request)
    (valid : EagerDFS.ScopesValid source.2.scopes) : ScopeSafe (.call request source) := by
  simpa only [ScopeSafe, PettaOccurrenceBinding.retained, List.mem_singleton, forall_eq] using valid

private theorem install_scopes {User : Type} (source : State User) (current : Scope User)
    (parents : List (Scope User)) (work pending : List (Work User))
    (valid : EagerDFS.ScopesValid source.2.scopes) (scopes : source.2.scopes = current :: parents) :
    EagerDFS.ScopesValid (install source current parents work pending).2.scopes :=
  (scopes ▸ valid).replace_head _ _

theorem source_scopes {User : Type} (program : SpaceSemantics.Program) (source : State User)
    (valid : EagerDFS.ScopesValid source.2.scopes) :
    ScopeSafe (liftSource (Bridges.ScopedQuerySource.ownedStep .eagerValue program source)) := by
  have kept := Bridges.ScopedReturnOwned.owned_step_scope_validity program source valid
  generalize computed : Bridges.ScopedQuerySource.ownedStep .eagerValue program source = action at kept ⊢
  cases action <;> simp_all [ScopeSafe, PettaOccurrenceBinding.retained, liftSource, EagerDFS.Destination.ScopesPreserved]

theorem enter_rows_scopes {User : Type} (services : Services User) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (valid : EagerDFS.ScopesValid source.2.scopes) (scopes : source.2.scopes = current :: parents) :
    ScopeSafe (enterRows services source current parents control context origins pending head arguments destination older) := by
  unfold enterRows
  split
  · exact call_scopes source _ valid
  · exact call_scopes source _ valid
  · dsimp only
    split
    · exact silent_scopes _ (install_scopes source current parents _ pending valid scopes)
    · exact call_scopes source _ valid

theorem next_argument_scopes {User : Type} (services : Services User) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame)
    (valid : EagerDFS.ScopesValid source.2.scopes) (scopes : source.2.scopes = current :: parents) :
    ScopeSafe (nextArgument services source current parents control context origins pending frame outside) := by
  unfold nextArgument
  repeat' first
    | exact silent_scopes _ (install_scopes source current parents _ pending valid scopes)
    | split

theorem argument_guard_scopes {User : Type} (services : Services User) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (formal : Ty String) (slot value : Atom)
    (valid : EagerDFS.ScopesValid source.2.scopes) (scopes : source.2.scopes = current :: parents) :
    ScopeSafe (consumeArgument services source current parents control context origins pending frame outside formal slot value) := by
  unfold consumeArgument
  repeat' first
    | exact call_scopes source _ valid
    | exact silent_scopes _ (install_scopes source current parents _ pending valid scopes)
    | split

theorem result_guard_scopes {User : Type} (services : Services User) (source : State User)
    (current : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (value : Atom)
    (valid : EagerDFS.ScopesValid source.2.scopes) (scopes : source.2.scopes = current :: parents) :
    ScopeSafe (consumeBody services source current parents control context origins pending frame outside value) := by
  unfold consumeBody
  repeat' first
    | exact call_scopes source _ valid
    | exact silent_scopes _ (install_scopes source current parents _ pending valid scopes)
    | split

theorem lifted_return {User : Type} (inputs : User → Atom)
    (action : Bridges.ScopedQuerySource.Action (Context User))
    (kept : PettaCallerReturnSourceInvocation.Preserves inputs action) :
    PettaCallerReturnTransitions.Preserves inputs (liftSource action) := by
  cases action <;> simpa only [PettaCallerReturnSourceInvocation.Preserves,
    EagerDFS.Destination.RefinementTransport.actionStates, PettaCallerReturnTransitions.Preserves,
    PettaOccurrenceBinding.retained, liftSource] using kept

theorem source_return {User : Type} (inputs : User → Atom) (program : SpaceSemantics.Program)
    (source : State User) (valid : EagerDFS.ScopesValid source.2.scopes)
    (held : PettaCallerReturnView.Holds inputs source) :
    PettaCallerReturnTransitions.Preserves inputs
      (liftSource (Bridges.ScopedQuerySource.ownedStep .eagerValue program source)) :=
  lifted_return inputs _ (PettaCallerReturnOwned.owned_step_preserves inputs program source valid held)

theorem delegate_scopes {User : Type} (services : Services User) (program : SpaceSemantics.Program)
    (source : State User) (current : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (valid : EagerDFS.ScopesValid source.2.scopes) (scopes : source.2.scopes = current :: parents) :
    ScopeSafe (delegate services .eagerValue program source current parents control context origins pending) := by
  unfold delegate
  repeat' first
    | exact source_scopes program source valid
    | exact enter_rows_scopes services source current parents control context origins pending _ _ _ _ valid scopes
    | split

theorem delegate_return {User : Type} (inputs : User → Atom) (services : Services User)
    (program : SpaceSemantics.Program) (source : State User) (current : Scope User)
    (parents : List (Scope User)) (control : DControl) (context : Context User)
    (origins : List Nat) (pending : List (Work User))
    (valid : EagerDFS.ScopesValid source.2.scopes) (held : PettaCallerReturnView.Holds inputs source)
    (scopes : source.2.scopes = current :: parents)
    (frontier : current.frontier = (control, context, origins) :: pending) :
    PettaCallerReturnTransitions.Preserves inputs
      (delegate services .eagerValue program source current parents control context origins pending) := by
  unfold delegate
  repeat' first
    | exact source_return inputs program source valid held
    | exact PettaCallerReturnTransitions.enter_rows_preserves inputs services source current parents control context
        origins pending _ _ _ _ held scopes frontier (by assumption) (by simp_all)
    | split

theorem step_scopes {User : Type} (services : Services User) (program : SpaceSemantics.Program)
    (source : State User) (valid : EagerDFS.ScopesValid source.2.scopes) :
    ScopeSafe (PettaOccurrenceOverlay.step services .eagerValue program source) := by
  unfold PettaOccurrenceOverlay.step
  split
  · exact source_scopes program source valid
  · rename_i current parents scopes
    split
    · exact source_scopes program source valid
    · rename_i control context origins pending _frontier
      repeat' first
        | exact delegate_scopes services program source current parents control context origins pending valid scopes
        | exact next_argument_scopes services source current parents control context origins pending _ _ valid scopes
        | exact argument_guard_scopes services source current parents control context origins pending _ _ _ _ _ valid scopes
        | exact result_guard_scopes services source current parents control context origins pending _ _ _ valid scopes
        | exact call_scopes source _ valid
        | split

theorem step_return {User : Type} (inputs : User → Atom) (services : Services User)
    (program : SpaceSemantics.Program) (source : State User)
    (valid : EagerDFS.ScopesValid source.2.scopes) (held : PettaCallerReturnView.Holds inputs source) :
    PettaCallerReturnTransitions.Preserves inputs (PettaOccurrenceOverlay.step services .eagerValue program source) := by
  unfold PettaOccurrenceOverlay.step
  split
  · exact source_return inputs program source valid held
  · rename_i current parents scopes
    split
    · exact source_return inputs program source valid held
    · rename_i control context origins pending frontier
      repeat' first
        | exact delegate_return inputs services program source current parents control context origins pending valid held scopes frontier
        | exact PettaCallerReturnTransitions.next_argument_preserves inputs services source current parents control context origins
            pending _ _ held scopes frontier (by assumption)
        | exact PettaCallerReturnTransitions.argument_guard_preserves inputs services source current parents control context origins
            pending _ _ _ _ _ held scopes frontier (by assumption)
        | exact PettaCallerReturnTransitions.result_guard_preserves inputs services source current parents control context origins
            pending _ _ _ held scopes frontier (by assumption)
        | exact PettaCallerReturnTransitions.call_preserves source _ held
        | split

def Invariant {User : Type} (inputs : User → Atom) (source : State User) : Prop :=
  EagerDFS.ScopesValid source.2.scopes ∧ PettaCallerReturnView.Holds inputs source

theorem step_invariant {User : Type} (inputs : User → Atom) (services : Services User)
    (program : SpaceSemantics.Program) (source : State User) (valid : Invariant inputs source) :
    ∀ next ∈ PettaOccurrenceBinding.retained (PettaOccurrenceOverlay.step services .eagerValue program source),
      Invariant inputs next := by
  intro next present
  exact ⟨step_scopes services program source valid.1 next present,
    step_return inputs services program source valid.1 valid.2 next present⟩

theorem path_invariant {User : Type} (inputs : User → Atom) (services : Services User)
    (program : SpaceSemantics.Program) {before after : State User}
    (path : Relation.ReflTransGen (PettaOccurrenceBinding.Continues services .eagerValue program) before after)
    (valid : Invariant inputs before) : Invariant inputs after := by
  induction path with
  | refl => exact valid
  | @tail current after previous advanced ih =>
      have kept := step_invariant inputs services program current ih
      rcases advanced with silent | ⟨events, published⟩
      · rw [silent] at kept
        exact kept after (by simp [PettaOccurrenceBinding.retained])
      · rw [published] at kept
        exact kept after (by simp [PettaOccurrenceBinding.retained])

def exitState {User : Type} : Outcome (State User) (State User) Request → Option (State User)
  | .finished final | .suspended _ final | .stuck final | .exhausted final => some final
  | .faulted => none

/-- Every exit carrying a state keeps the actual pending-return invariant.
No completion or body-success premise is needed. Published packets themselves
require the additional publication theorem, not this residual projection. -/
theorem run_retained_invariant {User : Type} (inputs : User → Atom) (services : Services User)
    (program : SpaceSemantics.Program) (fuel : Nat) (source : State User) (valid : Invariant inputs source) :
    ∀ final, exitState ((PettaOccurrenceOverlay.machine services .eagerValue program).run fuel source).2 = some final →
      Invariant inputs final := by
  induction fuel generalizing source with
  | zero =>
      intro final same
      cases Option.some.inj same
      exact valid
  | succ fuel ih =>
      have kept := step_invariant inputs services program source valid
      cases advanced : PettaOccurrenceOverlay.step services .eagerValue program source with
      | silent next =>
          rw [advanced] at kept
          simpa only [Machine.run, PettaOccurrenceOverlay.machine, advanced] using
            ih next (kept next (by simp [PettaOccurrenceBinding.retained]))
      | publish events next =>
          rw [advanced] at kept
          simpa only [Machine.run, PettaOccurrenceOverlay.machine, advanced] using
            ih next (kept next (by simp [PettaOccurrenceBinding.retained]))
      | finish final =>
          rw [advanced] at kept
          intro reached same
          simp only [Machine.run, PettaOccurrenceOverlay.machine, advanced, exitState] at same
          cases Option.some.inj same
          exact kept final (by simp [PettaOccurrenceBinding.retained])
      | call request final =>
          rw [advanced] at kept
          intro reached same
          simp only [Machine.run, PettaOccurrenceOverlay.machine, advanced, exitState] at same
          cases Option.some.inj same
          exact kept final (by simp [PettaOccurrenceBinding.retained])
      | fail events =>
          intro reached impossible
          simp [Machine.run, PettaOccurrenceOverlay.machine, advanced, exitState] at impossible

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnMachine
