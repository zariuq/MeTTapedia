import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceOverlay
import Mettapedia.Languages.MeTTa.PeTTa.DestinationScopeRefinement
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryBinding

/-!
# Reached branch contracts through the actual typed occurrence overlay

Source execution preserves branch-local logical binding contracts. The typed
adapter retains those same reached equations when it installs guarded
alternatives, starts the next producer, or restores a saved caller. This
module joins those two facts through the actual overlay step, keeping older
siblings and collection callers distinct. It does not supply a replacement
body evaluator or erase the adapter's type-store obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceBinding

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open PettaOccurrenceOverlay
open EagerDFS.Destination

def liftPredicate {User : Type} (predicate : RefinementTransport.BindingPredicate User) : RefinementTransport.BindingPredicate (Context User) where
  holds context bindings := predicate.holds context.user bindings
  closed context before after good extended := predicate.closed context.user before after good extended

def Safe {User : Type} (predicate : RefinementTransport.BindingPredicate User) (state : State User) : Prop :=
  EagerDFS.ScopesValid state.2.scopes ∧ RefinementTransport.ScopesGood (liftPredicate predicate) state.2.scopes

def retained {User : Type} : Step User → List (State User)
  | .silent state | .publish _ state | .finish state | .call _ state => [state]
  | .fail _ => []

def SafeAction {User : Type} (predicate : RefinementTransport.BindingPredicate User) (action : Step User) : Prop :=
  ∀ state ∈ retained action, Safe predicate state

theorem silent_safe {User : Type} {predicate : RefinementTransport.BindingPredicate User} (state : State User)
    (safe : Safe predicate state) : SafeAction predicate (.silent state) := by
  simpa only [SafeAction, retained, List.mem_singleton, forall_eq] using safe

theorem call_safe {User : Type} {predicate : RefinementTransport.BindingPredicate User} (state : State User)
    (request : Request) (safe : Safe predicate state) : SafeAction predicate (.call request state) := by
  simpa only [SafeAction, retained, List.mem_singleton, forall_eq] using safe

theorem source_safe {User : Type} (predicate : RefinementTransport.BindingPredicate User) (policy : EagerDFS.Destination.Policy)
    (program : SpaceSemantics.Program) (state : State User) (safe : Safe predicate state) :
    SafeAction predicate (liftSource (Bridges.ScopedQuerySource.ownedStep policy program state)) := by
  obtain ⟨valid, good⟩ := Bridges.ScopedQueryBinding.owned_step_safe
    (liftPredicate predicate) policy program state safe
  generalize actionEq : Bridges.ScopedQuerySource.ownedStep policy program state = action at valid good ⊢
  cases action <;> simp_all [SafeAction, retained, liftSource, Safe, EagerDFS.Destination.ScopesPreserved, RefinementTransport.ActionGood, RefinementTransport.actionStates]

theorem install_safe {User : Type} (predicate : RefinementTransport.BindingPredicate User)
    (source : State User) (scope : Scope User) (parents : List (Scope User))
    (work pending : List (Work User)) (safe : Safe predicate source)
    (scopes : source.2.scopes = scope :: parents)
    (works : ∀ item ∈ work, predicate.holds item.2.1.user item.1.bindings)
    (older : ∀ item ∈ pending, predicate.holds item.2.1.user item.1.bindings) :
    Safe predicate (install source scope parents work pending) := by
  have valid : EagerDFS.ScopesValid (scope :: parents) := scopes ▸ safe.1
  have allGood : RefinementTransport.ScopesGood (liftPredicate predicate) (scope :: parents) := scopes ▸ safe.2
  refine ⟨valid.replace_head _ _, ?_⟩
  apply RefinementTransport.scopes_cons
  · apply (allGood scope List.mem_cons_self).frontier
    intro item member
    rcases List.mem_append.mp member with here | there
    · exact works item here
    · exact older item there
  · intro parent member
    exact allGood parent (List.mem_cons_of_mem _ member)

theorem enterRows_safe {User : Type} (predicate : RefinementTransport.BindingPredicate User) (services : Services User)
    (source : State User) (scope : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List EagerDFS.Destination.Goal)
    (safe : Safe predicate source) (scopes : source.2.scopes = scope :: parents)
    (frontier : scope.frontier = (control, context, origins) :: pending) :
    SafeAction predicate (enterRows services source scope parents control context origins pending
      head arguments destination older) := by
  obtain ⟨_, _, active, pendingGood⟩ := RefinementTransport.focus_good (scopes ▸ safe.2) frontier
  unfold enterRows
  split
  · exact call_safe _ _ safe
  · exact call_safe _ _ safe
  · dsimp only
    split
    · apply silent_safe
      apply install_safe predicate source scope parents _ pending safe scopes _ pendingGood
      intro work member
      obtain ⟨pair, _present, rfl⟩ := List.mem_map.mp member
      exact active
    · exact call_safe _ _ safe

theorem nextArgument_safe {User : Type} (predicate : RefinementTransport.BindingPredicate User) (services : Services User)
    (source : State User) (scope : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame)
    (safe : Safe predicate source) (scopes : source.2.scopes = scope :: parents)
    (frontier : scope.frontier = (control, context, origins) :: pending) :
    SafeAction predicate (nextArgument services source scope parents control context origins pending frame outside) := by
  obtain ⟨_, _, active, pendingGood⟩ := RefinementTransport.focus_good (scopes ▸ safe.2) frontier
  unfold nextArgument
  split
  · apply silent_safe
    apply install_safe predicate source scope parents _ pending safe scopes _ pendingGood
    intro work member
    cases List.mem_singleton.mp member
    exact active
  · split <;> apply silent_safe
    all_goals
      apply install_safe predicate source scope parents _ pending safe scopes _ pendingGood
      intro work member
      cases List.mem_singleton.mp member
      exact active

theorem consumeArgument_safe {User : Type} (predicate : RefinementTransport.BindingPredicate User) (services : Services User)
    (source : State User) (scope : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (formal : Ty String) (slot value : Atom)
    (safe : Safe predicate source) (scopes : source.2.scopes = scope :: parents)
    (frontier : scope.frontier = (control, context, origins) :: pending) :
    SafeAction predicate (consumeArgument services source scope parents control context origins pending
      frame outside formal slot value) := by
  obtain ⟨_, _, active, pendingGood⟩ := RefinementTransport.focus_good (scopes ▸ safe.2) frontier
  unfold consumeArgument
  split
  · exact call_safe _ _ safe
  · apply silent_safe
    apply install_safe predicate source scope parents _ pending safe scopes _ pendingGood
    intro work member
    obtain ⟨pair, _present, rfl⟩ := List.mem_map.mp member
    exact active

theorem consumeBody_safe {User : Type} (predicate : RefinementTransport.BindingPredicate User) (services : Services User)
    (source : State User) (scope : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (value : Atom)
    (safe : Safe predicate source) (scopes : source.2.scopes = scope :: parents)
    (frontier : scope.frontier = (control, context, origins) :: pending) :
    SafeAction predicate (consumeBody services source scope parents control context origins pending
      frame outside value) := by
  obtain ⟨_, _, active, pendingGood⟩ := RefinementTransport.focus_good (scopes ▸ safe.2) frontier
  unfold consumeBody
  split
  · exact call_safe _ _ safe
  · apply silent_safe
    apply install_safe predicate source scope parents _ pending safe scopes _ pendingGood
    intro work member
    obtain ⟨pair, _present, rfl⟩ := List.mem_map.mp member
    exact active

theorem delegate_safe {User : Type} (predicate : RefinementTransport.BindingPredicate User)
    (services : Services User) (policy : EagerDFS.Destination.Policy) (program : SpaceSemantics.Program)
    (source : State User) (scope : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat) (pending : List (Work User))
    (safe : Safe predicate source) (scopes : source.2.scopes = scope :: parents)
    (frontier : scope.frontier = (control, context, origins) :: pending) :
    SafeAction predicate (delegate services policy program source scope parents control context origins pending) := by
  unfold delegate
  repeat' first
    | exact source_safe predicate policy program source safe
    | exact enterRows_safe predicate services source scope parents control context origins pending
        _ _ _ _ safe scopes frontier
    | split

/-- All actual typed-overlay phases preserve the reached binding contract.
Guards may branch, fail, or remain unserved; no case reinstates captured
caller equations or executes the next producer before consuming the guard. -/
theorem step_safe {User : Type} (predicate : RefinementTransport.BindingPredicate User)
    (services : Services User) (policy : EagerDFS.Destination.Policy) (program : SpaceSemantics.Program)
    (source : State User) (safe : Safe predicate source) :
    SafeAction predicate (PettaOccurrenceOverlay.step services policy program source) := by
  unfold PettaOccurrenceOverlay.step
  split
  · exact source_safe predicate policy program source safe
  · rename_i scope parents scopes
    split
    · exact source_safe predicate policy program source safe
    · rename_i control context origins pending frontier
      repeat' first
        | exact delegate_safe predicate services policy program source scope parents control context origins
            pending safe scopes frontier
        | exact nextArgument_safe predicate services source scope parents control context origins pending
            _ _ safe scopes frontier
        | exact consumeArgument_safe predicate services source scope parents control context origins pending
            _ _ _ _ _ safe scopes frontier
        | exact consumeBody_safe predicate services source scope parents control context origins pending
            _ _ _ safe scopes frontier
        | exact call_safe source _ safe
        | split

def Continues {User : Type} (services : Services User) (policy : EagerDFS.Destination.Policy)
    (program : SpaceSemantics.Program) (before after : State User) : Prop :=
  PettaOccurrenceOverlay.step services policy program before = .silent after ∨
    ∃ events, PettaOccurrenceOverlay.step services policy program before = .publish events after

theorem path_safe {User : Type} (predicate : RefinementTransport.BindingPredicate User)
    {services : Services User} {policy : EagerDFS.Destination.Policy} {program : SpaceSemantics.Program}
    {before after : State User}
    (path : Relation.ReflTransGen (Continues services policy program) before after)
    (safe : Safe predicate before) : Safe predicate after := by
  induction path with
  | refl => exact safe
  | @tail current after previous step induction =>
      have preserved := step_safe predicate services policy program current induction
      rcases step with silent | ⟨events, published⟩
      · rw [silent] at preserved
        exact preserved after (by simp [retained])
      · rw [published] at preserved
        exact preserved after (by simp [retained])

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceBinding
