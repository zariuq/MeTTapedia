import Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnRaw

/-!
# Compound return obligations in actual retained collection scopes

Each root occurrence carries its own fresh recipe. An inner collection does
not owe its parent's result: its saved caller retains that obligation while
the inner frontier computes unrestricted values.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnScopes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open DestinationDataReturnState (AliasHolds)

def WorkReturns {Context : Type} (program : SpaceSemantics.Program) (arguments : Context → Atom)
    (work : CollectionWork Context) : Prop := AliasHolds program (arguments work.2.1) work.1

def CallerReturns {Context : Type} (program : SpaceSemantics.Program) (arguments : Context → Atom)
    (scope : CollectionScope Context) : Prop :=
  ∀ caller, scope.caller = some caller → AliasHolds program (arguments caller.2.2.1) caller.1

inductive Stack {Context : Type} (program : SpaceSemantics.Program) (arguments : Context → Atom) :
    List (CollectionScope Context) → Prop where
  | root (scope : CollectionScope Context)
      (works : ∀ work ∈ scope.frontier, WorkReturns program arguments work) : Stack program arguments [scope]
  | nested (child parent : CollectionScope Context) (parents : List (CollectionScope Context))
      (rest : Stack program arguments (parent :: parents))
      (caller : parents = [] → CallerReturns program arguments child) :
      Stack program arguments (child :: parent :: parents)

theorem Stack.nonempty {Context : Type} {program : SpaceSemantics.Program} {arguments : Context → Atom}
    {scopes : List (CollectionScope Context)} (valid : Stack program arguments scopes) : scopes ≠ [] := by
  cases valid <;> simp

theorem Stack.replace_head {Context : Type} {program : SpaceSemantics.Program} {arguments : Context → Atom}
    {scope : CollectionScope Context} {parents : List (CollectionScope Context)}
    (valid : Stack program arguments (scope :: parents)) (frontier : List (CollectionWork Context))
    (collected : List CollectedAnswer)
    (rootWork : parents = [] → ∀ work ∈ frontier, WorkReturns program arguments work) :
    Stack program arguments ({scope with frontier, collected} :: parents) := by
  cases valid with
  | root scope works => exact .root _ (rootWork rfl)
  | nested child parent parents rest caller => exact .nested _ _ _ rest caller

theorem Stack.replace_active {Context : Type} {program : SpaceSemantics.Program} {arguments : Context → Atom}
    {scope : CollectionScope Context} {parents : List (CollectionScope Context)}
    (valid : Stack program arguments (scope :: parents)) (control : Control) (context : Context)
    (origins : List Nat) (pending generated : List (CollectionWork Context)) (collected : List CollectedAnswer)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (produced : AliasHolds program (arguments context) control →
      ∀ work ∈ generated, WorkReturns program arguments work) :
    Stack program arguments ({scope with frontier := generated ++ pending, collected} :: parents) := by
  apply valid.replace_head
  intro root work present
  subst parents
  cases valid with
  | root scope works =>
      rcases List.mem_append.mp present with newly | retained
      · exact produced (works (control, context, origins) (frontier ▸ List.mem_cons_self)) work newly
      · exact works work (frontier ▸ List.mem_cons_of_mem _ retained)

theorem Stack.root_work {Context : Type} {program : SpaceSemantics.Program} {arguments : Context → Atom}
    {scope : CollectionScope Context} (valid : Stack program arguments [scope]) :
    ∀ work ∈ scope.frontier, WorkReturns program arguments work := by
  cases valid with
  | root scope works => exact works

theorem Stack.push {Context : Type} {program : SpaceSemantics.Program} {arguments : Context → Atom}
    {scope : CollectionScope Context} {parents : List (CollectionScope Context)}
    (valid : Stack program arguments (scope :: parents)) (child : CollectionScope Context)
    (pending : List (CollectionWork Context))
    (retained : parents = [] → ∀ work ∈ pending, WorkReturns program arguments work)
    (caller : parents = [] → CallerReturns program arguments child) :
    Stack program arguments (child :: {scope with frontier := pending} :: parents) :=
  .nested _ _ _ (valid.replace_head pending scope.collected retained) caller

theorem Stack.resume {Context : Type} {program : SpaceSemantics.Program} {arguments : Context → Atom}
    {child parent : CollectionScope Context} {parents : List (CollectionScope Context)}
    (valid : Stack program arguments (child :: parent :: parents)) (caller : CollectionCaller Context)
    (saved : child.caller = some caller) (work : CollectionWork Context)
    (returned : AliasHolds program (arguments caller.2.2.1) caller.1 → WorkReturns program arguments work) :
    Stack program arguments ({parent with frontier := work :: parent.frontier} :: parents) := by
  cases valid with
  | nested child parent parents rest callerGood =>
      apply rest.replace_head
      intro root found member
      subst parents
      rcases List.mem_cons.mp member with rfl | older
      · exact returned (callerGood rfl caller saved)
      · exact rest.root_work found older

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataReturnScopes
