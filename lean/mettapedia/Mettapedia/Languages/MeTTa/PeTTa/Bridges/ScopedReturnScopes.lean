import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnDispatch

/-!
# Branch-local return obligations in retained collection scopes

The owning scope's work retains the return obligation. While a nested
collection runs, its immediate saved caller carries that obligation; child
answers are unrestricted. Each occurrence may have its own fresh recipe and
input read, even when two occurrences have equal context labels.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnScopes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open ScopedReturnLocal (AliasHolds)

def WorkReturns {Context : Type} (arguments : Context → Atom) (work : CollectionWork Context) : Prop :=
  AliasHolds (arguments work.2.1) work.1

def CallerReturns {Context : Type} (arguments : Context → Atom) (scope : CollectionScope Context) : Prop :=
  ∀ caller, scope.caller = some caller → AliasHolds (arguments caller.2.2.1) caller.1

inductive Stack {Context : Type} (arguments : Context → Atom) : List (CollectionScope Context) → Prop where
  | root (scope : CollectionScope Context) (works : ∀ work ∈ scope.frontier, WorkReturns arguments work) :
      Stack arguments [scope]
  | nested (child parent : CollectionScope Context) (parents : List (CollectionScope Context))
      (rest : Stack arguments (parent :: parents))
      (caller : parents = [] → CallerReturns arguments child) :
      Stack arguments (child :: parent :: parents)

theorem Stack.nonempty {Context : Type} {arguments : Context → Atom} {scopes : List (CollectionScope Context)}
    (valid : Stack arguments scopes) : scopes ≠ [] := by cases valid <;> simp

theorem Stack.replace_head {Context : Type} {arguments : Context → Atom}
    {scope : CollectionScope Context} {parents : List (CollectionScope Context)}
    (valid : Stack arguments (scope :: parents)) (frontier : List (CollectionWork Context))
    (collected : List CollectedAnswer)
    (rootWork : parents = [] → ∀ work ∈ frontier, WorkReturns arguments work) :
    Stack arguments ({scope with frontier, collected} :: parents) := by
  cases valid with
  | root scope works => exact .root _ (rootWork rfl)
  | nested child parent parents rest caller => exact .nested _ _ _ rest caller

theorem Stack.replace_active {Context : Type} {arguments : Context → Atom}
    {scope : CollectionScope Context} {parents : List (CollectionScope Context)}
    (valid : Stack arguments (scope :: parents)) (control : Control) (context : Context)
    (origins : List Nat) (pending generated : List (CollectionWork Context))
    (collected : List CollectedAnswer)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (produced : AliasHolds (arguments context) control →
      ∀ work ∈ generated, WorkReturns arguments work) :
    Stack arguments ({scope with frontier := generated ++ pending, collected} :: parents) := by
  apply valid.replace_head
  intro root work present
  subst parents
  cases valid with
  | root scope works =>
      rcases List.mem_append.mp present with newly | retained
      · exact produced (works (control, context, origins) (frontier ▸ List.mem_cons_self)) work newly
      · exact works work (frontier ▸ List.mem_cons_of_mem _ retained)

theorem Stack.root_work {Context : Type} {arguments : Context → Atom} {scope : CollectionScope Context}
    (valid : Stack arguments [scope]) : ∀ work ∈ scope.frontier, WorkReturns arguments work := by
  cases valid with
  | root scope works => exact works

theorem Stack.push {Context : Type} {arguments : Context → Atom}
    {scope : CollectionScope Context} {parents : List (CollectionScope Context)}
    (valid : Stack arguments (scope :: parents)) (child : CollectionScope Context)
    (pending : List (CollectionWork Context))
    (retained : parents = [] → ∀ work ∈ pending, WorkReturns arguments work)
    (caller : parents = [] → CallerReturns arguments child) :
    Stack arguments (child :: {scope with frontier := pending} :: parents) :=
  .nested _ _ _ (valid.replace_head pending scope.collected retained) caller

/-- A completed collection restores the saved caller's own record. No
relation between its arbitrary child answers and the outer input is needed. -/
theorem Stack.resume {Context : Type} {arguments : Context → Atom}
    {child parent : CollectionScope Context} {parents : List (CollectionScope Context)}
    (valid : Stack arguments (child :: parent :: parents)) (caller : CollectionCaller Context)
    (saved : child.caller = some caller) (work : CollectionWork Context)
    (returned : AliasHolds (arguments caller.2.2.1) caller.1 → WorkReturns arguments work) :
    Stack arguments ({parent with frontier := work :: parent.frontier} :: parents) := by
  cases valid with
  | nested child parent parents rest callerGood =>
      apply rest.replace_head
      intro root found member
      subst parents
      rcases List.mem_cons.mp member with rfl | older
      · exact returned (callerGood rfl caller saved)
      · exact rest.root_work found older

theorem Stack.allocated_return {Context : Type} {arguments : Context → Atom}
    {child parent : CollectionScope Context} {parents : List (CollectionScope Context)}
    (valid : Stack arguments (child :: parent :: parents)) (caller : CollectionCaller Context)
    (saved : child.caller = some caller)
    (copies : List (Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Token × (Atom × List Atom))) :
    Stack arguments ({parent with frontier := allocatedWork copies caller :: parent.frontier} :: parents) := by
  apply valid.resume caller saved
  rintro ⟨name, holds⟩
  exact ⟨name, ScopedReturnDispatch.allocated_collection_return name _ copies caller holds⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnScopes
