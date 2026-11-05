import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceDriver

/-!
# Numeric publication and finished root execution of the EU driver

The proved named invocation returns to its caller first. At a root boundary
with no pending alternatives or caller goals, the existing scope scheduler
then publishes the actual numeric answer and finishes. Prior recorded root
answers remain in the scope; this invocation emits one new occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceResult

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open ClosedOnceQueryFrame (placed)
open CTLUntilSourceRows (number)
open FlatQueryRowCodec (Codec)
open CTLUntilMixedStore (Row decodeRows satisfactionView frontSelect)

variable {Context Label : Type} [DecidableEq Label]
variable {codec : Codec Label} {label holds goal : Label} {call : CTLUntilNamedSeed.Call Context}
variable {entry : CTLUntilSourceDriver.Entry codec label holds goal call}

def packet (completed : CTLUntilSourceDriver.Completed entry) : CollectedAnswer :=
  ⟨number completed.counter, completed.control.bindings, completed.origins, []⟩

def finishedCursor (completed : CTLUntilSourceDriver.Completed entry) : ScopedCursor Context :=
  (completed.after.allocator, ⟨completed.after.world,
    [EagerDFS.Scope.record completed.after.scope [] (packet completed)]⟩)

theorem completed_publishes (completed : CTLUntilSourceDriver.Completed entry)
    (older : call.older = []) (pending : call.pending = []) (parents : call.state.parents = [])
    (root : call.state.scope.caller = none) (output : call.control.destination = .var entry.root) :
    (ScopedQuerySource.machine .relational call.program).run (completed.budget + 2) call.before =
      ([packet completed], .finished (finishedCursor completed)) := by
  have finalParents : completed.after.parents = [] := completed.parents.trans parents
  have finalGoals : completed.control.goals = [] := completed.goals.trans older
  have finalRoot : completed.after.scope.caller = none := by rw [completed.scope, root]
  have finalDestination : completed.control.destination = .var entry.root := completed.destination.trans output
  let reached : ScopedCursor Context := placed completed.after.allocator completed.after.world completed.after.scope []
    completed.control call.context completed.origins []
  have earlier : (ScopedQuerySource.machine .relational call.program).run completed.budget call.before =
      ([], .exhausted reached) := by
    simpa only [finalParents, pending, reached] using completed.execution
  have emitted : (ScopedQuerySource.machine .relational call.program).step reached =
      some (.publish [packet completed] (finishedCursor completed)) := by
    dsimp only [reached, placed]
    rw [ScopedQuerySource.Guards.empty_goals_step .relational call.program completed.after.allocator completed.after.world
      {completed.after.scope with frontier := [(completed.control, call.context, completed.origins)]} []
      completed.control call.context completed.origins [] rfl finalGoals]
    have actual := scope_terminal_value .relational call.program completed.after.allocator completed.after.world
      {completed.after.scope with frontier := [(completed.control, call.context, completed.origins)]} []
      completed.control call.context completed.origins [] completed.principal rfl finalGoals completed.resolved
    simpa only [finalRoot, Option.isNone_none, ↓reduceIte, finalDestination, completed.value,
      packet, finishedCursor, EagerDFS.Scope.record] using congrArg some actual
  have finished : (ScopedQuerySource.machine .relational call.program).step (finishedCursor completed) =
      some (.finish (finishedCursor completed)) := by
    dsimp only [finishedCursor]
    rw [ScopedQuerySource.Guards.empty_frontier_step .relational call.program completed.after.allocator
      completed.after.world (EagerDFS.Scope.record completed.after.scope [] (packet completed)) [] rfl]
    simp only [scopeStep, EagerDFS.Scope.record, finalRoot]
  have last : (ScopedQuerySource.machine .relational call.program).run 2 reached =
      ([packet completed], .finished (finishedCursor completed)) := by
    simp [Machine.run, emitted, finished]
  have joined := (ScopedQuerySource.machine .relational call.program).established_and_pending
    completed.budget 2 _ _ [] earlier
  rw [last] at joined
  simpa only [List.nil_append] using joined

/-- Initial source evidence and usable identity reserve construct the whole
root run, including answer publication. No completed source run is a premise. -/
theorem terminates (entry : CTLUntilSourceDriver.Entry codec label holds goal call)
    (reserve : entry.allowance ≤ call.state.allocator.usableCount)
    (older : call.older = []) (pending : call.pending = []) (parents : call.state.parents = [])
    (root : call.state.scope.caller = none) (output : call.control.destination = .var entry.root) :
    ∃ completed : CTLUntilSourceDriver.Completed entry,
      (ScopedQuerySource.machine .relational call.program).run (completed.budget + 2) call.before =
        ([packet completed], .finished (finishedCursor completed)) ∧
      ∃ atoms rows, (finishedCursor completed).2.world.state.read .self = some atoms ∧
        decodeRows codec atoms = some rows ∧
        (∀ vertex, vertex ∈ satisfactionView label rows ↔ Mettapedia.Logic.CTLFixedPoints.Until
          (Mettapedia.Machines.CTLUntilFrontier.Relation entry.edges.toFinset)
          ↑entry.holding.toFinset ↑entry.goals.toFinset vertex) ∧
        ∀ round, rows.filterMap (frontSelect label round) = [] := by
  obtain ⟨completed⟩ := CTLUntilSourceDriver.terminates entry reserve
  exact ⟨completed, completed_publishes completed older pending parents root output, completed.observed_until⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceResult
