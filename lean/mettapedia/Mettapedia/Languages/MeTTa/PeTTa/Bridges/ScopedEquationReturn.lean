import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedEquationSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedOnceQueryFrame

/-! Returning a named body restores its caller's predicate delimiter in one
actual scoped step. Bindings, world, allocator and pending work are retained. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedEquationReturn

open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open ClosedOnceQueryFrame (placed)

theorem restore_prefix {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (boundary : Nat) (older : List Goal)
    (atGoal : control.goals = .restoreCommit boundary :: older) :
    (ScopedQuerySource.machine policy program).run 1
      (placed allocator world scope parents control context origins pending) =
      ([], .exhausted (placed allocator world scope parents
        {control with goals := older, cutBoundary := boundary} context origins pending)) := by
  simp [Machine.run, ScopedQuerySource.machine, ScopedQuerySource.step, ScopedQuerySource.syntaxStep,
    ScopedQuerySource.constrainedCall, ScopedQuerySource.mutationCall, ScopedQuerySource.queryStep,
    placed, scopeStep, atGoal, enterCollapse?, enterSuperpose?, EagerDFS.Destination.machine,
    replace, retainChild, installChild]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedEquationReturn
