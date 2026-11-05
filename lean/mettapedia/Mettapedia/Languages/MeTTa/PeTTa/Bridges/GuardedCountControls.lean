import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedCountSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedNestedQueryControls

/-! Authored size/collapse returns, exact-capacity boundaries, aliases and
constrained-result handoff after the query's effects and copy return. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedCountSource.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open ScopedQuerySource.Controls (call number)

def base : Input Unit := {
  program := ScopedNestedQueryExecution.Controls.program
  state := ScopedNestedQueryExecution.Controls.initial
  caller := ScopedNestedQueryExecution.Controls.caller
  context := (), origins := [9], pending := [], destination := .var "answer"
  legs := ScopedNestedQueryExecution.Controls.legs
  template := ScopedNestedQueryExecution.Controls.template }

def sourceRun (input : Input Unit) (fuel : Nat := 600) :=
  (ScopedQuerySource.machine .relational input.program).run fuel input.before
def sourceRows (input : Input Unit) :=
  (EagerDFSStreaming.Scoped.readback (sourceRun input).2).bind (fun cursor => cursor.2.world.state.read .self)
def childAfter? (input : Input Unit) : Option (NamedGuardedCandidateBatch.State Unit) := match input.childExecution.stop with
  | .complete after => some after
  | _ => none
def allocationStopped (input : Input Unit) : Bool := match (sourceRun input).2 with
  | .suspended .allocation _ => true
  | _ => false

#guard base.childTemplate.source == base.template.source
#guard base.childTemplate.body.result != base.template.body.result
#guard base.childExecution.events.isEmpty
#guard base.childExecution.budget == 285
#guard (childAfter? base).map (fun after => after.scope.collected.length) == some 1
#guard (sourceRun base).1.map CollectedAnswer.value == [number 1]
#guard sourceRows base == some (CTLUntilMixedStore.Controls.atoms ++
  [call "sat" [number 10, number 1], call "fr" [number 10, number 1, number 1]])

def capacity (amount : Nat) : Input Unit := {base with state := {base.state with allocator := Allocator.empty amount 8}}
-- Seven held witnesses consume seven copy identities before collector exit.
#guard (childAfter? (capacity 7)).isSome
#guard allocationStopped (capacity 7)
#guard (sourceRun (capacity 7)).1.isEmpty
#guard sourceRows (capacity 7) == sourceRows base
#guard (sourceRun (capacity 8)).1.map CollectedAnswer.value == [number 1]
-- One fewer identity suspends inside the child, not at collector exit.
#guard (childAfter? (capacity 6)).isNone
#guard allocationStopped (capacity 6)

def emptyGraph : Input Unit := {capacity 0 with state := {(capacity 0).state with
  world := ⟨NamedSpaces.Store.new [] [], [], []⟩}}
#guard (childAfter? emptyGraph).map (fun after => after.scope.collected.length) == some 0
#guard (sourceRun emptyGraph).1.map CollectedAnswer.value == [number 0]

-- An already mentioned but unbound result alias remains an ordinary route.
def aliasOutput : Input Unit := {base with caller := {base.caller with
  bindings := base.caller.bindings ++ [(.var "answer", .var "alias")]}}
#guard (sourceRun aliasOutput).1.map CollectedAnswer.value == [number 1]

-- A constrained result retains reference service only after collecting and
-- copying the reached query result. The source writes are not replayed.
def constrained : Input Unit := {base with destination := number 1}
def countHandoff : Bool := match (sourceRun constrained).2 with
  | .suspended (.branch (.invoke "size-atom" _ _)) _ => true
  | _ => false
#guard countHandoff
#guard (sourceRun constrained).1.isEmpty
#guard sourceRows constrained == sourceRows base

def growing : Input Unit := {base with
  state := ScopedNestedQueryExecution.Controls.changingState
  legs := ScopedNestedQueryExecution.Controls.changingLegs
  template := ScopedNestedQueryExecution.Controls.changingTemplate }
#guard (sourceRun growing).1.map CollectedAnswer.value == [number 2]
#guard sourceRows growing == ScopedNestedQueryExecution.Controls.rows ScopedNestedQueryExecution.Controls.changing

#print axioms GuardedQueryCollection.return_boundary
#print axioms GuardedCountReturn.count_prefix
#print axioms GuardedCountReturn.constrained_prefix
#print axioms entry_prefix
#print axioms child_prefix
#print axioms completed_boundary
#print axioms copy_boundary
#print axioms counted_prefix
#print axioms constrained_prefix
#print axioms count_is_growth

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedCountSource.Controls
