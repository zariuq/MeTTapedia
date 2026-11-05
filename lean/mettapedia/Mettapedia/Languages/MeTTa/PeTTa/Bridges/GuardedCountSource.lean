import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedCountReturn
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CountedSourceEntry

/-!
# Authored size-of-collapse entry for guarded nested queries

The size operand and collapse construct the real child destination and
saved caller. Changing the leaf's result slot changes no source expression.
The child worker retains every preparation equation and pending source scope.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedCountSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor placed)
open NamedGuardedCandidateBatch (State)

structure Input (Context : Type) where
  program : SpaceSemantics.Program
  state : State Context
  caller : Control
  context : Context
  origins : List Nat
  pending : List (CollectionWork Context)
  destination : Atom
  legs : List NestedQuerySource.Leg
  template : GuardedNestedQuerySource.Template

variable {Context : Type}

def Input.body (input : Input Context) : Atom := ScopedNestedQueryExecution.source input.legs input.template.source

def Input.asCountedEntry (input : Input Context) : CountedSourceEntry.Input Context := {
  program := input.program, state := input.state, caller := input.caller
  context := input.context, origins := input.origins, pending := input.pending
  destination := input.destination, body := input.body }

def Input.collection (input : Input Context) : Atom := .expression [.symbol "collapse", input.body]
def Input.source (input : Input Context) : Atom := .expression [.symbol "size-atom", input.collection]
def Input.entry (input : Input Context) : Control :=
  {input.caller with goals := .evaluate input.source input.destination :: input.caller.goals}
def Input.slot (input : Input Context) : String := freshName input.entry 0
def Input.waiting (input : Input Context) : Control := GuardedCountReturn.waiting input.caller input.slot input.destination
def Input.preparing (input : Input Context) : Control :=
  {input.caller with goals := .evaluate input.collection (.var input.slot) :: input.waiting.goals}
def Input.before (input : Input Context) : ScopedCursor Context :=
  placed input.state.allocator input.state.world input.state.scope input.state.parents input.entry input.context input.origins input.pending
def Input.prepared (input : Input Context) : ScopedCursor Context :=
  placed input.state.allocator input.state.world input.state.scope input.state.parents input.preparing input.context input.origins input.pending
def Input.boundary (input : Input Context) : Finset String := collectionSupport input.prepared.2
def Input.childName (input : Input Context) : String := EagerDFS.Destination.childName input.preparing input.boundary
def Input.childTemplate (input : Input Context) : GuardedNestedQuerySource.Template :=
  {input.template with body := {input.template.body with result := input.childName}}
def Input.childCaller (input : Input Context) : Control :=
  {collapseChild input.preparing input.boundary input.body with goals := []}
def Input.savedCaller (input : Input Context) : CollectionCaller Context :=
  (input.waiting, .var input.slot, input.context, input.origins)
def Input.childState (input : Input Context) : State Context := {
  allocator := input.state.allocator, world := input.state.world
  scope := ⟨[], [], some input.savedCaller⟩
  parents := {input.state.scope with frontier := input.pending} :: input.state.parents }
def Input.childBefore (input : Input Context) : ScopedCursor Context :=
  ScopedMatchEntry.entrance (ScopedNestedQueryExecution.source input.legs input.childTemplate.source)
    (.var input.childTemplate.body.result) input.childCaller input.childState input.context input.origins []
def Input.childExecution (input : Input Context) : ScopedNestedQueryExecution.Execution Context :=
  ScopedNestedQueryExecution.run input.program (GuardedNestedQuerySource.leaf input.program input.childTemplate Context)
    input.legs input.childCaller input.childState input.context input.origins []

theorem child_source (input : Input Context) : input.childTemplate.source = input.template.source := rfl

theorem slot_fresh (input : Input Context) : FreshFor input.slot input.caller.bindings :=
  ClosedOnceQueryFrame.fresh_for_bindings input.entry _ (freshName_not_mem _ _)

theorem slot_apart (input : Input Context) : input.slot ∉ (encode input.destination).freeVars := by
  intro member
  apply freshName_not_mem input.entry 0
  apply Finset.mem_union_right
  apply (ClosedOnceQueryFrame.fold_support_iff _ _ _).mpr
  exact Or.inr ⟨input.destination, by simp [Input.entry, Goal.atoms], member⟩

theorem entry_prefix (input : Input Context) :
    (ScopedQuerySource.machine .relational input.program).run 2 input.before =
      ([], .exhausted input.childBefore) :=
  CountedSourceEntry.entry_prefix input.asCountedEntry

/-- No child completion is assumed: reference handoff and suspension retain
the reached scoped cursor after the two authored entry steps. -/
theorem child_prefix (input : Input Context) :
    (ScopedQuerySource.machine .relational input.program).run (2 + input.childExecution.budget) input.before =
      input.childExecution.observation [] := by
  have child := GuardedNestedQuerySource.run_exact input.program input.childTemplate input.legs
    input.childCaller input.childState input.context input.origins []
  change (ScopedQuerySource.machine .relational input.program).run input.childExecution.budget input.childBefore =
    input.childExecution.observation [] at child
  have joined := (ScopedQuerySource.machine .relational input.program).established_and_pending
    2 input.childExecution.budget _ _ [] (entry_prefix input)
  rw [child] at joined
  simpa only [List.nil_append] using joined

/-- Completion supplies the exact empty-frontier collector shape, not a
standalone readiness flag. Its original saved caller and parent are retained. -/
theorem completed_boundary (input : Input Context) (after : State Context)
    (completed : input.childExecution.stop = .complete after) :
    after.cursor [] = GuardedQueryCollection.boundary after.allocator after.world after.scope.collected
      input.savedCaller {input.state.scope with frontier := input.pending} input.state.parents := by
  have kept := GuardedNestedQuerySource.completed_context input.program input.childTemplate input.legs
    input.childCaller input.childState input.context input.origins [] after completed
  change after.scope.caller = some input.savedCaller ∧
    after.parents = {input.state.scope with frontier := input.pending} :: input.state.parents at kept
  simp only [State.cursor, GuardedQueryCollection.boundary, kept.2]
  congr 2
  cases scope : after.scope
  simp_all

theorem completed_packets (input : Input Context) (after : State Context)
    (completed : input.childExecution.stop = .complete after) : GuardedQueryPackets.CollectedReady after :=
  GuardedQueryPackets.completed_ready input.program input.childTemplate input.legs input.childCaller
    input.childState input.context input.origins [] after rfl completed

def Input.copies (_input : Input Context) (after : State Context) :=
  EagerDFS.Collection.copyOwnedAnswers? after.allocator (collectionSupport (after.cursor []).2)
    (after.scope.collected.map (fun packet => (packet.value, packet.associated)))

def Input.copiedCursor (input : Input Context) (after : State Context)
    (allocator : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Allocator) : ScopedCursor Context :=
  placed allocator after.world input.state.scope input.state.parents
    (GuardedCountReturn.tupleReturned input.caller input.slot input.destination after.scope.collected.length)
    input.context input.origins input.pending

/-- Collector copy success and refusal are both source outcomes. All query
effects and collected packets remain in the allocation-suspended cursor. -/
theorem copy_boundary (input : Input Context) (after : State Context)
    (completed : input.childExecution.stop = .complete after) :
    (ScopedQuerySource.machine .relational input.program).run (2 + input.childExecution.budget + 1) input.before =
      (input.childExecution.events, match input.copies after with
        | none => .suspended .allocation (after.cursor [])
        | some (next, _) => .exhausted (input.copiedCursor after next)) := by
  have reached := child_prefix input
  simp only [ScopedNestedQueryExecution.Execution.observation, completed, ScopedNestedQueryExecution.Stop.outcome] at reached
  have exited := GuardedQueryCollection.return_boundary input.program after.allocator after.world after.scope.collected
    input.savedCaller {input.state.scope with frontier := input.pending} input.state.parents (completed_packets input after completed)
  dsimp only at exited
  rw [← completed_boundary input after completed] at exited
  change (ScopedQuerySource.machine .relational input.program).run 1 (after.cursor []) =
    ([], match input.copies after with
      | none => .suspended .allocation (after.cursor [])
      | some (next, _) => .exhausted (input.copiedCursor after next)) at exited
  have joined := (ScopedQuerySource.machine .relational input.program).established_and_pending
    (2 + input.childExecution.budget) 1 _ _ _ reached
  rw [exited] at joined
  simpa only [List.append_nil] using joined

/-- Once actual copying succeeds, the source returns the computed packet
count to its unbound (possibly aliased) destination and original continuation. -/
theorem counted_prefix (input : Input Context) (after : State Context)
    (next : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Allocator)
    (copies : List (Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Token × (Atom × List Atom)))
    (principal : Environment) (representative : String)
    (resolved : resolve input.caller.bindings = some principal)
    (unbound : read principal input.destination = .var representative)
    (completed : input.childExecution.stop = .complete after)
    (copied : input.copies after = some (next, copies)) :
    (ScopedQuerySource.machine .relational input.program).run (2 + input.childExecution.budget + 1 + 3) input.before =
      (input.childExecution.events, .exhausted (placed next after.world input.state.scope input.state.parents
        (GuardedCountReturn.counted input.caller input.slot input.destination after.scope.collected.length)
        input.context (input.origins ++ [0]) input.pending)) := by
  have collected := copy_boundary input after completed
  rw [copied] at collected
  have returned := GuardedCountReturn.count_prefix input.program next after.world input.state.scope input.state.parents
    input.caller input.context input.origins input.pending input.slot input.destination after.scope.collected.length
    principal representative resolved unbound (slot_fresh input) (slot_apart input)
  change (ScopedQuerySource.machine .relational input.program).run 3 (input.copiedCursor after next) = _ at returned
  have joined := (ScopedQuerySource.machine .relational input.program).established_and_pending
    (2 + input.childExecution.budget + 1) 3 _ _ _ collected
  rw [returned] at joined
  simpa only [List.append_nil] using joined

/-- Constrained numeric results retain reference entry after the copied
tuple has been installed. Earlier query effects and allocation are kept. -/
theorem constrained_prefix (input : Input Context) (after : State Context)
    (next : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Allocator)
    (copies : List (Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Token × (Atom × List Atom)))
    (principal : Environment)
    (completed : input.childExecution.stop = .complete after)
    (copied : input.copies after = some (next, copies))
    (resolved : resolve (GuardedCountReturn.ready input.caller input.slot input.destination after.scope.collected.length).bindings = some principal)
    (constrained : ∀ name, read principal input.destination ≠ .var name) :
    (ScopedQuerySource.machine .relational input.program).run (2 + input.childExecution.budget + 1 + 2) input.before =
      (input.childExecution.events, .suspended (.branch (.invoke "size-atom" [.var input.slot] input.destination))
        (placed next after.world input.state.scope input.state.parents
          (GuardedCountReturn.ready input.caller input.slot input.destination after.scope.collected.length)
          input.context input.origins input.pending)) := by
  have collected := copy_boundary input after completed
  rw [copied] at collected
  have requested := GuardedCountReturn.constrained_prefix input.program next after.world input.state.scope input.state.parents
    input.caller input.context input.origins input.pending input.slot input.destination after.scope.collected.length
    principal (slot_fresh input) resolved constrained
  change (ScopedQuerySource.machine .relational input.program).run 2 (input.copiedCursor after next) = _ at requested
  have joined := (ScopedQuerySource.machine .relational input.program).established_and_pending
    (2 + input.childExecution.budget + 1) 2 _ _ _ collected
  rw [requested] at joined
  simpa only [List.append_nil] using joined

theorem count_is_growth (input : Input Context) (after : State Context) (fields : List Atom)
    (frontierCode : input.template.body.secondCode = .expression (.symbol "fr" :: fields))
    (completed : input.childExecution.stop = .complete after) :
    GuardedQueryGrowth.measure input.template.satisfactionHandle after.world.state =
      GuardedQueryGrowth.measure input.template.satisfactionHandle input.state.world.state + after.scope.collected.length :=
  GuardedQueryGrowth.nested_packet_count input.program input.childTemplate fields frontierCode input.legs
    input.childCaller input.childState input.context input.origins [] after rfl completed

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedCountSource
