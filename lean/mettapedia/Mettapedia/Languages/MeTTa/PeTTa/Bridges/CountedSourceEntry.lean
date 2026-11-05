import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedMatchEntry

/-!
# Authored size/collapse entry for an arbitrary raw body

Two actual source steps prepare the size operand and create its collapse
child. The original equations, caller continuation and surrounding scopes
are retained. This entry neither evaluates the body nor assumes a worker,
completed collection or successful result copy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CountedSourceEntry

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
  body : Atom

variable {Context : Type}

def Input.collection (input : Input Context) : Atom := .expression [.symbol "collapse", input.body]
def Input.source (input : Input Context) : Atom := .expression [.symbol "size-atom", input.collection]
def Input.entry (input : Input Context) : Control :=
  {input.caller with goals := .evaluate input.source input.destination :: input.caller.goals}
def Input.slot (input : Input Context) : String := freshName input.entry 0
def Input.waiting (input : Input Context) : Control :=
  {input.caller with goals := .invoke "size-atom" [.var input.slot] input.destination :: input.caller.goals}
def Input.preparing (input : Input Context) : Control :=
  {input.caller with goals := .evaluate input.collection (.var input.slot) :: input.waiting.goals}
def Input.before (input : Input Context) : ScopedCursor Context :=
  placed input.state.allocator input.state.world input.state.scope input.state.parents input.entry input.context input.origins input.pending
def Input.prepared (input : Input Context) : ScopedCursor Context :=
  placed input.state.allocator input.state.world input.state.scope input.state.parents input.preparing input.context input.origins input.pending
def Input.boundary (input : Input Context) : Finset String := collectionSupport input.prepared.2
def Input.childName (input : Input Context) : String := EagerDFS.Destination.childName input.preparing input.boundary
def Input.childCaller (input : Input Context) : Control :=
  {collapseChild input.preparing input.boundary input.body with goals := []}
def Input.savedCaller (input : Input Context) : CollectionCaller Context :=
  (input.waiting, .var input.slot, input.context, input.origins)
def Input.childState (input : Input Context) : State Context := {
  allocator := input.state.allocator, world := input.state.world
  scope := ⟨[], [], some input.savedCaller⟩
  parents := {input.state.scope with frontier := input.pending} :: input.state.parents }
def Input.childBefore (input : Input Context) : ScopedCursor Context :=
  ScopedMatchEntry.entrance input.body (.var input.childName) input.childCaller input.childState input.context input.origins []

theorem slot_fresh (input : Input Context) : FreshFor input.slot input.caller.bindings :=
  ClosedOnceQueryFrame.fresh_for_bindings input.entry _ (freshName_not_mem _ _)

theorem slot_apart (input : Input Context) : input.slot ∉ (encode input.destination).freeVars := by
  intro member
  apply freshName_not_mem input.entry 0
  apply Finset.mem_union_right
  apply (ClosedOnceQueryFrame.fold_support_iff _ _ _).mpr
  exact Or.inr ⟨input.destination, by simp [Input.entry, Goal.atoms], member⟩

theorem child_bindings (input : Input Context) : input.childCaller.bindings = input.caller.bindings := rfl

theorem child_result_fresh (input : Input Context) : FreshFor input.childName input.childCaller.bindings := by
  apply ClosedOnceQueryFrame.fresh_for_bindings input.preparing
  intro member
  exact childName_fresh input.preparing input.boundary (Finset.mem_union_left _ member)

theorem child_before (input : Input Context) :
    input.childBefore = (input.state.allocator,
      EagerDFS.Scope.enter input.state.world input.state.scope input.pending input.state.parents
        (collapseChild input.preparing input.boundary input.body, input.context, input.origins)
        input.savedCaller) := rfl

set_option maxHeartbeats 1200000 in
theorem entry_prefix (input : Input Context) :
    (ScopedQuerySource.machine .relational input.program).run 2 input.before =
      ([], .exhausted input.childBefore) := by
  have first : (ScopedQuerySource.machine .relational input.program).step input.before = some (.silent input.prepared) := by
    simp [ScopedQuerySource.machine, ScopedQuerySource.step, ScopedQuerySource.syntaxStep,
      ScopedQuerySource.constrainedCall, ScopedQuerySource.mutationCall, ScopedQuerySource.queryStep,
      Input.before, Input.prepared, placed, Input.entry, Input.preparing, Input.waiting, Input.source,
      Input.collection, Input.slot, scopeStep, enterCollapse?, enterSuperpose?,
      EagerDFS.Destination.machine, prepare, replace, installChild, retainChild, callable, StdLib.known,
      Eval.ioHead, callArguments, freshSlots, List.range_succ, Eval.argumentIsRaw, StdLib.rawArgument]
  have second : (ScopedQuerySource.machine .relational input.program).step input.prepared = some (.silent input.childBefore) := by
    simp only [Input.prepared]
    rw [ScopedQuerySource.Guards.placed_ordinary_step .relational input.program input.state.allocator input.state.world
      input.state.scope input.state.parents input.preparing input.context input.origins input.pending
      (.evaluate input.collection (.var input.slot)) input.waiting.goals rfl rfl]
    have entered := scope_collapse_entry .relational input.program input.state.allocator input.state.world
      {input.state.scope with frontier := (input.preparing, input.context, input.origins) :: input.pending}
      input.state.parents input.preparing input.context input.origins input.pending input.body (.var input.slot)
      input.waiting.goals rfl rfl
    change scopeStep .relational input.program input.prepared = .silent input.childBefore at entered
    exact congrArg some entered
  rw [Machine.run_succ_silent _ first, Machine.run_succ_silent _ second]
  rfl

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CountedSourceEntry
