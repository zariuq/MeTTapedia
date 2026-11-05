import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilNamedSeed
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceRecursion

/-!
# The authored EU driver from its actual named invocation

Initial decoded rows determine the graph, operand and goal occurrence bags.
The source seeds the output, prepares its actual recursive invocation and
executes finite-support recursion. The enclosing predicate delimiter is then
restored. No successful source execution or body-adequacy premise is supplied.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceDriver

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor placed)
open NamedGuardedCandidateBatch (State)
open FlatQueryRowCodec (Codec)
open CTLUntilMixedStore (Row render decodeRows graphView satisfactionView frontSelect)
open CTLUntilSourceRows (number)
open Mettapedia.Machines

variable {Context Label : Type} [DecidableEq Label]

structure Entry (codec : Codec Label) (label holds goal : Label) (call : CTLUntilNamedSeed.Call Context) where
  evidence : CTLUntilNamedSeed.Evidence codec label holds goal call
  authored : call.program = ScopedQuerySource.CTLUntilDriverControls.program
  root : String
  output : call.destination = .var root
  rootFresh : FreshFor root call.control.bindings
  atoms : List Atom
  rows : List (Row Label)
  snapshot : call.state.world.state.read .self = some atoms
  decoded : decodeRows codec atoms = some rows
  separate : label ≠ holds
  goalSeparate : label ≠ goal
  emptyKnown : satisfactionView label rows = []
  emptyFrontiers : ∀ round, rows.filterMap (frontSelect label round) = []

def Entry.edges {codec : Codec Label} {label holds goal : Label} {call : CTLUntilNamedSeed.Call Context}
    (entry : Entry codec label holds goal call) : List (Nat × Nat) := graphView entry.rows
def Entry.holding {codec : Codec Label} {label holds goal : Label} {call : CTLUntilNamedSeed.Call Context}
    (entry : Entry codec label holds goal call) : List Nat := satisfactionView holds entry.rows
def Entry.goals {codec : Codec Label} {label holds goal : Label} {call : CTLUntilNamedSeed.Call Context}
    (entry : Entry codec label holds goal call) : List Nat := satisfactionView goal entry.rows
def Entry.allowance {codec : Codec Label} {label holds goal : Label} {call : CTLUntilNamedSeed.Call Context}
    (entry : Entry codec label holds goal call) : Nat :=
  entry.goals.length + CTLUntilFiniteSupport.allowance entry.edges entry.holding ⟨entry.goals, entry.goals⟩
def Entry.seedReturned {codec : Codec Label} {label holds goal : Label} {call : CTLUntilNamedSeed.Call Context}
    (entry : Entry codec label holds goal call) : Control :=
  call.seedReturned (CTLUntilNamedSeed.values codec label holds goal) entry.goals.length
def Entry.loopCaller {codec : Codec Label} {label holds goal : Label} {call : CTLUntilNamedSeed.Call Context}
    (entry : Entry codec label holds goal call) : Control :=
  {entry.seedReturned with goals := .restoreCommit call.control.cutBoundary :: call.older}
def Entry.operands {codec : Codec Label} {label holds goal : Label} {call : CTLUntilNamedSeed.Call Context}
    (_entry : Entry codec label holds goal call) : List Atom := [.var (call.rename "f"), .var (call.rename "a"), number 0]
def Entry.ready {codec : Codec Label} {label holds goal : Label} {call : CTLUntilNamedSeed.Call Context}
    (entry : Entry codec label holds goal call) : Control :=
  ScopedAtomicCallOperands.ready entry.loopCaller "eu-loop" entry.operands (.var entry.root)
def Entry.arguments {codec : Codec Label} {label holds goal : Label} {call : CTLUntilNamedSeed.Call Context}
    (entry : Entry codec label holds goal call) : List Atom :=
  (ScopedAtomicCallOperands.slotNames entry.loopCaller "eu-loop" entry.operands (.var entry.root)).map Atom.var
def Entry.loopCall {codec : Codec Label} {label holds goal : Label} {call : CTLUntilNamedSeed.Call Context}
    (entry : Entry codec label holds goal call) (after : State Context) (allocator : Allocator) : CTLUntilNamedLoop.Call Context := {
  program := call.program
  state := {call.state with allocator, world := after.world}
  control := entry.ready
  context := call.context
  origins := (call.origins ++ [call.occurrence]) ++ [0]
  pending := call.pending
  arguments := entry.arguments
  root := entry.root
  older := .restoreCommit call.control.cutBoundary :: call.older
  occurrence := 3 }

theorem root_apart {codec : Codec Label} {label holds goal : Label} {call : CTLUntilNamedSeed.Call Context}
    (entry : Entry codec label holds goal call) (name : String) : entry.root ≠ call.rename name := by
  intro same
  apply ClauseChoice.rename_fresh call.protectedControl call.occurrence
    (ClauseChoice.clauseAtoms CTLUntilNamedSeed.definition.declaration) name
  change call.rename name ∈ call.protectedControl.support
  rw [← same, CTLUntilNamedSeed.Call.protectedControl, protectControl_support]
  apply Finset.mem_union_left
  apply ScopedClosedEquationSource.call_destination_retained call.control "do-eu" call.arguments call.destination call.older entry.evidence.atCall
  simp [entry.output, encode, Mettapedia.Logic.LP.Term.freeVars]

theorem prepared_frame {codec : Codec Label} {label holds goal : Label} {call : CTLUntilNamedSeed.Call Context}
    (entry : Entry codec label holds goal call) :
    ∃ principal, resolve entry.ready.bindings = some principal ∧
      entry.arguments.map (read principal) = CTLUntilNamedLoop.values codec label holds 0 ∧
      FreshFor entry.root entry.ready.bindings := by
  obtain ⟨before, resolved, formula, operand, _count⟩ := CTLUntilNamedSeed.returned_frame entry.evidence
    entry.atoms entry.rows entry.snapshot entry.decoded
  obtain ⟨principal, prepared⟩ := resolve_complete (ScopedAtomicCallOperands.ready_consistent entry.loopCaller
    "eu-loop" entry.operands (.var entry.root) ⟨before, resolve_sound resolved⟩)
  have readings := ScopedAtomicPrimitive.readings entry.loopCaller "eu-loop" entry.operands (.var entry.root)
    before principal resolved prepared (by
      intro atom member environment
      simp only [Entry.operands, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · rw [formula]; exact LiteralQuerySource.read_literal _ (codec.literal label) environment
      · rw [operand]; exact LiteralQuerySource.read_literal _ (codec.literal holds) environment
      · rw [CTLUntilSourceCapture.number_closed]; exact CTLUntilSourceCapture.number_closed 0 environment)
  have fresh := CTLUntilNamedSeed.returned_root_fresh entry.evidence entry.root entry.output entry.rootFresh entry.goals.length
  have preparedFresh : FreshFor entry.root entry.ready.bindings := by
    apply ScopedAtomicCallOperands.ready_fresh_of_entry_support entry.loopCaller "eu-loop" entry.operands (.var entry.root)
      entry.root fresh
    · apply GuardedInsertionPairSource.goal_atom_support _ (.var entry.root) entry.root
      · simp [ScopedAtomicCallOperands.entry, Goal.atoms]
      · simp [encode, Mettapedia.Logic.LP.Term.freeVars]
    · intro atom member
      simp only [Entry.operands, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · simpa [encode, Mettapedia.Logic.LP.Term.freeVars] using root_apart entry "f"
      · simpa [encode, Mettapedia.Logic.LP.Term.freeVars] using root_apart entry "a"
      · simp [number, encode, Mettapedia.Logic.LP.Term.freeVars]
  refine ⟨principal, prepared, ?_, preparedFresh⟩
  simpa only [Entry.arguments, Entry.operands, CTLUntilNamedLoop.values, List.map_cons, List.map_nil,
    formula, operand, CTLUntilSourceCapture.number_closed] using readings

theorem preparation_prefix {codec : Codec Label} {label holds goal : Label} {call : CTLUntilNamedSeed.Call Context}
    (entry : Entry codec label holds goal call) (after : State Context) (allocator : Allocator) :
    (ScopedQuerySource.machine .relational call.program).run 7
      (placed allocator after.world call.state.scope call.state.parents entry.seedReturned
        call.context ((call.origins ++ [call.occurrence]) ++ [0]) call.pending) =
      ([], .exhausted (entry.loopCall after allocator).before) := by
  obtain ⟨principal, resolved, _⟩ := CTLUntilNamedSeed.returned_frame entry.evidence entry.atoms entry.rows entry.snapshot entry.decoded
  have declared : callable call.program "eu-loop" = true := by rw [entry.authored]; decide
  have strict : ∀ index, index < entry.operands.length → Eval.argumentIsRaw call.program "eu-loop" index = false := by
    intro index _
    rw [entry.authored]
    exact CTLUntilAuthoredProgram.strict "eu-loop" index (by simp)
  have prepared := ScopedAtomicCallOperands.preparation .relational call.program allocator after.world call.state.scope call.state.parents
    entry.loopCaller call.context ((call.origins ++ [call.occurrence]) ++ [0]) call.pending "eu-loop" entry.operands (.var entry.root)
    (by intro atom member; simp only [Entry.operands, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact .variable _
        · exact .variable _
        · exact .grounded _)
    (by decide) rfl rfl declared strict ⟨principal, resolve_sound resolved⟩
  have sourceHead : ScopedAtomicCallOperands.entry entry.loopCaller "eu-loop" entry.operands (.var entry.root) = entry.seedReturned := by
    simp only [Entry.loopCaller, Entry.seedReturned, ScopedAtomicCallOperands.entry, Entry.operands,
      CTLUntilNamedSeed.Call.seedReturned, GuardedCountReturn.counted, GuardedCountReturn.ready, GuardedCountReturn.waiting,
      CTLUntilNamedSeed.Call.seedInput, CTLUntilNamedSeed.Call.producerCaller, ScopedLetSource.producerCaller,
      CTLUntilNamedSeed.Call.bodyCaller, CTLUntilNamedSeed.loop, entry.output]
  rw [sourceHead] at prepared
  simpa only [Entry.operands, List.length_cons, List.length_nil, Entry.loopCall, CTLUntilNamedLoop.Call.before, Entry.ready] using prepared

theorem loop_evidence {codec : Codec Label} {label holds goal : Label} {call : CTLUntilNamedSeed.Call Context}
    (entry : Entry codec label holds goal call) (after : State Context) (allocator : Allocator) :
    Nonempty (CTLUntilNamedLoop.Evidence codec label holds 0 (entry.loopCall after allocator)) := by
  obtain ⟨principal, resolved, readings, rootFresh⟩ := prepared_frame entry
  refine ⟨{atCall := rfl, principal, resolved, readings, rootFresh, row := ?_, otherHeads := ?_}⟩
  · change call.program.equations[3]? = _
    rw [entry.authored, CTLUntilNamedLoop.declaration_exact]
    rfl
  · intro index equation found different
    have foundAuthored : ScopedQuerySource.CTLUntilDriverControls.program.equations[index]? = some equation := by
      simpa only [Entry.loopCall, entry.authored] using found
    exact CTLUntilAuthoredProgram.ordinary_equation_unique index equation foundAuthored 3
      ScopedQuerySource.CTLUntilDriverControls.loopEquation rfl different

structure Completed {codec : Codec Label} {label holds goal : Label} {call : CTLUntilNamedSeed.Call Context}
    (entry : Entry codec label holds goal call) where
  budget : Nat
  after : State Context
  control : Control
  origins : List Nat
  result : CTLUntilCandidateBag.State Nat
  counter : Nat
  scope : after.scope = call.state.scope
  parents : after.parents = call.state.parents
  capacity : after.allocator.usableCount ≤ call.state.allocator.usableCount
  goals : control.goals = call.older
  cut : control.cutBoundary = call.control.cutBoundary
  destination : control.destination = call.control.destination
  principal : Environment
  resolved : resolve control.bindings = some principal
  value : read principal (.var entry.root) = number counter
  stored : CTLUntilLoopStore.Stored codec label holds entry.edges entry.holding counter result after.world.state
  positive : 0 < counter
  bound : counter ≤ (entry.holding.toFinset \ entry.goals.toFinset).card + 1
  quiet : result.delta = []
  meaning : ∀ vertex, vertex ∈ result.known ↔ Mettapedia.Logic.CTLFixedPoints.Until
    (CTLUntilFrontier.Relation entry.edges.toFinset) ↑entry.holding.toFinset ↑entry.goals.toFinset vertex
  execution : (ScopedQuerySource.machine .relational call.program).run budget call.before =
    ([], .exhausted (placed after.allocator after.world after.scope after.parents control call.context origins call.pending))

theorem terminates {codec : Codec Label} {label holds goal : Label} {call : CTLUntilNamedSeed.Call Context}
    (entry : Entry codec label holds goal call) (reserve : entry.allowance ≤ call.state.allocator.usableCount) :
    Nonempty (Completed entry) := by
  have seedReserve : entry.goals.length ≤ call.state.allocator.usableCount := by
    have bound := Nat.le_add_right entry.goals.length (CTLUntilFiniteSupport.allowance entry.edges entry.holding ⟨entry.goals, entry.goals⟩)
    exact bound.trans reserve
  obtain ⟨seeded, allocator, reading, decoded, _outside, _cells, debit, seedRun⟩ := CTLUntilNamedSeed.seeded entry.evidence
    entry.atoms entry.rows entry.snapshot entry.decoded seedReserve
  have stored : CTLUntilLoopStore.Stored codec label holds entry.edges entry.holding 0 ⟨entry.goals, entry.goals⟩ seeded.world.state :=
    CTLUntilLoopStore.seeded_stored codec label holds entry.separate entry.edges entry.holding entry.goals entry.rows seeded.world.state
      (CTLUntilMixedStore.decode_rows_sound codec entry.atoms entry.rows entry.decoded).2 rfl rfl
      entry.emptyKnown entry.emptyFrontiers reading
  have remaining : CTLUntilFiniteSupport.allowance entry.edges entry.holding ⟨entry.goals, entry.goals⟩ ≤ allocator.usableCount := by
    change allocator.usableCount + entry.goals.length = call.state.allocator.usableCount at debit
    change entry.goals.length + CTLUntilFiniteSupport.allowance entry.edges entry.holding ⟨entry.goals, entry.goals⟩ ≤ _ at reserve
    omega
  obtain ⟨evidence⟩ := loop_evidence entry seeded allocator
  obtain ⟨result, counter, ⟨loopDone⟩, positive, bound, quiet, meaning⟩ :=
    CTLUntilSourceRecursion.terminates codec label holds entry.edges entry.holding entry.goals (entry.loopCall seeded allocator)
      evidence entry.authored stored remaining
  let returned : Control := {loopDone.control with goals := call.older, cutBoundary := call.control.cutBoundary}
  have restored := ScopedEquationReturn.restore_prefix .relational call.program loopDone.after.allocator loopDone.after.world
    loopDone.after.scope loopDone.after.parents loopDone.control call.context loopDone.origins call.pending
    call.control.cutBoundary call.older loopDone.goals
  have prepared := preparation_prefix entry seeded allocator
  change (ScopedQuerySource.machine .relational call.program).run (14 + 14 * entry.goals.length) call.before =
    ([], .exhausted (placed allocator seeded.world call.state.scope call.state.parents entry.seedReturned
      call.context ((call.origins ++ [call.occurrence]) ++ [0]) call.pending)) at seedRun
  have start := (ScopedQuerySource.machine .relational call.program).established_and_pending
    (14 + 14 * entry.goals.length) 7 _ _ [] seedRun
  rw [prepared] at start
  simp only [List.nil_append] at start
  have repeated := (ScopedQuerySource.machine .relational call.program).established_and_pending
    ((14 + 14 * entry.goals.length) + 7) loopDone.budget _ _ [] start
  have loopRun := loopDone.execution
  change (ScopedQuerySource.machine .relational call.program).run loopDone.budget (entry.loopCall seeded allocator).before =
    ([], .exhausted (placed loopDone.after.allocator loopDone.after.world loopDone.after.scope loopDone.after.parents
      loopDone.control call.context loopDone.origins call.pending)) at loopRun
  rw [loopRun] at repeated
  simp only [List.nil_append] at repeated
  have finished := (ScopedQuerySource.machine .relational call.program).established_and_pending
    (((14 + 14 * entry.goals.length) + 7) + loopDone.budget) 1 _ _ [] repeated
  rw [restored] at finished
  exact ⟨{
    budget := ((14 + 14 * entry.goals.length) + 7) + loopDone.budget + 1
    after := loopDone.after, control := returned, origins := loopDone.origins, result, counter
    scope := loopDone.scope, parents := loopDone.parents
    capacity := loopDone.capacity.trans (by change allocator.usableCount ≤ _; omega)
    goals := rfl, cut := rfl, destination := loopDone.destination
    principal := loopDone.principal, resolved := loopDone.resolved, value := loopDone.value
    stored := loopDone.stored, positive, bound, quiet, meaning
    execution := by simpa only [List.nil_append, returned, Entry.loopCall] using finished }⟩

theorem Completed.observed_until {codec : Codec Label} {label holds goal : Label} {call : CTLUntilNamedSeed.Call Context}
    {entry : Entry codec label holds goal call} (completed : Completed entry) :
    ∃ atoms rows, completed.after.world.state.read .self = some atoms ∧ decodeRows codec atoms = some rows ∧
      (∀ vertex, vertex ∈ satisfactionView label rows ↔ Mettapedia.Logic.CTLFixedPoints.Until
        (CTLUntilFrontier.Relation entry.edges.toFinset) ↑entry.holding.toFinset ↑entry.goals.toFinset vertex) ∧
      ∀ round, rows.filterMap (frontSelect label round) = [] := by
  obtain ⟨atoms, rows, snapshot, decoded, views⟩ := completed.stored
  refine ⟨atoms, rows, snapshot, decoded, ?_, ?_⟩
  · intro vertex
    rw [views.known]
    exact completed.meaning vertex
  · intro round
    by_cases same : round = completed.counter
    · rw [same, views.current, completed.quiet]
    · exact views.other round same

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceDriver

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceDriver.terminates
