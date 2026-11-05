import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopRound
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopDrop
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopStore
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilAuthoredProgram
import Mettapedia.Machines.CTLUntilFiniteSupport

/-! Source receipts at one authored EU iteration boundary. The caller's
predicate-return delimiter is retained until the enclosing call returns. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceIteration

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor placed)
open FlatQueryRowCodec (Codec)
open NamedGuardedCandidateBatch (State)
open CTLUntilSourceRows (number)
open CTLUntilLoopStore (Stored RoundStored)

open Mettapedia.Machines
open CTLUntilCandidateBag (advance candidates)

variable {Context Label : Type} [DecidableEq Label]

structure Receipt (codec : Codec Label) (label holds : Label) (edges : List (Nat × Nat))
    (holding : List Nat) (round : Nat) (bag : CTLUntilCandidateBag.State Nat) (call : CTLUntilNamedLoop.Call Context) where
  budget : Nat
  after : State Context
  control : Control
  origins : List Nat
  stored : Stored codec label holds edges holding (round + 1) (advance edges holding bag) after.world.state
  scope : after.scope = call.state.scope
  parents : after.parents = call.state.parents
  debit : after.allocator.usableCount + (candidates edges holding bag.delta).length + bag.delta.length =
    call.state.allocator.usableCount
  destination : control.destination = call.control.destination
  cut : control.cutBoundary = call.pending.length
  boundary :
    ((advance edges holding bag).delta = [] ∧
      control.goals = .restoreCommit call.control.cutBoundary :: call.older ∧
      ∃ principal, resolve control.bindings = some principal ∧
        read principal (.var call.root) = number (round + 1)) ∨
    ((advance edges holding bag).delta ≠ [] ∧
      ∃ arguments principal,
        control.goals = .invoke "eu-loop" arguments (.var call.root) ::
          .restoreCommit call.control.cutBoundary :: call.older ∧
        resolve control.bindings = some principal ∧
        arguments.map (read principal) = CTLUntilNamedLoop.values codec label holds (round + 1) ∧
        FreshFor call.root control.bindings)
  execution : (ScopedQuerySource.machine .relational call.program).run budget call.before =
    ([], .exhausted (placed after.allocator after.world after.scope after.parents control
      call.context origins call.pending))

def roundProfile (codec : Codec Label) (label : Label) :
    CTLUntilLoopRound.Profile codec label ScopedQuerySource.CTLUntilDriverControls.program where
  query := CTLUntilAuthoredProgram.query
  distinct := CTLUntilAuthoredProgram.query_distinct
  occurrence := 1
  row := by rw [CTLUntilAuthoredProgram.round_declaration]; rfl
  otherHeads := by
    intro index equation row different
    exact CTLUntilAuthoredProgram.ordinary_equation_unique index equation row 1
      ScopedQuerySource.CTLUntilControls.roundEquation rfl different
  guard := CTLUntilAuthoredProgram.guardProfile codec label
  allSelf := by
    intro handle member
    simpa [CTLUntilAuthoredProgram.query, CTLUntilScopedRound.Query.handles] using member
  strict := fun index _ => CTLUntilAuthoredProgram.strict "eu-round" index (by simp)

set_option maxHeartbeats 1200000 in
theorem step {codec : Codec Label} {label holds : Label} {round : Nat} {call : CTLUntilNamedLoop.Call Context}
    (evidence : CTLUntilNamedLoop.Evidence codec label holds round call)
    (authored : call.program = ScopedQuerySource.CTLUntilDriverControls.program)
    (edges : List (Nat × Nat)) (holding : List Nat) (bag : CTLUntilCandidateBag.State Nat)
    (stored : Stored codec label holds edges holding round bag call.state.world.state)
    (reserve : CTLUntilFiniteSupport.allowance edges holding bag ≤ call.state.allocator.usableCount) :
    Nonempty (Receipt codec label holds edges holding round bag call) := by
  let profile : CTLUntilLoopRound.Profile codec label call.program :=
    authored.symm ▸ roundProfile codec label
  have remainingCost := CTLUntilFiniteSupport.allowance_advance edges holding bag
  have candidateReserve : (candidates edges holding bag.delta).length ≤ call.state.allocator.usableCount := by omega
  obtain ⟨frame⟩ := CTLUntilNamedLoop.body_frame evidence
  obtain ⟨roundBudget, roundState, roundControl, ⟨roundFrame⟩, roundStored, roundScope, roundParents,
    roundGoals, roundDestination, roundCut, roundDebit, roundRun⟩ :=
    CTLUntilLoopRound.from_body profile call.state (call.bodyCaller (CTLUntilNamedLoop.values codec label holds round))
      (call.names evidence.root_retained) call.context (call.origins ++ [call.occurrence]) call.pending
      frame edges holding bag stored candidateReserve
      (by intro index _; rw [authored]; exact CTLUntilAuthoredProgram.strict "+" index (by simp))
  have entered := CTLUntilNamedLoop.enter_prefix evidence
  have roundPrefix := (ScopedQuerySource.machine .relational call.program).established_and_pending 1 roundBudget _ _ [] entered
  rw [roundRun] at roundPrefix
  simp only [List.nil_append] at roundPrefix
  let roundOrigins := (call.origins ++ [call.occurrence]) ++ [0, profile.occurrence, 0]
  let drop : CTLUntilLoopDrop.Input Context := {
    program := call.program
    state := roundState
    control := roundControl
    names := call.names evidence.root_retained
    older := (call.bodyCaller (CTLUntilNamedLoop.values codec label holds round)).goals
    context := call.context
    origins := roundOrigins
    pending := call.pending
    occurrence := 2 }
  obtain ⟨atoms, rows, snapshot, decoded, views⟩ := roundStored
  let entry : CTLUntilLoopDrop.Entry codec label holds round (advance edges holding bag).delta.length drop := {
    atGoal := roundGoals
    frame := roundFrame
    row := by change call.program.equations[2]? = _; rw [authored]; rfl
    otherHeads := by
      intro index equation row different
      rw [show drop.program = call.program from rfl, authored] at row
      exact CTLUntilAuthoredProgram.ordinary_equation_unique index equation row 2
        ScopedQuerySource.CTLUntilDriverControls.dropEquation rfl different
    strict := by
      intro index _
      change Eval.argumentIsRaw call.program "drop" index = false
      rw [authored]
      exact CTLUntilAuthoredProgram.strict "drop" index (by simp)
    atoms := atoms
    rows := rows
    snapshot := snapshot
    decoded := decoded }
  have removed : entry.removed = bag.delta.length := CTLUntilLoopStore.cleanup_count views
  have dropReserve : entry.removed ≤ drop.state.allocator.usableCount := by
    change entry.removed ≤ roundState.allocator.usableCount
    rw [removed]
    omega
  obtain ⟨receipt⟩ := CTLUntilLoopDrop.executes entry dropReserve
  let after : State Context := {roundState with allocator := receipt.allocator, world := receipt.after.world}
  have afterStored : Stored codec label holds edges holding (round + 1) (advance edges holding bag) after.world.state :=
    CTLUntilLoopStore.cleanup_stored codec label holds edges holding round bag rows after.world.state views receipt.reading
  have debit : after.allocator.usableCount + (candidates edges holding bag.delta).length + bag.delta.length =
      call.state.allocator.usableCount := by
    have cleanupDebit := receipt.debit
    change receipt.allocator.usableCount + entry.removed = roundState.allocator.usableCount at cleanupDebit
    rw [removed] at cleanupDebit
    change receipt.allocator.usableCount + _ + _ = _
    omega
  change (ScopedQuerySource.machine .relational call.program).run (1 + roundBudget) call.before =
    ([], .exhausted drop.before) at roundPrefix
  have throughDrop := (ScopedQuerySource.machine .relational call.program).established_and_pending
    (1 + roundBudget) receipt.budget _ _ [] roundPrefix
  have dropRun := receipt.exact
  change (ScopedQuerySource.machine .relational call.program).run receipt.budget drop.before = _ at dropRun
  rw [dropRun] at throughDrop
  simp only [List.nil_append] at throughDrop
  rw [CTLUntilLoopDrop.returned_branch] at throughDrop
  let caller := drop.branchCaller codec label round entry.removed
  let names := CTLUntilLoopFrames.branchNames drop.names
  have equalityStrict : ∀ index, index < 2 → Eval.argumentIsRaw call.program "==" index = false := by
    intro index _
    rw [authored]
    exact CTLUntilAuthoredProgram.strict "==" index (by simp)
  by_cases quiet : (advance edges holding bag).delta = []
  · have quietFrame : CTLUntilLoopBranch.Frame codec label holds (round + 1) 0 names caller := by
      simpa only [quiet, List.length_nil] using receipt.frame
    obtain ⟨principal, resolved, reading, branchRun⟩ := CTLUntilLoopBranch.quiet_prefix codec label holds (round + 1)
      names call.program after.allocator after.world after.scope after.parents caller call.context drop.returnOrigins
      call.pending quietFrame equalityStrict
    have joined := (ScopedQuerySource.machine .relational call.program).established_and_pending
      (1 + roundBudget + receipt.budget) 11 _ _ [] throughDrop
    change (ScopedQuerySource.machine .relational call.program).run 11 _ = _ at branchRun
    rw [branchRun] at joined
    refine ⟨{
      budget := 1 + roundBudget + receipt.budget + 11
      after := after
      control := CTLUntilLoopBranch.quietReturned caller names
      origins := drop.returnOrigins ++ [0]
      stored := afterStored
      scope := roundScope
      parents := roundParents
      debit := debit
      destination := ?_
      cut := ?_
      boundary := Or.inl ⟨quiet, rfl, principal, resolved, reading⟩
      execution := ?_ }⟩
    · exact roundDestination
    · exact roundCut
    · simpa only [List.nil_append] using joined
  · have positive : (advance edges holding bag).delta.length ≠ 0 := by
      intro zero
      exact quiet (List.eq_nil_of_length_eq_zero zero)
    have declared : callable call.program "eu-loop" = true := by
      rw [authored]
      rfl
    have recursiveStrict : ∀ index, index < 3 → Eval.argumentIsRaw call.program "eu-loop" index = false := by
      intro index _
      rw [authored]
      exact CTLUntilAuthoredProgram.strict "eu-loop" index (by simp)
    obtain ⟨principal, resolved, readings, fresh, _unbound, branchRun⟩ :=
      CTLUntilLoopBranch.recursive_prefix codec label holds (round + 1) (advance edges holding bag).delta.length
        names call.program after.allocator after.world after.scope after.parents caller call.context drop.returnOrigins
        call.pending receipt.frame positive equalityStrict declared recursiveStrict
    have joined := (ScopedQuerySource.machine .relational call.program).established_and_pending
      (1 + roundBudget + receipt.budget) 16 _ _ [] throughDrop
    rw [branchRun] at joined
    refine ⟨{
      budget := 1 + roundBudget + receipt.budget + 16
      after := after
      control := CTLUntilLoopBranch.recursiveReady caller names (advance edges holding bag).delta.length
      origins := drop.returnOrigins ++ [0]
      stored := afterStored
      scope := roundScope
      parents := roundParents
      debit := debit
      destination := ?_
      cut := ?_
      boundary := Or.inr ⟨quiet, CTLUntilLoopBranch.recursiveArguments caller names (advance edges holding bag).delta.length,
        principal, rfl, resolved, readings, fresh⟩
      execution := ?_ }⟩
    · exact roundDestination
    · exact roundCut
    · simpa only [List.nil_append] using joined

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceIteration
