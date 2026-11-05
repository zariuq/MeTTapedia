import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceIteration
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedEquationReturn

/-!
# Repeated authored EU source iterations

The induction consumes the concrete source-iteration theorem and the existing
independent candidate-bag run. Each recursive invocation retains the enclosing
predicate-return delimiter, which is restored by a real final source step.
Finite input support then discharges the mathematical completion premise.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceRecursion

open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open ClosedOnceQueryFrame (placed)
open FlatQueryRowCodec (Codec)
open CTLUntilSourceRows (number)
open CTLUntilLoopStore (Stored)
open Mettapedia.Machines
open CTLUntilCandidateBag (advance candidates)

variable {Context Label : Type} [DecidableEq Label]

structure Completed (codec : Codec Label) (label holds : Label) (edges : List (Nat × Nat))
    (holding : List Nat) (counter : Nat) (bag : CTLUntilCandidateBag.State Nat)
    (call : CTLUntilNamedLoop.Call Context) where
  budget : Nat
  after : NamedGuardedCandidateBatch.State Context
  control : Control
  origins : List Nat
  stored : Stored codec label holds edges holding counter bag after.world.state
  scope : after.scope = call.state.scope
  parents : after.parents = call.state.parents
  capacity : after.allocator.usableCount ≤ call.state.allocator.usableCount
  destination : control.destination = call.control.destination
  goals : control.goals = call.older
  cut : control.cutBoundary = call.control.cutBoundary
  principal : Environment
  resolved : resolve control.bindings = some principal
  value : read principal (.var call.root) = number counter
  execution : (ScopedQuerySource.machine .relational call.program).run budget call.before =
    ([], .exhausted (placed after.allocator after.world after.scope after.parents control
      call.context origins call.pending))

/-- Actual source completion for the independent ordered model's finite run.
The source step is a proved concrete theorem, not a correctness-law parameter. -/
theorem of_run (codec : Codec Label) (label holds : Label) (edges : List (Nat × Nat))
    (holding : List Nat) (fuel round : Nat) (bag result : CTLUntilCandidateBag.State Nat) (answer : Nat)
    (call : CTLUntilNamedLoop.Call Context)
    (evidence : CTLUntilNamedLoop.Evidence codec label holds round call)
    (authored : call.program = ScopedQuerySource.CTLUntilDriverControls.program)
    (stored : Stored codec label holds edges holding round bag call.state.world.state)
    (reserve : CTLUntilFiniteSupport.allowance edges holding bag ≤ call.state.allocator.usableCount)
    (computed : CTLUntilCandidateBag.run edges holding fuel round bag = some (result, answer)) :
    Nonempty (Completed codec label holds edges holding answer result call) := by
  induction fuel generalizing round bag result answer call with
  | zero => cases computed
  | succ fuel ih =>
      obtain ⟨receipt⟩ := CTLUntilSourceIteration.step evidence authored edges holding bag stored reserve
      rcases receipt.boundary with quiet | productive
      · obtain ⟨quiet, atReturn, principal, resolved, value⟩ := quiet
        rw [CTLUntilCandidateBag.run, if_pos quiet] at computed
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj computed)
        let returned : Control := {receipt.control with
          goals := call.older
          cutBoundary := call.control.cutBoundary}
        have last := ScopedEquationReturn.restore_prefix .relational call.program receipt.after.allocator receipt.after.world
          receipt.after.scope receipt.after.parents receipt.control call.context receipt.origins call.pending
          call.control.cutBoundary call.older atReturn
        have joined := (ScopedQuerySource.machine .relational call.program).established_and_pending
          receipt.budget 1 _ _ [] receipt.execution
        rw [last] at joined
        refine ⟨{
          budget := receipt.budget + 1
          after := receipt.after
          control := returned
          origins := receipt.origins
          stored := receipt.stored
          scope := receipt.scope
          parents := receipt.parents
          capacity := by have debit := receipt.debit; omega
          destination := receipt.destination
          goals := rfl
          cut := rfl
          principal
          resolved
          value
          execution := by simpa only [List.nil_append, returned] using joined}⟩
      · obtain ⟨nonquiet, arguments, principal, atCall, resolved, readings, rootFresh⟩ := productive
        rw [CTLUntilCandidateBag.run, if_neg nonquiet] at computed
        let nextCall : CTLUntilNamedLoop.Call Context := {
          program := call.program
          state := receipt.after
          control := receipt.control
          context := call.context
          origins := receipt.origins
          pending := call.pending
          arguments
          root := call.root
          older := .restoreCommit call.control.cutBoundary :: call.older
          occurrence := 3 }
        have row : nextCall.program.equations[3]? = some CTLUntilNamedLoop.definition.declaration := by
          rw [CTLUntilNamedLoop.declaration_exact]
          change call.program.equations[3]? = _
          rw [authored]
          rfl
        let nextEvidence : CTLUntilNamedLoop.Evidence codec label holds (round + 1) nextCall := {
          atCall, principal, resolved, readings, rootFresh, row
          otherHeads := by
            intro index equation found different
            have foundAuthored : ScopedQuerySource.CTLUntilDriverControls.program.equations[index]? = some equation := by
              simpa only [nextCall, authored] using found
            exact CTLUntilAuthoredProgram.ordinary_equation_unique index equation foundAuthored 3
              ScopedQuerySource.CTLUntilDriverControls.loopEquation rfl different }
        have nextReserve : CTLUntilFiniteSupport.allowance edges holding (advance edges holding bag) ≤
            nextCall.state.allocator.usableCount := by
          have balance := CTLUntilFiniteSupport.allowance_advance edges holding bag
          have debit := receipt.debit
          change CTLUntilFiniteSupport.allowance edges holding (advance edges holding bag) ≤ receipt.after.allocator.usableCount
          omega
        obtain ⟨later⟩ := ih (round := round + 1) (bag := advance edges holding bag) (result := result)
          (answer := answer) (call := nextCall) nextEvidence authored receipt.stored nextReserve computed
        have laterRun := later.execution
        change (ScopedQuerySource.machine .relational call.program).run later.budget
          (placed receipt.after.allocator receipt.after.world receipt.after.scope receipt.after.parents receipt.control
            call.context receipt.origins call.pending) =
          ([], .exhausted (placed later.after.allocator later.after.world later.after.scope later.after.parents later.control
            call.context later.origins call.pending)) at laterRun
        have first := (ScopedQuerySource.machine .relational call.program).established_and_pending
          receipt.budget later.budget _ _ [] receipt.execution
        rw [laterRun] at first
        simp only [List.nil_append] at first
        have atReturn : later.control.goals = .restoreCommit call.control.cutBoundary :: call.older := later.goals
        let returned : Control := {later.control with
          goals := call.older
          cutBoundary := call.control.cutBoundary}
        have last := ScopedEquationReturn.restore_prefix .relational call.program later.after.allocator later.after.world
          later.after.scope later.after.parents later.control call.context later.origins call.pending
          call.control.cutBoundary call.older atReturn
        have joined := (ScopedQuerySource.machine .relational call.program).established_and_pending
          (receipt.budget + later.budget) 1 _ _ [] first
        rw [last] at joined
        refine ⟨{
          budget := receipt.budget + later.budget + 1
          after := later.after
          control := returned
          origins := later.origins
          stored := later.stored
          scope := later.scope.trans receipt.scope
          parents := later.parents.trans receipt.parents
          capacity := le_trans later.capacity (by
            change receipt.after.allocator.usableCount ≤ call.state.allocator.usableCount
            have debit := receipt.debit
            omega)
          destination := later.destination.trans receipt.destination
          goals := rfl
          cut := rfl
          principal := later.principal
          resolved := later.resolved
          value := later.value
          execution := by simpa only [List.nil_append, nextCall, returned] using joined}⟩

/-- Finite source data and an initial identity reserve suffice. Both the
ordered mathematical run and its actual source execution are constructed. -/
theorem terminates (codec : Codec Label) (label holds : Label) (edges : List (Nat × Nat))
    (holding goals : List Nat) (call : CTLUntilNamedLoop.Call Context)
    (evidence : CTLUntilNamedLoop.Evidence codec label holds 0 call)
    (authored : call.program = ScopedQuerySource.CTLUntilDriverControls.program)
    (stored : Stored codec label holds edges holding 0 ⟨goals, goals⟩ call.state.world.state)
    (reserve : CTLUntilFiniteSupport.allowance edges holding ⟨goals, goals⟩ ≤ call.state.allocator.usableCount) :
    ∃ result counter, Nonempty (Completed codec label holds edges holding counter result call) ∧
      0 < counter ∧ counter ≤ (holding.toFinset \ goals.toFinset).card + 1 ∧ result.delta = [] ∧
      ∀ vertex, vertex ∈ result.known ↔ Mettapedia.Logic.CTLFixedPoints.Until
        (CTLUntilFrontier.Relation edges.toFinset) ↑holding.toFinset ↑goals.toFinset vertex := by
  obtain ⟨result, counter, computed, positive, bound, quiet, meaning⟩ :=
    CTLUntilFiniteSupport.finite_completion edges holding goals
  exact ⟨result, counter, of_run codec label holds edges holding _ 0 ⟨goals, goals⟩ result counter call
    evidence authored stored reserve computed, positive, bound, quiet, meaning⟩

#print axioms of_run
#print axioms terminates

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceRecursion
