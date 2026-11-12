import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedBodyFrontier

/-!
# Selected held bodies restore the predicate delimiter before the result guard

The original matcher earns the selected constraints, and the literal-family
readout earns the mode. The existing scoped machine executes the quoted
body, its return equation and the actual saved-delimiter goal. Refusal keeps
older alternatives; acceptance derives a resolver and reaches the existing
typed guard. No body success or body-result service is assumed.

This realizes the selected scheduling component, not the native C driver or
its explicit execution escape.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedBodyExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open PettaOccurrenceOverlay
open Bridges.ClosedOnceQueryFrame (placed)

theorem quoted_prefix {User : Type} (services : Services User) (policy : Policy)
    (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : Scope User) (parents : List (Scope User)) (caller : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (body : Atom) (older : List EagerDFS.Destination.Goal)
    (bindings : Equations) (calls : context.calls = frame :: outside) (phase : frame.phase = .body)
    (depth : frame.scopeDepth = (scope :: parents).length)
    (accepted : refine caller.bindings body frame.callDestination = some bindings) :
    (PettaOccurrenceOverlay.machine services policy program).run 2
      (placed allocator world scope parents
        {caller with goals := .evaluate (OutputPlan.hold body) frame.callDestination :: older, destination := frame.callDestination} context origins pending) =
      ([], .exhausted (placed allocator world scope parents
        {caller with bindings, goals := older, destination := frame.callDestination} context origins pending)) := by
  simp [Machine.run, PettaOccurrenceOverlay.machine, PettaOccurrenceOverlay.step,
    delegate, sourceOwned, EagerDFS.eagerControlForm, calls, phase, depth, liftSource,
    Bridges.ScopedQuerySource.ownedStep, Bridges.ScopedQuerySource.ownershipStep,
    Bridges.ScopedCaseSource.entryStep, Bridges.ScopedCaseSource.readyStep,
    Bridges.ScopedQuerySource.step, Bridges.ScopedQuerySource.syntaxStep,
    Bridges.ScopedQuerySource.constrainedCall, Bridges.ScopedQuerySource.mutationCall,
    Bridges.ScopedQuerySource.queryStep, placed, scopeStep, enterCollapse?, enterSuperpose?,
    EagerDFS.Destination.machine, prepare, replace, installChild, retainChild, accepted,
    OutputPlan.hold, OutputPlan.call]

theorem quoted_prefix_refused {User : Type} (services : Services User) (policy : Policy)
    (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : Scope User) (parents : List (Scope User)) (caller : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (body : Atom) (older : List EagerDFS.Destination.Goal)
    (calls : context.calls = frame :: outside) (phase : frame.phase = .body)
    (depth : frame.scopeDepth = (scope :: parents).length)
    (refused : refine caller.bindings body frame.callDestination = none) :
    (PettaOccurrenceOverlay.machine services policy program).run 2
      (placed allocator world scope parents
        {caller with goals := .evaluate (OutputPlan.hold body) frame.callDestination :: older, destination := frame.callDestination} context origins pending) =
      ([], .exhausted (allocator, ⟨world, {scope with frontier := pending} :: parents⟩)) := by
  simp [Machine.run, PettaOccurrenceOverlay.machine, PettaOccurrenceOverlay.step,
    delegate, sourceOwned, EagerDFS.eagerControlForm, calls, phase, depth, liftSource,
    Bridges.ScopedQuerySource.ownedStep, Bridges.ScopedQuerySource.ownershipStep,
    Bridges.ScopedCaseSource.entryStep, Bridges.ScopedCaseSource.readyStep,
    Bridges.ScopedQuerySource.step, Bridges.ScopedQuerySource.syntaxStep,
    Bridges.ScopedQuerySource.constrainedCall, Bridges.ScopedQuerySource.mutationCall,
    Bridges.ScopedQuerySource.queryStep, placed, scopeStep, enterCollapse?, enterSuperpose?,
    EagerDFS.Destination.machine, prepare, replace, installChild, retainChild, refused,
    OutputPlan.hold, OutputPlan.call]

theorem restore_delimiter {User : Type} (services : Services User) (policy : Policy)
    (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : Scope User) (parents : List (Scope User)) (caller : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (saved : Nat) (older : List EagerDFS.Destination.Goal)
    (calls : context.calls = frame :: outside) (phase : frame.phase = .body)
    (depth : frame.scopeDepth = (scope :: parents).length) :
    PettaOccurrenceOverlay.step services policy program
      (placed allocator world scope parents {caller with goals := .restoreCommit saved :: older}
        context origins pending) =
      .silent (placed allocator world scope parents {caller with goals := older, cutBoundary := saved}
        context origins pending) := by
  simp [PettaOccurrenceOverlay.step, delegate, calls, phase, depth, liftSource,
    Bridges.ScopedQuerySource.ownedStep, Bridges.ScopedQuerySource.ownershipStep,
    Bridges.ScopedCaseSource.entryStep, Bridges.ScopedCaseSource.readyStep,
    Bridges.ScopedQuerySource.step, Bridges.ScopedQuerySource.syntaxStep,
    Bridges.ScopedQuerySource.constrainedCall, Bridges.ScopedQuerySource.mutationCall,
    Bridges.ScopedQuerySource.queryStep, placed, scopeStep, enterCollapse?, enterSuperpose?,
    EagerDFS.Destination.machine, prepare, replace, installChild, retainChild]

theorem held_predicate_outcome {User : Type} (services : Services User) (policy : Policy)
    (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : Scope User) (parents : List (Scope User)) (caller : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (body : Atom) (retained : Nat)
    (calls : context.calls = frame :: outside) (phase : frame.phase = .body)
    (depth : frame.scopeDepth = (scope :: parents).length) :
    let initial := placed allocator world scope parents
      (predicateEntry retained {caller with goals := [.evaluate (OutputPlan.hold body) frame.callDestination], destination := frame.callDestination}) context origins pending
    match refine caller.bindings body frame.callDestination with
    | none => (PettaOccurrenceOverlay.machine services policy program).run 2 initial =
        ([], .exhausted (allocator, ⟨world, {scope with frontier := pending} :: parents⟩))
    | some bindings => ∃ environment, resolve bindings = some environment ∧
        let reachedControl := {caller with bindings, goals := [], destination := frame.callDestination}
        let reached := placed allocator world scope parents reachedControl context origins pending
        (PettaOccurrenceOverlay.machine services policy program).run 3 initial = ([], .exhausted reached) ∧
          PettaOccurrenceOverlay.step services policy program reached =
            consumeBody services reached {scope with frontier := (reachedControl, context, origins) :: pending}
              parents reachedControl context origins pending frame outside (read environment body) := by
  dsimp only
  cases refined : refine caller.bindings body frame.callDestination with
  | none =>
    simpa only [predicateEntry] using quoted_prefix_refused services policy program allocator world scope parents
      {caller with cutBoundary := retained} context origins pending frame outside body
      [.restoreCommit caller.cutBoundary] calls phase depth refined
  | some bindings =>
    have consistent : ∃ environment, EagerDFS.Destination.Solves environment bindings := by
      obtain ⟨rfl, environment, old, related⟩ := (refine_iff _ _ _ _).mp refined
      exact ⟨environment, (solves_append_equation _ _ _ _).mpr ⟨old, related⟩⟩
    obtain ⟨environment, resolved⟩ := resolve_complete consistent
    refine ⟨environment, resolved, ?_, ?_⟩
    · have prefixRun := quoted_prefix services policy program allocator world scope parents
        {caller with cutBoundary := retained} context origins pending frame outside body
        [.restoreCommit caller.cutBoundary] bindings calls phase depth refined
      rw [show 3 = 2 + 1 by rfl, Machine.run_add]
      simp only [predicateEntry] at prefixRun ⊢
      rw [prefixRun]
      simp only [Machine.continueRun, List.nil_append]
      apply Machine.run_succ_silent
      exact congrArg some (restore_delimiter services policy program allocator world scope parents
        {caller with bindings, destination := frame.callDestination, cutBoundary := retained}
        context origins pending frame outside caller.cutBoundary [] calls phase depth)
    · have actual := PettaHeldBodyReturn.held_body_then_guard services policy program allocator world scope parents
        caller context origins pending frame outside body bindings environment calls phase depth refined resolved
      exact actual.2

/-- Actual frontier membership earns the equation, its complete source
arity, matching constraints and held-body execution. The only result cases
are those of the real return unifier; successful resolution is derived. -/
theorem selected_held_outcome {User : Type} (services : Services User) (policy : Policy)
    (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : Scope User) (parents : List (Scope User)) (caller next : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (head : String) (arguments : List Atom)
    (occurrence retained : Nat)
    (selected : (occurrence, next) ∈ PettaSelectedBodyFrontier.frontier program caller head arguments
      frame.callDestination [])
    (held : SelectedBodyPolicy.descriptorHolding .complete arguments.length
      ((PettaSelectedBodyDeclarations.family program head).map CallGuardOptimization.compile) = true)
    (destination : caller.destination = frame.callDestination)
    (calls : context.calls = frame :: outside) (phase : frame.phase = .body)
    (depth : frame.scopeDepth = (scope :: parents).length) :
    ∃ equation, program.equations[occurrence]? = some equation ∧ equation.head = head ∧
      equation.arguments.length = arguments.length ∧
      let body := ClauseChoice.freshBody caller occurrence equation
      let initial := placed allocator world scope parents (predicateEntry retained next) context origins pending
      match refine next.bindings body frame.callDestination with
      | none => (PettaOccurrenceOverlay.machine services policy program).run 2 initial =
          ([], .exhausted (allocator, ⟨world, {scope with frontier := pending} :: parents⟩))
      | some bindings => ∃ environment, resolve bindings = some environment ∧
          let reachedControl := {next with bindings, goals := []}
          let reached := placed allocator world scope parents reachedControl context origins pending
          (PettaOccurrenceOverlay.machine services policy program).run 3 initial = ([], .exhausted reached) ∧
            PettaOccurrenceOverlay.step services policy program reached =
              consumeBody services reached {scope with frontier := (reachedControl, context, origins) :: pending}
                parents reachedControl context origins pending frame outside (read environment body) := by
  have raw : OutputPlan.rawOutput program head arguments.length = true := by
    simpa only [PettaSelectedBodyDeclarations.frozen_descriptors_eq_compiler_mode] using held
  have entry := (PettaSelectedBodyFrontier.member_iff ..).mp selected
  cases entry with
  | held equation matching row sameHead matched literal =>
    refine ⟨equation, row, sameHead, PettaSelectedBodyFrontier.matched_arity caller head arguments occurrence equation
      matching matched, ?_⟩
    have executed := held_predicate_outcome services policy program allocator world scope parents
      {caller with bindings := matching} context origins pending frame outside
      (ClauseChoice.freshBody caller occurrence equation) retained calls phase depth
    simpa only [predicateEntry, destination] using executed
  | evaluated equation matching row sameHead matched notLiteral =>
    exact False.elim (notLiteral ((PettaSelectedBodyDeclarations.rawOutput_iff ..).mp raw))

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedBodyExecution
