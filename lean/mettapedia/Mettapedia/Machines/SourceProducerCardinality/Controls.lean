import Mettapedia.Machines.SourceProducerCardinality

/-!
# Kernel-checked controls of the source producer cardinality development

Concrete runs, refusals and observations of the body/call worker, its admission, shared,
weighted, authored, handoff, publication and calling-mode layers. Each control is stated
in the namespace of the layer it exercises.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SourceProducerCardinality

open AnswerCardinality RecursiveFiniteProducer SourceProducerAdmission
universe u v
variable {Item : Type u} {Value : Type v}

namespace Controls

def disjoint : List (Equation Nat) :=
  [⟨⟨.empty, .any⟩, false, .singleton 7⟩,
   ⟨⟨.cons, .any⟩, false, .singleton 11⟩]

theorem bound_shapes_derive_direct :
    sourceGrade disjoint ([] : List Nat) 0 = .one ∧
      sourceGrade disjoint [3] 0 = .one := by decide

def duplicates : List (Equation Nat) :=
  [⟨⟨.any, .any⟩, false, .singleton 7⟩,
   ⟨⟨.any, .any⟩, false, .singleton 7⟩]

theorem equal_answers_require_a_producer :
    convention (sourceGrade duplicates ([] : List Nat) 0) = .nonemptyProducer ∧
      source (fun (item value : Nat) => item + value) (fun _ left right => left + right)
        duplicates ([] : List Nat) 0 = [[7], [7]] := by decide

def failingMatch : List (Equation Nat) := [⟨⟨.empty, .any⟩, false, .callTail⟩]

theorem matching_failure_is_not_an_empty_collection :
    sourceGrade failingMatch ([] : List Nat) 0 = .zero ∧
      sourceGrade ([⟨⟨.empty, .any⟩, false, .empty⟩] : List (Equation Nat))
        ([] : List Nat) 0 = .one := by decide

theorem a_failing_equation_does_not_commit :
    source (fun (item value : Nat) => item + value) (fun _ left right => left + right)
      [⟨⟨.empty, .any⟩, false, .callTail⟩, ⟨⟨.empty, .any⟩, false, .singleton 7⟩]
      ([] : List Nat) 0 = [[7]] ∧
      sourceGrade [⟨⟨.empty, .any⟩, false, .callTail⟩,
        ⟨⟨.empty, .any⟩, false, .singleton 7⟩] ([] : List Nat) 0 = .one := by decide

def recursive : List (Equation Nat) :=
  [⟨⟨.empty, .any⟩, false, .empty⟩,
   ⟨⟨.cons, .any⟩, false, .mapHead .callTail⟩]

theorem recursive_summary_comes_from_descent (items : List Nat) (parameter : Nat) :
    sourceGrade recursive items parameter = .one := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      change choice (sourceGrade recursive tail parameter) .zero = .one
      rw [ih]
      rfl

theorem unsupported_keeps_unknown :
    convention (sourceGrade ([⟨⟨.any, .any⟩, false, .unsupported⟩] : List (Equation Nat))
      ([] : List Nat) 0) = .producer ∧
    BodyCall.supportedProgram ([⟨⟨.any, .any⟩, false, .unsupported⟩] : List (Equation Nat)) = false ∧
    selectSourceWorker ([⟨⟨.any, .any⟩, false, .unsupported⟩] : List (Equation Nat)) .producer =
      .reference .producer := by
  exact ⟨by decide, rfl, rfl⟩

theorem unmatched_and_matching_failure_stay_distinct :
    observedGrade .retainFallback failingMatch ([] : List Nat) 0 = .zero ∧
      observedGrade .retainFallback failingMatch [3] 0 = .one ∧
      observedGrade .noAnswers failingMatch [3] 0 = .zero := by decide

theorem source_commit_is_not_a_determinism_claim :
    sourceGrade (duplicates.map fun equation => {equation with commit := true})
      ([] : List Nat) 0 = .one ∧
      sourceGrade duplicates ([] : List Nat) 0 = .nonempty := by decide

theorem overlapping_equal_equations_select_body_cursor :
    compile duplicates = none ∧
      (match selectWorker duplicates ([] : List Nat) 0 with
        | .bodyCall .nonemptyProducer => true
        | _ => false) = true := by decide

theorem recursive_worker_is_constructed :
    ∃ compiled, compile recursive = some compiled ∧
      ∀ (items : List Nat) parameter,
        selectWorker recursive items parameter = .directCode compiled := by
  refine ⟨?_, ?_, ?_⟩
  · exact (SourceProducerAdmission.DecisionTree.code
      ⟨.empty, .mapHead .callTail, .empty, .mapHead .callTail⟩)
  · rfl
  · intro items parameter
    rfl

def recursiveWorld : OrderedDependencyStore.Store (Equation Nat) 2 :=
  OrderedDependencyStore.initial 914 (fun _ => recursive)

theorem added_equation_refuses_old_direct_code :
    OrderedDependencyStore.checkRead
      (OrderedDependencyStore.appendOwn recursiveWorld 0 [⟨⟨.any, .any⟩, false, .singleton 7⟩])
      (OrderedDependencyStore.readStamp recursiveWorld 0) = false ∧
      (match checkedWorker recursiveWorld
          (OrderedDependencyStore.appendOwn recursiveWorld 0 [⟨⟨.any, .any⟩, false, .singleton 7⟩])
          0 ([] : List Nat) 0 with
        | .bodyCall .producer => true
        | _ => false) = true := by decide

theorem unrelated_equation_update_keeps_direct_code :
    OrderedDependencyStore.checkRead
      (OrderedDependencyStore.appendOwn recursiveWorld 1 [⟨⟨.any, .any⟩, false, .singleton 7⟩])
      (OrderedDependencyStore.readStamp recursiveWorld 0) = true ∧
      (match checkedWorker recursiveWorld
          (OrderedDependencyStore.appendOwn recursiveWorld 1 [⟨⟨.any, .any⟩, false, .singleton 7⟩])
          0 ([3] : List Nat) 0 with
        | .directCode _ => true
        | _ => false) = true := by decide

end Controls

namespace OptionalControls

def headProgram : List (Equation Nat) :=
  SourceProducerAdmission.OptionalControls.maybeHead

theorem ordinary_source_selects_optional :
    selectWorker headProgram ([] : List Nat) 0 =
      .optionalCode ⟨none, some (.mapHead (.singleton 7)),
        none, some (.mapHead (.singleton 7))⟩ := by rfl

theorem optional_source_keeps_values_and_absence :
    executeWorker Nat.add (fun _ left _ => left) headProgram [] 0
      (selectWorker headProgram ([] : List Nat) 0) = some [] ∧
    executeWorker Nat.add (fun _ left _ => left) headProgram [3] 0
      (selectWorker headProgram [3] 0) = some [[10]] := by decide

def recursiveOptional : List (Equation Nat) := [⟨⟨.cons, .any⟩, false,
  .append (.mapHead (.singleton 7)) .callTail⟩]

theorem recursive_empty_propagates :
    executeWorker Nat.add (fun _ left _ => left) recursiveOptional [3, 5] 0
      (selectWorker recursiveOptional [3, 5] 0) = some [] := by decide

def optionalWorld : OrderedDependencyStore.Store (Equation Nat) 2 :=
  OrderedDependencyStore.initial 915 (fun cell => if cell = 0 then headProgram else [])

theorem mutation_restores_every_equation_occurrence :
    let current := OrderedDependencyStore.appendOwn optionalWorld 0
      [⟨⟨.cons, .any⟩, false, .singleton 11⟩]
    executeWorker Nat.add (fun _ left _ => left)
      (OrderedDependencyStore.query current 0) [3] 0
      (checkedWorker optionalWorld current 0 [3] 0) = some [[10], [11]] := by
  dsimp only
  have refused : OrderedDependencyStore.checkRead
      (OrderedDependencyStore.appendOwn optionalWorld 0
        [⟨⟨.cons, .any⟩, false, .singleton 11⟩])
      (OrderedDependencyStore.readStamp optionalWorld 0) = false := by decide
  simp only [checkedWorker, refused, Bool.false_eq_true, ↓reduceIte]
  rw [source_worker_refines_source]
  decide

theorem value_only_interface_retains_the_source :
    selectWorker headProgram ([] : List Nat) 0 .singleValue = .bodyCall .optional ∧
    executeWorker Nat.add (fun _ left _ => left) headProgram [] 0
      (selectWorker headProgram ([] : List Nat) 0 .singleValue) = some [] ∧
    executeWorker Nat.add (fun _ left _ => left) headProgram [3] 0
      (selectWorker headProgram [3] 0 .singleValue) = some [[10]] := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [selected_worker_refines_source Nat.add (fun _ left _ => left)
      headProgram [] 0 .singleValue]
    decide
  · rw [selected_worker_refines_source Nat.add (fun _ left _ => left)
      headProgram [3] 0 .singleValue]
    decide

theorem interface_does_not_assert_success_or_commit :
    selectWorker Controls.duplicates ([] : List Nat) 0 .singleValue =
      .bodyCall .nonemptyProducer ∧
    executeWorker Nat.add (fun _ left _ => left) Controls.duplicates [] 0
      (selectWorker Controls.duplicates ([] : List Nat) 0 .singleValue) = some [[7], [7]] := by
  refine ⟨rfl, ?_⟩
  rw [selected_worker_refines_source Nat.add (fun _ left _ => left)
    Controls.duplicates [] 0 .singleValue]
  decide

end OptionalControls


namespace FrontierControls

def noneHere : List (Equation Nat) := []

def oneHere : List (Equation Nat) := [⟨⟨.empty, .any⟩, false, .singleton 7⟩]

def manyHere : List (Equation Nat) :=
  [⟨⟨.any, .any⟩, false, .singleton 7⟩, ⟨⟨.any, .any⟩, false, .singleton 7⟩]

def committed : List (Equation Nat) :=
  [⟨⟨.any, .any⟩, true, .singleton 7⟩, ⟨⟨.any, .any⟩, false, .singleton 9⟩]

def captured : List (Equation Nat) := [⟨⟨.cons, .any⟩, false, .mapHead (.singleton 7)⟩]

def failedMatch : List (Equation Nat) := [⟨⟨.empty, .any⟩, false, .callTail⟩]

def emptyCollection : List (Equation Nat) := [⟨⟨.empty, .any⟩, false, .empty⟩]

def tailOf (program : List (Equation Nat)) (items : List Nat) : Nat → List (List Nat) :=
  sourceTail Nat.add (fun _ left _ => left) program items

theorem zero_budget_is_pending_empty :
    let opened := openFrontier manyHere ([] : List Nat) 0 (.observe .noAnswers)
    driveFrontier Nat.add (fun _ left _ => left) (tailOf manyHere []) [] 0 opened = ([], opened) ∧
      opened.isPending = true ∧ opened.phase = .running := by
  exact ⟨rfl, rfl, rfl⟩

theorem finished_empty_is_not_pending :
    let opened := openFrontier noneHere ([] : List Nat) 0 (.observe .noAnswers)
    let result := driveFrontier Nat.add (fun _ left _ => left) (tailOf noneHere []) [] 1 opened
    result.1 = [] ∧ result.2.phase = .finished ∧ result.2.isPending = false ∧
      opened.isPending = false := by
  decide

theorem one_occurrence_then_finishes :
    let opened := openFrontier oneHere ([] : List Nat) 0 (.observe .noAnswers)
    let once := driveFrontier Nat.add (fun _ left _ => left) (tailOf oneHere []) [] 1 opened
    let done := driveFrontier Nat.add (fun _ left _ => left) (tailOf oneHere []) [] 2 opened
    once.1 = [[7]] ∧ once.2.phase = .running ∧ done.1 = [[7]] ∧ done.2.phase = .finished := by
  decide

theorem many_occurrences_are_not_termination :
    let opened := openFrontier manyHere ([] : List Nat) 0 (.observe .noAnswers)
    let yielded := driveFrontier Nat.add (fun _ left _ => left) (tailOf manyHere []) [] 2 opened
    let done := driveFrontier Nat.add (fun _ left _ => left) (tailOf manyHere []) [] 3 opened
    yielded.1 = [[7], [7]] ∧ yielded.2.phase = .running ∧ yielded.2.isPending = false ∧
      done.1 = [[7], [7]] ∧ done.2.phase = .finished := by
  decide

theorem split_loans_the_prefix_and_resume_keeps_the_rest :
    let opened := openFrontier manyHere ([] : List Nat) 0 (.observe .noAnswers)
    let first := driveFrontier Nat.add (fun _ left _ => left) (tailOf manyHere []) [] 1 opened
    let second := driveFrontier Nat.add (fun _ left _ => left) (tailOf manyHere []) [] 2 first.2
    first.1 = [[7]] ∧ second.1 = [[7]] ∧ first.1 ++ second.1 = [[7], [7]] ∧
      second.2.phase = .finished ∧ second.2.authored = manyHere := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem resume_of_finished_does_not_replay :
    let opened := openFrontier oneHere ([] : List Nat) 0 (.observe .noAnswers)
    let done := driveFrontier Nat.add (fun _ left _ => left) (tailOf oneHere []) [] 2 opened
    driveFrontier Nat.add (fun _ left _ => left) (tailOf oneHere []) [] 2 done.2 = ([], done.2) := by
  rfl

theorem commit_retains_the_later_equation_and_does_not_run_it :
    let opened := openFrontier committed ([] : List Nat) 0 (.observe .noAnswers)
    let done := driveFrontier Nat.add (fun _ left _ => left) (tailOf committed []) [] 2 opened
    done.1 = [[7]] ∧ done.2.phase = .finished ∧ done.2.authored = committed ∧
      done.2.sealed = true ∧ committed.drop 1 = [⟨⟨.any, .any⟩, false, .singleton 9⟩] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem captured_bindings_are_the_ones_retained :
    let three := openFrontier captured [3] 0 (.observe .noAnswers)
    let four := openFrontier captured [4] 0 (.observe .noAnswers)
    (driveFrontier Nat.add (fun _ left _ => left) (tailOf captured [3]) [] 1 three).1 = [[10]] ∧
      (driveFrontier Nat.add (fun _ left _ => left) (tailOf captured [4]) [] 1 four).1 = [[11]] ∧
      three.items = [3] ∧ four.items = [4] := by
  decide

theorem empty_collection_is_one_occurrence :
    let opened := openFrontier emptyCollection ([] : List Nat) 0 (.observe .noAnswers)
    (driveFrontier Nat.add (fun _ left _ => left) (tailOf emptyCollection []) [] 1 opened).1 =
      [[]] := by
  decide

theorem matching_failure_finishes_empty_without_fallback :
    let opened := openFrontier failedMatch ([] : List Nat) 0 (.observe .retainFallback)
    let done := driveFrontier Nat.add (fun _ left _ => left) (tailOf failedMatch []) [9] 2 opened
    done.1 = [] ∧ done.2.phase = .finished ∧ done.2.matched = true := by
  decide

theorem unmatched_decline_is_not_finished_empty :
    let opened := openFrontier noneHere ([] : List Nat) 0 .decline
    let stopped := driveFrontier Nat.add (fun _ left _ => left) (tailOf noneHere []) [9] 1 opened
    stopped.1 = [] ∧ stopped.2.phase = .declined ∧ stopped.2.phase ≠ .finished := by
  decide

theorem unmatched_fallback_is_one_occurrence :
    let opened := openFrontier noneHere ([] : List Nat) 0 (.observe .retainFallback)
    (driveFrontier Nat.add (fun _ left _ => left) (tailOf noneHere []) [9] 1 opened).1 = [[9]] ∧
      (driveFrontier Nat.add (fun _ left _ => left) (tailOf noneHere []) [9] 1
        (openFrontier noneHere [] 0 (.observe .noAnswers))).1 = [] := by
  decide

theorem producer_convention_uses_body_cursor :
    selectWorker manyHere ([] : List Nat) 0 = .bodyCall .nonemptyProducer ∧
      executeWorker Nat.add (fun _ left _ => left) manyHere [] 0
        (selectWorker manyHere ([] : List Nat) 0) =
        some (driveFrontier Nat.add (fun _ left _ => left) (tailOf manyHere []) []
          (manyHere.length + 1) (openFrontier manyHere [] 0 (.observe .noAnswers))).1 := by
  refine ⟨rfl, ?_⟩
  rw [selected_worker_refines_source]
  exact congrArg some (retained_frontier_eq_source Nat.add (fun _ left _ => left)
    [] manyHere [] 0).symm

end FrontierControls


namespace BodyCallOwned

open Cursor.Fold.OwnedSequence.CallbackBoundary
variable {Input Output Context : Type}
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)

namespace Controls

def warming (ready : Bool) (_ : Returned Nat.add (fun _ left _ => left) (fun _ _ => [])) :
    Bool × Bool := (ready, true)

abbrev actual (quantum : Nat) :=
  provider Nat.add (fun _ left _ => left) (fun _ _ => []) quantum warming

def initial : State Nat.add (fun _ left _ => left) (fun _ _ => []) (Context := Bool) :=
  openState Nat.add (fun _ left _ => left) (fun _ _ => []) BodyCallRun.paired [] 0 false

def refused := fromCallbacks (actual 64) (fun _ _ => 1) 1 none 0 initial
  (terminalAfter Nat.add (fun _ left _ => left) (fun _ _ => []))

/-- A paid pending projection can be retried with no source inspections. -/
def retried := resumeCall (actual 0) (fun _ _ => 1) 1 refused
  (terminalAfter Nat.add (fun _ left _ => left) (fun _ _ => []))

def continued := resumeCall (actual 64) (fun _ _ => 1) 1 retried
  (terminalAfter Nat.add (fun _ left _ => left) (fun _ _ => []))

theorem real_return_refusal_and_zero_quantum_retry :
    refused.2.1.pending.isSome = true ∧ refused.2.1.accepted = 0 ∧
      refused.2.2.context = ([], true) ∧
      retried.2.1.pending.isNone = true ∧ retried.2.1.accepted = 1 ∧
      retried.2.2.context = ([[1, 2]], true) ∧
      retried.2.2.computation.1 = refused.2.2.computation.1 := by decide

theorem zero_acceptance_allowance_is_inert :
    resumeCall (actual 0) (fun _ _ => 1) 0 refused
      (terminalAfter Nat.add (fun _ left _ => left) (fun _ _ => [])) = refused :=
  resumeCall_zero _ _ _ _

theorem accepted_yield_does_not_certify_exhaustion :
    retried.2.1.terminal.isNone = true ∧
      (BodyCallProtocol.stateView Nat.add (fun _ left _ => left) (fun _ _ => [])
        retried.2.2.computation.2).phase = .running ∧
      continued.2.1.terminal.map (fun returned => returned.2.2.val.phase) = some .finished ∧
      continued.2.2.context.1 = [[1, 2]] ∧ continued.2.1.accepted = 1 := by decide

def replayed := fromCallbacks (actual 64) (fun _ _ => 1) 1 none retried.2.1.accepted
  { retried.2.2 with computation := initial.computation }
  (terminalAfter Nat.add (fun _ left _ => left) (fun _ _ => []))

theorem restarting_the_source_replays_an_accepted_occurrence :
    replayed.2.2.context.1 = [[1, 2], [1, 2]] ∧
      continued.2.2.context.1 = [[1, 2]] ∧
      replayed.2.2.context.1 ≠ continued.2.2.context.1 := by decide

def atReading (authored : List (Equation Nat)) (reading : NoRuleReading) :
    State Nat.add (fun _ left _ => left) (fun _ _ => []) (Context := Bool) :=
  ⟨(0, .paused (BodyCallProtocol.packet Nat.add (fun _ left _ => left) (fun _ _ => [])
    (BodyCall.openState authored [] 0 reading))), ([], false)⟩

def declined := fromCallbacks (actual 64) (fun _ _ => 1) 1 none 0
  (atReading BodyCallRun.missedCons .decline)
  (terminalAfter Nat.add (fun _ left _ => left) (fun _ _ => []))

def handedOff := fromCallbacks (actual 64) (fun _ _ => 1) 1 none 0
  (atReading BodyCallRun.alienAppend (.observe .noAnswers))
  (terminalAfter Nat.add (fun _ left _ => left) (fun _ _ => []))

def finished := fromCallbacks (actual 64) (fun _ _ => 1) 1 none 0
  (atReading BodyCallRun.missedCons (.observe .noAnswers))
  (terminalAfter Nat.add (fun _ left _ => left) (fun _ _ => []))

theorem terminal_records_keep_distinct_producer_phases :
    declined.2.1.terminal.map (fun returned => returned.2.2.val.phase) = some .declined ∧
      handedOff.2.1.terminal.map (fun returned => returned.2.2.val.phase) = some .handoff ∧
      finished.2.1.terminal.map (fun returned => returned.2.2.val.phase) = some .finished ∧
      declined.2.1.accepted = 0 ∧ handedOff.2.1.accepted = 0 ∧ finished.2.1.accepted = 0 := by decide

def finalRefused := fromCallbacks (actual 64) (fun _ _ => 1) 1 none 0
  (atReading [] (.observe .retainFallback))
  (terminalAfter Nat.add (fun _ left _ => left) (fun _ _ => []))

def finalRetried := resumeCall (actual 0) (fun _ _ => 1) 1 finalRefused
  (terminalAfter Nat.add (fun _ left _ => left) (fun _ _ => []))

theorem final_return_keeps_its_loan_until_acceptance :
    finalRefused.2.1.pending.isSome = true ∧ finalRefused.2.1.terminal.isNone = true ∧
      finalRefused.2.1.accepted = 0 ∧
      (BodyCallProtocol.stateView Nat.add (fun _ left _ => left) (fun _ _ => [])
        finalRefused.2.2.computation.2).phase = .finished ∧
      finalRetried.2.1.terminal.map (fun returned => returned.2.2.val.phase) = some .finished ∧
      finalRetried.2.1.pending.isNone = true ∧ finalRetried.2.1.accepted = 1 ∧
      finalRetried.2.2.context.1 = [[]] ∧
      finalRetried.2.2.computation.1 = finalRefused.2.2.computation.1 := by decide

def recursiveCalls := fromCallbacks (actual 64) (fun _ _ => 1) 3 none 0
  (openState Nat.add (fun _ left _ => left) (fun _ _ => []) BodyCallRun.called [0] 0 true)
  (terminalAfter Nat.add (fun _ left _ => left) (fun _ _ => []))

theorem recursive_occurrences_are_accepted_in_source_order :
    recursiveCalls.2.2.context.1 = [[7, 1], [8, 1]] ∧ recursiveCalls.2.1.accepted = 2 ∧
      recursiveCalls.2.1.terminal.map (fun returned => returned.2.2.val.phase) = some .finished := by decide

#print axioms real_return_refusal_and_zero_quantum_retry
#print axioms zero_acceptance_allowance_is_inert
#print axioms accepted_yield_does_not_certify_exhaustion
#print axioms restarting_the_source_replays_an_accepted_occurrence
#print axioms terminal_records_keep_distinct_producer_phases
#print axioms final_return_keeps_its_loan_until_acceptance
#print axioms recursive_occurrences_are_accepted_in_source_order

end Controls

end BodyCallOwned


namespace BodyCallAdmission
namespace CurrentAuthority

open Cursor.Fold.OwnedSequence.CallbackBoundary
variable {Input Output Context : Type}
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)
open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.SeparationTransport
open _root_.CategoryTheory
open scoped Mettapedia.GSLT.SeparationAlgebra
variable {World : Type} [Category.{0} World] (authority : IndexedAuthority.{0, 0, 0} World)

namespace Controls

local instance : Fintype Access :=
  ⟨{.none, .read, .consume}, by intro access; cases access <;> simp⟩

local instance (held required : Access) : Decidable (FrameUpdate held required) :=
  inferInstanceAs (Decidable (∀ frame : Access, held ## frame → required ## frame))

local instance (held required : Access × Access) : Decidable (FrameUpdate held required) :=
  inferInstanceAs (Decidable (∀ frame : Access × Access,
    (held.1 ## frame.1 ∧ held.2 ## frame.2) → (required.1 ## frame.1 ∧ required.2 ## frame.2)))

def revocationDecision (world : Bool) (held required : revocationWorlds.Fibre world) :
    Decidable (@FrameUpdate (revocationWorlds.Fibre world) (revocationWorlds.zero world)
      (revocationWorlds.add world) (revocationWorlds.sep world) held required) :=
  inferInstanceAs (Decidable (∀ frame : Access,
    Access.separate held frame = true → Access.separate required frame = true))

def world : OrderedDependencyStore.Store (Equation Nat) 3 :=
  OrderedDependencyStore.link
    (OrderedDependencyStore.initial 131 (fun member => if member = 1 then BodyCallRun.blank else [])) 0 1

def newEquation : Equation Nat := ⟨⟨.any, .any⟩, false, .singleton 8⟩
def related := OrderedDependencyStore.appendOwn world 1 [newEquation]
def unrelated := OrderedDependencyStore.appendOwn world 2 [newEquation]

def held : IndexedAuthority.Point revocationWorlds := ⟨false, .consume⟩
def revoked := IndexedAuthority.push held (homOfLE (by decide) : false ⟶ true)
def readOnly : IndexedAuthority.Point revocationWorlds := ⟨false, .read⟩

def initial : Call Nat.add (fun _ left _ => left) (fun _ _ => []) (Context := Bool) :=
  openCall Nat.add (fun _ left _ => left) (fun _ _ => []) (OrderedDependencyStore.query world 0) [] 0 true

abbrev charges (quantum : Nat) :=
  fun (_ : (BodyCallOwned.provider Nat.add (fun _ left _ => left) (fun _ _ => [])
    quantum BodyCallOwned.Controls.warming).State () ())
    (_ : Request (BodyCallOwned.Returned Nat.add (fun _ left _ => left) (fun _ _ => []))) => 1

def run (current : OrderedDependencyStore.Store (Equation Nat) 3)
    (point : IndexedAuthority.Point revocationWorlds)
    (call : Call Nat.add (fun _ left _ => left) (fun _ _ => []) (Context := Bool)) :=
  resume (permissionDecidable := revocationDecision point.world point.authority Access.consume)
    Nat.add (fun _ left _ => left) (fun _ _ => []) revocationWorlds world current 0 point .consume
    64 1 BodyCallOwned.Controls.warming (charges _) call

def first := run unrelated held initial
def finished := run unrelated held first.2

theorem revoked_right_refuses_unchanged_data_and_preserves_the_call :
    revoked.authority = .none ∧
      OrderedDependencyStore.checkRead world (OrderedDependencyStore.readStamp world 0) = true ∧
      run world revoked initial = (false, initial) := by
  refine ⟨rfl, by decide, ?_⟩
  exact refused (permissionDecidable := revocationDecision revoked.world revoked.authority Access.consume)
    Nat.add (fun _ left _ => left) (fun _ _ => []) revocationWorlds world world 0 revoked .consume
    64 1 BodyCallOwned.Controls.warming (charges _) initial (Or.inr (by change ¬ FrameUpdate Access.none Access.consume; decide))

theorem stale_data_refuses_a_current_exclusive_right :
    held.authority = .consume ∧
      OrderedDependencyStore.checkRead related (OrderedDependencyStore.readStamp world 0) = false ∧
      run related held initial = (false, initial) := by
  refine ⟨rfl, by decide, ?_⟩
  exact refused (permissionDecidable := revocationDecision held.world held.authority Access.consume)
    Nat.add (fun _ left _ => left) (fun _ _ => []) revocationWorlds world related 0 held .consume
    64 1 BodyCallOwned.Controls.warming (charges _) initial (Or.inl (by decide))

theorem unrelated_change_permits_real_retained_advancement :
    OrderedDependencyStore.checkRead unrelated (OrderedDependencyStore.readStamp world 0) = true ∧
      first.1 = true ∧ first.2.2.2.context.1 = [[]] ∧
      complete Nat.add (fun _ left _ => left) (fun _ _ => []) first.2 = false ∧
      finished.1 = true ∧ complete Nat.add (fun _ left _ => left) (fun _ _ => []) finished.2 = true := by decide

theorem initial_captured :
    captured Nat.add (fun _ left _ => left) (fun _ _ => []) (OrderedDependencyStore.query world 0) [] 0 initial :=
  open_captured Nat.add (fun _ left _ => left) (fun _ _ => []) _ [] 0 true

theorem first_captured :
    captured Nat.add (fun _ left _ => left) (fun _ _ => []) (OrderedDependencyStore.query world 0) [] 0 first.2 :=
  preserves_captured (permissionDecidable := revocationDecision held.world held.authority Access.consume)
    Nat.add (fun _ left _ => left) (fun _ _ => []) revocationWorlds world unrelated 0
    held .consume 64 1 BodyCallOwned.Controls.warming (charges _) [] 0 initial initial_captured

theorem finished_captured :
    captured Nat.add (fun _ left _ => left) (fun _ _ => []) (OrderedDependencyStore.query world 0) [] 0 finished.2 :=
  preserves_captured (permissionDecidable := revocationDecision held.world held.authority Access.consume)
    Nat.add (fun _ left _ => left) (fun _ _ => []) revocationWorlds world unrelated 0
    held .consume 64 1 BodyCallOwned.Controls.warming (charges _) [] 0 first.2 first_captured

theorem captured_completion_outlives_revocation_and_staleness :
    run related revoked finished.2 = (false, finished.2) ∧
      (readout Nat.add (fun _ left _ => left) (fun _ _ => []) finished.2 finished_captured.2.1).1 = some [[]] := by
  refine ⟨?_, by decide⟩
  exact refused (permissionDecidable := revocationDecision revoked.world revoked.authority Access.consume)
    Nat.add (fun _ left _ => left) (fun _ _ => []) revocationWorlds world related 0 revoked .consume
    64 1 BodyCallOwned.Controls.warming (charges _) finished.2 (Or.inr (by change ¬ FrameUpdate Access.none Access.consume; decide))

theorem duplicated_read_evidence_cannot_advance :
    Access.read ## Access.read ∧ Access.read + Access.read = Access.read ∧
      run world readOnly initial = (false, initial) := by
  refine ⟨Access.read_selfSeparate, rfl, ?_⟩
  exact selfSeparate_refuses_exclusive
    (permissionDecidable := revocationDecision false (revocationWorlds.transport (𝟙 false) Access.read) Access.consume)
    Nat.add (fun _ left _ => left) (fun _ _ => []) revocationWorlds
    (𝟙 false) Access.read Access.consume world world 0 64 1 BodyCallOwned.Controls.warming
    (charges _) initial Access.read_selfSeparate Access.consume_exclusive

abbrev pairedAuthority := IndexedAuthority.still Bool (Access × Access)
def pairedDecision (world : Bool) (held required : pairedAuthority.Fibre world) :
    Decidable (@FrameUpdate (pairedAuthority.Fibre world) (pairedAuthority.zero world)
      (pairedAuthority.add world) (pairedAuthority.sep world) held required) :=
  inferInstanceAs (Decidable (∀ frame : Access × Access,
    (Access.separate held.1 frame.1 = true ∧ Access.separate held.2 frame.2 = true) →
      (Access.separate required.1 frame.1 = true ∧ Access.separate required.2 frame.2 = true)))

def pairedOwner : IndexedAuthority.Point pairedAuthority := ⟨false, (.consume, .none)⟩
def otherWork : pairedAuthority.Fibre pairedOwner.world := (.none, .read)

theorem unrelated_authority_frame_composes_with_execution :
    ((Access.consume, Access.none) : Access × Access) ## otherWork ∧
      resume (permissionDecidable := pairedDecision pairedOwner.world
        (pairedOwner.authority + otherWork) (pairedOwner.authority + otherWork))
        Nat.add (fun _ left _ => left) (fun _ _ => []) pairedAuthority world unrelated 0
        ⟨pairedOwner.world, pairedOwner.authority + otherWork⟩
        (pairedOwner.authority + otherWork)
        64 1 BodyCallOwned.Controls.warming (charges _) initial = (true, first.2) := by
  have framed := framed_granted (permissionDecidable := pairedDecision pairedOwner.world
    (pairedOwner.authority + otherWork) (pairedOwner.authority + otherWork)) Nat.add (fun _ left _ => left) (fun _ _ => []) pairedAuthority
    world unrelated 0 pairedOwner pairedOwner.authority otherWork 64 1 BodyCallOwned.Controls.warming
    (charges _) initial (by decide) (FrameUpdate.refl _) (by constructor <;> decide)
  exact ⟨by constructor <;> decide, framed.2⟩

def bothRights : IndexedAuthority.Point pairedAuthority := ⟨false, (.consume, .consume)⟩
def afterCrossing : IndexedAuthority.Point pairedAuthority := ⟨true, (.consume, .read)⟩
def afterRelease : IndexedAuthority.Point pairedAuthority := ⟨true, (.consume, .none)⟩

def crossing : bothRights ⟶ afterCrossing :=
  IndexedAuthority.homOf (homOfLE (by decide) : false ⟶ true) (by
    intro frame separate
    exact ⟨separate.1, Access.consume_updates_read frame.2 separate.2⟩)

def releaseOther : afterCrossing ⟶ afterRelease :=
  IndexedAuthority.homOf (𝟙 true) (by
    intro frame separate
    exact ⟨separate.1, FrameUpdate.to_zero Access.read frame.2 separate.2⟩)

theorem lawful_world_crossing_and_updates_compose_with_execution :
    resume (permissionDecidable := pairedDecision true
      (pairedAuthority.transport (crossing.1 ≫ releaseOther.1) bothRights.authority) afterRelease.authority)
      Nat.add (fun _ left _ => left) (fun _ _ => []) pairedAuthority world unrelated 0
      (IndexedAuthority.push bothRights (crossing.1 ≫ releaseOther.1)) afterRelease.authority
      64 1 BodyCallOwned.Controls.warming (charges _) initial = (true, first.2) :=
  composite_granted (permissionDecidable := pairedDecision true
    (pairedAuthority.transport (crossing.1 ≫ releaseOther.1) bothRights.authority) afterRelease.authority) Nat.add (fun _ left _ => left) (fun _ _ => []) pairedAuthority world unrelated 0
    bothRights afterCrossing afterRelease crossing releaseOther afterRelease.authority 64 1 BodyCallOwned.Controls.warming
    (charges _) initial (by decide) (FrameUpdate.refl _)

#print axioms revoked_right_refuses_unchanged_data_and_preserves_the_call
#print axioms stale_data_refuses_a_current_exclusive_right
#print axioms unrelated_change_permits_real_retained_advancement
#print axioms initial_captured
#print axioms first_captured
#print axioms finished_captured
#print axioms captured_completion_outlives_revocation_and_staleness
#print axioms duplicated_read_evidence_cannot_advance
#print axioms unrelated_authority_frame_composes_with_execution
#print axioms lawful_world_crossing_and_updates_compose_with_execution

end Controls

end CurrentAuthority
end BodyCallAdmission


namespace BodyCallAdmission

open Cursor.Fold.OwnedSequence.CallbackBoundary
variable {Input Output Context : Type}
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)

namespace Controls

def start (authored : List (Equation Nat)) (items : List Nat) (reading : NoRuleReading)
    (warm : Bool) : BodyCallOwned.State Nat.add (fun _ left _ => left) (fun _ _ => []) (Context := Bool) :=
  ⟨(0, .paused (BodyCallProtocol.packet Nat.add (fun _ left _ => left) (fun _ _ => [])
    (BodyCall.openState authored items 0 reading))), ([], warm)⟩

def run (authored : List (Equation Nat)) (items : List Nat) (reading : NoRuleReading)
    (allowance : Nat) (warm : Bool := true) :
    Call Nat.add (fun _ left _ => left) (fun _ _ => []) (Context := Bool) :=
  fromCallbacks (BodyCallOwned.Controls.actual 64) (fun _ _ => 1) allowance none 0
    (start authored items reading warm)
    (BodyCallOwned.terminalAfter Nat.add (fun _ left _ => left) (fun _ _ => []))

theorem earned (authored : List (Equation Nat)) (items : List Nat) (reading : NoRuleReading)
    (allowance : Nat) (warm : Bool := true) :
    quiet Nat.add (fun _ left _ => left) (fun _ _ => []) (run authored items reading allowance warm).2.2 := by
  exact call_quiet Nat.add (fun _ left _ => left) (fun _ _ => []) 64 allowance 0
    BodyCallOwned.Controls.warming none _
    (by simp [quiet, start, BodyCallProtocol.finishedQuiet, BodyCallProtocol.stateView,
      BodyCallProtocol.packet, BodyCallProtocol.replyPacket, BodyCall.Move.next, BodyCall.openState]) (fun _ _ => 1)

def failed := run BodyCallRun.missed [] (.observe .noAnswers) 3
def emptyCollection := run BodyCallRun.blank [] (.observe .noAnswers) 3
def duplicateAnswers := run SourceProducerCardinality.Controls.duplicates [] (.observe .noAnswers) 4
def recursiveAnswers := run BodyCallRun.called [0] (.observe .noAnswers) 3
def incomplete := run BodyCallRun.paired [] (.observe .noAnswers) 1
def pendingFinal := run [] [] (.observe .retainFallback) 1 false
def declined := run BodyCallRun.missedCons [] .decline 3
def handedOff := run BodyCallRun.alienAppend [] (.observe .noAnswers) 3

theorem pending_final_and_nonfinished_stops_are_not_completed :
    (readout Nat.add (fun _ left _ => left) (fun _ _ => []) pendingFinal (earned _ _ _ _ _)).1 = none ∧
      (readout Nat.add (fun _ left _ => left) (fun _ _ => []) incomplete (earned _ _ _ _)).1 = none ∧
      (readout Nat.add (fun _ left _ => left) (fun _ _ => []) declined (earned _ _ _ _)).1 = none ∧
      (readout Nat.add (fun _ left _ => left) (fun _ _ => []) handedOff (earned _ _ _ _)).1 = none := by decide

theorem terminal_failure_and_singleton_empty_collection_differ :
    (readout Nat.add (fun _ left _ => left) (fun _ _ => []) failed (earned _ _ _ _)).1 = some [] ∧
      (optionalValue Nat.add (fun _ left _ => left) (fun _ _ => []) BodyCallRun.missed [] 0
        failed (earned _ _ _ _)).1 = some none ∧
      (readout Nat.add (fun _ left _ => left) (fun _ _ => []) emptyCollection (earned _ _ _ _)).1 = some [[]] ∧
      (directValue Nat.add (fun _ left _ => left) (fun _ _ => []) BodyCallRun.blank [] 0
        emptyCollection (earned _ _ _ _)).1 = some [] ∧
      (optionalValue Nat.add (fun _ left _ => left) (fun _ _ => []) BodyCallRun.blank [] 0
        emptyCollection (earned _ _ _ _)).1 = some (some []) := by decide

theorem equal_occurrences_and_recursive_order_survive_mode_admission :
    (admit Nat.add (fun _ left _ => left) (fun _ _ => []) .nonemptyProducer .optionalValue
      SourceProducerCardinality.Controls.duplicates [] 0 duplicateAnswers (earned _ _ _ _)).1 = some [[7], [7]] ∧
      (admit Nat.add (fun _ left _ => left) (fun _ _ => []) .producer .optionalValue
        SourceProducerCardinality.Controls.duplicates [] 0 duplicateAnswers (earned _ _ _ _)).1 = some [[7], [7]] ∧
      (admit Nat.add (fun _ left _ => left) (fun _ _ => []) .producer .optionalValue
        BodyCallRun.called [0] 0 recursiveAnswers (earned _ _ _ _)).1 = some [[7, 1], [8, 1]] ∧
      (admit Nat.add (fun _ left _ => left) (fun _ _ => []) .nonemptyProducer .optionalValue
        BodyCallRun.called [0] 0 recursiveAnswers (earned _ _ _ _)).1 = none := by decide

theorem wrong_mode_and_scalar_interface_are_refused :
    (admit Nat.add (fun _ left _ => left) (fun _ _ => []) .direct .singleValue
      SourceProducerCardinality.Controls.duplicates [] 0 duplicateAnswers (earned _ _ _ _)).1 = none ∧
      (admit Nat.add (fun _ left _ => left) (fun _ _ => []) .optional .singleValue
        BodyCallRun.missed [] 0 failed (earned _ _ _ _)).1 = none ∧
      (admit Nat.add (fun _ left _ => left) (fun _ _ => []) .nonemptyProducer .optionalValue
        BodyCallRun.missed [] 0 failed (earned _ _ _ _)).1 = none := by decide

def capturedWorld : OrderedDependencyStore.Store (Equation Nat) 1 :=
  OrderedDependencyStore.initial 998 (fun _ => BodyCallRun.blank)

def editedWorld := OrderedDependencyStore.appendOwn capturedWorld 0
  [⟨⟨.any, .any⟩, false, .singleton 8⟩]

theorem stale_dispatch_does_not_unearn_captured_completion :
    OrderedDependencyStore.checkRead editedWorld (OrderedDependencyStore.readStamp capturedWorld 0) = false ∧
      (liveAdmission Nat.add (fun _ left _ => left) (fun _ _ => []) capturedWorld editedWorld 0
        .direct .singleValue [] 0 emptyCollection (earned _ _ _ _)).1 = none ∧
      (readout Nat.add (fun _ left _ => left) (fun _ _ => []) emptyCollection (earned _ _ _ _)).1 = some [[]] := by decide

def forgedFinished : BodyCall.State Nat Nat :=
  ⟨[.body [] (.observe .noAnswers) ⟨.singleton 7, [], 0, []⟩ .emit], .finished⟩

theorem forged_finished_work_cannot_supply_the_readout_invariant :
    ¬ BodyCallProtocol.finishedQuiet Nat.add (fun _ left _ => left) forgedFinished := by
  intro purported
  have empty := purported rfl
  change [[7]] = [] at empty
  cases empty

#print axioms pending_final_and_nonfinished_stops_are_not_completed
#print axioms terminal_failure_and_singleton_empty_collection_differ
#print axioms equal_occurrences_and_recursive_order_survive_mode_admission
#print axioms wrong_mode_and_scalar_interface_are_refused
#print axioms stale_dispatch_does_not_unearn_captured_completion
#print axioms forged_finished_work_cannot_supply_the_readout_invariant

namespace Resumption

abbrev charges (quantum : Nat)
    (accept : Bool → BodyCallOwned.Returned Nat.add (fun _ left _ => left) (fun _ _ => []) → Bool × Bool) :
    Cursor.Charge (BodyCallOwned.provider Nat.add (fun _ left _ => left) (fun _ _ => []) quantum accept) :=
  fun _ _ => 1

def grant (quantum allowance : Nat) : Grant Nat.add (fun _ left _ => left) (fun _ _ => []) (Context := Bool) :=
  (quantum, allowance, BodyCallOwned.Controls.warming)

def refuseAndWarm (_ : Bool)
    (_ : BodyCallOwned.Returned Nat.add (fun _ left _ => left) (fun _ _ => [])) : Bool × Bool :=
  (false, true)

def sliced (authored : List (Equation Nat)) (items : List Nat) (warm : Bool)
    (grants : List (Grant Nat.add (fun _ left _ => left) (fun _ _ => []) (Context := Bool))) :=
  schedule Nat.add (fun _ left _ => left) (fun _ _ => []) charges grants
    (openCall Nat.add (fun _ left _ => left) (fun _ _ => []) authored items 0 warm)

theorem sliced_captured (authored : List (Equation Nat)) (items : List Nat) (warm : Bool)
    (grants : List (Grant Nat.add (fun _ left _ => left) (fun _ _ => []) (Context := Bool))) :
    captured Nat.add (fun _ left _ => left) (fun _ _ => []) authored items 0
      (sliced authored items warm grants) :=
  schedule_open_captured Nat.add (fun _ left _ => left) (fun _ _ => []) charges grants authored items 0 warm

def pausedOnce := sliced BodyCallRun.blank [] false [grant 1 1]
def pausedTwice := sliced BodyCallRun.blank [] false [grant 1 1, grant 1 1]
def refusedGrants := [grant 1 1, grant 1 1, (64, 1, refuseAndWarm)]
def acceptedGrants := refusedGrants ++ [grant 0 1]
def completedGrants := acceptedGrants ++ [grant 64 1]
def refused := sliced BodyCallRun.blank [] false refusedGrants
def accepted := sliced BodyCallRun.blank [] false acceptedGrants
def completed := sliced BodyCallRun.blank [] false completedGrants

theorem multiple_pauses_keep_actual_progress_without_publishing :
    pausedOnce.2.2.computation.1 < pausedTwice.2.2.computation.1 ∧
      pausedOnce.2.2.context.1 = [] ∧ pausedTwice.2.2.context.1 = [] ∧
      pausedOnce.2.1.terminal.isNone = true ∧ pausedTwice.2.1.terminal.isNone = true ∧
      complete Nat.add (fun _ left _ => left) (fun _ _ => []) pausedTwice = false := by decide

theorem changed_refusal_context_is_used_without_repolling :
    refused.2.1.pending.isSome = true ∧ refused.2.2.context = ([], true) ∧
      accepted.2.1.pending.isNone = true ∧ accepted.2.2.context = ([[]], true) ∧
      accepted.2.2.computation.1 = refused.2.2.computation.1 ∧
      BodyCallProtocol.stateView Nat.add (fun _ left _ => left) (fun _ _ => []) accepted.2.2.computation.2 =
        BodyCallProtocol.stateView Nat.add (fun _ left _ => left) (fun _ _ => []) refused.2.2.computation.2 ∧
      complete Nat.add (fun _ left _ => left) (fun _ _ => []) accepted = false ∧
      complete Nat.add (fun _ left _ => left) (fun _ _ => []) completed = true := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, rfl, by decide, by decide⟩

theorem completed_sliced_empty_collection_is_a_value :
    (readout Nat.add (fun _ left _ => left) (fun _ _ => []) completed
      (sliced_captured _ _ _ _).2.1).1 = some [[]] ∧
      (directValue Nat.add (fun _ left _ => left) (fun _ _ => []) BodyCallRun.blank [] 0 completed
        (sliced_captured _ _ _ _).2.1).1 = some [] ∧
      (optionalValue Nat.add (fun _ left _ => left) (fun _ _ => []) BodyCallRun.blank [] 0 completed
        (sliced_captured _ _ _ _).2.1).1 = some (some []) := by decide

def duplicateGrants := [grant 1 1, grant 64 1, grant 64 1, grant 64 1]
def duplicates := sliced SourceProducerCardinality.Controls.duplicates [] true duplicateGrants
def failureGrants := [grant 1 1, grant 64 1]
def failure := sliced BodyCallRun.missed [] true failureGrants

theorem resumed_modes_preserve_occurrences_and_completed_failure :
    (admit Nat.add (fun _ left _ => left) (fun _ _ => []) .nonemptyProducer .optionalValue
      SourceProducerCardinality.Controls.duplicates [] 0 duplicates (sliced_captured _ _ _ _).2.1).1 =
        some [[7], [7]] ∧
      (admit Nat.add (fun _ left _ => left) (fun _ _ => []) .producer .optionalValue
        SourceProducerCardinality.Controls.duplicates [] 0 duplicates (sliced_captured _ _ _ _).2.1).1 =
          some [[7], [7]] ∧
      (admit Nat.add (fun _ left _ => left) (fun _ _ => []) .direct .singleValue
        SourceProducerCardinality.Controls.duplicates [] 0 duplicates (sliced_captured _ _ _ _).2.1).1 = none ∧
      (optionalValue Nat.add (fun _ left _ => left) (fun _ _ => []) BodyCallRun.missed [] 0 failure
        (sliced_captured _ _ _ _).2.1).1 = some none := by decide

def finalRetried := resume Nat.add (fun _ left _ => left) (fun _ _ => []) 0 1
  BodyCallOwned.Controls.warming (charges _ _) pendingFinal

theorem pending_final_retry_acknowledges_the_original_computation :
    complete Nat.add (fun _ left _ => left) (fun _ _ => []) pendingFinal = false ∧
      complete Nat.add (fun _ left _ => left) (fun _ _ => []) finalRetried = true ∧
      finalRetried.2.2.computation.1 = pendingFinal.2.2.computation.1 ∧
      finalRetried.2.2.context.1 = [[]] ∧
      finalRetried.2.1.accepted = pendingFinal.2.1.accepted + 1 := by decide

theorem completed_reentry_keeps_the_whole_call (quantum allowance : Nat) :
    resume Nat.add (fun _ left _ => left) (fun _ _ => []) quantum allowance refuseAndWarm
      (charges _ _) completed = completed :=
  completed_resume_inert _ _ _ _ _ _ _ _ (by decide)

theorem zero_acceptance_allowance_keeps_even_a_pending_loan (quantum : Nat) :
    resume Nat.add (fun _ left _ => left) (fun _ _ => []) quantum 0 refuseAndWarm
      (charges _ _) refused = refused := resume_zero _ _ _ _ _ _ _

theorem stale_new_eligibility_does_not_undo_resumed_completion :
    (liveAdmission Nat.add (fun _ left _ => left) (fun _ _ => []) capturedWorld editedWorld 0
      .direct .singleValue [] 0 completed (sliced_captured _ _ _ _).2.1).1 = none ∧
      (readout Nat.add (fun _ left _ => left) (fun _ _ => []) completed
        (sliced_captured _ _ _ _).2.1).1 = some [[]] := by decide

theorem yield_decline_and_handoff_are_not_resumed_completion :
    complete Nat.add (fun _ left _ => left) (fun _ _ => [])
      (resume Nat.add (fun _ left _ => left) (fun _ _ => []) 0 1 BodyCallOwned.Controls.warming
        (charges _ _) declined) = false ∧
      complete Nat.add (fun _ left _ => left) (fun _ _ => [])
        (resume Nat.add (fun _ left _ => left) (fun _ _ => []) 0 1 BodyCallOwned.Controls.warming
          (charges _ _) handedOff) = false ∧
      complete Nat.add (fun _ left _ => left) (fun _ _ => []) accepted = false := by decide

#print axioms sliced_captured
#print axioms multiple_pauses_keep_actual_progress_without_publishing
#print axioms changed_refusal_context_is_used_without_repolling
#print axioms completed_sliced_empty_collection_is_a_value
#print axioms resumed_modes_preserve_occurrences_and_completed_failure
#print axioms pending_final_retry_acknowledges_the_original_computation
#print axioms completed_reentry_keeps_the_whole_call
#print axioms zero_acceptance_allowance_keeps_even_a_pending_loan
#print axioms stale_new_eligibility_does_not_undo_resumed_completion
#print axioms yield_decline_and_handoff_are_not_resumed_completion

end Resumption

end Controls

end BodyCallAdmission


namespace BodyCallShared

open Cursor.Fold.OwnedSequence.CallbackBoundary
open Mettapedia.GSLT.Contracts
open _root_.CategoryTheory
variable {Input Output Context : Type}
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)
open Cursor.Fold.OwnedSequence.CallbackBoundary
variable {World : Type} [Category.{0} World] (authority : IndexedAuthority.{0, 0, 0} World)
    {size : Nat} (before current : OrderedDependencyStore.Store (Equation Output) size)
    (reader : Fin size) (point : IndexedAuthority.Point authority)
    (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]

namespace Controls

open Mettapedia.GSLT.Contracts
open Cursor.ProducerOccurrenceLog

abbrev sourceAuthority := revocationWorlds
abbrev held := BodyCallAdmission.CurrentAuthority.Controls.held
abbrev revoked := BodyCallAdmission.CurrentAuthority.Controls.revoked
abbrev readOnly := BodyCallAdmission.CurrentAuthority.Controls.readOnly

def world : OrderedDependencyStore.Store (Equation Nat) 3 :=
  OrderedDependencyStore.link
    (OrderedDependencyStore.initial 813 (fun member =>
      if member = 1 then SourceProducerCardinality.Controls.duplicates else [])) 0 1

def changed := OrderedDependencyStore.appendOwn world 1
  [⟨⟨.any, .any⟩, false, .singleton 8⟩]

def unrelated := OrderedDependencyStore.appendOwn world 2
  [⟨⟨.any, .any⟩, false, .singleton 8⟩]

abbrev State := Configuration Nat.add (fun _ left _ => left) (fun _ _ => [])
  (Context := Unit) (size := 3) Nat 2

def initialState : State := initial Nat.add (fun _ left _ => left) (fun _ _ => [])
  world 0 [] 0 () Nat 2 8

def initialCall := BodyCallAdmission.openCall Nat.add (fun _ left _ => left) (fun _ _ => [])
  (OrderedDependencyStore.query world 0) ([] : List Nat) 0 ()

def actualStep (current : OrderedDependencyStore.Store (Equation Nat) 3)
    (point : IndexedAuthority.Point sourceAuthority) (quantum : Nat) :=
  step (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision
    point.world point.authority Access.consume)
    Nat.add (fun _ left _ => left) (fun _ _ => []) sourceAuthority world current 0 point .consume quantum
    (Context := Unit)

def ordinary (ticks : Nat) (state : State) :=
  Cursor.ProducerOccurrenceLog.ordinary (actualStep world held 64)
    (capture Nat.add (fun _ left _ => left) (fun _ _ => [])) (fun _ => true) (fun _ => true) ticks state

def ready := ordinary 16 initialState
def pending := ordinary 1 initialState
def capturedLoan := ordinary 2 initialState
def acknowledgedLoan := ordinary 3 initialState

def first := deliver (fun _ => true) ready 0 100
def retired := retireConsumer first.2 0
def surviving := deliver (fun _ => true) retired 1 101

theorem duplicate_source_is_one_ordered_production_for_both_consumers :
    ready.delivery.log.rows = [(0, [[7]]), (1, [[7]])] ∧ ready.delivery.log.completed = true ∧
      first.1 = .observed (.answer 0 (0, [[7]])) ∧
      surviving.1 = .observed (.answer 0 (0, [[7]])) ∧
      (deliver (fun _ => true) surviving.2 1 101).1 = .observed (.answer 1 (1, [[7]])) ∧
      surviving.2.execution = ready.execution ∧ surviving.2.context = world := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, rfl, rfl⟩

theorem cancellation_does_not_restore_or_read_the_retired_consumer :
    (deliver (fun _ => true) retired 0 100).1 = .observed .cancelled ∧
      Cursor.SharedOccurrenceLog.unread retired.delivery.log 0 = [] ∧
      Cursor.SharedOccurrenceLog.unread retired.delivery.log 1 = [(0, [[7]]), (1, [[7]])] ∧
      retired.delivery.published = first.2.delivery.published := by decide

theorem held_source_loan_is_captured_then_acknowledged_without_new_source :
    (pending.execution.bind (·.pending)).isSome = true ∧
      (capturedLoan.execution.bind (fun execution => execution.producer.2.1.pending)).isSome = true ∧
      (acknowledgedLoan.execution.bind (fun execution => execution.producer.2.1.pending)).isNone = true ∧
      capturedLoan.execution.map (fun execution => execution.producer.2.2.computation.1) =
        acknowledgedLoan.execution.map (fun execution => execution.producer.2.2.computation.1) ∧
      capturedLoan.execution.map (fun execution => BodyCallProtocol.stateView Nat.add (fun _ left _ => left)
        (fun _ _ => []) execution.producer.2.2.computation.2) =
        acknowledgedLoan.execution.map (fun execution => BodyCallProtocol.stateView Nat.add (fun _ left _ => left)
          (fun _ _ => []) execution.producer.2.2.computation.2) := by
  exact ⟨by decide, by decide, by decide, by decide, rfl⟩

theorem admission_refusal_retains_the_entire_paid_pending_call :
    pump (actualStep world held 64) (capture Nat.add (fun _ left _ => left) (fun _ _ => []))
      (fun _ => false) (fun _ => true) pending = (.admissionRefused, pending) ∧
      ordinary 0 pending = pending := ⟨rfl, rfl⟩

def resumeAfterRevocation := Cursor.ProducerOccurrenceLog.ordinary (actualStep world revoked 64)
  (capture Nat.add (fun _ left _ => left) (fun _ _ => [])) (fun _ => true) (fun _ => true) 3 pending

theorem revoked_authority_does_not_unearn_the_buffered_pure_value :
    resumeAfterRevocation.delivery.log.rows = [(0, [[7]])] ∧
      resumeAfterRevocation.delivery.log.completed = false ∧
      (deliver (fun _ => true) resumeAfterRevocation 1 101).1 = .observed (.answer 0 (0, [[7]])) ∧
      (actualStep world revoked 64 initialCall).next =
        initialCall := by
  exact ⟨by decide, by decide, by decide, rfl⟩

theorem stale_or_read_only_new_work_is_inert_but_unrelated_change_is_admitted :
    (actualStep changed held 64 initialCall).next = initialCall ∧
      (actualStep world readOnly 64 initialCall).next = initialCall ∧
      (actualStep unrelated held 64 initialCall).returns.length = 1 := by
  exact ⟨rfl, rfl, by decide⟩

def programRun (authored : List (Equation Nat)) :
    Configuration Nat.add (fun _ left _ => left) (fun _ _ => []) (Context := Unit) (size := 1) Nat 2 :=
  let captured := OrderedDependencyStore.initial 849 (fun (_ : Fin 1) => authored)
  Cursor.ProducerOccurrenceLog.ordinary
    (step (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision
      held.world held.authority Access.consume)
      Nat.add (fun _ left _ => left) (fun _ _ => []) sourceAuthority captured captured 0 held .consume 64)
    (capture Nat.add (fun _ left _ => left) (fun _ _ => [])) (fun _ => true) (fun _ => true) 16
    (initial Nat.add (fun _ left _ => left) (fun _ _ => []) captured 0 [] 0 () Nat 2 8)

theorem absence_yield_handoff_and_exhaustion_remain_distinct :
    pending.delivery.log.completed = false ∧ pending.delivery.log.rows = [] ∧
      (programRun BodyCallRun.missed).delivery.log.completed = true ∧
      (programRun BodyCallRun.missed).delivery.log.rows = [] ∧
      (programRun BodyCallRun.blank).delivery.log.rows = [(0, [[]])] ∧
      (programRun BodyCallRun.alienAppend).delivery.log.completed = false ∧
      ((programRun BodyCallRun.alienAppend).execution.map fun execution =>
        match execution.mode with | .handoff _ => true | _ => false) = some true := by decide

theorem retiring_the_entire_cohort_stops_demand_without_finishing :
    let cancelled := retireConsumer (retireConsumer pending 0) 1
    pump (actualStep world held 64) (capture Nat.add (fun _ left _ => left) (fun _ _ => []))
      (fun _ => true) (fun _ => true) cancelled = (.noConsumers, cancelled) ∧
      cancelled.delivery.log.completed = false := ⟨rfl, rfl⟩

theorem factors_follow_production_positions_and_cannot_be_paid_twice :
    let paid := Coefficients.ledger Nat.add (fun _ left _ => left) (fun _ _ => []) 0 (fun _ => (7 : Nat)) ready
    paid.map (·.identity) = [0, 1] ∧ paid.map (·.coefficient) = [7, 7] ∧
      Mettapedia.Algebra.SharedCoefficientLedger.merge? paid paid = some paid ∧
      Mettapedia.Algebra.SharedCoefficientLedger.append? paid
        ⟨0, OrderedDependencyStore.readStamp world 0, 7⟩ = none := by decide

end Controls

#print axioms Controls.duplicate_source_is_one_ordered_production_for_both_consumers

#print axioms Controls.cancellation_does_not_restore_or_read_the_retired_consumer

#print axioms Controls.held_source_loan_is_captured_then_acknowledged_without_new_source

#print axioms Controls.admission_refusal_retains_the_entire_paid_pending_call

#print axioms Controls.revoked_authority_does_not_unearn_the_buffered_pure_value

#print axioms Controls.stale_or_read_only_new_work_is_inert_but_unrelated_change_is_admitted

#print axioms Controls.factors_follow_production_positions_and_cannot_be_paid_twice

#print axioms Controls.absence_yield_handoff_and_exhaustion_remain_distinct

#print axioms Controls.retiring_the_entire_cohort_stops_demand_without_finishing

end BodyCallShared


namespace BodyCallShared
namespace History

open Cursor.Fold.OwnedSequence.CallbackBoundary
open Mettapedia.GSLT.Contracts
open _root_.CategoryTheory
variable {Input Output Context : Type}
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)
open Cursor.Fold.OwnedSequence.CallbackBoundary
variable {World : Type} [Category.{0} World] (authority : IndexedAuthority.{0, 0, 0} World)
    {size : Nat} (before current : OrderedDependencyStore.Store (Equation Output) size)
    (reader : Fin size) (point : IndexedAuthority.Point authority)
    (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]
open Cursor.ProducerOccurrenceLog
open Cursor.ProducerOccurrenceLog.Accounting
open Mettapedia.GSLT.Core.InferenceControl.Recording
variable {Owner : Type} {clients : Nat} [DecidableEq Output] [DecidableEq Owner]
    (quantum : Nat) (capacity : Stored (Output := Output) → Bool)
local notation "sourceStep" => step construct callbackConstruct fallback authority before current reader point required quantum
local notation "sourceCapture" => capture construct callbackConstruct fallback
local notation "Cfg" => Configuration construct callbackConstruct fallback (Context := Context) (size := size) Owner clients
local notation "Action" => Cursor.ProducerOccurrenceLog.Accounting.Action Owner clients
local notation "Occurrence" => CausalEvent (HistoryOccurrence clients)

namespace Controls

open Mettapedia.GSLT.Contracts
open Mettapedia.Algebra.SharedCoefficientLedger

local instance : DecidableEq (FreeMonoid Nat) := inferInstanceAs (DecidableEq (List Nat))

abbrev State := BodyCallShared.Controls.State
abbrev SourceAccount := Scoped Nat (OrderedDependencyStore.ReadStamp 3) (FreeMonoid Nat) Nat
abbrev start := BodyCallShared.Controls.initialState

abbrev sourceDecision := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision false Access.consume Access.consume

def observeActual (history : Option (Prefix (CausalEvent (HistoryOccurrence 2))))
    (account : Option ProtocolAccount) (actions : List (Accounting.Action Nat 2)) (state : State) :=
  observe (permissionDecidable := sourceDecision) Nat.add (fun _ left _ => left) (fun _ _ => [])
    BodyCallShared.Controls.sourceAuthority BodyCallShared.Controls.world BodyCallShared.Controls.world 0
    BodyCallShared.Controls.held Access.consume 64 (fun _ => true) history account actions state

def word (actions : List (Accounting.Action Nat 2)) (state : State) :=
  events (permissionDecidable := sourceDecision) Nat.add (fun _ left _ => left) (fun _ _ => [])
    BodyCallShared.Controls.sourceAuthority BodyCallShared.Controls.world BodyCallShared.Controls.world 0
    BodyCallShared.Controls.held Access.consume 64 (fun _ => true) actions state

def coefficient (stored : Stored (Output := Nat)) : FreeMonoid Nat := FreeMonoid.ofList [stored.1 + 5]

def scope (actions : List (Accounting.Action Nat 2)) (state : State) (entry : SourceAccount) (observer : Nat) :=
  Scopes.resume (permissionDecidable := sourceDecision) Nat.add (fun _ left _ => left) (fun _ _ => [])
    BodyCallShared.Controls.sourceAuthority BodyCallShared.Controls.world BodyCallShared.Controls.world 0
    BodyCallShared.Controls.held Access.consume 64 (fun _ => true) coefficient actions state entry observer

def startingAccount : SourceAccount := Scopes.begin Nat.add (fun _ left _ => left) (fun _ _ => []) 0 coefficient start

def firstActions : List (Accounting.Action Nat 2) := List.replicate 2 .pump
def laterActions : List (Accounting.Action Nat 2) := List.replicate 14 .pump ++ [.deliver 0 100, .deliver 1 101]
def allActions := firstActions ++ laterActions

def observed := observeActual (some (Prefix.initial 1)) (some (1, 1)) allActions start
def ordinary := observeActual none none allActions start
def earlier := observeActual (some (Prefix.initial 1)) (some (1, 1)) firstActions start
def forgotten := observeActual none earlier.2.1 laterActions earlier.2.2

def firstClaim := scope firstActions start startingAccount 11
def secondClaim := match firstClaim.1 with
  | some (entry, _) => scope laterActions firstClaim.2 entry 22
  | none => (none, firstClaim.2)

def outerRead := match secondClaim.1 with
  | some (entry, _) => Scopes.readScope Nat.add (fun _ left _ => left) (fun _ _ => []) 0 coefficient
      secondClaim.2 startingAccount entry 33
  | none => none

theorem actual_history_records_admissions_and_independent_deliveries :
    word allActions start = [admissionCausal 0, admissionCausal 1, deliveryCausal 0 0, deliveryCausal 1 0] ∧
      observed.1.map Prefix.items = some [admissionCausal 0] ∧
      observed.1.map (·.omitted) = some 3 ∧
      observed.2.2.delivery.log.rows = [(0, [[7]]), (1, [[7]])] := by decide

theorem producer_return_and_refused_admission_are_not_history_occurrences :
    word [.pump] start = [] ∧
      word [.pump, .pump] start = [admissionCausal 0] ∧
      word [] BodyCallShared.Controls.pending = [] := by decide

theorem erasure_and_forgetting_keep_actual_state_and_paid_account :
    observed.2.2 = ordinary.2.2 ∧ forgotten.2.2 = ordinary.2.2 ∧
      forgotten.2.1 = observed.2.1 ∧ forgotten.1 = none := ⟨rfl, rfl, rfl, rfl⟩

theorem scoped_claims_follow_equal_source_occurrences_without_double_selection :
    firstClaim.1.map (fun result => result.2.map (·.identity)) = some [0] ∧
      secondClaim.1.map (fun result => result.2.map (·.identity)) = some [1] ∧
      secondClaim.1.map (fun result => [result.1.claims 0, result.1.claims 1]) = some [some 11, some 22] ∧
      outerRead.map (fun result => result.2.map (·.identity)) = some [] ∧
      outerRead.map (fun result => [result.1.claims 0, result.1.claims 1]) = some [some 11, some 22] := by decide

def lostClaimRead := match firstClaim.1, secondClaim.1 with
  | some (capture, _), some (entry, _) =>
      Scopes.readScope Nat.add (fun _ left _ => left) (fun _ _ => []) 0 coefficient secondClaim.2 capture
        {entry with claims := fun _ => none} 33
  | _, _ => none

def forgedCaptureRead := match firstClaim.1, secondClaim.1 with
  | some (capture, _), some (entry, _) =>
      Scopes.readScope Nat.add (fun _ left _ => left) (fun _ _ => []) 0 coefficient secondClaim.2
        {capture with productions := capture.productions.map (fun (factor : Factor Nat (OrderedDependencyStore.ReadStamp 3) (FreeMonoid Nat)) =>
          {factor with coefficient := FreeMonoid.ofList [99]})}
        entry 33
  | _, _ => none

theorem erased_claim_or_forged_factor_capture_is_refused :
    lostClaimRead.isNone = true ∧ forgedCaptureRead.isNone = true := by decide

def freshWorld := firstClaim.1.map fun result =>
  Scopes.carry Nat.add (fun _ left _ => left) (fun _ _ => []) 0 coefficient result.1 secondClaim.2

def transportedFresh := match firstClaim.1, freshWorld with
  | some (entry, _), some world =>
      some (Scopes.transport (fun identity => identity + 100) (fun (stamp : OrderedDependencyStore.ReadStamp 3) => stamp.identity) (fun owner => owner + 1000) world,
        rename (fun identity => identity + 100) (fun (stamp : OrderedDependencyStore.ReadStamp 3) => stamp.identity) entry.productions)
  | _, _ => none

theorem constructed_transport_keeps_claims_and_ordered_fresh_coefficient :
    transportedFresh.map (fun result => result.1.claims 100) = some (some 1011) ∧
      transportedFresh.map (fun result => FreeMonoid.toList
        (denote (Scoped.selectedSince result.2 result.1))) = some [6] ∧
      freshWorld.map (fun world => world.productions.map (·.identity)) = some [0, 1] := by decide

def collapsed := secondClaim.1.map fun result => rename (fun (_ : Nat) => 0) id result.1.productions

theorem coalescing_physical_factor_identities_is_not_lawful_transport :
    collapsed.map (fun factors => decide (Valid factors)) = some false ∧
      collapsed.map (fun factors => (Mettapedia.Algebra.SharedCoefficientLedger.merge? factors factors).isNone) = some true := by decide

#print axioms actual_history_records_admissions_and_independent_deliveries
#print axioms producer_return_and_refused_admission_are_not_history_occurrences
#print axioms erasure_and_forgetting_keep_actual_state_and_paid_account
#print axioms scoped_claims_follow_equal_source_occurrences_without_double_selection
#print axioms erased_claim_or_forged_factor_capture_is_refused
#print axioms constructed_transport_keeps_claims_and_ordered_fresh_coefficient
#print axioms coalescing_physical_factor_identities_is_not_lawful_transport

end Controls

end History
end BodyCallShared


namespace BodyCallWeighted

open Mettapedia.Algebra.SharedCoefficientLedger
open Mettapedia.GSLT.Core.WeightedMuScheduler
open Cursor.Fold.OwnedSequence.CallbackBoundary
variable {Input Output Weight Context : Type} [Semiring Weight]
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)
    (clause : WeighClause Weight (BodyCall.Graded.Activation Input Output))

namespace Controls

abbrev build := Nat.add
def callback (tag left right : Nat) := tag + left + right
def noFallback (_ : List Nat) (_ : Nat) : List Nat := []

def valuation : WeighClause Nat (BodyCall.Graded.Activation Nat Nat) :=
  .observe (fun activation => if activation.frontier.ordinal = 0 then 11
    else if activation.frontier.ordinal = 1 then 3 else 5)

def attempted : List (Equation Nat) :=
  [⟨⟨.any, .any⟩, false, .mapHead (.singleton 9)⟩,
   ⟨⟨.any, .any⟩, false, .singleton 7⟩,
   ⟨⟨.any, .any⟩, false, .singleton 7⟩]

def acceptWeights (weights : List Nat) (returned : Returned build callback noFallback valuation) : Bool × List Nat :=
  (true, weights ++ [BodyCall.Graded.loanWeight returned.2.2.val.val])

def runProgram (clause : WeighClause Nat (BodyCall.Graded.Activation Nat Nat))
    (program : List (Equation Nat)) (items : List Nat) (allowance : Nat)
    (accept : List Nat → Returned build callback noFallback clause → Bool × List Nat) :=
  fromCallbacks (Owned.provider build callback noFallback clause 64 accept) (fun _ _ => 1) allowance none 0
    (Owned.openState build callback noFallback clause program items 0 [])
    (Owned.terminalAfter build callback noFallback clause)

def completed := runProgram valuation attempted [] 3 acceptWeights

def paidWeights (call : Owned.Call build callback noFallback valuation (Context := List Nat)) :=
  (stateView build callback noFallback valuation call.2.2.computation.2).val.paid.map Factor.coefficient

/-- A failed activation is physical work, but it contributes no later branch
coefficient. Equal source values retain their distinct activation factors. -/
theorem failed_activation_and_equal_answers :
    completed.2.2.context = ([[7], [7]], [3, 5]) ∧
      paidWeights completed = [11, 3, 5] ∧ completed.2.1.accepted = 2 ∧
      Owned.complete build callback noFallback valuation completed = true := by decide

def warming (context : Bool × List Nat) (returned : Returned build callback noFallback valuation) :
    Bool × (Bool × List Nat) :=
  (context.1, (true, if context.1 then context.2 ++ [BodyCall.Graded.loanWeight returned.2.2.val.val] else context.2))

def refused := fromCallbacks (Owned.provider build callback noFallback valuation 64 warming) (fun _ _ => 1) 1 none 0
  (Owned.openState build callback noFallback valuation attempted [] 0 (false, []))
  (Owned.terminalAfter build callback noFallback valuation)

def retried := resumeCall (Owned.provider build callback noFallback valuation 0 warming) (fun _ _ => 1) 1 refused
  (Owned.terminalAfter build callback noFallback valuation)

theorem refusal_and_zero_source_retry_keep_the_actual_paid_loan :
    refused.2.1.pending.isSome = true ∧ refused.2.2.context = ([], true, []) ∧
      refused.2.1.pending.map (fun loan => BodyCall.Graded.loanWeight loan.2.2.val.val) = some 3 ∧
      retried.2.2.context = ([[7]], true, [3]) ∧ retried.2.1.accepted = 1 ∧
      retried.2.2.computation.1 = refused.2.2.computation.1 ∧
      (stateView build callback noFallback valuation retried.2.2.computation.2).val.paid.map Factor.coefficient = [11, 3] := by decide

theorem zero_acceptance_allowance_retains_pending_factor :
    resumeCall (Owned.provider build callback noFallback valuation 0 warming) (fun _ _ => 1) 0 refused
      (Owned.terminalAfter build callback noFallback valuation) = refused := resumeCall_zero _ _ _ _

def cartesian : List (Equation Nat) :=
  [⟨⟨.cons, .any⟩, false,
      .append (.map (.constructor 10 .argument (.value 1)) .callTail) .callTail⟩,
   ⟨⟨.empty, .any⟩, false, .singleton 7⟩,
   ⟨⟨.empty, .any⟩, false, .singleton 7⟩]

def cartesianValuation : WeighClause Nat (BodyCall.Graded.Activation Nat Nat) :=
  .observe (fun activation => if activation.frontier.ordinal = 0 then 2
    else if activation.frontier.ordinal = 1 then 3 else 5)

def acceptCartesian (weights : List Nat) (returned : Returned build callback noFallback cartesianValuation) : Bool × List Nat :=
  (true, weights ++ [BodyCall.Graded.loanWeight returned.2.2.val.val])

def cartesianCompleted := runProgram cartesianValuation cartesian [0] 5 acceptCartesian

theorem recursive_cartesian_lineage_and_callback_capture :
    cartesianCompleted.2.2.context = ([[18, 7], [18, 7], [18, 7], [18, 7]], [18, 30, 30, 50]) ∧
      (stateView build callback noFallback cartesianValuation cartesianCompleted.2.2.computation.2).val.paid.map Factor.coefficient =
        [2, 3, 3, 5, 5, 3, 5] ∧
      Owned.complete build callback noFallback cartesianValuation cartesianCompleted = true := by decide

def zeroValuation : WeighClause Nat (BodyCall.Graded.Activation Nat Nat) := .scalar 0

def acceptZero (weights : List Nat) (returned : Returned build callback noFallback zeroValuation) : Bool × List Nat :=
  (true, weights ++ [BodyCall.Graded.loanWeight returned.2.2.val.val])

def emptyCompleted := runProgram zeroValuation BodyCallRun.blank [] 2 acceptZero

theorem zero_factor_and_empty_collection_remain_physical :
    emptyCompleted.2.2.context = ([[]], [0]) ∧ emptyCompleted.2.1.accepted = 1 ∧
      (stateView build callback noFallback zeroValuation emptyCompleted.2.2.computation.2).val.paid.length = 1 ∧
      Owned.complete build callback noFallback zeroValuation emptyCompleted = true := by decide

def handedOff := runProgram valuation BodyCallRun.alienAppend [] 2 acceptWeights

theorem handoff_and_unacknowledged_loan_are_not_completion :
    Owned.complete build callback noFallback valuation handedOff = false ∧
      Owned.complete build callback noFallback valuation refused = false ∧
      handedOff.2.1.terminal.map (fun loan => loan.2.2.val.val.core.phase) = some .handoff := by decide

#print axioms failed_activation_and_equal_answers
#print axioms refusal_and_zero_source_retry_keep_the_actual_paid_loan
#print axioms zero_acceptance_allowance_retains_pending_factor
#print axioms recursive_cartesian_lineage_and_callback_capture
#print axioms zero_factor_and_empty_collection_remain_physical
#print axioms handoff_and_unacknowledged_loan_are_not_completion

end Controls

end BodyCallWeighted


namespace BodyCallWeighted

open Mettapedia.Algebra.SharedCoefficientLedger
open Mettapedia.GSLT.Core.WeightedMuScheduler
open Cursor.Fold.OwnedSequence.CallbackBoundary
variable {Input Output Weight Context : Type} [Semiring Weight]
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)
    (clause : WeighClause Weight (BodyCall.Graded.Activation Input Output))

namespace AttachmentControls

open _root_.Mettapedia.Machines.SourceProducerCardinality.BodyCallWeighted.Controls

abbrev Activation := BodyCall.Graded.Activation Nat Nat
abbrev Selection := Activation → Option (WeighClause Nat Activation)

def absent : Selection := fun _ => none
def unit : Selection := fun _ => some (.scalar 1)
def scalarProgram : List (Equation Nat) := [⟨⟨.any, .any⟩, false, .singleton 7⟩]

def accept (selection : Selection) (context : List (Nat × List Nat))
    (returned : Compact.Attachment.SparseReturned build callback noFallback selection) :
    Bool × List (Nat × List Nat) :=
  (true, context ++ [(denote returned.2.2.val.loan, identities returned.2.2.val.loan)])

def call (selection : Selection) (program : List (Equation Nat)) (items : List Nat) (allowance : Nat) :=
  fromCallbacks (Compact.Attachment.ownedProvider build callback noFallback selection 64 (accept selection))
    (fun _ _ => 1) allowance none 0 (Compact.Attachment.ownedOpen build callback noFallback selection program items 0 [])
    (Compact.Attachment.terminalAfter build callback noFallback selection)

def absentCompleted := call absent scalarProgram [] 2
def unitCompleted := call unit scalarProgram [] 2

def ordinal (selection : Selection) (outcome : Compact.Attachment.SparseOutcome build callback noFallback selection) : Nat :=
  match outcome with
  | .paused saved => saved.2.2.val.nextOrdinal
  | .done returned => returned.2.2.val.nextOrdinal

theorem absent_and_explicit_unit_are_physically_distinct :
    absentCompleted.2.2.context = ([[7]], [(1, [])]) ∧
      unitCompleted.2.2.context = ([[7]], [(1, [0])]) ∧
      ordinal absent absentCompleted.2.2.computation.2 = 1 ∧
      ordinal unit unitCompleted.2.2.computation.2 = 1 ∧
      absentCompleted.2.2.computation.1 = unitCompleted.2.2.computation.1 := by decide

def mixed : Selection := fun activation =>
  if activation.frontier.ordinal = 0 then none
  else if activation.frontier.ordinal = 1 then some (.scalar 11)
  else if activation.frontier.ordinal = 2 then some (.scalar 3) else some (.scalar 5)

def mixedProgram : List (Equation Nat) :=
  [⟨⟨.cons, .any⟩, false,
      .append (.map (.constructor 10 .argument (.value 1)) .callTail) .callTail⟩,
   ⟨⟨.empty, .any⟩, false, .mapHead (.singleton 99)⟩,
   ⟨⟨.empty, .any⟩, false, .singleton 7⟩,
   ⟨⟨.empty, .any⟩, false, .singleton 7⟩]

def mixedCompleted := call mixed mixedProgram [0] 5

/-- The unannotated wrapper has no factor. Failed graded activations leave
firing-identity gaps and never contaminate either saved Cartesian branch. -/
theorem mixed_failed_cartesian_and_captured_callback :
    mixedCompleted.2.2.context =
      ([[18, 7], [18, 7], [18, 7], [18, 7]],
        [(9, [2, 4]), (15, [2, 5]), (15, [6, 8]), (25, [6, 9])]) ∧
      ordinal mixed mixedCompleted.2.2.computation.2 = 10 ∧ mixedCompleted.2.1.accepted = 4 ∧
      mixedCompleted.2.1.terminal.map (fun returned => returned.2.2.val.core.phase) = some .finished := by decide

def warming (context : Bool × List (Nat × List Nat))
    (returned : Compact.Attachment.SparseReturned build callback noFallback unit) :
    Bool × (Bool × List (Nat × List Nat)) :=
  (context.1, (true, if context.1 then context.2 ++ [(denote returned.2.2.val.loan, identities returned.2.2.val.loan)] else context.2))

def refused := fromCallbacks (Compact.Attachment.ownedProvider build callback noFallback unit 64 warming)
  (fun _ _ => 1) 1 none 0 (Compact.Attachment.ownedOpen build callback noFallback unit scalarProgram [] 0 (false, []))
  (Compact.Attachment.terminalAfter build callback noFallback unit)

def retried := resumeCall (Compact.Attachment.ownedProvider build callback noFallback unit 0 warming)
  (fun _ _ => 1) 1 refused (Compact.Attachment.terminalAfter build callback noFallback unit)

theorem sparse_refusal_retry_keeps_unit_factor_and_firing_counter :
    refused.2.1.pending.map (fun returned => identities returned.2.2.val.loan) = some [0] ∧
      refused.2.2.context = ([], true, []) ∧ retried.2.2.context = ([[7]], true, [(1, [0])]) ∧
      retried.2.2.computation.1 = refused.2.2.computation.1 ∧
      ordinal unit retried.2.2.computation.2 = ordinal unit refused.2.2.computation.2 ∧
      retried.2.1.accepted = 1 := by decide

theorem sparse_zero_acceptance_allowance_is_inert :
    resumeCall (Compact.Attachment.ownedProvider build callback noFallback unit 0 warming)
      (fun _ _ => 1) 0 refused (Compact.Attachment.terminalAfter build callback noFallback unit) = refused :=
  resumeCall_zero _ _ _ _

#print axioms absent_and_explicit_unit_are_physically_distinct
#print axioms mixed_failed_cartesian_and_captured_callback
#print axioms sparse_refusal_retry_keeps_unit_factor_and_firing_counter
#print axioms sparse_zero_acceptance_allowance_is_inert

end AttachmentControls

end BodyCallWeighted


namespace BodyCallShared.Weighted

open Mettapedia.Algebra.SharedCoefficientLedger
open Mettapedia.GSLT.Core.WeightedMuScheduler
open Cursor.Fold.OwnedSequence.CallbackBoundary
open Mettapedia.GSLT.Contracts
open _root_.CategoryTheory
variable {Input Output Weight Context : Type} [Semiring Weight]
    (construct : Input → Output → Output) (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)
    (selection : BodyCall.Graded.Activation Input Output → Option (WeighClause Weight (BodyCall.Graded.Activation Input Output)))
variable {World : Type} [Category.{0} World] (authority : IndexedAuthority.{0, 0, 0} World)
    {size : Nat} (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]
variable {Owner : Type} {clients : Nat} (quantum : Nat)
local notation "sourceStep" => step construct callbackConstruct fallback selection authority before current reader point required quantum
local notation "sourceCapture" => capture construct callbackConstruct fallback selection
local notation "Cfg" => Configuration construct callbackConstruct fallback selection (Context := Context) (size := size) Owner clients
variable [DecidableEq Output] [DecidableEq Weight] [DecidableEq Owner]

namespace Controls

open Cursor.ProducerOccurrenceLog
open Mettapedia.GSLT.Contracts
open _root_.Mettapedia.Machines.SourceProducerCardinality.BodyCallWeighted.Controls (build callback noFallback)
open _root_.Mettapedia.Machines.SourceProducerCardinality.BodyCallShared.Controls (sourceAuthority held revoked)

abbrev Activation := BodyCall.Graded.Activation Nat Nat

def attachment (activation : Activation) : Option (WeighClause Nat Activation) :=
  some (.scalar (if activation.frontier.ordinal = 0 then 2
    else if activation.frontier.ordinal = 1 then 11 else if activation.frontier.ordinal = 2 then 3 else 5))

def authored : List (Equation Nat) :=
  [⟨⟨.cons, .any⟩, false, .mapHead .callTail⟩,
   ⟨⟨.empty, .any⟩, false, .mapHead (.singleton 99)⟩,
   ⟨⟨.empty, .any⟩, false, .singleton 7⟩,
   ⟨⟨.empty, .any⟩, false, .singleton 7⟩]

def world : OrderedDependencyStore.Store (Equation Nat) 1 := OrderedDependencyStore.initial 947 (fun _ => authored)

abbrev State := Configuration build callback noFallback attachment (Context := Unit) (size := 1) Nat 2

def start : State := initial build callback noFallback attachment world 0 [0] 0 () Nat 2 8

def actualStep (quantum : Nat) :=
  step (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision held.world held.authority Access.consume)
    build callback noFallback attachment sourceAuthority world world 0 held .consume quantum (Context := Unit)

def captureRow := capture build callback noFallback attachment

def ordinary (ticks : Nat) (state : State) :=
  Cursor.ProducerOccurrenceLog.ordinary (actualStep 64) captureRow (fun _ => true) (fun _ => true) ticks state

def ready := ordinary 16 start
def pending := ordinary 1 start
def captured := ordinary 2 start
def acknowledged := ordinary 3 start

def ordinal (call : Call build callback noFallback attachment (Context := Unit)) : Nat :=
  match call.2.2.computation.2 with
  | .paused saved => saved.2.2.val.nextOrdinal
  | .done returned => returned.2.2.val.nextOrdinal

def sourceState (call : Call build callback noFallback attachment (Context := Unit)) : BodyCall.Graded.Compact.State Nat Nat Nat :=
  match call.2.2.computation.2 with
  | .paused saved => saved.2.2.val
  | .done returned => returned.2.2.val

def leftRow := ready.delivery.log.rows[0]!
def rightRow := ready.delivery.log.rows[1]!

/-- The failed coefficient belongs to physical work, not either branch.
Equal answers share the real outer factor and retain distinct alternatives. -/
theorem shared_outer_failed_and_equal_alternatives :
    ready.delivery.log.rows.map (fun row => (row.1, row.2.1, identities row.2.2,
      Mettapedia.Algebra.SharedCoefficientLedger.denote row.2.2)) =
        [(0, [[7]], [0, 2], 6), (1, [[7]], [0, 3], 10)] ∧
      ready.delivery.log.completed = true ∧ ready.execution.map (fun execution => ordinal execution.producer) = some 4 ∧
      leftRow.2.2.head? = rightRow.2.2.head? := by decide

def first := deliver (fun _ => true) captured 0 100
def cancelled := retireConsumer first.2 0
def otherFinished := ordinary 16 cancelled

theorem independent_delivery_and_cancel_keep_existing_branch_factors :
    first.1 = .observed (.answer 0 (0, [[7]], [⟨0, 0, 2⟩, ⟨2, 2, 3⟩])) ∧
      (deliver (fun _ => true) otherFinished 1 101).1 = first.1 ∧
      otherFinished.delivery.log.rows = ready.delivery.log.rows ∧
      Cursor.SharedOccurrenceLog.unread otherFinished.delivery.log 0 = [] ∧
      Cursor.SharedOccurrenceLog.unread otherFinished.delivery.log 1 = ready.delivery.log.rows ∧
      otherFinished.execution.map (fun execution => ordinal execution.producer) = some 4 := by
  exact ⟨rfl, rfl, by decide, by decide, by decide, by decide⟩

/-- A refused capture keeps the actual paid loan and producer residual.
The later acknowledgment accepts that loan with no provider operation. -/
theorem refusal_zero_and_acknowledgment_keep_the_actual_loan :
    pump (actualStep 64) captureRow (fun _ => false) (fun _ => true) pending = (.admissionRefused, pending) ∧
      ordinary 0 pending = pending ∧
      captured.execution.map (fun execution => execution.producer.2.2.computation.1) =
        acknowledged.execution.map (fun execution => execution.producer.2.2.computation.1) ∧
      captured.execution.map (fun execution => sourceState execution.producer) =
        acknowledged.execution.map (fun execution => sourceState execution.producer) ∧
      captured.execution.map (fun execution => execution.producer.2.1.pending.isSome) = some true ∧
      acknowledged.execution.map (fun execution => execution.producer.2.1.pending.isSome) = some false := by
  exact ⟨rfl, rfl, rfl, rfl, by decide, by decide⟩

def outer : Scoped Nat Nat Nat Nat := ⟨[⟨0, 0, 2⟩], fun _ => none⟩
def leftWorld : Scoped Nat Nat Nat Nat := ⟨leftRow.2.2, fun _ => none⟩
def rightWorld : Scoped Nat Nat Nat Nat := ⟨rightRow.2.2, fun _ => none⟩
def handled := observeBranch leftRow outer leftWorld 17

theorem scoped_readout_excludes_shared_prefix_and_rejects_sibling_capture :
    handled.map (fun result => (result.2.map Factor.identity, Mettapedia.Algebra.SharedCoefficientLedger.denote result.2)) = some ([2], 3) ∧
      (observeBranch rightRow outer rightWorld 18).map (fun result => (identities result.2,
        Mettapedia.Algebra.SharedCoefficientLedger.denote result.2)) = some ([3], 5) ∧
      (handled.bind fun result => observeBranch leftRow outer result.1 19).map (fun result => identities result.2) = some [] ∧
      observeBranch rightRow leftWorld rightWorld 19 = none ∧
      observeBranch leftRow outer rightWorld 19 = none := by decide

namespace Stateful

open _root_.Mettapedia.Machines.SourceProducerCardinality.BodyCallWeighted.AttachmentControls (unit scalarProgram warming)

def initialCall := BodyCallWeighted.Compact.Attachment.openCall build callback noFallback unit scalarProgram ([] : List Nat) 0 (false, ([] : List (Nat × List Nat)))
def paused := BodyCallWeighted.Compact.Attachment.resumeCallSource build callback noFallback unit 1 1 warming initialCall
def refused := BodyCallWeighted.Compact.Attachment.resumeCallSource build callback noFallback unit 64 1 warming paused
def retried := BodyCallWeighted.Compact.Attachment.resumeCallSource build callback noFallback unit 0 1 warming refused

theorem state_changing_refusal_resumes_same_paid_source :
    paused.2.1.pending.isNone = true ∧ (match paused.2.2.computation.2 with | .paused _ => true | .done _ => false) = true ∧
      refused.2.1.pending.isSome = true ∧ refused.2.2.context = ([], true, []) ∧
      retried.2.2.context = ([[7]], true, [(1, [0])]) ∧
      retried.2.2.computation.1 = refused.2.2.computation.1 ∧
      retried.2.1.accepted = 1 := by decide

end Stateful


def programRun (program : List (Equation Nat)) : State :=
  let capturedWorld := OrderedDependencyStore.initial 948 (fun (_ : Fin 1) => program)
  Cursor.ProducerOccurrenceLog.ordinary
    (step (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision held.world held.authority Access.consume)
      build callback noFallback attachment sourceAuthority capturedWorld capturedWorld 0 held .consume 64)
    captureRow (fun _ => true) (fun _ => true) 16
    (initial build callback noFallback attachment capturedWorld 0 [] 0 () Nat 2 8)

theorem yield_failure_empty_collection_and_handoff_remain_distinct :
    pending.delivery.log.completed = false ∧ pending.delivery.log.rows = [] ∧
      (programRun BodyCallRun.missed).delivery.log.completed = true ∧
      (programRun BodyCallRun.missed).delivery.log.rows = [] ∧
      (programRun BodyCallRun.blank).delivery.log.rows.map (fun row => (row.2.1, identities row.2.2)) = [([[]], [0])] ∧
      (programRun BodyCallRun.alienAppend).delivery.log.completed = false ∧
      (programRun BodyCallRun.alienAppend).execution.map (fun execution =>
        match execution.mode with | .handoff _ => true | _ => false) = some true := by decide

namespace Observation

open Mettapedia.GSLT.Core.InferenceControl.Recording

abbrev Word := List (Cursor.ProducerOccurrenceLog.Accounting.Action Nat 2)
def first : Word := [.pump, .pump, .deliver 0 100]
def rest : Word := List.replicate 16 .pump ++ [.deliver 1 101]

def recorded := History.observe
  (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision held.world held.authority Access.consume)
  build callback noFallback attachment sourceAuthority world world 0 held .consume 64 (fun _ => true)
  (some (Prefix.initial 1)) (some 1) first start

def forgotten := History.observe
  (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision held.world held.authority Access.consume)
  build callback noFallback attachment sourceAuthority world world 0 held .consume 64 (fun _ => true)
  none recorded.2.1 rest recorded.2.2

theorem forgetting_keeps_actual_source_factors_and_paid_account :
    forgotten = (none,
      some (Cursor.ProducerOccurrenceLog.Accounting.count (actualStep 64) captureRow (fun _ => true) (fun _ => true)
        (first ++ rest) 1 start).2,
      Cursor.ProducerOccurrenceLog.Accounting.runActions (actualStep 64) captureRow (fun _ => true) (fun _ => true) (first ++ rest) start) :=
  History.forget_keeps_source_and_account
    (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision held.world held.authority Access.consume)
    build callback noFallback attachment sourceAuthority world world 0 held .consume 64 (fun _ => true)
    (Prefix.initial 1) 1 first rest start

end Observation

#print axioms yield_failure_empty_collection_and_handoff_remain_distinct
#print axioms Observation.forgetting_keeps_actual_source_factors_and_paid_account

#print axioms shared_outer_failed_and_equal_alternatives
#print axioms independent_delivery_and_cancel_keep_existing_branch_factors
#print axioms refusal_zero_and_acknowledgment_keep_the_actual_loan
#print axioms scoped_readout_excludes_shared_prefix_and_rejects_sibling_capture
#print axioms Stateful.state_changing_refusal_resumes_same_paid_source

end Controls

end BodyCallShared.Weighted


namespace BodyCallWeighted.Authored

open Mettapedia.Algebra.SharedCoefficientLedger
open Mettapedia.GSLT.Core.WeightedMuScheduler
open Cursor.Fold.OwnedSequence.CallbackBoundary
variable {Input Output Weight Context : Type} [Semiring Weight]
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)
    (attachment : BodyCall.WeightedSource.Attachment Input Output Weight)
local notation "M" => Compact.Attachment.SparseProvider construct callbackConstruct fallback (selection attachment)
local notation "C" => (BodyCallProtocol.client (Item := Input) (Value := Output))
local notation "Packet" => Cursor.Packet M C (⟨()⟩ : ULift Unit)
local notation "Outcome" => Cursor.Outcome M C (⟨()⟩ : ULift Unit)
local notation "Returned" => Cursor.Finished M (Return := fun _ _ => BodyCall.Move Input Output) (⟨()⟩ : ULift Unit)
local notation "Owned" => Compact.Attachment.OwnedState construct callbackConstruct fallback (selection attachment)
  (Context := List (BodyCall.WeightedSource.Row Output Weight) × Context)
local notation "Call" => Compact.Attachment.Call construct callbackConstruct fallback (selection attachment)
  (Context := List (BodyCall.WeightedSource.Row Output Weight) × Context)

namespace Controls

open _root_.Mettapedia.Machines.SourceProducerCardinality.BodyCallWeighted.Controls (build callback noFallback)

abbrev SourceAttachment := BodyCall.WeightedSource.Attachment Nat Nat Nat

def branches : SourceAttachment := fun ordinal _ _ _ =>
  some (if ordinal = 0 then 2 else if ordinal = 1 then 11 else if ordinal = 2 then 3 else 5)

def cartesian : SourceAttachment := fun ordinal _ _ _ =>
  some (if ordinal = 0 then 2 else if ordinal = 1 then 3 else 5)

def accepted (attachment : SourceAttachment)
    (program : List (Equation Nat)) (items : List Nat) :=
  Compact.Attachment.resumeCallSource build callback noFallback (selection attachment) 64 32
    (reader build callback noFallback attachment (fun (_ : Unit) _ => (true, ())))
    (Compact.Attachment.openCall build callback noFallback (selection attachment) program items 0 ([], ()))

def equalBranches := accepted branches BodyCallShared.Weighted.Controls.authored [0]

/-- The independently authored meaning and actual completed callback agree;
failed and alternative firings cannot become a global branch multiplier. -/
theorem duplicate_answers_exclude_failed_and_sibling_factors :
    equalBranches.2.2.context.2.1 = [([7], [2, 3]), ([7], [2, 5])] ∧
      BodyCall.WeightedSource.source build callback branches BodyCallShared.Weighted.Controls.authored [0] 0 =
        [([7], [2, 3]), ([7], [2, 5])] ∧
      Compact.Attachment.complete build callback noFallback (selection branches) equalBranches = true ∧
      (stateView build callback noFallback branches equalBranches.2.2.computation.2).nextOrdinal = 4 ∧
      equalBranches.2.2.context.2.1 ≠ [([7], [2, 11, 3, 5]), ([7], [2, 11, 3, 5])] := by decide

def recursive := accepted cartesian BodyCallWeighted.Controls.cartesian [0]

/-- Left and right recursive calls contribute in authored Cartesian order.
The retained result rejects a permuted factor word even when scalar products coincide. -/
theorem recursive_cartesian_order_is_not_a_commutative_reordering :
    recursive.2.2.context.2.1 =
      [([18, 7], [2, 3, 3]), ([18, 7], [2, 3, 5]), ([18, 7], [2, 5, 3]), ([18, 7], [2, 5, 5])] ∧
      BodyCall.WeightedSource.source build callback cartesian BodyCallWeighted.Controls.cartesian [0] 0 =
        recursive.2.2.context.2.1 ∧
      recursive.2.2.context.2.1 ≠
        [([18, 7], [3, 2, 3]), ([18, 7], [3, 2, 5]), ([18, 7], [5, 2, 3]), ([18, 7], [5, 2, 5])] := by decide

def zero : SourceAttachment := fun _ _ _ _ => some 0
def sparse : SourceAttachment := fun ordinal _ _ _ => if ordinal = 0 then none else some 1

def equalProgram : List (Equation Nat) :=
  [⟨⟨.any, .any⟩, false, .singleton 7⟩, ⟨⟨.any, .any⟩, false, .singleton 7⟩]

def zeroResult := accepted zero BodyCallRun.blank []
def sparseResult := accepted sparse equalProgram []

theorem zero_unit_and_absence_preserve_distinct_occurrences :
    zeroResult.2.2.context.2.1 = [([], [0])] ∧
      Compact.Attachment.complete build callback noFallback (selection zero) zeroResult = true ∧
      sparseResult.2.2.context.2.1 = [([7], []), ([7], [1])] ∧
      sparseResult.2.2.context.2.1.map (fun row => (row.1, row.2.prod)) = [([7], 1), ([7], 1)] ∧
      (admit build callback noFallback zero .direct .singleValue BodyCallRun.blank [] 0 zeroResult).1 = some [([], [0])] ∧
      (admit build callback noFallback sparse .direct .singleValue equalProgram [] 0 sparseResult).1 = none := by decide

def committedFailure : List (Equation Nat) :=
  [⟨⟨.any, .any⟩, true, .mapHead (.singleton 9)⟩, ⟨⟨.any, .any⟩, false, .singleton 7⟩]

def committedResult := accepted branches committedFailure []

theorem committed_failure_is_completed_empty_not_zero_weight_success :
    committedResult.2.2.context.2.1 = [] ∧
      BodyCall.WeightedSource.source build callback branches committedFailure [] 0 = [] ∧
      Compact.Attachment.complete build callback noFallback (selection branches) committedResult = true ∧
      (stateView build callback noFallback branches committedResult.2.2.computation.2).nextOrdinal = 1 ∧
      zeroResult.2.2.context.2.1 ≠ committedResult.2.2.context.2.1 := by decide

def warming (ready : Bool) (_ : Compact.Attachment.SparseReturned build callback noFallback (selection branches)) :=
  (ready, true)

def refused := Compact.Attachment.resumeCallSource build callback noFallback (selection branches) 64 1
  (reader build callback noFallback branches warming)
  (Compact.Attachment.openCall build callback noFallback (selection branches)
    BodyCallShared.Weighted.Controls.authored [0] 0 ([], false))

def retried := Compact.Attachment.resumeCallSource build callback noFallback (selection branches) 0 1
  (reader build callback noFallback branches warming) refused

def completed := Compact.Attachment.resumeCallSource build callback noFallback (selection branches) 64 8
  (reader build callback noFallback branches warming) retried

theorem stateful_refusal_and_zero_source_retry_preserve_the_weighted_loan :
    refused.2.1.pending.isSome = true ∧ refused.2.2.context.2 = ([], true) ∧
      (readout build callback noFallback branches refused).1 = none ∧
      retried.2.2.context.2 = ([([7], [2, 3])], true) ∧
      retried.2.2.computation.1 = refused.2.2.computation.1 ∧
      Compact.Attachment.resumeCallSource build callback noFallback (selection branches) 0 0
        (reader build callback noFallback branches warming) refused = refused ∧
      completed.2.2.context.2.1 = [([7], [2, 3]), ([7], [2, 5])] ∧
      (readout build callback noFallback branches completed).1 = some [([7], [2, 3]), ([7], [2, 5])] := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, by decide, by decide⟩
  exact resumeCall_zero _ _ _ _

#print axioms duplicate_answers_exclude_failed_and_sibling_factors
#print axioms recursive_cartesian_order_is_not_a_commutative_reordering
#print axioms zero_unit_and_absence_preserve_distinct_occurrences
#print axioms committed_failure_is_completed_empty_not_zero_weight_success
#print axioms stateful_refusal_and_zero_source_retry_preserve_the_weighted_loan

end Controls

end BodyCallWeighted.Authored


namespace BodyCallShared.Weighted.Authored

open Mettapedia.Algebra.SharedCoefficientLedger
open Cursor.Fold.OwnedSequence.CallbackBoundary
open Mettapedia.GSLT.Contracts
open _root_.CategoryTheory
variable {Input Output Weight Context : Type} [Semiring Weight]
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)
    (attachment : BodyCall.WeightedSource.Attachment Input Output Weight)
local notation "selected" => BodyCallWeighted.Authored.selection attachment
local notation "Call" => Weighted.Call construct callbackConstruct fallback selected (Context := Context)
local notation "Borrowed" => Weighted.Borrowed construct callbackConstruct fallback selected
local notation "Source" => BodyCallWeighted.Authored.stateView construct callbackConstruct fallback attachment
local notation "View" => BodyCallWeighted.Authored.unaccepted construct callbackConstruct fallback attachment
variable {size : Nat} (before : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
variable {World : Type} [Category.{0} World] (authority : IndexedAuthority.{0, 0, 0} World)
    (current : OrderedDependencyStore.Store (Equation Output) size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)] (quantum : Nat)
local notation "sourceStep" => Weighted.step construct callbackConstruct fallback selected authority before current reader point required quantum
variable {Owner : Type} {clients : Nat}
local notation "Cfg" => Weighted.Configuration construct callbackConstruct fallback selected
  (Context := Context) (size := size) Owner clients
local notation "sourceCapture" => Weighted.capture construct callbackConstruct fallback selected
local notation "Execution" => Cursor.ProducerOccurrenceLog.Execution Call Borrowed Empty
  (Weighted.Loan construct callbackConstruct fallback selected)

namespace Controls

open _root_.Mettapedia.Machines.SourceProducerCardinality.BodyCallWeighted.Controls (build callback noFallback)
open _root_.Mettapedia.Machines.SourceProducerCardinality.BodyCallShared.Weighted.Controls
  (authored actualStep captureRow start pending captured acknowledged otherFinished)

abbrev sourceAttachment := BodyCallWeighted.Authored.Controls.branches

def expected := BodyCall.WeightedSource.source build callback sourceAttachment authored [0] 0

def actions : List (Cursor.ProducerOccurrenceLog.Accounting.Action Nat 2) := List.replicate 16 .pump

def produced := Cursor.ProducerOccurrenceLog.Accounting.runActions (actualStep 64) captureRow
  (fun _ => true) (fun _ => true) actions start

/-- Existing action execution, independent delivery and cancellation all retain
one captured semantic branch word, including the common outer occurrence. -/
theorem actual_shared_storage_and_cancellation_match_weighted_source :
    produced.delivery.log.rows.flatMap storedRows = expected ∧
      produced.delivery.log.completed = true ∧
      otherFinished.delivery.log.rows.flatMap storedRows = expected ∧
      expected = [([7], [2, 3]), ([7], [2, 5])] ∧
      produced.delivery.log.rows.map (fun row => identities row.2.2) = [[0, 2], [0, 3]] ∧
      expected ≠ [([7], [2, 2, 3]), ([7], [2, 2, 5])] := by decide

/-- Outer pending capture and the retained source loan describe the same row.
Capture, refusal and acknowledgment do not duplicate its weighted occurrence. -/
theorem pending_capture_and_acknowledgment_count_the_same_loan_once :
    pending.delivery.log.rows = [] ∧
      pending.execution.map (fun execution => view build callback noFallback sourceAttachment pending execution.producer) = some expected ∧
      captured.execution.map (fun execution => view build callback noFallback sourceAttachment captured execution.producer) = some expected ∧
      acknowledged.execution.map (fun execution => view build callback noFallback sourceAttachment acknowledged execution.producer) = some expected ∧
      captured.delivery.log.rows.flatMap storedRows = [([7], [2, 3])] ∧
      (Cursor.ProducerOccurrenceLog.pump (actualStep 64) captureRow (fun _ => false) (fun _ => true) pending).1 = .admissionRefused ∧
      pending.execution.map (fun execution => view build callback noFallback sourceAttachment pending execution.producer) ≠
        some [([7], [2, 3]), ([7], [2, 3]), ([7], [2, 5])] := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, rfl, by decide⟩

#print axioms actual_shared_storage_and_cancellation_match_weighted_source
#print axioms pending_capture_and_acknowledgment_count_the_same_loan_once

end Controls

end BodyCallShared.Weighted.Authored


namespace BodyCallShared.Handoff

open Cursor.ProducerOccurrenceLog
open Cursor.Fold.OwnedSequence.CallbackBoundary
open Mettapedia.GSLT.Contracts
open _root_.CategoryTheory
variable {Input Output Context Owner : Type} {clients size : Nat}
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)
local notation "Call" => BodyCallShared.Call construct callbackConstruct fallback (Context := Context)
local notation "Loan" => BodyCallShared.Loan construct callbackConstruct fallback
local notation "Borrowed" => BodyCallShared.Borrowed construct callbackConstruct fallback
local notation "Cfg" => BodyCallShared.Configuration construct callbackConstruct fallback
  (Context := Context) (size := size) Owner clients
variable {World : Type} [Category.{0} World] (authority : IndexedAuthority.{0, 0, 0} World)
    (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]
local notation "sourceStep" => BodyCallShared.step construct callbackConstruct fallback authority before current reader point required
local notation "sourceCapture" => BodyCallShared.capture construct callbackConstruct fallback
local notation "gate" => compatible authority current reader point required

namespace Controls

open BodyCallShared.Controls (world changed unrelated held revoked sourceAuthority)

abbrev State := BodyCallShared.Controls.State
abbrev OwnedCall := BodyCallShared.Call Nat.add (fun _ left _ => left) (fun _ _ => []) (Context := Unit)
def accept := BodyCallShared.accept Nat.add (fun _ left _ => left) (fun _ _ => []) (Context := Unit)
def refuse := BodyCallShared.refuse Nat.add (fun _ left _ => left) (fun _ _ => []) (Context := Unit)

def ordinary (consumer : Unit → BodyCallShared.Loan Nat.add (fun _ left _ => left) (fun _ _ => []) → Bool × Unit)
    (call : OwnedCall) :=
  BodyCallAdmission.resume Nat.add (fun _ left _ => left) (fun _ _ => []) 64 1 consumer
    (BodyCallShared.charge Nat.add (fun _ left _ => left) (fun _ _ => []) _ _) call

def firstAccepted := ordinary accept BodyCallShared.Controls.initialCall
def secondHeld := ordinary refuse firstAccepted
def heldFirst := ordinary refuse BodyCallShared.Controls.initialCall

def transfer (call : OwnedCall) : State :=
  adopt Nat.add (fun _ left _ => left) (fun _ _ => []) world 8 call

def progress (current : OrderedDependencyStore.Store (Equation Nat) 3)
    (point : IndexedAuthority.Point sourceAuthority) (quantum : Nat)
    (actions : List (Accounting.Action Nat 2)) (state : State) :=
  advance (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision
    point.world point.authority Access.consume)
    Nat.add (fun _ left _ => left) (fun _ _ => []) sourceAuthority world current 0 point .consume
    quantum (fun _ => true) actions state

def currentGate (current : OrderedDependencyStore.Store (Equation Nat) 3)
    (point : IndexedAuthority.Point sourceAuthority) :=
  compatible (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision
    point.world point.authority Access.consume) sourceAuthority current 0 point .consume

def secondAdopted := transfer secondHeld
def secondCaptured := progress world held 0 [.pump] secondAdopted
def suffixDone := progress world held 64 (List.replicate 16 .pump) secondCaptured

theorem ordinary_pending_handoff_keeps_origin_prefix_and_paid_cut :
    firstAccepted.2.2.context.1 = [[7]] ∧ secondHeld.2.1.pending.isSome = true ∧
      (pending secondAdopted).map (·.1) = some 1 ∧
      secondAdopted.execution.map (·.producer) = some secondHeld ∧
      (release Nat.add (fun _ left _ => left) (fun _ _ => []) secondAdopted).1 = some secondHeld ∧
      progress world held 0 [] secondAdopted = secondAdopted :=
  ⟨by decide, by decide, by decide, rfl, rfl, rfl⟩

theorem capture_and_handback_do_not_reissue_or_repoll :
    secondCaptured.delivery.log.rows = [(1, [[7]])] ∧
      (release Nat.add (fun _ left _ => left) (fun _ _ => []) secondCaptured).1.map
        (fun call => (call.2.1.pending.isNone, call.2.1.accepted, call.2.2.context.1, call.2.2.computation.1)) =
        some (true, 2, [[7], [7]], secondHeld.2.2.computation.1) ∧
      (release Nat.add (fun _ left _ => left) (fun _ _ => []) secondCaptured).2.delivery = secondCaptured.delivery ∧
      suffixDone.delivery.log.rows = [(1, [[7]])] ∧ suffixDone.delivery.log.completed = true :=
  ⟨by decide, by decide, rfl, by decide, by decide⟩

theorem refusal_and_zero_source_retry_keep_the_same_loan :
    pump (BodyCallShared.Controls.actualStep world held 0)
      (BodyCallShared.capture Nat.add (fun _ left _ => left) (fun _ _ => []))
      (fun _ => false) (currentGate world held) secondAdopted = (.admissionRefused, secondAdopted) ∧
      secondCaptured.execution.map (fun execution => execution.producer.2.2.computation) =
        secondAdopted.execution.map (fun execution => execution.producer.2.2.computation) ∧
      secondCaptured.execution.map (fun execution => execution.producer.1) =
        secondAdopted.execution.map (fun execution => execution.producer.1) :=
  ⟨rfl, rfl, by decide⟩

def both := progress world held 64 (List.replicate 16 .pump) (transfer heldFirst)
def firstReader := deliver (currentGate world held) both 0 100
def oneCancelled := retireConsumer firstReader.2 0
def otherReader := deliver (currentGate world held) oneCancelled 1 101

theorem independent_readers_keep_equal_occurrences_after_cancellation :
    both.delivery.log.rows = [(0, [[7]]), (1, [[7]])] ∧
      firstReader.1 = .observed (.answer 0 (0, [[7]])) ∧
      otherReader.1 = .observed (.answer 0 (0, [[7]])) ∧
      (deliver (currentGate world held) otherReader.2 1 101).1 = .observed (.answer 1 (1, [[7]])) ∧
      otherReader.2.execution = both.execution ∧
      (deliver (currentGate world held) oneCancelled 0 100).1 = .observed .cancelled :=
  ⟨by decide, by decide, by decide, by decide, rfl, by decide⟩

theorem current_source_and_permission_gate_progress_and_buffered_delivery :
    progress changed held 64 [.pump] secondAdopted = secondAdopted ∧
      progress world revoked 64 [.pump] secondAdopted = secondAdopted ∧
      progress unrelated held 0 [.pump] secondAdopted = secondCaptured ∧
      deliver (currentGate changed held) both 1 101 = (.contextRefused, both) ∧
      deliver (currentGate world revoked) both 1 101 = (.contextRefused, both) ∧
      (release Nat.add (fun _ left _ => left) (fun _ _ => []) both).1.map (fun call =>
        (BodyCallAdmission.complete Nat.add (fun _ left _ => left) (fun _ _ => []) call, call.2.2.context.1)) =
        some (true, [[7], [7]]) :=
  ⟨rfl, rfl, rfl, rfl, rfl, by decide⟩

def closedCall (authored : List (Equation Nat)) : OwnedCall :=
  BodyCallAdmission.resume Nat.add (fun _ left _ => left) (fun _ _ => []) 64 8 accept
    (BodyCallShared.charge Nat.add (fun _ left _ => left) (fun _ _ => []) _ _)
    (BodyCallAdmission.openCall Nat.add (fun _ left _ => left) (fun _ _ => []) authored ([] : List Nat) 0 ())

theorem terminal_empty_value_failure_and_yield_are_separate :
    (closedCall BodyCallRun.blank).2.2.context.1 = [[]] ∧
      (closedCall BodyCallRun.missed).2.2.context.1 = [] ∧
      BodyCallAdmission.complete Nat.add (fun _ left _ => left) (fun _ _ => []) (closedCall BodyCallRun.blank) = true ∧
      BodyCallAdmission.complete Nat.add (fun _ left _ => left) (fun _ _ => []) (closedCall BodyCallRun.missed) = true ∧
      BodyCallAdmission.complete Nat.add (fun _ left _ => left) (fun _ _ => []) secondHeld = false ∧
      (release Nat.add (fun _ left _ => left) (fun _ _ => []) (transfer (closedCall BodyCallRun.blank))).1 =
        some (closedCall BodyCallRun.blank) :=
  ⟨by decide, by decide, by decide, by decide, by decide, rfl⟩

#print axioms ordinary_pending_handoff_keeps_origin_prefix_and_paid_cut
#print axioms capture_and_handback_do_not_reissue_or_repoll
#print axioms refusal_and_zero_source_retry_keep_the_same_loan
#print axioms independent_readers_keep_equal_occurrences_after_cancellation
#print axioms current_source_and_permission_gate_progress_and_buffered_delivery
#print axioms terminal_empty_value_failure_and_yield_are_separate

end Controls

end BodyCallShared.Handoff


namespace BodyCallShared.Weighted.Authored.Handoff

open Mettapedia.Algebra.SharedCoefficientLedger
open Cursor.ProducerOccurrenceLog
open Cursor.Fold.OwnedSequence.CallbackBoundary
open Mettapedia.GSLT.Contracts
open _root_.CategoryTheory
variable {Input Output Weight Context Owner : Type} [Semiring Weight] {clients size : Nat}
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)
    (attachment : BodyCall.WeightedSource.Attachment Input Output Weight)
local notation "selected" => BodyCallWeighted.Authored.selection attachment
local notation "Row" => BodyCall.WeightedSource.Row Output Weight
local notation "Call" => Weighted.Call construct callbackConstruct fallback selected (Context := List Row × Context)
local notation "Loan" => Weighted.Loan construct callbackConstruct fallback selected
local notation "Borrowed" => Weighted.Borrowed construct callbackConstruct fallback selected
local notation "Cfg" => Weighted.Configuration construct callbackConstruct fallback selected
  (Context := List Row × Context) (size := size) Owner clients
local notation "Source" => BodyCallWeighted.Authored.stateView construct callbackConstruct fallback attachment
local notation "Residual" => Authored.residual construct callbackConstruct fallback attachment
local notation "loanRows" => Authored.loanRows construct callbackConstruct fallback attachment
local notation "storedRows" => Authored.storedRows (Output := Output) (Weight := Weight)
variable {World : Type} [Category.{0} World] (authority : IndexedAuthority.{0, 0, 0} World)
    (before current : OrderedDependencyStore.Store (Equation Output) size) (reader : Fin size)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [permissionDecidable : Decidable (FrameUpdate point.authority required)]
local notation "gate" => BodyCallShared.Handoff.compatible authority current reader point required
local notation "sourceStep" => step construct callbackConstruct fallback attachment authority before current reader point required
local notation "sourceCapture" => Weighted.capture construct callbackConstruct fallback selected
local notation "View" => Authored.view construct callbackConstruct fallback attachment

namespace Controls

open _root_.Mettapedia.Machines.SourceProducerCardinality.BodyCallWeighted.Controls (build callback noFallback)
open BodyCallAdmission.CurrentAuthority.Controls (held revoked)
abbrev sourceAuthority := BodyCallShared.Controls.sourceAuthority
abbrev authored := BodyCallShared.Weighted.Controls.authored
abbrev world := BodyCallShared.Weighted.Controls.world
open Mettapedia.GSLT.Core.InferenceControl.Recording

abbrev profile := BodyCallWeighted.Authored.Controls.branches
abbrev chosen := BodyCallWeighted.Authored.selection profile
abbrev ControlCall := Weighted.Call build callback noFallback chosen
  (Context := List (BodyCall.WeightedSource.Row Nat Nat) × Unit)
abbrev State := Weighted.Configuration build callback noFallback chosen
  (Context := List (BodyCall.WeightedSource.Row Nat Nat) × Unit) (size := 1) Nat 2

def initialCall : ControlCall := BodyCallWeighted.Compact.Attachment.openCall build callback noFallback chosen authored [0] 0 ([], ())
def firstAccepted := resume build callback noFallback profile 64 1 (accept build callback noFallback profile) initialCall
def secondHeld := resume build callback noFallback profile 64 1 (refuse build callback noFallback profile) firstAccepted
def heldFirst := resume build callback noFallback profile 64 1 (refuse build callback noFallback profile) initialCall

def transfer (call : ControlCall) : State := adopt build callback noFallback profile world 8 call

def progress (current : OrderedDependencyStore.Store (Equation Nat) 1)
    (point : IndexedAuthority.Point sourceAuthority) (quantum : Nat)
    (actions : List (Accounting.Action Nat 2)) (state : State) :=
  advance (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision
    point.world point.authority Access.consume)
    build callback noFallback profile sourceAuthority world current 0 point .consume quantum (fun _ => true) actions state

def currentGate (current : OrderedDependencyStore.Store (Equation Nat) 1)
    (point : IndexedAuthority.Point sourceAuthority) :=
  BodyCallShared.Handoff.compatible (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision
    point.world point.authority Access.consume) sourceAuthority current 0 point .consume

def observe (bound : Nat) (actions : List (Accounting.Action Nat 2)) (state : State) :=
  History.observe (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision held.world held.authority Access.consume)
    build callback noFallback profile sourceAuthority world world 0 held .consume 64 (fun _ => true)
    (some (Prefix.initial bound)) (some 1) actions state

def seed := transfer secondHeld
def captured := progress world held 0 [.pump] seed
def acknowledged := progress world held 0 [.pump] captured
def finished := progress world held 64 (List.replicate 16 .pump) acknowledged

def factorView (state : State) := state.delivery.log.rows.map (fun row =>
  (row.1, row.2.1, identities row.2.2, Mettapedia.Algebra.SharedCoefficientLedger.denote row.2.2))

theorem nonfresh_handoff_keeps_original_weighted_prefix_and_loan :
    firstAccepted.2.2.context.2.1 = [([7], [2, 3])] ∧
      (pending seed).map (fun loan => (loan.1, identities loan.2.2.2.val.loan)) = some (1, [0, 3]) ∧
      factorView captured = [(1, [[7]], [0, 3], 10)] ∧
      (release build callback noFallback profile seed).1 = some secondHeld :=
  ⟨by decide, by decide, by decide, rfl⟩

theorem acknowledgment_and_handback_keep_source_factors_without_global_fold :
    acknowledged.execution.map (fun execution => execution.producer.2.2.context.2.1) =
        some [([7], [2, 3]), ([7], [2, 5])] ∧
      captured.execution.map (fun execution => execution.producer.2.2.computation.1) =
        acknowledged.execution.map (fun execution => execution.producer.2.2.computation.1) ∧
      captured.execution.map (fun execution => BodyCallWeighted.Authored.stateView build callback noFallback profile execution.producer.2.2.computation.2) =
        acknowledged.execution.map (fun execution => BodyCallWeighted.Authored.stateView build callback noFallback profile execution.producer.2.2.computation.2) ∧
      (release build callback noFallback profile captured).1 = acknowledged.execution.map (·.producer) ∧
      factorView finished = [(1, [[7]], [0, 3], 10)] ∧
      (release build callback noFallback profile finished).1.map
        (fun call => (BodyCallWeighted.Compact.Attachment.complete build callback noFallback chosen call, call.2.2.context.2.1)) =
        some (true, [([7], [2, 3]), ([7], [2, 5])]) :=
  ⟨by decide, rfl, rfl, rfl, by decide, by decide⟩

def both := progress world held 64 (List.replicate 16 .pump) (transfer heldFirst)
def left := deliver (currentGate world held) both 0 100
def cancelled := retireConsumer left.2 0
def right := deliver (currentGate world held) cancelled 1 101

theorem equal_payloads_share_outer_identity_but_keep_distinct_branch_factors :
    factorView both = [(0, [[7]], [0, 2], 6), (1, [[7]], [0, 3], 10)] ∧
      both.delivery.log.rows[0]!.2.2.head? = both.delivery.log.rows[1]!.2.2.head? ∧
      right.1 = left.1 ∧ right.2.execution = both.execution ∧
      (deliver (currentGate world held) right.2 1 101).1 =
        .observed (.answer 1 (1, [[7]], [⟨0, 0, 2⟩, ⟨3, 3, 5⟩])) ∧
      Cursor.SharedOccurrenceLog.unread cancelled.delivery.log 0 = [] :=
  ⟨by decide, by decide, rfl, rfl, by decide, by decide⟩

def word : List (Accounting.Action Nat 2) := [.pump, .pump, .deliver 0 100, .deliver 1 101]
def recorded := observe 1 word seed

def forgotten := History.observe
  (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision held.world held.authority Access.consume)
  build callback noFallback profile sourceAuthority world world 0 held .consume 64 (fun _ => true)
  none recorded.2.1 (List.replicate 16 .pump) recorded.2.2

theorem bounded_history_distinguishes_admission_delivery_and_source_work :
    recorded.1.map (fun diary => (diary.items.length, diary.omitted)) = some (1, 2) ∧
      recorded.2.1.map (fun account => (Multiplicative.toAdd account.1, Multiplicative.toAdd account.2)) = some (1, 2) ∧
      recorded.2.2.execution.map (fun execution => execution.producer.2.2.computation.1) =
        seed.execution.map (fun execution => execution.producer.2.2.computation.1) ∧
      forgotten.1 = none ∧ factorView forgotten.2.2 = factorView finished ∧
      forgotten.2.2.execution = finished.execution :=
  ⟨by decide, by decide, rfl, rfl, by decide, rfl⟩

def late := observe 0 [.pump, .deliver 1 101] captured

theorem late_recording_omits_prior_admission_and_retains_the_weighted_residual :
    late.1.map (fun diary => (diary.items.length, diary.omitted)) = some (0, 1) ∧
      late.2.2.execution = recorded.2.2.execution ∧
      factorView late.2.2 = factorView captured ∧
      (release build callback noFallback profile late.2.2).1.map (fun call => call.2.2.context.2.1) =
        some [([7], [2, 3]), ([7], [2, 5])] :=
  ⟨by decide, rfl, by decide, by decide⟩

def changed := OrderedDependencyStore.appendOwn world 0 [⟨⟨.any, .any⟩, false, .singleton 8⟩]

theorem refusal_currentness_and_mode_checks_keep_the_same_earned_weighted_cut :
    pump (step (permissionDecidable := BodyCallAdmission.CurrentAuthority.Controls.revocationDecision held.world held.authority Access.consume)
      build callback noFallback profile sourceAuthority world world 0 held .consume 0)
      (Weighted.capture build callback noFallback chosen) (fun _ => false) (currentGate world held) seed = (.admissionRefused, seed) ∧
      progress changed held 64 [.pump] seed = seed ∧
      progress world revoked 64 [.pump] seed = seed ∧
      deliver (currentGate changed held) both 1 101 = (.contextRefused, both) ∧
      (release build callback noFallback profile finished).1.map
        (fun call => (BodyCallWeighted.Authored.admit build callback noFallback profile .direct .singleValue authored [0] 0 call).1) = some none ∧
      (release build callback noFallback profile seed).1.map
        (fun call => BodyCallWeighted.Compact.Attachment.complete build callback noFallback chosen call) = some false :=
  ⟨rfl, rfl, rfl, rfl, by decide, by decide⟩

#print axioms nonfresh_handoff_keeps_original_weighted_prefix_and_loan
#print axioms acknowledgment_and_handback_keep_source_factors_without_global_fold
#print axioms equal_payloads_share_outer_identity_but_keep_distinct_branch_factors
#print axioms bounded_history_distinguishes_admission_delivery_and_source_work
#print axioms late_recording_omits_prior_admission_and_retains_the_weighted_residual
#print axioms refusal_currentness_and_mode_checks_keep_the_same_earned_weighted_cut

end Controls

end BodyCallShared.Weighted.Authored.Handoff


namespace PreparationControls

private def constant (body : Code Nat) : Code Nat :=
  DecisionTree.code ⟨body, body, body, body⟩

def committedPrefix : List (Equation Nat) :=
  [⟨⟨.any, .any⟩, true, .singleton 7⟩,
   ⟨⟨.any, .any⟩, false, .unsupported⟩]

/-- Selected bodies and whole-source cursor support have different scopes. -/
theorem committed_body_compiles_while_discarded_source_is_unsupported :
    (Preparation.prepare committedPrefix).supported = false ∧
    Preparation.strictCode (Preparation.prepare committedPrefix) = some (constant (.singleton 7)) ∧
    Preparation.optionalTree (Preparation.prepare committedPrefix) =
      some ⟨some (.singleton 7), some (.singleton 7), some (.singleton 7), some (.singleton 7)⟩ ∧
    ∀ (items : List Nat) parameter interface,
      selectWorker committedPrefix items parameter interface = .directCode (constant (.singleton 7)) :=
  ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩

theorem duplicate_equations_keep_ambiguity_and_both_equal_occurrences :
    (Preparation.prepare Controls.duplicates).choices.branch ⟨false, false⟩ = none ∧
    Preparation.strictCode (Preparation.prepare Controls.duplicates) = none ∧
    Preparation.optionalTree (Preparation.prepare Controls.duplicates) = none ∧
    (match selectWorker Controls.duplicates ([] : List Nat) 0 with
      | .bodyCall .nonemptyProducer => true | _ => false) = true ∧
    executeWorker Nat.add (fun _ left _ => left) Controls.duplicates [] 0
      (selectWorker Controls.duplicates ([] : List Nat) 0) = some [[7], [7]] := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  rw [selected_worker_refines_source]
  rfl

theorem matched_failure_absence_and_returned_empty_remain_distinct :
    noMatch ⟨false, false⟩ Controls.failingMatch = false ∧
    Preparation.optionalBranch (Preparation.prepare Controls.failingMatch) ⟨false, false⟩ =
      some (some .callTail) ∧
    Preparation.optionalBranch (Preparation.prepare Controls.failingMatch) ⟨true, false⟩ =
      some none ∧
    source Nat.add (fun _ left _ => left) Controls.failingMatch ([] : List Nat) 0 = [] ∧
    source Nat.add (fun _ left _ => left)
      [⟨⟨.any, .any⟩, false, .empty⟩] ([] : List Nat) 0 = [[]] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

def committedFailure : List (Equation Nat) :=
  [⟨⟨.any, .any⟩, true, .callTail⟩, ⟨⟨.any, .any⟩, false, .singleton 9⟩]

theorem committed_failure_never_retargets_to_a_later_success :
    Preparation.strictCode (Preparation.prepare committedFailure) = none ∧
    Preparation.optionalBranch (Preparation.prepare committedFailure) ⟨false, false⟩ =
      some (some .callTail) ∧
    executeWorker Nat.add (fun _ left _ => left) committedFailure [] 0
      (selectWorker committedFailure ([] : List Nat) 0) = some [] :=
  ⟨rfl, rfl, rfl⟩

/-- Preparation inspects code, independently of the invocation's item values.
A value-only receiver still refuses the optional representation. -/
theorem optional_preparation_preserves_deferred_inputs_and_receiver :
    ∀ (items : List Nat) parameter,
      selectWorker OptionalControls.headProgram items parameter =
        .optionalCode ⟨none, some (.mapHead (.singleton 7)),
          none, some (.mapHead (.singleton 7))⟩ ∧
      ∀ tree, selectWorker OptionalControls.headProgram items parameter .singleValue ≠
        .optionalCode tree := by
  intro items parameter
  exact ⟨rfl, value_only_selector_refuses_optional _ _ _⟩

theorem recursive_preparation_and_current_source_validation :
    (∃ compiled, Preparation.strictCode (Preparation.prepare Controls.recursive) = some compiled ∧
      ∀ (items : List Nat) parameter,
        selectWorker Controls.recursive items parameter = .directCode compiled) ∧
    OrderedDependencyStore.checkRead
      (OrderedDependencyStore.appendOwn Controls.recursiveWorld 0
        [⟨⟨.any, .any⟩, false, .singleton 7⟩])
      (OrderedDependencyStore.readStamp Controls.recursiveWorld 0) = false ∧
    (match checkedWorker Controls.recursiveWorld
        (OrderedDependencyStore.appendOwn Controls.recursiveWorld 0
          [⟨⟨.any, .any⟩, false, .singleton 7⟩]) 0 ([] : List Nat) 0 with
      | .bodyCall .producer => true | _ => false) = true := by
  obtain ⟨compiled, built, selected⟩ := Controls.recursive_worker_is_constructed
  exact ⟨⟨compiled, by simpa only [Preparation.strictCode_eq] using built, selected⟩,
    Controls.added_equation_refuses_old_direct_code⟩

#print axioms committed_body_compiles_while_discarded_source_is_unsupported
#print axioms duplicate_equations_keep_ambiguity_and_both_equal_occurrences
#print axioms matched_failure_absence_and_returned_empty_remain_distinct
#print axioms committed_failure_never_retargets_to_a_later_success
#print axioms optional_preparation_preserves_deferred_inputs_and_receiver
#print axioms recursive_preparation_and_current_source_validation

end PreparationControls

namespace AdmissionControls

/-- The same current class can have different future answer multiplicities. -/
def recursiveChoice : List (Equation Nat) :=
  [⟨⟨.empty, .any⟩, false, .singleton 7⟩,
   ⟨⟨.cons, .any⟩, false, .ifZero .callTail .callPredecessor⟩,
   ⟨⟨.cons, .zero⟩, false, .singleton 9⟩]

theorem equal_current_shapes_do_not_probe_distinct_recursive_futures :
    shape ([0] : List Nat) 1 = shape ([0, 1] : List Nat) 1 ∧
    sourceGrade recursiveChoice ([0] : List Nat) 1 = .one ∧
    sourceGrade recursiveChoice ([0, 1] : List Nat) 1 = .nonempty ∧
    source Nat.add (fun _ left _ => left) recursiveChoice [0] 1 = [[7]] ∧
    source Nat.add (fun _ left _ => left) recursiveChoice [0, 1] 1 = [[7], [9]] ∧
    (Preparation.prepare recursiveChoice).bounds.branch (shape ([0] : List Nat) 1) = .any ∧
    selectWorker recursiveChoice ([0] : List Nat) 1 = .bodyCall .producer ∧
    selectWorker recursiveChoice ([0, 1] : List Nat) 1 = .bodyCall .producer :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def knownAfterCall : List (Equation Nat) :=
  [⟨⟨.any, .any⟩, false, .callTail⟩,
   ⟨⟨.any, .any⟩, false, .singleton 7⟩]

/-- A known answer establishes nonemptiness even beside an unknown call.
Equal payloads remain separate source occurrences. -/
theorem known_alternative_gives_a_useful_nonempty_producer :
    (Preparation.prepare knownAfterCall).bounds.branch ⟨true, false⟩ = .nonempty ∧
    selectWorker knownAfterCall ([0] : List Nat) 0 = .bodyCall .nonemptyProducer ∧
    executeWorker Nat.add (fun _ left _ => left) knownAfterCall [0] 0
      (selectWorker knownAfterCall ([0] : List Nat) 0) = some [[7], [7]] := by
  refine ⟨rfl, rfl, ?_⟩
  rw [selected_worker_refines_source]
  rfl

/-- Unknown recursion supplies no nonfailure guarantee; commit cannot borrow
a later known answer. Current guards can still establish immediate failure. -/
theorem recursive_unknown_does_not_license_success_or_ignore_commit :
    (Preparation.analyze (Code.callPredecessor : Code Nat)).bounds.branch ⟨true, false⟩ = .zero ∧
    (Preparation.analyze (Code.callPredecessor : Code Nat)).bounds.branch ⟨true, true⟩ = .any ∧
    (Preparation.prepare PreparationControls.committedFailure).bounds.branch ⟨true, false⟩ = .any ∧
    selectWorker PreparationControls.committedFailure ([0] : List Nat) 0 .singleValue =
      .bodyCall .producer ∧
    sourceGrade PreparationControls.committedFailure ([0] : List Nat) 0 = .zero ∧
    source Nat.add (fun _ left _ => left) PreparationControls.committedFailure [0] 0 = [] ∧
    ¬ ConventionAllows .nonemptyProducer
      (source Nat.add (fun _ left _ => left) PreparationControls.committedFailure [0] 0).length :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, by change ¬ 1 ≤ 0; decide⟩

#print axioms equal_current_shapes_do_not_probe_distinct_recursive_futures
#print axioms known_alternative_gives_a_useful_nonempty_producer
#print axioms recursive_unknown_does_not_license_success_or_ignore_commit

end AdmissionControls

namespace BodyCallWeighted.Authored.Publication

open Cursor.Fold.OwnedSequence.CallbackBoundary
variable {Input Output Weight Context Term Environment Consumer : Type} [Semiring Weight]
    (construct : Input → Output → Output)
    (callbackConstruct : Nat → Output → Output → Output)
    (fallback : List Input → Nat → List Output)
    (attachment : BodyCall.WeightedSource.Attachment Input Output Weight)
local notation "selected" => selection attachment
local notation "Row" => BodyCall.WeightedSource.Row Output Weight
local notation "Record" => Cursor.Fold.OwnedSequence.Returned Term Environment
local notation "SourceCall" => Compact.Attachment.Call construct callbackConstruct fallback selected
  (Context := List Row × Context)
local notation "Loan" => Compact.Attachment.SparseReturned construct callbackConstruct fallback selected
local notation "OpenReturn" => Record × (List Record × SourceCall)
local notation "Item" => Record ⊕ OpenReturn

namespace Controls

open _root_.Mettapedia.Machines.SourceProducerCardinality.BodyCallWeighted.Controls
  (build callback noFallback)

private def encode (row : BodyCall.WeightedSource.Row Nat Nat) :
    Cursor.Fold.OwnedSequence.Returned (BodyCall.WeightedSource.Row Nat Nat) Nat :=
  ⟨row, if row.2 = [2, 3] then 11 else 22, .completed, [row]⟩

private def observation (_ : Compact.Attachment.Call build callback noFallback
    (selection Authored.Controls.branches)
    (Context := List (BodyCall.WeightedSource.Row Nat Nat) × Unit)) :
    Cursor.Fold.OwnedSequence.Returned (BodyCall.WeightedSource.Row Nat Nat) Nat :=
  ⟨([99], []), 71, .completed, []⟩

/-- Equal answer values keep distinct coefficient words and complete records.
The finished-failure control is a zero-row bag, not one empty collection. -/
theorem actual_closed_records_and_zero_bag :
    (match reply build callback noFallback Authored.Controls.branches encode observation
        Authored.Controls.equalBranches with
      | .returned rows => some rows
      | _ => none) = some [encode ([7], [2, 3]), encode ([7], [2, 5])] ∧
    (match reply build callback noFallback Authored.Controls.branches encode observation
        Authored.Controls.committedResult with
      | .returned rows => some rows
      | _ => none) = some [] := by decide

private def unfinished := Compact.Attachment.resumeCallSource build callback noFallback
  (selection Authored.Controls.branches) 0 1
  (reader build callback noFallback Authored.Controls.branches (fun (_ : Unit) _ => (true, ())))
  (Compact.Attachment.openCall build callback noFallback (selection Authored.Controls.branches)
    BodyCallShared.Weighted.Controls.authored [0] 0 ([], ()))

theorem zero_source_grant_is_neither_closed_nor_an_observation :
    (match reply build callback noFallback Authored.Controls.branches encode observation unfinished with
      | .paused => false
      | _ => true) = false ∧
    Compact.Attachment.complete build callback noFallback (selection Authored.Controls.branches) unfinished = false := by
  decide

private def handoffProgram : List (Equation Nat) :=
  [⟨⟨.any, .any⟩, false, .singleton 7⟩, ⟨⟨.any, .any⟩, false, .unsupported⟩]

private def handedOff := Authored.Controls.accepted Authored.Controls.branches handoffProgram []

theorem actual_handoff_is_one_observation_with_earned_prefix :
    (match reply build callback noFallback Authored.Controls.branches encode observation handedOff with
      | .terminal (observed, rows, retained) =>
          some (observed.environment, rows, retained.2.2.context.2.1)
      | _ => none) = some (71, [encode ([7], [2])], [([7], [2])]) ∧
    Compact.Attachment.complete build callback noFallback (selection Authored.Controls.branches) handedOff = false := by
  constructor <;> rfl

end Controls

#print axioms Controls.actual_closed_records_and_zero_bag

#print axioms Controls.zero_source_grant_is_neither_closed_nor_an_observation

#print axioms Controls.actual_handoff_is_one_observation_with_earned_prefix

end BodyCallWeighted.Authored.Publication


namespace CallingModes

open Mettapedia.Machines.Cursor
open Mettapedia.GSLT.LanguageDef.HostCalls (Pull)
open Mettapedia.GSLT.LanguageDef.NativeControlCursor (protocol provider)
open _root_.CategoryTheory
variable {Item HState : Type}

namespace Controls

def listPull : List Item → Pull (List Item) Item
  | [] => .done
  | first :: rest => .yield first rest

/-- The source has one answer and then an effect before exhaustion. Its
singleton count cannot license dropping that later work. -/
def lateEffect : Nat × List Nat → Pull (Nat × List Nat) (Except Nat Nat)
  | (0, effects) => .yield (.ok 7) (1, effects)
  | (1, effects) => .suspend (2, effects ++ [9])
  | _ => .done

def fault : Except Nat Nat → Bool
  | .ok _ => false
  | .error _ => true

theorem unknown_hands_over_the_actual_unforced_source :
    let mode := selectMode .direct .producer .singleValue
    advance (provider lateEffect) (client mode (Except Nat Nat)) (fun _ _ => 1) 1
      (start mode (provider lateEffect) (0, [])) =
      (0, .done ⟨(), [], (0, [])⟩) := rfl

theorem nonempty_keeps_first_and_unrun_effectful_tail :
    receive .nonemptyProducer fault (provider lateEffect)
      (advance (provider lateEffect) (client .nonemptyProducer (Except Nat Nat))
        (fun _ _ => 1) 2 (start .nonemptyProducer (provider lateEffect) (0, []))).2 =
      .inr (.nonempty (.ok 7) [], (1, [])) := rfl

theorem a_singleton_source_is_not_finished_after_its_first_value :
    advance (provider lateEffect) (client .direct (Except Nat Nat)) (fun _ _ => 1) 2
      (start .direct (provider lateEffect) (0, [])) =
      (2, .paused ⟨(), .pulling [.ok 7], (2, [9])⟩) := rfl

theorem direct_completion_keeps_the_late_effect :
    receive .direct fault (provider lateEffect)
      (advance (provider lateEffect) (client .direct (Except Nat Nat)) (fun _ _ => 1) 4
        (start .direct (provider lateEffect) (0, []))).2 =
      .inr (.direct (.ok 7), (2, [9])) := rfl

theorem optional_absence_requires_exhaustion :
    receive .optional (fun _ : Nat => false) (provider listPull)
      (advance (provider listPull) (client .optional Nat) (fun _ _ => 1) 2
        (start .optional (provider listPull) [])).2 = .inr (.optional none, []) := rfl

theorem direct_absence_is_incompatible_not_pending :
    receive .direct (fun _ : Nat => false) (provider listPull)
      (advance (provider listPull) (client .direct Nat) (fun _ _ => 1) 2
        (start .direct (provider listPull) [])).2 = .inr (.incompatible [], []) := rfl

theorem equal_occurrences_cannot_fit_the_direct_interface :
    receive .direct (fun _ : Nat => false) (provider listPull)
      (advance (provider listPull) (client .direct Nat) (fun _ _ => 1) 4
        (start .direct (provider listPull) [7, 7])).2 =
      .inr (.incompatible [7, 7], []) := rfl

theorem nonempty_retains_the_equal_second_occurrence :
    receive .nonemptyProducer (fun _ : Nat => false) (provider listPull)
      (advance (provider listPull) (client .nonemptyProducer Nat) (fun _ _ => 1) 2
        (start .nonemptyProducer (provider listPull) [7, 7])).2 =
      .inr (.nonempty 7 [], [7]) := rfl

theorem a_fault_is_not_an_optional_absence :
    receive .optional fault (provider listPull)
      (advance (provider listPull) (client .optional (Except Nat Nat)) (fun _ _ => 1) 4
        (start .optional (provider listPull) [.error 12, .ok 7])).2 =
      .inr (.faulted [.error 12, .ok 7], []) := rfl

theorem splitting_does_not_repeat_the_late_effect :
    resume (provider lateEffect) (client .direct (Except Nat Nat)) (fun _ _ => 1) 2
      (advance (provider lateEffect) (client .direct (Except Nat Nat)) (fun _ _ => 1) 2
        (start .direct (provider lateEffect) (0, []))) =
      (3, .done ⟨(), [.ok 7], (2, [9])⟩) := rfl

end Controls

end CallingModes


end Mettapedia.Machines.SourceProducerCardinality
