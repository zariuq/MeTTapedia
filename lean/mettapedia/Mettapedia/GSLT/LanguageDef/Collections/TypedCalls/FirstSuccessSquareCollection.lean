import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypedSquareCollection
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.FirstSuccessBoundary
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectiveRangeGate
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEInvocationFrontier
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.FirstSuccessArgumentBoundary
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HELiteralWorkerDelivery

/-!
# First-success typed squaring at the retained collection boundary

The source, multiplication service and ordered collector are reused from
`TypedSquareCollection`. The concrete producer is the existing resource-checked
scoped first-success worker. Its result includes the actual equation binding;
equal numeric outputs from different input occurrences are not identified.

The concrete run starts with an empty caller record and evaluator depth 16.
Its input is an arbitrary mathematical integer; native arithmetic overflow is
a separate service obligation. Arbitrary lists of these isolated producer
occurrences feed the existing retained collector. This is not the full surface
`collapse (sq (range ...))` elaboration or a contextual host-source adequacy
theorem under arbitrary caller names. The generic source/worker observation
transport is supplied separately by `FirstSuccessCollectedRegions`.

Actual inner and outer pre-selection checkpoints are derived before their
filter frames run. Their successful integer rows justify native three-class
selection locally, rather than attempting to repair an earlier binary filter.
The 109 worker steps and the collector's administrative bound are model costs,
not native instruction or allocation bounds.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.FirstSuccessSquareCollection

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open TypedSquareCollection

attribute [local cbv_eval] FirstSuccessArgumentBoundary.numeric_self_equal
  FirstSuccessArgumentBoundary.grounded_not_stopped
  FirstSuccessArgumentBoundary.grounded_argument_entry
  FirstSuccessArgumentBoundary.checked_grounded_argument_step
  FirstSuccessArgumentBoundary.numeric_cast
  FirstSuccessArgumentBoundary.numeric_cast_covered
  Bool.and_false

abbrev worker := FirstSuccessRecursiveExecution.Checked.machine multiplication
  FirstSuccessRecursiveExecution.scopedTypes

theorem closed_annotations : FirstSuccessScopedAdequacy.ClosedTypeAnnotations squareSpace :=
  (FirstSuccessScopedAdequacy.closedColonAnnotations_of_bool (by decide +kernel)).closedTypeAnnotations

theorem worker_raw (budget : Nat) (state : Configuration) (same : state.space = squareSpace) :
    worker.run budget state =
      (FirstSuccessRecursiveExecution.Checked.machine multiplication
        FirstSuccessRecursiveExecution.rawTypes).run budget state :=
  FirstSuccessScopedAdequacy.checked_run_scopedTypes_eq_rawTypes multiplication budget state
    (by rw [same]; exact closed_annotations)

def initial (n : Int) : Configuration :=
  Configuration.initial squareSpace (.atom (apply "sq" [num n]) Atom.undefinedType Bindings.empty 16 [])

def delivered (n : Int) : Configuration :=
  ⟨squareSpace, .returning [squareResult n], [], []⟩

def final (n : Int) : Configuration :=
  ⟨squareSpace, .returning [], [], [squareResult n]⟩

def arrow1 : Atom := .expression [.symbol "->", number, number]
def arrow2 : Atom := .expression [.symbol "->", number, number, number]

def squareTail (n : Int) : List Frame :=
  [.append (.calls number 14 [] []),
   .append (.bindingAlternatives (apply "sq" [num n]) arrow1 number 14 [] []), .filter]

def selected (n : Int) : Configuration :=
  ⟨squareSpace, .work (.bindingAlternatives (apply "sq" [num n]) arrow1 number 14 [Bindings.empty] []),
    [.filter], []⟩

def queried (n : Int) : Configuration :=
  ⟨squareSpace, .work (.producerResults (.ordinary number) (apply "sq" [num n]) Bindings.empty
    13 [] Atom.notReducible [(apply "*" [num n, num n], squareBindings n)]), squareTail n, []⟩

def argumentsDone (n : Int) : Configuration :=
  ⟨squareSpace, .returning [],
    [.prepend [(apply "sq" [num n], Bindings.empty)], .calls number 14 [],
     .append (.bindingAlternatives (apply "sq" [num n]) arrow1 number 14 [] []), .filter], []⟩

def argumentsStack (n : Int) : List Frame :=
  [.functionTail (.symbol "sq"), .append (.heads arrow1 [num n] 13 [] [number]),
   .calls number 14 [], .append (.bindingAlternatives (apply "sq" [num n]) arrow1 number 14 [] []), .filter]

def argumentsStart (n : Int) : Configuration :=
  ⟨squareSpace, .work (.args [num n] [number] Bindings.empty 13 [.symbol "sq", number]),
    argumentsStack n, []⟩

def argumentsReturned (n : Int) : Configuration :=
  ⟨squareSpace, .returning [(argumentPacket [num n], Bindings.empty)], argumentsStack n, []⟩

def headStack (n : Int) : List Frame :=
  [.heads arrow1 [num n] 13 [number], .calls number 14 [],
   .append (.bindingAlternatives (apply "sq" [num n]) arrow1 number 14 [] []), .filter]

def headStart (n : Int) : Configuration :=
  ⟨squareSpace, .work (.atom (.symbol "sq") arrow1 Bindings.empty 13 [arrow1, num n, number]),
    headStack n, []⟩

def headReturned (n : Int) : Configuration :=
  ⟨squareSpace, .returning [(.symbol "sq", Bindings.empty)], headStack n, []⟩

def multiplyEntry (n : Int) : Configuration :=
  ⟨squareSpace, .work (.expression (apply "*" [num n, num n]) number (squareBindings n) 12 []),
    [.filter, .append (.returns (apply "sq" [num n]) number 13 [] [])] ++ squareTail n, []⟩

def multiplied (n : Int) : Configuration :=
  ⟨squareSpace, .returning [squareResult n],
    [.append (.productions 10 [] [number] (some (apply "*" [num n, num n])) .emitted),
     .invocationReturn (.ordinary number) (apply "*" [num n, num n]) 10 [],
     .append (.calls number 11 [] []),
     .append (.bindingAlternatives (apply "*" [num n, num n]) arrow2 number 11 [] []),
     .filter, .append (.returns (apply "sq" [num n]) number 13 [] [])] ++ squareTail n, []⟩

def multiplyArgumentsStack (n : Int) : List Frame :=
    [.functionTail (.symbol "*"),
     .append (.heads arrow2 [num n, num n] 10 [] [number]), .calls number 11 [],
     .append (.bindingAlternatives (apply "*" [num n, num n]) arrow2 number 11 [] []),
     .filter, .append (.returns (apply "sq" [num n]) number 13 [] [])] ++ squareTail n

def multiplyArgumentsStart (n : Int) : Configuration :=
  ⟨squareSpace, .work (.args [num n, num n] [number, number] (squareBindings n) 10 [.symbol "*", number]),
    multiplyArgumentsStack n, []⟩

def multiplyArgumentsReturned (n : Int) : Configuration :=
  ⟨squareSpace, .returning [(argumentPacket [num n, num n], squareBindings n)],
    multiplyArgumentsStack n, []⟩

def multiplyHeadStack (n : Int) : List Frame :=
  [.heads arrow2 [num n, num n] 10 [number], .calls number 11 [],
   .append (.bindingAlternatives (apply "*" [num n, num n]) arrow2 number 11 [] []),
   .filter, .append (.returns (apply "sq" [num n]) number 13 [] [])] ++ squareTail n

def multiplyHeadStart (n : Int) : Configuration :=
  ⟨squareSpace, .work (.atom (.symbol "*") arrow2 (squareBindings n) 10 [arrow2, num n, num n, number]),
    multiplyHeadStack n, []⟩

def multiplyHeadReturned (n : Int) : Configuration :=
  ⟨squareSpace, .returning [(.symbol "*", squareBindings n)], multiplyHeadStack n, []⟩

def outerReturn (n : Int) : Configuration :=
  ⟨squareSpace, .returning [squareResult n], squareTail n, []⟩

def innerFrontier (n : Int) : Configuration :=
  ⟨squareSpace, .returning [squareResult n],
    [.filter, .append (.returns (apply "sq" [num n]) number 13 [] [])] ++ squareTail n, []⟩

def outerFrontier (n : Int) : Configuration :=
  ⟨squareSpace, .returning [squareResult n], [.filter], []⟩

set_option maxHeartbeats 1000000 in
theorem selection_block (n : Int) :
    worker.run 3 (initial n) = ([], .exhausted (selected n)) := by
  rw [worker_raw 3 (initial n) rfl]
  cbv

theorem head_entry_block (n : Int) :
    worker.run 2 (selected n) = ([], .exhausted (headStart n)) := by
  rw [worker_raw 2 (selected n) rfl]
  cbv

theorem head_step (n : Int) :
    (FirstSuccessRecursiveExecution.Checked.machine multiplication FirstSuccessRecursiveExecution.scopedTypes).step
      ⟨squareSpace, .work (.atom (.symbol "sq") (CompletedDelivery.arrowType [number] number)
        Bindings.empty (12 + 1) [arrow1, num n, number]), headStack n, []⟩ =
      some (.silent ⟨squareSpace, .returning [(.symbol "sq", Bindings.empty)], headStack n, []⟩) := by
  have declared : getAtomTypes squareSpace (.symbol "sq") =
      [CompletedDelivery.arrowType [number] number] := by decide +kernel
  have enough : CompletedDelivery.matchFuel (CompletedDelivery.arrowType [number] number) ≤ 12 := by decide
  have covered : matchTypesCovered (CompletedDelivery.arrowType [number] number)
      (CompletedDelivery.arrowType [number] number) Bindings.empty 12 = true :=
    HELiteralWorkerDelivery.unary_number_arrow_covered _ 7
  exact HELiteralWorkerDelivery.scoped_closed_head_step squareSpace multiplication "sq" [number] number
    Bindings.empty 12 [arrow1, num n, number] (headStack n) [] declared
    (by decide) rfl enough covered

theorem head_tail_block (n : Int) :
    worker.run 2 (headReturned n) = ([], .exhausted (argumentsStart n)) := by
  rw [worker_raw 2 (headReturned n) rfl]
  cbv

theorem argument_entry_block (n : Int) :
    worker.run 5 (selected n) = ([], .exhausted (argumentsStart n)) := by
  rw [show 5 = 2 + 3 from rfl,
    worker.established_and_pending 2 3 (selected n) (headStart n) [] (head_entry_block n)]
  simp only [List.nil_append]
  have castRun := (FirstSuccessRecursiveExecution.Checked.machine multiplication
    FirstSuccessRecursiveExecution.scopedTypes).run_succ_silent (fuel := 2) (head_step n)
  change worker.run 3 (headStart n) = worker.run 2 (headReturned n) at castRun
  rw [castRun, head_tail_block]

theorem literal_argument_block (n : Int) :
    worker.run 9 (argumentsStart n) = ([], .exhausted (argumentsReturned n)) :=
  HELiteralWorkerDelivery.one_argument squareSpace multiplication
    FirstSuccessRecursiveExecution.scopedTypes HELiteralWorkerDelivery.scoped_numeric n
    Bindings.empty 13 (by omega) [.symbol "sq", number] (argumentsStack n) [] 0

theorem argument_drain_block (n : Int) :
    worker.run 3 (argumentsReturned n) = ([], .exhausted (argumentsDone n)) := by
  rw [worker_raw 3 (argumentsReturned n) rfl]
  cbv

theorem arguments_block (n : Int) :
    worker.run 17 (selected n) = ([], .exhausted (argumentsDone n)) := by
  rw [show 17 = 5 + 12 from rfl,
    worker.established_and_pending 5 12 (selected n) (argumentsStart n) [] (argument_entry_block n)]
  simp only [List.nil_append]
  rw [show 12 = 9 + 3 from rfl,
    worker.established_and_pending 9 3 (argumentsStart n) (argumentsReturned n) [] (literal_argument_block n),
    argument_drain_block]
  rfl

set_option maxHeartbeats 2000000 in
theorem query_tail_block (n : Int) :
    worker.run 10 (argumentsDone n) = ([], .exhausted (queried n)) := by
  rw [worker_raw 10 (argumentsDone n) rfl]
  cbv

theorem query_block (n : Int) :
    worker.run 27 (selected n) = ([], .exhausted (queried n)) := by
  rw [show 27 = 17 + 10 from rfl,
    worker.established_and_pending 17 10 (selected n) (argumentsDone n) [] (arguments_block n),
    query_tail_block]
  rfl

set_option maxHeartbeats 1000000 in
theorem produced_entry_block (n : Int) :
    worker.run 10 (queried n) = ([], .exhausted (multiplyEntry n)) := by
  rw [worker_raw 10 (queried n) rfl]
  cbv

set_option maxHeartbeats 1000000 in
theorem multiplication_head_entry_block (n : Int) :
    worker.run 4 (multiplyEntry n) = ([], .exhausted (multiplyHeadStart n)) := by
  rw [worker_raw 4 (multiplyEntry n) rfl]
  cbv

theorem multiplication_head_step (n : Int) :
    (FirstSuccessRecursiveExecution.Checked.machine multiplication FirstSuccessRecursiveExecution.scopedTypes).step
      ⟨squareSpace, .work (.atom (.symbol "*") (CompletedDelivery.arrowType [number, number] number)
        (squareBindings n) (9 + 1) [arrow2, num n, num n, number]), multiplyHeadStack n, []⟩ =
      some (.silent ⟨squareSpace, .returning [(.symbol "*", squareBindings n)], multiplyHeadStack n, []⟩) := by
  have declared : getAtomTypes squareSpace (.symbol "*") =
      [CompletedDelivery.arrowType [number, number] number] := by decide +kernel
  have enough : CompletedDelivery.matchFuel (CompletedDelivery.arrowType [number, number] number) ≤ 9 := by decide
  have covered : matchTypesCovered (CompletedDelivery.arrowType [number, number] number)
      (CompletedDelivery.arrowType [number, number] number) (squareBindings n) 9 = true :=
    HELiteralWorkerDelivery.binary_number_arrow_covered _ 3
  exact HELiteralWorkerDelivery.scoped_closed_head_step squareSpace multiplication "*" [number, number] number
    (squareBindings n) 9 [arrow2, num n, num n, number] (multiplyHeadStack n) [] declared
    (by decide) rfl enough covered

theorem multiplication_head_tail_block (n : Int) :
    worker.run 2 (multiplyHeadReturned n) = ([], .exhausted (multiplyArgumentsStart n)) := by
  rw [worker_raw 2 (multiplyHeadReturned n) rfl]
  cbv

theorem multiplication_entry_block (n : Int) :
    worker.run 7 (multiplyEntry n) = ([], .exhausted (multiplyArgumentsStart n)) := by
  rw [show 7 = 4 + 3 from rfl,
    worker.established_and_pending 4 3 (multiplyEntry n) (multiplyHeadStart n) [] (multiplication_head_entry_block n)]
  simp only [List.nil_append]
  have castRun := (FirstSuccessRecursiveExecution.Checked.machine multiplication
    FirstSuccessRecursiveExecution.scopedTypes).run_succ_silent (fuel := 2) (multiplication_head_step n)
  change worker.run 3 (multiplyHeadStart n) = worker.run 2 (multiplyHeadReturned n) at castRun
  rw [castRun, multiplication_head_tail_block]

theorem multiplication_arguments_block (n : Int) :
    worker.run 17 (multiplyArgumentsStart n) = ([], .exhausted (multiplyArgumentsReturned n)) :=
  HELiteralWorkerDelivery.two_arguments squareSpace multiplication
    FirstSuccessRecursiveExecution.scopedTypes HELiteralWorkerDelivery.scoped_numeric n n
    (squareBindings n) 10 (by omega) [.symbol "*", number] (multiplyArgumentsStack n) [] 0

set_option maxHeartbeats 2000000 in
theorem multiplication_tail_block (n : Int) :
    worker.run 16 (multiplyArgumentsReturned n) = ([], .exhausted (multiplied n)) := by
  rw [worker_raw 16 (multiplyArgumentsReturned n) rfl]
  cbv

theorem multiplication_block (n : Int) :
    worker.run 40 (multiplyEntry n) = ([], .exhausted (multiplied n)) := by
  rw [show 40 = 7 + 33 from rfl,
    worker.established_and_pending 7 33 (multiplyEntry n) (multiplyArgumentsStart n) []
      (multiplication_entry_block n)]
  simp only [List.nil_append]
  rw [show 33 = 17 + 16 from rfl,
    worker.established_and_pending 17 16 (multiplyArgumentsStart n) (multiplyArgumentsReturned n) []
      (multiplication_arguments_block n), multiplication_tail_block]
  rfl

set_option maxHeartbeats 1000000 in
theorem return_block (n : Int) :
    worker.run 20 (multiplied n) = ([], .exhausted (outerReturn n)) := by
  rw [worker_raw 20 (multiplied n) rfl]
  cbv

theorem drain_block (n : Int) :
    worker.run 7 (outerReturn n) = ([], .exhausted (delivered n)) := by
  rw [worker_raw 7 (outerReturn n) rfl]
  cbv

theorem square_worker_reaches_multiplication (n : Int) :
    worker.run 80 (initial n) = ([], .exhausted (multiplied n)) := by
  rw [show 80 = 3 + 77 from rfl,
    worker.established_and_pending 3 77 (initial n) (selected n) [] (selection_block n)]
  simp only [List.nil_append]
  rw [show 77 = 27 + 50 from rfl,
    worker.established_and_pending 27 50 (selected n) (queried n) [] (query_block n)]
  simp only [List.nil_append]
  rw [show 50 = 10 + 40 from rfl,
    worker.established_and_pending 10 40 (queried n) (multiplyEntry n) [] (produced_entry_block n)]
  simp only [List.nil_append, multiplication_block]

/-- The actual checked scoped worker executes the source call in six
retained blocks before publication. The arithmetic service is unchanged. -/
theorem square_worker_reaches_return (n : Int) :
    worker.run 107 (initial n) = ([], .exhausted (delivered n)) := by
  rw [show 107 = 80 + 27 from rfl,
    worker.established_and_pending 80 27 (initial n) (multiplied n) [] (square_worker_reaches_multiplication n)]
  simp only [List.nil_append]
  rw [show 27 = 20 + 7 from rfl,
    worker.established_and_pending 20 7 (multiplied n) (outerReturn n) [] (return_block n)]
  simp only [List.nil_append, drain_block]

/-- Publication and completion are distinct existing worker transitions. -/
theorem square_worker_finishes (n : Int) :
    worker.run 109 (initial n) = ([squareResult n], .finished (final n)) := by
  have continuation := worker.established_and_pending 107 2 (initial n) (delivered n) []
    (square_worker_reaches_return n)
  exact continuation.trans (by rfl)

theorem square_worker_answers (n : Int) :
    (worker.run 109 (initial n)).1 = [squareResult n] :=
  congrArg Prod.fst (square_worker_finishes n)

/-- Every observed pause has exactly the unconsumed part of the proved
source result. The caller resumes the saved configuration, not the source
expression, and earlier publications are not repeated. -/
theorem saved_residual_completes (n : Int) (used : Nat) (within : used ≤ 109)
    (published : ResultSet) (saved : Configuration)
    (paused : worker.run used (initial n) = (published, .exhausted saved)) :
    published ++ (worker.run (109 - used) saved).1 = [squareResult n] ∧
      (worker.run (109 - used) saved).2 = .finished (final n) := by
  have joined := worker.established_and_pending used (109 - used) (initial n) saved published paused
  rw [Nat.add_sub_of_le within, square_worker_finishes] at joined
  exact ⟨(congrArg Prod.fst joined).symm, (congrArg Prod.snd joined).symm⟩

/-- The independently checked evaluator theorem and actual first-success
worker agree for this source; this is not a claim that the two strategies
agree on arbitrary programs or on overloaded signatures. -/
theorem source_call_agrees (context : TypedSquareCollection.Context) (n : Int) :
    sourceCall context n = (worker.run 109 (initial n)).1 := by
  rw [sourceCall_exact, square_worker_answers]

def workerBatch (inputs : List Int) : ResultSet :=
  inputs.flatMap fun n => (worker.run 109 (initial n)).1

theorem workerBatch_exact (inputs : List Int) : workerBatch inputs = inputs.map squareResult := by
  simp only [workerBatch, square_worker_answers]
  rw [List.map_eq_flatMap]

theorem source_batch_agrees (context : TypedSquareCollection.Context) (inputs : List Int) :
    sourceBatch context inputs = workerBatch inputs := by
  rw [sourceBatch_exact, workerBatch_exact]

/-- The existing admitted pending arithmetic shortcut is exactly the
derived first-success producer output, including its equation record. -/
theorem pending_native_agrees (context : TypedSquareCollection.Context)
    (pending : TypedSquareCollection.Pending context) :
    pending.native = (worker.run 109 (initial pending.input)).1 := by
  rw [square_worker_answers]
  simp only [TypedSquareCollection.Pending.native, pending.retained,
    TypedSquareCollection.returnFrame, squareResult]

theorem existing_collector_completes (context : TypedSquareCollection.Context) (inputs : List Int) :
    TypedSquareCollection.drive context (3 * inputs.length + 1)
      (TypedSquareCollection.initial context inputs) = (some (workerBatch inputs), none) := by
  rw [TypedSquareCollection.drive_complete, workerBatch_exact]

theorem existing_collector_preserves (context : TypedSquareCollection.Context)
    (budget : Nat) (inputs : List Int) :
    match TypedSquareCollection.drive context budget (TypedSquareCollection.initial context inputs) with
    | (some answers, none) => answers = workerBatch inputs
    | (none, some saved) => TypedSquareCollection.residual context saved = workerBatch inputs
    | _ => False := by
  rw [workerBatch_exact]
  exact TypedSquareCollection.drive_initial_preserves context budget inputs

/-- These producer outputs are all successful integers. Hence the native
three-class output policy agrees with the existing binary collector here,
without asserting that agreement for a mixed Empty frontier. -/
theorem native_frontier_exact (inputs : List Int) :
    HEInvocationFrontier.normalize (workerBatch inputs) = workerBatch inputs := by
  apply (HEInvocationFrontier.normalize_eq_model_of_no_empty (workerBatch inputs) ?_).trans
  · apply HEReturns.keep_clean
    intro answer member
    rw [workerBatch_exact] at member
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp member
    rfl
  · intro answer member
    rw [workerBatch_exact] at member
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp member
    rfl

theorem inner_frontier_block (n : Int) :
    worker.run 16 (multiplied n) = ([], .exhausted (innerFrontier n)) := by
  rw [worker_raw 16 (multiplied n) rfl]
  cbv

theorem outer_frontier_block (n : Int) :
    worker.run 6 (outerReturn n) = ([], .exhausted (outerFrontier n)) := by
  rw [worker_raw 6 (outerReturn n) rfl]
  cbv

/-- The multiplication call's completed frontier is reached before its
binary selection frame runs. Its contents are derived, not postulated from
the final output of the enclosing square call. -/
theorem multiplication_preselection (n : Int) :
    worker.run 96 (initial n) = ([], .exhausted (innerFrontier n)) := by
  rw [show 96 = 80 + 16 from rfl,
    worker.established_and_pending 80 16 (initial n) (multiplied n) [] (square_worker_reaches_multiplication n),
    inner_frontier_block]
  rfl

theorem square_preselection (n : Int) :
    worker.run 106 (initial n) = ([], .exhausted (outerFrontier n)) := by
  rw [show 106 = 80 + 26 from rfl,
    worker.established_and_pending 80 26 (initial n) (multiplied n) [] (square_worker_reaches_multiplication n)]
  simp only [List.nil_append]
  rw [show 26 = 20 + 6 from rfl,
    worker.established_and_pending 20 6 (multiplied n) (outerReturn n) [] (return_block n), outer_frontier_block]
  rfl

theorem preselection_rows_are_successes (n : Int) :
    isEmptyOrError (squareResult n).1 = false ∧
      HEInvocationFrontier.normalize [squareResult n] = [squareResult n] := by
  refine ⟨rfl, ?_⟩
  simpa only [workerBatch_exact, List.map_cons, List.map_nil] using native_frontier_exact [n]

/-- Replacing precisely this reached inner output selector by the native
three-class selector leaves the actual remaining worker state unchanged. -/
theorem inner_selection_native (n : Int) :
    worker.step (innerFrontier n) = some (.silent
      ⟨squareSpace, .returning (HEInvocationFrontier.normalize [squareResult n]),
        .append (.returns (apply "sq" [num n]) number 13 [] []) :: squareTail n, []⟩) := by
  rw [(preselection_rows_are_successes n).2]
  rfl

theorem outer_selection_native (n : Int) :
    worker.step (outerFrontier n) = some (.silent
      ⟨squareSpace, .returning (HEInvocationFrontier.normalize [squareResult n]), [], []⟩) := by
  rw [(preselection_rows_are_successes n).2]
  rfl

namespace Controls

def wrongCall : Atom := apply "sq" [.grounded (.string "text")]
def wrongInitial : Configuration := Configuration.initial squareSpace
  (.atom wrongCall Atom.undefinedType Bindings.empty 16 [])

theorem wrong_argument_keeps_source_call_error :
    (worker.run 20 wrongInitial).1 =
      [(mkError wrongCall (.badArgType 1 number (.symbol "String")), Bindings.empty)] := by
  decide +kernel

theorem duplicate_values_retain_distinct_records :
    workerBatch [2, -2, 2] =
      [squareResult 2, squareResult (-2), squareResult 2] ∧
      (squareResult 2).1 = (squareResult (-2)).1 ∧
      (squareResult 2).2 ≠ (squareResult (-2)).2 := by
  exact ⟨workerBatch_exact _, TypedSquareCollection.Controls.equal_values_distinct_records⟩

theorem return_frontier_is_not_yet_publication (n : Int) :
    (worker.run 107 (initial n)).1 = [] ∧
      (worker.run 109 (initial n)).1 = [squareResult n] := by
  exact ⟨congrArg Prod.fst (square_worker_reaches_return n), square_worker_answers n⟩

theorem no_input_is_completed_empty :
    workerBatch [] = [] ∧
      TypedSquareCollection.drive TypedSquareCollection.Controls.collectionContext 1
        (TypedSquareCollection.initial TypedSquareCollection.Controls.collectionContext []) =
          (some [], none) := by
  constructor <;> rfl

theorem deduplicating_is_not_collection : workerBatch [2, 2] ≠ [squareResult 2] := by
  rw [workerBatch_exact]
  simp

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.FirstSuccessSquareCollection
