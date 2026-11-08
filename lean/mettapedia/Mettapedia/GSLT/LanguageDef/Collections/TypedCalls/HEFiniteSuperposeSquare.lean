import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFiniteSuperposeSource

/-! # Reached square calls under the finite superpose source boundary -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFiniteSuperposeSquare

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open TypedSquareCollection HEFiniteSuperposeSource

attribute [local cbv_eval] FirstSuccessArgumentBoundary.numeric_self_equal
  FirstSuccessArgumentBoundary.grounded_not_stopped
  FirstSuccessArgumentBoundary.grounded_argument_entry
  FirstSuccessArgumentBoundary.checked_grounded_argument_step
  FirstSuccessArgumentBoundary.numeric_cast
  FirstSuccessArgumentBoundary.numeric_cast_covered Bool.and_false

def callState (n : Int) (stack : List Frame) (emitted : ResultSet) : Configuration :=
  ⟨space, .work (.call (apply "sq" [num n]) number Bindings.empty 20 []), stack, emitted⟩

def queried (n : Int) (stack : List Frame) (emitted : ResultSet) : Configuration :=
  ⟨space, .work (.producerResults (.ordinary number) (apply "sq" [num n]) Bindings.empty
    19 [] Atom.notReducible [(apply "*" [num n, num n], squareBindings n)]), stack, emitted⟩

def multiplyTail (n : Int) (stack : List Frame) : List Frame :=
  [.filter, .append (.returns (apply "sq" [num n]) number 19 [] [])] ++ stack

def multiplyEntry (n : Int) (stack : List Frame) (emitted : ResultSet) : Configuration :=
  ⟨space, .work (.expression (apply "*" [num n, num n]) number (squareBindings n) 18 []),
    multiplyTail n stack, emitted⟩

def arrow2 : Atom := CompletedDelivery.arrowType [number, number] number

def headStack (n : Int) (stack : List Frame) : List Frame :=
  [.heads arrow2 [num n, num n] 16 [number], .calls number 17 [],
   .append (.bindingAlternatives (apply "*" [num n, num n]) arrow2 number 17 [] [])] ++ multiplyTail n stack

def headStart (n : Int) (stack : List Frame) (emitted : ResultSet) : Configuration :=
  ⟨space, .work (.atom (.symbol "*") arrow2 (squareBindings n) 16 [arrow2, num n, num n, number]),
    headStack n stack, emitted⟩

def headReturned (n : Int) (stack : List Frame) (emitted : ResultSet) : Configuration :=
  ⟨space, .returning [(.symbol "*", squareBindings n)], headStack n stack, emitted⟩

def argumentStack (n : Int) (stack : List Frame) : List Frame :=
  [.functionTail (.symbol "*"), .append (.heads arrow2 [num n, num n] 16 [] [number]),
   .calls number 17 [], .append (.bindingAlternatives (apply "*" [num n, num n]) arrow2 number 17 [] [])] ++
    multiplyTail n stack

def argumentsStart (n : Int) (stack : List Frame) (emitted : ResultSet) : Configuration :=
  ⟨space, .work (.args [num n, num n] [number, number] (squareBindings n) 16 [.symbol "*", number]),
    argumentStack n stack, emitted⟩

def argumentsReturned (n : Int) (stack : List Frame) (emitted : ResultSet) : Configuration :=
  ⟨space, .returning [(argumentPacket [num n, num n], squareBindings n)], argumentStack n stack, emitted⟩

def multiplied (n : Int) (stack : List Frame) (emitted : ResultSet) : Configuration :=
  ⟨space, .returning [squareResult n],
    [.append (.productions 16 [] [number] (some (apply "*" [num n, num n])) .emitted),
     .invocationReturn (.ordinary number) (apply "*" [num n, num n]) 16 [],
     .append (.calls number 17 [] []),
     .append (.bindingAlternatives (apply "*" [num n, num n]) arrow2 number 17 [] [])] ++ multiplyTail n stack,
    emitted⟩

set_option maxHeartbeats 2000000 in
theorem query_block (n : Int) (stack : List Frame) (emitted : ResultSet) :
    worker.run 7 (callState n stack emitted) = ([], .exhausted (queried n stack emitted)) := by
  rw [worker_raw _ _ rfl]
  cbv

theorem producer_block (n : Int) (stack : List Frame) (emitted : ResultSet) :
    worker.run 10 (queried n stack emitted) = ([], .exhausted (multiplyEntry n stack emitted)) := by
  rw [worker_raw _ _ rfl]
  cbv

theorem head_entry (n : Int) (stack : List Frame) (emitted : ResultSet) :
    worker.run 4 (multiplyEntry n stack emitted) = ([], .exhausted (headStart n stack emitted)) := by
  rw [worker_raw _ _ rfl]
  cbv

theorem head_step (n : Int) (stack : List Frame) (emitted : ResultSet) :
    (FirstSuccessRecursiveExecution.Checked.machine dispatch FirstSuccessRecursiveExecution.scopedTypes).step
      ⟨space, .work (.atom (.symbol "*") (CompletedDelivery.arrowType [number, number] number)
        (squareBindings n) (15 + 1) [arrow2, num n, num n, number]), headStack n stack, emitted⟩ =
      some (.silent ⟨space, .returning [(.symbol "*", squareBindings n)], headStack n stack, emitted⟩) := by
  have declared : getAtomTypes space (.symbol "*") = [CompletedDelivery.arrowType [number, number] number] := by decide +kernel
  exact HELiteralWorkerDelivery.scoped_closed_head_step space dispatch "*" [number, number] number
    (squareBindings n) 15 _ _ emitted declared (by decide) rfl (by decide)
    (HELiteralWorkerDelivery.binary_number_arrow_covered _ 9)

theorem head_tail (n : Int) (stack : List Frame) (emitted : ResultSet) :
    worker.run 2 (headReturned n stack emitted) = ([], .exhausted (argumentsStart n stack emitted)) := by
  rw [worker_raw _ _ rfl]
  cbv

theorem arguments_block (n : Int) (stack : List Frame) (emitted : ResultSet) :
    worker.run 17 (argumentsStart n stack emitted) = ([], .exhausted (argumentsReturned n stack emitted)) :=
  HELiteralWorkerDelivery.two_arguments space dispatch FirstSuccessRecursiveExecution.scopedTypes
    HELiteralWorkerDelivery.scoped_numeric n n (squareBindings n) 16 (by omega)
    [.symbol "*", number] (argumentStack n stack) emitted 0

set_option maxHeartbeats 2000000 in
theorem arithmetic_block (n : Int) (stack : List Frame) (emitted : ResultSet) :
    worker.run 16 (argumentsReturned n stack emitted) = ([], .exhausted (multiplied n stack emitted)) := by
  rw [worker_raw _ _ rfl]
  cbv

theorem return_block (n : Int) (stack : List Frame) (emitted : ResultSet) :
    worker.run 20 (multiplied n stack emitted) =
      ([], .exhausted ⟨space, .returning [squareResult n], stack, emitted⟩) := by
  rw [worker_raw _ _ rfl]
  cbv

/-- The actual reached call executes the authored equation and multiplication
service. Its source-selected fresh record survives the complete return. -/
theorem ordinary_square (n : Int) (stack : List Frame) (emitted : ResultSet) :
    worker.run 77 (callState n stack emitted) =
      ([], .exhausted ⟨space, .returning [squareResult n], stack, emitted⟩) := by
  rw [show 77 = 7 + 70 from rfl,
    worker.established_and_pending 7 70 _ _ [] (query_block n stack emitted)]
  simp only [List.nil_append]
  rw [show 70 = 10 + 60 from rfl,
    worker.established_and_pending 10 60 _ _ [] (producer_block n stack emitted)]
  simp only [List.nil_append]
  rw [show 60 = 4 + 56 from rfl,
    worker.established_and_pending 4 56 _ _ [] (head_entry n stack emitted)]
  simp only [List.nil_append]
  have castRun := (FirstSuccessRecursiveExecution.Checked.machine dispatch
    FirstSuccessRecursiveExecution.scopedTypes).run_succ_silent (fuel := 55) (head_step n stack emitted)
  change worker.run 56 (headStart n stack emitted) = worker.run 55 (headReturned n stack emitted) at castRun
  rw [castRun, show 55 = 2 + 53 from rfl,
    worker.established_and_pending 2 53 _ _ [] (head_tail n stack emitted)]
  simp only [List.nil_append]
  rw [show 53 = 17 + 36 from rfl,
    worker.established_and_pending 17 36 _ _ [] (arguments_block n stack emitted)]
  simp only [List.nil_append]
  rw [show 36 = 16 + 20 from rfl,
    worker.established_and_pending 16 20 _ _ [] (arithmetic_block n stack emitted), return_block]
  rfl

def calls (inputs : List Int) : ResultSet := inputs.map fun n => (apply "sq" [num n], Bindings.empty)

/-- Every reached call is executed; the loop is the existing `calls` task,
not a separate batch evaluator. -/
theorem ordinary_squares (inputs : List Int) (stack : List Frame) (emitted : ResultSet) : ∀ budget,
    worker.run (80 * inputs.length + 1 + budget)
      ⟨space, .work (.calls number 20 (calls inputs) []), stack, emitted⟩ =
      worker.run budget ⟨space, .returning (inputs.map squareResult), stack, emitted⟩ := by
  induction inputs generalizing stack with
  | nil =>
      intro budget
      have enter : worker.step ⟨space, .work (.calls number 20 [] []), stack, emitted⟩ =
          some (.silent ⟨space, .returning [], stack, emitted⟩) := rfl
      simpa [calls, Nat.add_comm 1] using worker.run_succ_silent (fuel := budget) enter
  | cons n rest ih =>
      intro budget
      let next := Task.calls number 20 (calls rest) []
      have enter : worker.step ⟨space, .work (.calls number 20 (calls (n :: rest)) []), stack, emitted⟩ =
          some (.silent (callState n (.append next :: stack) emitted)) := rfl
      have save : worker.step ⟨space, .returning [squareResult n], .append next :: stack, emitted⟩ =
          some (.silent ⟨space, .work next, .prepend [squareResult n] :: stack, emitted⟩) := rfl
      have finish : worker.step
          ⟨space, .returning (rest.map squareResult), .prepend [squareResult n] :: stack, emitted⟩ =
          some (.silent ⟨space, .returning ((n :: rest).map squareResult), stack, emitted⟩) := rfl
      rw [show 80 * (n :: rest).length + 1 + budget = (80 * rest.length + 80 + budget) + 1 by simp; omega,
        worker.run_succ_silent enter]
      rw [show 80 * rest.length + 80 + budget = 77 + (80 * rest.length + 3 + budget) by omega,
        worker.established_and_pending 77 _ _ _ [] (ordinary_square n (.append next :: stack) emitted)]
      simp only [List.nil_append]
      rw [show 80 * rest.length + 3 + budget = (80 * rest.length + 2 + budget) + 1 by omega,
        worker.run_succ_silent save]
      rw [show 80 * rest.length + 2 + budget = 80 * rest.length + 1 + (1 + budget) by omega]
      rw [show next = .calls number 20 (calls rest) [] from rfl,
        ih (.prepend [squareResult n] :: stack) (1 + budget), Nat.add_comm 1 budget,
        worker.run_succ_silent finish]

def argumentReplies (inputs : List Int) : ResultSet :=
  inputs.map fun n => (argumentPacket [num n], Bindings.empty)

/-- Delivered alternatives retain the original source argument while each
numeric occurrence becomes its own argument packet. -/
theorem argument_alternatives (inputs : List Int) (original : Atom) (live : List Atom)
    (stack : List Frame) (emitted : ResultSet) : ∀ budget,
    worker.run (5 * inputs.length + 1 + budget)
      ⟨space, .work (.argumentHeads original [] [] 18 (rows inputs) live), stack, emitted⟩ =
      worker.run budget ⟨space, .returning (argumentReplies inputs), stack, emitted⟩ := by
  induction inputs generalizing stack with
  | nil =>
      intro budget
      have enter : worker.step ⟨space, .work (.argumentHeads original [] [] 18 [] live), stack, emitted⟩ =
          some (.silent ⟨space, .returning [], stack, emitted⟩) := rfl
      simpa [argumentReplies, rows, Nat.add_comm 1] using worker.run_succ_silent (fuel := budget) enter
  | cons n rest ih =>
      intro budget
      let next := Task.argumentHeads original [] [] 18 (rows rest) live
      let packet : ResultSet := [(argumentPacket [num n], Bindings.empty)]
      have enter : worker.step
          ⟨space, .work (.argumentHeads original [] [] 18 (rows (n :: rest)) live), stack, emitted⟩ =
          some (.silent ⟨space, .work (.args [] [] Bindings.empty 18 (num n :: live)),
            .argumentTail (num n) :: .append next :: stack, emitted⟩) :=
        FirstSuccessArgumentBoundary.checked_grounded_argument_step space dispatch
          FirstSuccessRecursiveExecution.scopedTypes original [] [] 18 (.int n) Bindings.empty
            (rows rest) live stack emitted
      have emptyArgs : worker.step
          ⟨space, .work (.args [] [] Bindings.empty 18 (num n :: live)),
            .argumentTail (num n) :: .append next :: stack, emitted⟩ =
          some (.silent ⟨space, .returning [(argumentPacket [], Bindings.empty)],
            .argumentTail (num n) :: .append next :: stack, emitted⟩) := rfl
      have buildPacket : worker.step
          ⟨space, .returning [(argumentPacket [], Bindings.empty)], .argumentTail (num n) :: .append next :: stack, emitted⟩ =
          some (.silent ⟨space, .returning packet, .append next :: stack, emitted⟩) := rfl
      have save : worker.step ⟨space, .returning packet, .append next :: stack, emitted⟩ =
          some (.silent ⟨space, .work next, .prepend packet :: stack, emitted⟩) := rfl
      have finish : worker.step ⟨space, .returning (argumentReplies rest), .prepend packet :: stack, emitted⟩ =
          some (.silent ⟨space, .returning (argumentReplies (n :: rest)), stack, emitted⟩) := rfl
      rw [show 5 * (n :: rest).length + 1 + budget = (5 * rest.length + 5 + budget) + 1 by simp; omega,
        worker.run_succ_silent enter]
      rw [show 5 * rest.length + 5 + budget = (5 * rest.length + 4 + budget) + 1 by omega,
        worker.run_succ_silent emptyArgs]
      rw [show 5 * rest.length + 4 + budget = (5 * rest.length + 3 + budget) + 1 by omega,
        worker.run_succ_silent buildPacket]
      rw [show 5 * rest.length + 3 + budget = (5 * rest.length + 2 + budget) + 1 by omega,
        worker.run_succ_silent save]
      rw [show 5 * rest.length + 2 + budget = 5 * rest.length + 1 + (1 + budget) by omega]
      rw [show next = .argumentHeads original [] [] 18 (rows rest) live from rfl,
        ih (.prepend packet :: stack) (1 + budget), Nat.add_comm 1 budget,
        worker.run_succ_silent finish]

theorem source_arguments (first : Int) (rest : List Int) (live : List Atom)
    (stack : List Frame) (emitted : ResultSet) :
    worker.run (17 * (first :: rest).length + 41)
      ⟨space, .work (.args [superpose ((first :: rest).map num)] [number] Bindings.empty 19 live), stack, emitted⟩ =
      ([], .exhausted ⟨space, .returning (argumentReplies (first :: rest)), stack, emitted⟩) := by
  let inputs := first :: rest
  let original := superpose (inputs.map num)
  let receiver := Frame.argumentHeads original [] [] 18 live
  have enter : worker.step
      ⟨space, .work (.args [original] [number] Bindings.empty 19 live), stack, emitted⟩ =
      some (.silent ⟨space, .work (.atom original number Bindings.empty 18 live), receiver :: stack, emitted⟩) := rfl
  have receive : worker.step ⟨space, .returning (rows inputs), receiver :: stack, emitted⟩ =
      some (.silent ⟨space, .work (.argumentHeads original [] [] 18 (rows inputs) live), stack, emitted⟩) := rfl
  rw [show 17 * (first :: rest).length + 41 = (17 * inputs.length + 40) + 1 by rfl,
    worker.run_succ_silent enter]
  rw [show 17 * inputs.length + 40 = (12 * inputs.length + 38) + (5 * inputs.length + 2) by omega,
    worker.established_and_pending _ _ _ _ [] (superpose_source_returns first rest live (receiver :: stack) emitted)]
  simp only [List.nil_append]
  rw [show 5 * inputs.length + 2 = (5 * inputs.length + 1) + 1 by omega,
    worker.run_succ_silent receive]
  exact argument_alternatives inputs original live stack emitted 0

def arrow1 : Atom := CompletedDelivery.arrowType [number] number

def outerTail (inputs : List Int) : List Frame :=
  [.append (.bindingAlternatives (squareSuperpose inputs) arrow1 number 20 [] []), .filter]

def outerHeadStack (inputs : List Int) : List Frame :=
  [.heads arrow1 [superpose (inputs.map num)] 19 [number], .calls number 20 []] ++ outerTail inputs

def outerHeadStart (inputs : List Int) : Configuration :=
  ⟨space, .work (.atom (.symbol "sq") arrow1 Bindings.empty 19
    [arrow1, superpose (inputs.map num), number]), outerHeadStack inputs, []⟩

def outerHeadReturned (inputs : List Int) : Configuration :=
  ⟨space, .returning [(.symbol "sq", Bindings.empty)], outerHeadStack inputs, []⟩

def outerArgumentStack (inputs : List Int) : List Frame :=
  [.functionTail (.symbol "sq"),
   .append (.heads arrow1 [superpose (inputs.map num)] 19 [] [number]),
   .calls number 20 []] ++ outerTail inputs

def outerArgumentsStart (inputs : List Int) : Configuration :=
  ⟨space, .work (.args [superpose (inputs.map num)] [number] Bindings.empty 19 [.symbol "sq", number]),
    outerArgumentStack inputs, []⟩

theorem outer_head_entry (inputs : List Int) :
    worker.run 2 (selected inputs) = ([], .exhausted (outerHeadStart inputs)) := by
  rw [worker_raw _ _ rfl]
  cbv

theorem outer_head_step (inputs : List Int) :
    (FirstSuccessRecursiveExecution.Checked.machine dispatch FirstSuccessRecursiveExecution.scopedTypes).step
      ⟨space, .work (.atom (.symbol "sq") (CompletedDelivery.arrowType [number] number)
        Bindings.empty (18 + 1) [arrow1, superpose (inputs.map num), number]), outerHeadStack inputs, []⟩ =
      some (.silent ⟨space, .returning [(.symbol "sq", Bindings.empty)], outerHeadStack inputs, []⟩) :=
  HELiteralWorkerDelivery.scoped_closed_head_step space dispatch "sq" [number] number Bindings.empty 18
    _ _ [] square_declared (by decide) rfl (by decide)
    (HELiteralWorkerDelivery.unary_number_arrow_covered _ 13)

theorem outer_head_tail (inputs : List Int) :
    worker.run 2 (outerHeadReturned inputs) = ([], .exhausted (outerArgumentsStart inputs)) := by
  rw [worker_raw _ _ rfl]
  cbv

theorem source_arguments_prefix (inputs : List Int) :
    worker.run 8 (initial inputs) = ([], .exhausted (outerArgumentsStart inputs)) := by
  rw [show 8 = 3 + 5 from rfl,
    worker.established_and_pending 3 5 _ _ [] (source_square_selection inputs)]
  simp only [List.nil_append]
  rw [show 5 = 2 + 3 from rfl,
    worker.established_and_pending 2 3 _ _ [] (outer_head_entry inputs)]
  simp only [List.nil_append]
  have castRun := (FirstSuccessRecursiveExecution.Checked.machine dispatch
    FirstSuccessRecursiveExecution.scopedTypes).run_succ_silent (fuel := 2) (outer_head_step inputs)
  change worker.run 3 (outerHeadStart inputs) = worker.run 2 (outerHeadReturned inputs) at castRun
  rw [castRun, outer_head_tail]

theorem assembled_calls (inputs : List Int) :
    RecursiveTasks.functionTail (.symbol "sq") (argumentReplies inputs) = calls inputs := by
  simp [RecursiveTasks.functionTail, argumentReplies, calls, List.map_map,
    argumentPacket, argumentsSucceeded, argumentValues, unpackArguments, apply]

theorem source_arguments_tail (inputs : List Int) :
    worker.run 5 ⟨space, .returning (argumentReplies inputs), outerArgumentStack inputs, []⟩ =
      ([], .exhausted ⟨space, .work (.calls number 20 (calls inputs) []), outerTail inputs, []⟩) := by
  have assemble : worker.step
      ⟨space, .returning (argumentReplies inputs), outerArgumentStack inputs, []⟩ =
      some (.silent ⟨space, .returning (calls inputs),
        .append (.heads arrow1 [superpose (inputs.map num)] 19 [] [number]) ::
          .calls number 20 [] :: outerTail inputs, []⟩) := by
    simp [FirstSuccessRecursiveExecution.Checked.machine, RecursiveMachine.Checked.guardMachine,
      FirstSuccessRecursiveExecution.Checked.blocked, RecursiveMachine.Checked.frameReady,
      FirstSuccessRecursiveExecution.machine, FirstSuccessRecursiveExecution.next,
      RecursiveMachine.resume, Transition.relabel, outerArgumentStack, assembled_calls]
  rw [show 5 = 4 + 1 from rfl, worker.run_succ_silent assemble, worker_raw _ _ rfl]
  simp [Machine.run, FirstSuccessRecursiveExecution.Checked.machine,
    RecursiveMachine.Checked.guardMachine, FirstSuccessRecursiveExecution.Checked.blocked,
    RecursiveMachine.Checked.frameReady, FirstSuccessRecursiveStrategy.taskReady,
    RecursiveMachine.Checked.taskReady, FirstSuccessRecursiveExecution.machine,
    FirstSuccessRecursiveExecution.next, FirstSuccessRecursiveStrategy.enter,
    RecursiveMachine.enter, RecursiveMachine.resume, Transition.relabel]

theorem square_results_clean (inputs : List Int) :
    successPriority (inputs.map squareResult) = inputs.map squareResult := by
  apply HEReturns.keep_clean
  intro row member
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp member
  rfl

theorem source_drain (inputs : List Int) :
    worker.run 4 ⟨space, .returning (inputs.map squareResult), outerTail inputs, []⟩ =
      ([], .exhausted ⟨space, .returning (inputs.map squareResult), [], []⟩) := by
  rw [worker_raw _ _ rfl]
  simp [Machine.run, outerTail, FirstSuccessRecursiveExecution.Checked.machine,
    RecursiveMachine.Checked.guardMachine, FirstSuccessRecursiveExecution.Checked.blocked,
    RecursiveMachine.Checked.frameReady, FirstSuccessRecursiveStrategy.taskReady,
    RecursiveMachine.Checked.taskReady, FirstSuccessRecursiveExecution.machine,
    FirstSuccessRecursiveExecution.next, FirstSuccessRecursiveStrategy.enter,
    RecursiveMachine.enter, RecursiveMachine.resume, Transition.relabel, square_results_clean]

/-- The complete unevaluated source `sq(superpose(...))` reaches the proved
ordered square frontier. Source selection and argument evaluation precede
the ordinary calls; the theorem assumes no finished child results. -/
theorem source_calls_complete (first : Int) (rest : List Int) :
    worker.run (97 * (first :: rest).length + 55) (initial (first :: rest)) =
      ([], .exhausted ⟨space, .returning ((first :: rest).map squareResult), outerTail (first :: rest), []⟩) := by
  let inputs := first :: rest
  rw [show 97 * inputs.length + 55 = 8 + (17 * inputs.length + 41 + (80 * inputs.length + 6)) by omega,
    worker.established_and_pending 8 _ _ _ [] (source_arguments_prefix inputs)]
  simp only [List.nil_append]
  have argumentRun := source_arguments first rest [.symbol "sq", number] (outerArgumentStack inputs) []
  change worker.run (17 * inputs.length + 41) (outerArgumentsStart inputs) =
    ([], .exhausted ⟨space, .returning (argumentReplies inputs), outerArgumentStack inputs, []⟩) at argumentRun
  rw [worker.established_and_pending (17 * inputs.length + 41) _ _ _ [] argumentRun]
  simp only [List.nil_append]
  rw [show 80 * inputs.length + 6 = 5 + (80 * inputs.length + 1) by omega,
    worker.established_and_pending 5 _ _ _ [] (source_arguments_tail inputs)]
  simp only [List.nil_append]
  have callsRun := ordinary_squares inputs (outerTail inputs) [] 0
  simp only [Nat.add_zero] at callsRun
  change worker.run (80 * inputs.length + 1)
    ⟨space, .work (.calls number 20 (calls inputs) []), outerTail inputs, []⟩ =
      ([], .exhausted ⟨space, .returning (inputs.map squareResult), outerTail inputs, []⟩) at callsRun
  rw [callsRun]

theorem source_returns (first : Int) (rest : List Int) :
    worker.run (97 * (first :: rest).length + 59) (initial (first :: rest)) =
      ([], .exhausted ⟨space, .returning ((first :: rest).map squareResult), [], []⟩) := by
  rw [show 97 * (first :: rest).length + 59 = (97 * (first :: rest).length + 55) + 4 by omega,
    worker.established_and_pending _ 4 _ _ [] (source_calls_complete first rest), source_drain]
  rfl

theorem source_preselection (first : Int) (rest : List Int) :
    worker.run (97 * (first :: rest).length + 58) (initial (first :: rest)) =
      ([], .exhausted ⟨space, .returning ((first :: rest).map squareResult), [.filter], []⟩) := by
  rw [show 97 * (first :: rest).length + 58 = (97 * (first :: rest).length + 55) + 3 by omega,
    worker.established_and_pending _ 3 _ _ [] (source_calls_complete first rest)]
  simp only [List.nil_append]
  rw [worker_raw _ _ rfl]
  simp [Machine.run, outerTail, FirstSuccessRecursiveExecution.Checked.machine,
    RecursiveMachine.Checked.guardMachine, FirstSuccessRecursiveExecution.Checked.blocked,
    RecursiveMachine.Checked.frameReady, FirstSuccessRecursiveStrategy.taskReady,
    RecursiveMachine.Checked.taskReady, FirstSuccessRecursiveExecution.machine,
    FirstSuccessRecursiveExecution.next, FirstSuccessRecursiveStrategy.enter,
    RecursiveMachine.enter, RecursiveMachine.resume, Transition.relabel]

/-- Native three-class selection is justified at the actually reached
preselection frontier, rather than repaired after a binary selection. -/
theorem source_selection_native (inputs : List Int) :
    worker.step ⟨space, .returning (inputs.map squareResult), [.filter], []⟩ =
      some (.silent ⟨space, .returning (HEInvocationFrontier.normalize (inputs.map squareResult)), [], []⟩) := by
  have normalized : HEInvocationFrontier.normalize (inputs.map squareResult) = inputs.map squareResult := by
    simpa only [FirstSuccessSquareCollection.workerBatch_exact] using
      FirstSuccessSquareCollection.native_frontier_exact inputs
  rw [normalized]
  simp [FirstSuccessRecursiveExecution.Checked.machine, RecursiveMachine.Checked.guardMachine,
    FirstSuccessRecursiveExecution.Checked.blocked, RecursiveMachine.Checked.frameReady,
    FirstSuccessRecursiveExecution.machine, FirstSuccessRecursiveExecution.next,
    RecursiveMachine.resume, Transition.relabel, square_results_clean]

theorem source_finishes (first : Int) (rest : List Int) :
    worker.run (98 * (first :: rest).length + 60) (initial (first :: rest)) =
      ((first :: rest).map squareResult,
        .finished ⟨space, .returning [], [], (first :: rest).map squareResult⟩) := by
  rw [show 98 * (first :: rest).length + 60 =
      (97 * (first :: rest).length + 59) + (((first :: rest).map squareResult).length + 1 + 0) by simp; omega,
    worker.established_and_pending _ _ _ _ [] (source_returns first rest)]
  simp only [List.nil_append]
  simpa only [List.nil_append] using
    FirstSuccessScopedAdequacy.scoped_drain_returning space ((first :: rest).map squareResult) [] 0 dispatch

theorem empty_arguments :
    worker.run 47 (outerArgumentsStart []) =
      ([], .exhausted ⟨space, .returning [(Atom.empty, Bindings.empty)], outerArgumentStack [], []⟩) := by
  let receiver := Frame.argumentHeads (superpose []) [] [] 18 [.symbol "sq", number]
  have enter : worker.step (outerArgumentsStart []) =
      some (.silent ⟨space, .work (.atom (superpose []) number Bindings.empty 18 [.symbol "sq", number]),
        receiver :: outerArgumentStack [], []⟩) := rfl
  rw [show 47 = 46 + 1 from rfl, worker.run_succ_silent enter]
  rw [show 46 = 41 + 5 from rfl,
    worker.established_and_pending 41 5 _ _ []
      (empty_superpose_source_returns [.symbol "sq", number] (receiver :: outerArgumentStack []) [])]
  simp only [List.nil_append]
  rw [worker_raw _ _ rfl]
  cbv

set_option maxHeartbeats 1000000 in
theorem empty_calls :
    worker.run 20 ⟨space, .returning [(Atom.empty, Bindings.empty)], outerArgumentStack [], []⟩ =
      ([], .exhausted ⟨space, .returning [(Atom.empty, Bindings.empty)], outerTail [], []⟩) := by
  rw [worker_raw _ _ rfl]
  cbv

theorem empty_close :
    worker.run 6 ⟨space, .returning [(Atom.empty, Bindings.empty)], outerTail [], []⟩ =
      ([(Atom.empty, Bindings.empty)],
        .finished ⟨space, .returning [], [], [(Atom.empty, Bindings.empty)]⟩) := by
  rw [worker_raw _ _ rfl]
  cbv

theorem empty_source_finishes :
    worker.run 81 (initial []) =
      ([(Atom.empty, Bindings.empty)],
        .finished ⟨space, .returning [], [], [(Atom.empty, Bindings.empty)]⟩) := by
  rw [show 81 = 8 + 73 from rfl,
    worker.established_and_pending 8 73 _ _ [] (source_arguments_prefix [])]
  simp only [List.nil_append]
  rw [show 73 = 47 + 26 from rfl,
    worker.established_and_pending 47 26 _ _ [] empty_arguments]
  simp only [List.nil_append]
  rw [show 26 = 20 + 6 from rfl,
    worker.established_and_pending 20 6 _ _ [] empty_calls, empty_close]
  rfl

def sourceResults (inputs : List Int) : ResultSet :=
  if inputs.isEmpty then [(Atom.empty, Bindings.empty)] else inputs.map squareResult

def sourceBudget (inputs : List Int) : Nat :=
  if inputs.isEmpty then 81 else 98 * inputs.length + 60

theorem finite_source_finishes (inputs : List Int) :
    worker.run (sourceBudget inputs) (initial inputs) =
      (sourceResults inputs, .finished ⟨space, .returning [], [], sourceResults inputs⟩) := by
  cases inputs with
  | nil => exact empty_source_finishes
  | cons first rest => exact source_finishes first rest

/-- Pausing retains the complete source continuation and already published
prefix. Resumption supplies only the remaining publications. -/
theorem source_residual_completes (inputs : List Int) (used : Nat)
    (within : used ≤ sourceBudget inputs) (published : ResultSet) (saved : Configuration)
    (paused : worker.run used (initial inputs) = (published, .exhausted saved)) :
    published ++ (worker.run (sourceBudget inputs - used) saved).1 = sourceResults inputs ∧
      (worker.run (sourceBudget inputs - used) saved).2 =
        .finished ⟨space, .returning [], [], sourceResults inputs⟩ := by
  have joined := worker.established_and_pending used (sourceBudget inputs - used) _ _ published paused
  rw [Nat.add_sub_of_le within, finite_source_finishes] at joined
  exact ⟨(congrArg Prod.fst joined).symm, (congrArg Prod.snd joined).symm⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFiniteSuperposeSquare
