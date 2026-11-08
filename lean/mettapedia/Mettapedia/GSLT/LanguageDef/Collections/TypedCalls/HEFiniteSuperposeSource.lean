import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.FirstSuccessSquareCollection

/-!
# Finite superposition at the typed square source boundary

The superpose service accepts an expression and emits its children in their
written order, as the grounded HE operation does. Its declared signature is
Expression -> %Undefined%. This is an operation service, not another evaluator.
The multiplication operation and checked first-success worker are unchanged.

The source application and the delivered argument packets are kept separate:
the source argument of sq is a superpose call, not an integer literal.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFiniteSuperposeSource

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open TypedSquareCollection

def superposeType : Atom := CompletedDelivery.arrowType [Atom.expressionType] Atom.undefinedType

def space : Space := Space.ofList (squareSpace.atoms ++
  [.expression [.symbol ":", .symbol "superpose", superposeType]])

def dispatch : GroundedDispatch where
  isExecutable head := head == .symbol "superpose" || multiplication.isExecutable head
  execute head arguments :=
    if head == .symbol "superpose" then
      match arguments with
      | .expression children :: _ => .ok (children.map fun child => (child, Bindings.empty))
      | _ => .incorrectArgument
    else multiplication.execute head arguments

def superpose (values : List Atom) : Atom := apply "superpose" [.expression values]
def squareSuperpose (inputs : List Int) : Atom := apply "sq" [superpose (inputs.map num)]
def surface (inputs : List Int) : Atom := apply "collapse" [squareSuperpose inputs]

abbrev worker := FirstSuccessRecursiveExecution.Checked.machine dispatch
  FirstSuccessRecursiveExecution.scopedTypes

theorem superpose_emits_children (values : List Atom) :
    dispatch.execute (.symbol "superpose") [.expression values] =
      .ok (values.map fun value => (value, Bindings.empty)) := rfl

theorem multiplication_unchanged (left right : Int) :
    dispatch.execute (.symbol "*") [num left, num right] =
      .ok [(num (left * right), Bindings.empty)] := rfl

theorem closed_annotations : FirstSuccessScopedAdequacy.ClosedTypeAnnotations space :=
  (FirstSuccessScopedAdequacy.closedColonAnnotations_of_bool (by decide +kernel)).closedTypeAnnotations

theorem worker_raw (budget : Nat) (state : Configuration) (same : state.space = space) :
    worker.run budget state =
      (FirstSuccessRecursiveExecution.Checked.machine dispatch
        FirstSuccessRecursiveExecution.rawTypes).run budget state :=
  FirstSuccessScopedAdequacy.checked_run_scopedTypes_eq_rawTypes dispatch budget state
    (by rw [same]; exact closed_annotations)

theorem square_declared : getAtomTypes space (.symbol "sq") =
    [CompletedDelivery.arrowType [number] number] := by decide +kernel

theorem superpose_declared : getAtomTypes space (.symbol "superpose") = [superposeType] := by decide +kernel

theorem source_argument_lookup (values : List Atom) :
    getAtomTypes space (superpose values) = [Atom.undefinedType] := by
  cbv

theorem source_square_applicable (inputs : List Int) :
    checkIfFunctionTypeIsApplicable (squareSuperpose inputs)
      (CompletedDelivery.arrowType [number] number) Atom.undefinedType space Bindings.empty 20 =
      .inr [Bindings.empty] := by
  cbv

theorem source_superpose_applicable (values : List Atom) :
    checkIfFunctionTypeIsApplicable (superpose values) superposeType number space Bindings.empty 18 =
      .inr [Bindings.empty] := by
  cases values <;> cbv

def initial (inputs : List Int) : Configuration :=
  Configuration.initial space (.atom (squareSuperpose inputs) Atom.undefinedType Bindings.empty 22 [])

def selected (inputs : List Int) : Configuration :=
  ⟨space, .work (.bindingAlternatives (squareSuperpose inputs)
    (CompletedDelivery.arrowType [number] number) number 20 [Bindings.empty] []), [.filter], []⟩

theorem source_square_selection (inputs : List Int) :
    worker.run 3 (initial inputs) = ([], .exhausted (selected inputs)) := by
  rw [worker_raw 3 (initial inputs) rfl]
  cbv

/-- Selection examines the original superpose call and its Expression
formal before any of its elements have been delivered to sq. -/
theorem source_superpose_selection (inputs : List Int) (live : List Atom)
    (stack : List Frame) (emitted : ResultSet) :
    worker.run 3
      ⟨space, .work (.atom (superpose (inputs.map num)) number Bindings.empty 18 live), stack, emitted⟩ =
      ([], .exhausted ⟨space,
        .work (.bindingAlternatives (superpose (inputs.map num)) superposeType Atom.undefinedType
          16 [Bindings.empty] live), .filter :: stack, emitted⟩) := by
  rw [worker_raw _ _ rfl]
  cases inputs <;> cbv

theorem atom_self_equal (value : Atom) : (value == value) = true := by simp

attribute [local cbv_eval] atom_self_equal

theorem held_expression_step (values : List Atom) (depth : Nat) (live : List Atom)
    (stack : List Frame) (emitted : ResultSet) :
    (FirstSuccessRecursiveExecution.Checked.machine dispatch FirstSuccessRecursiveExecution.rawTypes).step
      ⟨space, .work (.atom (.expression values) Atom.expressionType Bindings.empty (depth + 1) live),
        stack, emitted⟩ =
      some (.silent ⟨space, .returning [(.expression values, Bindings.empty)], stack, emitted⟩) := by
  simp [FirstSuccessRecursiveExecution.Checked.machine, RecursiveMachine.Checked.guardMachine,
    FirstSuccessRecursiveExecution.Checked.blocked, FirstSuccessRecursiveStrategy.taskReady,
    RecursiveMachine.Checked.taskReady, FirstSuccessRecursiveExecution.machine,
    FirstSuccessRecursiveExecution.next, FirstSuccessRecursiveStrategy.enter,
    RecursiveMachine.enter, getMetaType, Atom.expressionType, Transition.relabel]

attribute [local cbv_eval] held_expression_step

/-- The expression operand is held intact. This block neither runs its
elements nor converts their syntax into a precomputed answer list. -/
theorem held_expression_argument (values : List Atom) (depth : Nat) (live : List Atom)
    (stack : List Frame) (emitted : ResultSet) :
    worker.run 9
      ⟨space, .work (.args [.expression values] [Atom.expressionType] Bindings.empty (depth + 2) live),
        stack, emitted⟩ =
      ([], .exhausted ⟨space,
        .returning [(argumentPacket [.expression values], Bindings.empty)], stack, emitted⟩) := by
  rw [worker_raw _ _ rfl]
  let m := FirstSuccessRecursiveExecution.Checked.machine dispatch FirstSuccessRecursiveExecution.rawTypes
  have enter : m.step
      ⟨space, .work (.args [.expression values] [Atom.expressionType] Bindings.empty (depth + 2) live), stack, emitted⟩ =
      some (.silent ⟨space, .work (.atom (.expression values) Atom.expressionType Bindings.empty (depth + 1) live),
        .argumentHeads (.expression values) [] [] (depth + 1) live :: stack, emitted⟩) := rfl
  change m.run (8 + 1) _ = _
  rw [m.run_succ_silent enter]
  rw [show 8 = 7 + 1 from rfl,
    m.run_succ_silent (held_expression_step values depth live _ emitted)]
  cbv

def rows (inputs : List Int) : ResultSet := inputs.map fun n => (num n, Bindings.empty)

theorem grounded_number_step (n : Int) (original expected : Atom) (remaining : ResultSet)
    (live : List Atom) (stack : List Frame) (emitted : ResultSet) :
    worker.step
      ⟨space, .work (.grounded original expected Bindings.empty 15
        ((num n, Bindings.empty) :: remaining) live), stack, emitted⟩ =
      some (.silent ⟨space, .returning [(num n, Bindings.empty)],
        .append (.grounded original expected Bindings.empty 15 remaining live) :: stack, emitted⟩) := by
  cbv

/-- The actual host-result traversal merges and materializes each occurrence
before production. It preserves every integer and its reached empty record. -/
theorem grounded_numbers (inputs : List Int) (original expected : Atom)
    (live : List Atom) (stack : List Frame) (emitted : ResultSet) : ∀ budget,
    worker.run (3 * inputs.length + 1 + budget)
      ⟨space, .work (.grounded original expected Bindings.empty 15 (rows inputs) live), stack, emitted⟩ =
      worker.run budget ⟨space, .returning (rows inputs), stack, emitted⟩ := by
  induction inputs generalizing stack with
  | nil =>
      intro budget
      have enter : worker.step
          ⟨space, .work (.grounded original expected Bindings.empty 15 [] live), stack, emitted⟩ =
          some (.silent ⟨space, .returning [], stack, emitted⟩) := rfl
      simpa [rows, Nat.add_comm 1] using worker.run_succ_silent (fuel := budget) enter
  | cons n rest ih =>
      intro budget
      let next := Task.grounded original expected Bindings.empty 15 (rows rest) live
      let head : ResultSet := [(num n, Bindings.empty)]
      have enter : worker.step
          ⟨space, .work (.grounded original expected Bindings.empty 15 (rows (n :: rest)) live), stack, emitted⟩ =
          some (.silent ⟨space, .returning head, .append next :: stack, emitted⟩) :=
        grounded_number_step n original expected (rows rest) live stack emitted
      have save : worker.step ⟨space, .returning head, .append next :: stack, emitted⟩ =
          some (.silent ⟨space, .work next, .prepend head :: stack, emitted⟩) := rfl
      have finish : worker.step ⟨space, .returning (rows rest), .prepend head :: stack, emitted⟩ =
          some (.silent ⟨space, .returning (rows (n :: rest)), stack, emitted⟩) := rfl
      rw [show 3 * (n :: rest).length + 1 + budget = (3 * rest.length + 3 + budget) + 1 by simp; omega,
        worker.run_succ_silent enter]
      rw [show 3 * rest.length + 3 + budget = (3 * rest.length + 2 + budget) + 1 by omega,
        worker.run_succ_silent save]
      rw [show 3 * rest.length + 2 + budget = 3 * rest.length + 1 + (1 + budget) by omega]
      rw [show next = .grounded original expected Bindings.empty 15 (rows rest) live from rfl,
        ih (.prepend head :: stack) (1 + budget), Nat.add_comm 1 budget,
        worker.run_succ_silent finish]

/-- Production visits the real emitted row spine; no final result list is
substituted for a suspended source computation. -/
theorem produced_numbers (inputs : List Int) (live : List Atom) (caller : Option Atom)
    (stack : List Frame) (emitted : ResultSet) : ∀ budget,
    worker.run (4 * inputs.length + 1 + budget)
      ⟨space, .work (.productions 15 (rows inputs) live caller .emitted), stack, emitted⟩ =
      worker.run budget ⟨space, .returning (rows inputs), stack, emitted⟩ := by
  induction inputs generalizing stack with
  | nil =>
      intro budget
      have enter : worker.step
          ⟨space, .work (.productions 15 [] live caller .emitted), stack, emitted⟩ =
          some (.silent ⟨space, .returning [], stack, emitted⟩) := rfl
      simpa [rows, Nat.add_comm 1] using worker.run_succ_silent (fuel := budget) enter
  | cons n rest ih =>
      intro budget
      let next := Task.productions 15 (rows rest) live caller .emitted
      let head : ResultSet := [(num n, Bindings.empty)]
      have enter : worker.step
          ⟨space, .work (.productions 15 (rows (n :: rest)) live caller .emitted), stack, emitted⟩ =
          some (.silent ⟨space, .work (.produced (num n) Bindings.empty 15 live caller .emitted),
            .append next :: stack, emitted⟩) := rfl
      have produce : worker.step
          ⟨space, .work (.produced (num n) Bindings.empty 15 live caller .emitted), .append next :: stack, emitted⟩ =
          some (.silent ⟨space, .returning head, .append next :: stack, emitted⟩) := rfl
      have save : worker.step ⟨space, .returning head, .append next :: stack, emitted⟩ =
          some (.silent ⟨space, .work next, .prepend head :: stack, emitted⟩) := rfl
      have finish : worker.step ⟨space, .returning (rows rest), .prepend head :: stack, emitted⟩ =
          some (.silent ⟨space, .returning (rows (n :: rest)), stack, emitted⟩) := rfl
      rw [show 4 * (n :: rest).length + 1 + budget = (4 * rest.length + 4 + budget) + 1 by simp; omega,
        worker.run_succ_silent enter]
      rw [show 4 * rest.length + 4 + budget = (4 * rest.length + 3 + budget) + 1 by omega,
        worker.run_succ_silent produce]
      rw [show 4 * rest.length + 3 + budget = (4 * rest.length + 2 + budget) + 1 by omega,
        worker.run_succ_silent save]
      rw [show 4 * rest.length + 2 + budget = 4 * rest.length + 1 + (1 + budget) by omega]
      rw [show next = .productions 15 (rows rest) live caller .emitted from rfl,
        ih (.prepend head :: stack) (1 + budget), Nat.add_comm 1 budget,
        worker.run_succ_silent finish]

/-- The ordinary return gate evaluates emitted numeric values under the
superpose operation's declared undemanded result type. -/
theorem returned_numbers (inputs : List Int) (original : Atom) (live : List Atom)
    (stack : List Frame) (emitted : ResultSet) : ∀ budget,
    worker.run (5 * inputs.length + 1 + budget)
      ⟨space, .work (.returns original Atom.undefinedType 15 (rows inputs) live), stack, emitted⟩ =
      worker.run budget ⟨space, .returning (rows inputs), stack, emitted⟩ := by
  induction inputs generalizing stack with
  | nil =>
      intro budget
      have enter : worker.step
          ⟨space, .work (.returns original Atom.undefinedType 15 [] live), stack, emitted⟩ =
          some (.silent ⟨space, .returning [], stack, emitted⟩) := rfl
      simpa [rows, Nat.add_comm 1] using worker.run_succ_silent (fuel := budget) enter
  | cons n rest ih =>
      intro budget
      let next := Task.returns original Atom.undefinedType 15 (rows rest) live
      let head : ResultSet := [(num n, Bindings.empty)]
      have enter : worker.step
          ⟨space, .work (.returns original Atom.undefinedType 15 (rows (n :: rest)) live), stack, emitted⟩ =
          some (.silent ⟨space, .work (.returned original (num n) Atom.undefinedType Bindings.empty 15 live),
            .append next :: stack, emitted⟩) := rfl
      have returned : worker.step
          ⟨space, .work (.returned original (num n) Atom.undefinedType Bindings.empty 15 live), .append next :: stack, emitted⟩ =
          some (.silent ⟨space, .work (.atom (num n) Atom.undefinedType Bindings.empty 15 live),
            .append next :: stack, emitted⟩) := rfl
      have cast : worker.step
          ⟨space, .work (.atom (num n) Atom.undefinedType Bindings.empty 15 live), .append next :: stack, emitted⟩ =
          some (.silent ⟨space, .returning head, .append next :: stack, emitted⟩) := by
        rw [FirstSuccessScopedAdequacy.checked_step_scopedTypes_eq_rawTypes dispatch _ closed_annotations]
        cbv
      have save : worker.step ⟨space, .returning head, .append next :: stack, emitted⟩ =
          some (.silent ⟨space, .work next, .prepend head :: stack, emitted⟩) := rfl
      have finish : worker.step ⟨space, .returning (rows rest), .prepend head :: stack, emitted⟩ =
          some (.silent ⟨space, .returning (rows (n :: rest)), stack, emitted⟩) := rfl
      rw [show 5 * (n :: rest).length + 1 + budget = (5 * rest.length + 5 + budget) + 1 by simp; omega,
        worker.run_succ_silent enter]
      rw [show 5 * rest.length + 5 + budget = (5 * rest.length + 4 + budget) + 1 by omega,
        worker.run_succ_silent returned]
      rw [show 5 * rest.length + 4 + budget = (5 * rest.length + 3 + budget) + 1 by omega,
        worker.run_succ_silent cast]
      rw [show 5 * rest.length + 3 + budget = (5 * rest.length + 2 + budget) + 1 by omega,
        worker.run_succ_silent save]
      rw [show 5 * rest.length + 2 + budget = 5 * rest.length + 1 + (1 + budget) by omega]
      rw [show next = .returns original Atom.undefinedType 15 (rows rest) live from rfl,
        ih (.prepend head :: stack) (1 + budget), Nat.add_comm 1 budget,
        worker.run_succ_silent finish]

/-- The grounded service is entered with the held expression, not with an
already evaluated answer list. -/
theorem superpose_host_step (values : List Atom) (live : List Atom)
    (stack : List Frame) (emitted : ResultSet) :
    worker.step
      ⟨space, .work (.invocation (.ordinary Atom.undefinedType) (superpose values) Bindings.empty 16 live), stack, emitted⟩ =
      some (.silent ⟨space, .work (.grounded (superpose values) Atom.undefinedType Bindings.empty 15
        (values.map fun value => (value, Bindings.empty)) live),
        .producerResults (.ordinary Atom.undefinedType) (superpose values) Bindings.empty 15 live Atom.empty :: stack,
        emitted⟩) := by
  cbv

/-- A complete nonempty host invocation derives its result spine from the
held operand and traverses all existing producer/return continuations. -/
theorem superpose_invocation (first : Int) (rest : List Int) (live : List Atom)
    (stack : List Frame) (emitted : ResultSet) (budget : Nat) :
    worker.run (12 * (first :: rest).length + 7 + budget)
      ⟨space, .work (.invocation (.ordinary Atom.undefinedType)
        (superpose ((first :: rest).map num)) Bindings.empty 16 live), stack, emitted⟩ =
      worker.run budget ⟨space, .returning (rows (first :: rest)), stack, emitted⟩ := by
  let inputs := first :: rest
  let original := superpose (inputs.map num)
  let receiver := Frame.producerResults (.ordinary Atom.undefinedType) original Bindings.empty 15 live Atom.empty
  let returned := Frame.invocationReturn (.ordinary Atom.undefinedType) original 15 live
  have enter : worker.step
      ⟨space, .work (.invocation (.ordinary Atom.undefinedType) original Bindings.empty 16 live), stack, emitted⟩ =
      some (.silent ⟨space, .work (.grounded original Atom.undefinedType Bindings.empty 15 (rows inputs) live),
        receiver :: stack, emitted⟩) := by
    simpa only [List.map_map, Function.comp_def, rows, original, receiver] using
      superpose_host_step (inputs.map num) live stack emitted
  have collect : worker.step ⟨space, .returning (rows inputs), receiver :: stack, emitted⟩ =
      some (.silent ⟨space, .work (.producerResults (.ordinary Atom.undefinedType) original Bindings.empty
        15 live Atom.empty (rows inputs)), stack, emitted⟩) := rfl
  have produce : worker.step
      ⟨space, .work (.producerResults (.ordinary Atom.undefinedType) original Bindings.empty
        15 live Atom.empty (rows inputs)), stack, emitted⟩ =
      some (.silent ⟨space, .work (.productions 15 (rows inputs) (Atom.undefinedType :: live)
        (some original) .emitted), returned :: stack, emitted⟩) := rfl
  have returnGate : worker.step ⟨space, .returning (rows inputs), returned :: stack, emitted⟩ =
      some (.silent ⟨space, .work (.returns original Atom.undefinedType 15 (rows inputs) live), stack, emitted⟩) := rfl
  change worker.run (12 * inputs.length + 7 + budget)
    ⟨space, .work (.invocation (.ordinary Atom.undefinedType) original Bindings.empty 16 live), stack, emitted⟩ = _
  rw [show 12 * inputs.length + 7 + budget = (12 * inputs.length + 6 + budget) + 1 by omega,
    worker.run_succ_silent enter]
  rw [show 12 * inputs.length + 6 + budget = 3 * inputs.length + 1 + (9 * inputs.length + 5 + budget) by omega,
    grounded_numbers inputs original Atom.undefinedType live (receiver :: stack) emitted]
  rw [show 9 * inputs.length + 5 + budget = (9 * inputs.length + 4 + budget) + 1 by omega,
    worker.run_succ_silent collect]
  rw [show 9 * inputs.length + 4 + budget = (9 * inputs.length + 3 + budget) + 1 by omega,
    worker.run_succ_silent produce]
  rw [show 9 * inputs.length + 3 + budget = 4 * inputs.length + 1 + (5 * inputs.length + 2 + budget) by omega,
    produced_numbers inputs (Atom.undefinedType :: live) (some original) (returned :: stack) emitted]
  rw [show 5 * inputs.length + 2 + budget = (5 * inputs.length + 1 + budget) + 1 by omega,
    worker.run_succ_silent returnGate, returned_numbers]

/-- An empty operation completes with Empty at its invocation boundary.
It is not a suspended operation and is not mistaken for a successful number. -/
theorem empty_superpose_invocation (live : List Atom) (stack : List Frame) (emitted : ResultSet) :
    worker.run 10
      ⟨space, .work (.invocation (.ordinary Atom.undefinedType) (superpose []) Bindings.empty 16 live), stack, emitted⟩ =
      ([], .exhausted ⟨space, .returning [(Atom.empty, Bindings.empty)], stack, emitted⟩) := by
  rw [worker_raw _ _ rfl]
  cbv

def superTail (inputs : List Int) (live : List Atom) (stack : List Frame) : List Frame :=
  [.append (.calls Atom.undefinedType 16 [] live),
   .append (.bindingAlternatives (superpose (inputs.map num)) superposeType Atom.undefinedType 16 [] live),
   .filter] ++ stack

def superHeadStack (inputs : List Int) (live : List Atom) (stack : List Frame) : List Frame :=
  [.heads superposeType [.expression (inputs.map num)] 15 (Atom.undefinedType :: live),
   .calls Atom.undefinedType 16 live,
   .append (.bindingAlternatives (superpose (inputs.map num)) superposeType Atom.undefinedType 16 [] live),
   .filter] ++ stack

def superHeadStart (inputs : List Int) (live : List Atom) (stack : List Frame) (emitted : ResultSet) : Configuration :=
  ⟨space, .work (.atom (.symbol "superpose") superposeType Bindings.empty 15
    (superposeType :: .expression (inputs.map num) :: Atom.undefinedType :: live)),
    superHeadStack inputs live stack, emitted⟩

def superHeadReturned (inputs : List Int) (live : List Atom) (stack : List Frame) (emitted : ResultSet) : Configuration :=
  ⟨space, .returning [(.symbol "superpose", Bindings.empty)], superHeadStack inputs live stack, emitted⟩

def superArgumentStack (inputs : List Int) (live : List Atom) (stack : List Frame) : List Frame :=
  [.functionTail (.symbol "superpose"),
   .append (.heads superposeType [.expression (inputs.map num)] 15 [] (Atom.undefinedType :: live)),
   .calls Atom.undefinedType 16 live,
   .append (.bindingAlternatives (superpose (inputs.map num)) superposeType Atom.undefinedType 16 [] live),
   .filter] ++ stack

def superArgumentsStart (inputs : List Int) (live : List Atom) (stack : List Frame) (emitted : ResultSet) : Configuration :=
  ⟨space, .work (.args [.expression (inputs.map num)] [Atom.expressionType] Bindings.empty 15
    (.symbol "superpose" :: Atom.undefinedType :: live)), superArgumentStack inputs live stack, emitted⟩

def superArgumentsReturned (inputs : List Int) (live : List Atom) (stack : List Frame) (emitted : ResultSet) : Configuration :=
  ⟨space, .returning [(argumentPacket [.expression (inputs.map num)], Bindings.empty)],
    superArgumentStack inputs live stack, emitted⟩

theorem superpose_head_entry (inputs : List Int) (live : List Atom) (stack : List Frame) (emitted : ResultSet) :
    worker.run 2
      ⟨space, .work (.bindingAlternatives (superpose (inputs.map num)) superposeType Atom.undefinedType
        16 [Bindings.empty] live), .filter :: stack, emitted⟩ =
      ([], .exhausted (superHeadStart inputs live stack emitted)) := by
  rw [worker_raw _ _ rfl]
  cbv

theorem superpose_head_step (inputs : List Int) (live : List Atom) (stack : List Frame) (emitted : ResultSet) :
    (FirstSuccessRecursiveExecution.Checked.machine dispatch FirstSuccessRecursiveExecution.scopedTypes).step
      ⟨space, .work (.atom (.symbol "superpose")
        (CompletedDelivery.arrowType [Atom.expressionType] Atom.undefinedType) Bindings.empty (14 + 1)
        (superposeType :: .expression (inputs.map num) :: Atom.undefinedType :: live)),
        superHeadStack inputs live stack, emitted⟩ =
      some (.silent ⟨space, .returning [(.symbol "superpose", Bindings.empty)],
        superHeadStack inputs live stack, emitted⟩) := by
  exact HELiteralWorkerDelivery.scoped_closed_head_step space dispatch "superpose"
    [Atom.expressionType] Atom.undefinedType Bindings.empty 14 _ _ emitted superpose_declared
    (by decide) rfl (by decide) (by cbv)

theorem superpose_head_tail (inputs : List Int) (live : List Atom) (stack : List Frame) (emitted : ResultSet) :
    worker.run 2 (superHeadReturned inputs live stack emitted) =
      ([], .exhausted (superArgumentsStart inputs live stack emitted)) := by
  rw [worker_raw _ _ rfl]
  cbv

theorem superpose_arguments (inputs : List Int) (live : List Atom) (stack : List Frame) (emitted : ResultSet) :
    worker.run 9 (superArgumentsStart inputs live stack emitted) =
      ([], .exhausted (superArgumentsReturned inputs live stack emitted)) :=
  held_expression_argument (inputs.map num) 13 (.symbol "superpose" :: Atom.undefinedType :: live)
    (superArgumentStack inputs live stack) emitted

theorem superpose_arguments_tail (inputs : List Int) (live : List Atom) (stack : List Frame) (emitted : ResultSet) :
    worker.run 7 (superArgumentsReturned inputs live stack emitted) =
      ([], .exhausted ⟨space, .work (.invocation (.ordinary Atom.undefinedType)
        (superpose (inputs.map num)) Bindings.empty 16 live), superTail inputs live stack, emitted⟩) := by
  rw [worker_raw _ _ rfl]
  cbv

/-- The actual typed source call reaches its host invocation by checking the
source expression, retaining the selected record, and holding its operand. -/
theorem superpose_source_prefix (inputs : List Int) (live : List Atom)
    (stack : List Frame) (emitted : ResultSet) :
    worker.run 24
      ⟨space, .work (.atom (superpose (inputs.map num)) number Bindings.empty 18 live), stack, emitted⟩ =
      ([], .exhausted ⟨space, .work (.invocation (.ordinary Atom.undefinedType)
        (superpose (inputs.map num)) Bindings.empty 16 live), superTail inputs live stack, emitted⟩) := by
  rw [show 24 = 3 + 21 from rfl,
    worker.established_and_pending 3 21 _ _ [] (source_superpose_selection inputs live stack emitted)]
  simp only [List.nil_append]
  rw [show 21 = 2 + 19 from rfl,
    worker.established_and_pending 2 19 _ _ [] (superpose_head_entry inputs live stack emitted)]
  simp only [List.nil_append]
  have castRun := (FirstSuccessRecursiveExecution.Checked.machine dispatch
    FirstSuccessRecursiveExecution.scopedTypes).run_succ_silent (fuel := 18)
      (superpose_head_step inputs live stack emitted)
  change worker.run 19 (superHeadStart inputs live stack emitted) =
    worker.run 18 (superHeadReturned inputs live stack emitted) at castRun
  rw [castRun, show 18 = 2 + 16 from rfl,
    worker.established_and_pending 2 16 _ _ [] (superpose_head_tail inputs live stack emitted)]
  simp only [List.nil_append]
  rw [show 16 = 9 + 7 from rfl,
    worker.established_and_pending 9 7 _ _ [] (superpose_arguments inputs live stack emitted),
    superpose_arguments_tail]
  rfl

theorem rows_success_priority (inputs : List Int) : successPriority (rows inputs) = rows inputs := by
  apply HEReturns.keep_clean
  intro row member
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp member
  rfl

theorem superpose_drain (inputs : List Int) (live : List Atom) (stack : List Frame) (emitted : ResultSet) :
    worker.run 7 ⟨space, .returning (rows inputs), superTail inputs live stack, emitted⟩ =
      ([], .exhausted ⟨space, .returning (rows inputs), stack, emitted⟩) := by
  rw [worker_raw _ _ rfl]
  simp [Machine.run, superTail, FirstSuccessRecursiveExecution.Checked.machine,
    RecursiveMachine.Checked.guardMachine, FirstSuccessRecursiveExecution.Checked.blocked,
    RecursiveMachine.Checked.frameReady, FirstSuccessRecursiveStrategy.taskReady,
    RecursiveMachine.Checked.taskReady, FirstSuccessRecursiveExecution.machine,
    FirstSuccessRecursiveExecution.next, FirstSuccessRecursiveStrategy.enter,
    RecursiveMachine.enter, RecursiveMachine.resume, Transition.relabel, rows_success_priority]

/-- Arbitrary nonempty integer superpositions run to their complete return
frontier on the existing worker, with every duplicate and caller frame kept. -/
theorem superpose_source_returns (first : Int) (rest : List Int) (live : List Atom)
    (stack : List Frame) (emitted : ResultSet) :
    worker.run (12 * (first :: rest).length + 38)
      ⟨space, .work (.atom (superpose ((first :: rest).map num)) number Bindings.empty 18 live), stack, emitted⟩ =
      ([], .exhausted ⟨space, .returning (rows (first :: rest)), stack, emitted⟩) := by
  rw [show 12 * (first :: rest).length + 38 = 24 + (12 * (first :: rest).length + 7 + 7) by omega,
    worker.established_and_pending 24 _ _ _ [] (superpose_source_prefix (first :: rest) live stack emitted)]
  simp only [List.nil_append]
  rw [superpose_invocation, superpose_drain]

theorem empty_superpose_source_returns (live : List Atom) (stack : List Frame) (emitted : ResultSet) :
    worker.run 41
      ⟨space, .work (.atom (superpose []) number Bindings.empty 18 live), stack, emitted⟩ =
      ([], .exhausted ⟨space, .returning [(Atom.empty, Bindings.empty)], stack, emitted⟩) := by
  have enteredSource := superpose_source_prefix [] live stack emitted
  simp only [List.map_nil] at enteredSource
  rw [show 41 = 24 + 17 from rfl,
    worker.established_and_pending 24 17 _ _ [] enteredSource]
  simp only [List.nil_append]
  rw [show 17 = 10 + 7 from rfl,
    worker.established_and_pending 10 7 _ _ [] (empty_superpose_invocation live (superTail [] live stack) emitted)]
  simp only [List.nil_append]
  rw [worker_raw _ _ rfl]
  cbv


/-- A nonliteral source argument may pass source applicability. It is not
the same syntax as any of the integer values subsequently emitted. -/
theorem source_not_delivered_integer (values : List Atom) (n : Int) : superpose values ≠ num n := by
  simp [superpose, apply, num]

theorem superpose_duplicates_retained (n : Int) :
    dispatch.execute (.symbol "superpose") [.expression [num n, num n]] =
      .ok [(num n, Bindings.empty), (num n, Bindings.empty)] := rfl

theorem surface_not_supported_by_plain_worker (inputs : List Int) :
    minimalCoreSupported (apply "collapse-bind" [squareSuperpose inputs]) = false := rfl

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFiniteSuperposeSource
