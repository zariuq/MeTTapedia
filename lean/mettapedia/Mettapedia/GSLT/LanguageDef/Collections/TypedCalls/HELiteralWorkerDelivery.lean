import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.FirstSuccessArgumentBoundary

/-!
# Literal argument delivery in the checked first-success worker

The worker's existing argument frames deliver integer operands at Number
without changing their binding record. The proof composes one checked cast
with the actual argument continuation steps; it does not unfold a whole
program execution or introduce another evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HELiteralWorkerDelivery

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open RecursiveTasks FirstSuccessRecursiveExecution
open FirstSuccessScopedAdequacy.UniversalScopedCastAndHeadBoundary

def number : Atom := .symbol "Number"
def num (value : Int) : Atom := .grounded (.int value)

/-- This is a local query contract, not a global closed-annotation condition.
The raw and scoped policies both satisfy it at integer literals. -/
def NumericPolicy (policy : TypePolicy) : Prop :=
  ∀ state bindings n, policy.types state bindings (num n) number = [number]

theorem raw_numeric : NumericPolicy rawTypes := by
  intro state bindings n
  rfl

theorem scoped_numeric : NumericPolicy scopedTypes := by
  intro state bindings n
  exact invocationTypes_closed state bindings (num n) number (by
    intro signature member
    change signature ∈ [number] at member
    obtain rfl := List.mem_singleton.mp member
    rfl)

theorem numeric_cast_lookup (space : Space) (bindings : Bindings) (n : Int) (depth : Nat)
    (lookup : TypeLookup) (queried : lookup bindings (num n) number = [number]) :
    typeCast (num n) number space bindings (depth + 2) lookup = [(num n, bindings)] := by
  have same : typeCast (num n) number space bindings (depth + 2) lookup =
      typeCast (num n) number space bindings (depth + 2) := by
    unfold typeCast
    rw [queried]
    rfl
  rw [same]
  exact FirstSuccessArgumentBoundary.numeric_cast space bindings n depth

theorem numeric_covered_lookup (space : Space) (bindings : Bindings) (n : Int) (depth : Nat)
    (lookup : TypeLookup) (queried : lookup bindings (num n) number = [number]) :
    typeCastCovered (num n) number space bindings (depth + 2) lookup = true := by
  rw [typeCastCovered_of_singleton_lookup _ _ _ _ _ _ _ queried]
  have raw := FirstSuccessArgumentBoundary.numeric_cast_covered space bindings n depth
  rw [typeCastCovered_of_singleton_lookup _ _ _ _ _ _ _ rfl] at raw
  exact raw

theorem numeric_step (space : Space) (dispatch : GroundedDispatch)
    (policy : TypePolicy) (numeric : NumericPolicy policy)
    (bindings : Bindings) (n : Int) (depth : Nat) (live : List Atom)
    (stack : List Frame) (emitted : ResultSet) :
    (Checked.machine dispatch policy).step
      ⟨space, .work (.atom (num n) number bindings (depth + 3) live), stack, emitted⟩ =
        some (.silent ⟨space, .returning [(num n, bindings)], stack, emitted⟩) := by
  have queried := numeric
    ⟨space, .work (.atom (num n) number bindings (depth + 3) live), stack, emitted⟩ bindings n
  have covered := numeric_covered_lookup space bindings n depth _ queried
  have cast := numeric_cast_lookup space bindings n depth _ queried
  dsimp only [num, number] at covered cast
  simp [Checked.machine, RecursiveMachine.Checked.guardMachine, Checked.blocked,
    FirstSuccessRecursiveStrategy.taskReady, RecursiveMachine.Checked.taskReady,
    FirstSuccessRecursiveExecution.machine, FirstSuccessRecursiveExecution.next,
    FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
    isEmptyOrError, isEmptyAtom, isErrorAtom, num, number, getMetaType,
    Atom.empty, Atom.atomType, Atom.variableType, Atom.symbolType, Atom.groundedType,
    covered, cast, Transition.relabel]

/-- Operator delivery is likewise one checked cast. Lookup and matcher
coverage are local leaf obligations, not a premise about a whole run. -/
theorem closed_head_step (space : Space) (dispatch : GroundedDispatch) (policy : TypePolicy)
    (head : String) (params : List Atom) (range : Atom) (bindings : Bindings)
    (depth : Nat) (live : List Atom) (stack : List Frame) (emitted : ResultSet)
    (notEmpty : head ≠ "Empty")
    (ground : atomVariables (CompletedDelivery.arrowType params range) = [])
    (enough : CompletedDelivery.matchFuel (CompletedDelivery.arrowType params range) ≤ depth)
    (queried : policy.types
      ⟨space, .work (.atom (.symbol head) (CompletedDelivery.arrowType params range) bindings
        (depth + 1) live), stack, emitted⟩ bindings (.symbol head)
          (CompletedDelivery.arrowType params range) = [CompletedDelivery.arrowType params range])
    (matchCovered : matchTypesCovered (CompletedDelivery.arrowType params range)
      (CompletedDelivery.arrowType params range) bindings depth = true) :
    (Checked.machine dispatch policy).step
      ⟨space, .work (.atom (.symbol head) (CompletedDelivery.arrowType params range) bindings
        (depth + 1) live), stack, emitted⟩ =
        some (.silent ⟨space, .returning [(.symbol head, bindings)], stack, emitted⟩) := by
  have covered := typeCastCovered_of_singleton_lookup (.symbol head)
    (CompletedDelivery.arrowType params range) (CompletedDelivery.arrowType params range)
    space bindings depth _ queried
  rw [matchCovered] at covered
  have matched := CompletedDelivery.matchTypes_accepted ground
    (CompletedDelivery.accepts_self (CompletedDelivery.arrowType params range)) bindings enough
  have cast := typeCast_of_singleton_lookup (.symbol head)
    (CompletedDelivery.arrowType params range) (CompletedDelivery.arrowType params range)
    space bindings depth _ bindings [] queried matched
  simp only [List.map_cons, List.map_nil] at cast
  simp [Checked.machine, RecursiveMachine.Checked.guardMachine, Checked.blocked,
    FirstSuccessRecursiveStrategy.taskReady, RecursiveMachine.Checked.taskReady,
    FirstSuccessRecursiveExecution.machine, FirstSuccessRecursiveExecution.next,
    FirstSuccessRecursiveStrategy.enter, RecursiveMachine.enter,
    CompletedDelivery.isEmptyOrError_symbol notEmpty, getMetaType,
    Atom.atomType, Atom.variableType, Atom.symbolType,
    covered, cast, Transition.relabel]

theorem scoped_closed_head_step (space : Space) (dispatch : GroundedDispatch)
    (head : String) (params : List Atom) (range : Atom) (bindings : Bindings)
    (depth : Nat) (live : List Atom) (stack : List Frame) (emitted : ResultSet)
    (declared : getAtomTypes space (.symbol head) = [CompletedDelivery.arrowType params range])
    (notEmpty : head ≠ "Empty")
    (ground : atomVariables (CompletedDelivery.arrowType params range) = [])
    (enough : CompletedDelivery.matchFuel (CompletedDelivery.arrowType params range) ≤ depth)
    (matchCovered : matchTypesCovered (CompletedDelivery.arrowType params range)
      (CompletedDelivery.arrowType params range) bindings depth = true) :
    (Checked.machine dispatch scopedTypes).step
      ⟨space, .work (.atom (.symbol head) (CompletedDelivery.arrowType params range) bindings
        (depth + 1) live), stack, emitted⟩ =
        some (.silent ⟨space, .returning [(.symbol head, bindings)], stack, emitted⟩) := by
  apply closed_head_step space dispatch scopedTypes head params range bindings depth live stack emitted
    notEmpty ground enough ?_ matchCovered
  dsimp only [scopedTypes]
  rw [invocationTypes_closed _ _ _ _ (by
    intro signature member
    rw [declared, List.mem_singleton] at member
    simpa only [member] using ground), declared]

theorem unary_number_arrow_covered (bindings : Bindings) (extra : Nat) :
    matchTypesCovered (CompletedDelivery.arrowType [number] number)
      (CompletedDelivery.arrowType [number] number) bindings (extra + 5) = true := by
  cbv

theorem binary_number_arrow_covered (bindings : Bindings) (extra : Nat) :
    matchTypesCovered (CompletedDelivery.arrowType [number, number] number)
      (CompletedDelivery.arrowType [number, number] number) bindings (extra + 6) = true := by
  cbv

/-- The exact worker block for a finite Number argument spine. The evaluator
depth bound covers every literal cast; administrative budget remains separate.
Caller bindings, live roots, saved frames and emitted history are unchanged. -/
theorem numeric_arguments (space : Space) (dispatch : GroundedDispatch)
    (policy : TypePolicy) (numeric : NumericPolicy policy) (numbers : List Int)
    (bindings : Bindings) (depth : Nat) (live : List Atom)
    (stack : List Frame) (emitted : ResultSet) : ∀ budget,
    (Checked.machine dispatch policy).run (8 * numbers.length + 1 + budget)
      ⟨space, .work (.args (numbers.map num) (List.replicate numbers.length number)
        bindings (depth + numbers.length + 3) live), stack, emitted⟩ =
      (Checked.machine dispatch policy).run budget
        ⟨space, .returning [(argumentPacket (numbers.map num), bindings)], stack, emitted⟩ := by
  induction numbers generalizing live stack with
  | nil =>
      intro budget
      have step : (Checked.machine dispatch policy).step
          ⟨space, .work (.args [] [] bindings (depth + 3) live), stack, emitted⟩ =
            some (.silent ⟨space, .returning [(argumentPacket [], bindings)], stack, emitted⟩) := rfl
      simpa only [List.length_nil, List.map_nil, List.replicate_zero, Nat.mul_zero,
        Nat.add_zero, Nat.add_comm 1] using
        (Checked.machine dispatch policy).run_succ_silent (fuel := budget) step
  | cons first rest ih =>
      intro budget
      let m := Checked.machine dispatch policy
      let remaining := rest.map num
      let types := List.replicate rest.length number
      let leafDepth := depth + rest.length + 3
      let headFrame := Frame.argumentHeads (num first) remaining types leafDepth live
      let appendFrame := Frame.append (.argumentHeads (num first) remaining types leafDepth [] live)
      let tailStack := Frame.argumentTail (num first) :: appendFrame :: stack
      let packet := (argumentPacket (num first :: remaining), bindings)
      have enterArgs : m.step
          ⟨space, .work (.args (num first :: remaining) (number :: types) bindings (leafDepth + 1) live),
            stack, emitted⟩ =
          some (.silent ⟨space, .work (.atom (num first) number bindings leafDepth
            (remaining ++ types ++ live)), headFrame :: stack, emitted⟩) := rfl
      have cast := numeric_step space dispatch policy numeric bindings first (depth + rest.length)
        (remaining ++ types ++ live) (headFrame :: stack) emitted
      have receiveHead : m.step
          ⟨space, .returning [(num first, bindings)], headFrame :: stack, emitted⟩ =
          some (.silent ⟨space, .work (.argumentHeads (num first) remaining types leafDepth
            [(num first, bindings)] live), stack, emitted⟩) := rfl
      have enterTail : m.step
          ⟨space, .work (.argumentHeads (num first) remaining types leafDepth
            [(num first, bindings)] live), stack, emitted⟩ =
          some (.silent ⟨space, .work (.args remaining types bindings leafDepth (num first :: live)),
            tailStack, emitted⟩) :=
        FirstSuccessArgumentBoundary.checked_grounded_argument_step space dispatch policy
          (num first) remaining types leafDepth (.int first) bindings [] live stack emitted
      have receiveTail : m.step
          ⟨space, .returning [(argumentPacket remaining, bindings)], tailStack, emitted⟩ =
          some (.silent ⟨space, .returning [packet], appendFrame :: stack, emitted⟩) := by
        simp [m, Checked.machine, RecursiveMachine.Checked.guardMachine, Checked.blocked,
          RecursiveMachine.Checked.frameReady, FirstSuccessRecursiveExecution.machine,
          FirstSuccessRecursiveExecution.next, RecursiveMachine.resume, RecursiveTasks.argumentTail,
          tailStack, packet, argumentPacket, argumentsSucceeded, unpackArguments, argumentValues,
          Transition.relabel]
      have appendTail : m.step
          ⟨space, .returning [packet], appendFrame :: stack, emitted⟩ =
          some (.silent ⟨space, .work (.argumentHeads (num first) remaining types leafDepth [] live),
            .prepend [packet] :: stack, emitted⟩) := rfl
      have emptyTail : m.step
          ⟨space, .work (.argumentHeads (num first) remaining types leafDepth [] live),
            .prepend [packet] :: stack, emitted⟩ =
          some (.silent ⟨space, .returning [], .prepend [packet] :: stack, emitted⟩) := rfl
      have returnPacket : m.step
          ⟨space, .returning [], .prepend [packet] :: stack, emitted⟩ =
          some (.silent ⟨space, .returning [packet], stack, emitted⟩) := by
        simp [m, Checked.machine, RecursiveMachine.Checked.guardMachine, Checked.blocked,
          RecursiveMachine.Checked.frameReady, FirstSuccessRecursiveExecution.machine,
          FirstSuccessRecursiveExecution.next, RecursiveMachine.resume, Transition.relabel]
      have tail := ih (num first :: live) tailStack (4 + budget)
      change m.run (8 * (rest.length + 1) + 1 + budget)
        ⟨space, .work (.args (num first :: remaining) (number :: types)
          bindings (leafDepth + 1) live), stack, emitted⟩ =
          m.run budget ⟨space, .returning [packet], stack, emitted⟩
      rw [show 8 * (rest.length + 1) + 1 + budget =
          (8 * rest.length + 8 + budget) + 1 by omega,
        m.run_succ_silent enterArgs]
      rw [show 8 * rest.length + 8 + budget = (8 * rest.length + 7 + budget) + 1 by omega,
        m.run_succ_silent cast]
      rw [show 8 * rest.length + 7 + budget = (8 * rest.length + 6 + budget) + 1 by omega,
        m.run_succ_silent receiveHead]
      rw [show 8 * rest.length + 6 + budget = (8 * rest.length + 5 + budget) + 1 by omega,
        m.run_succ_silent enterTail]
      rw [show 8 * rest.length + 5 + budget = (8 * rest.length + 1) + (4 + budget) by omega]
      rw [tail]
      rw [show 4 + budget = (3 + budget) + 1 by omega, m.run_succ_silent receiveTail]
      rw [show 3 + budget = (2 + budget) + 1 by omega, m.run_succ_silent appendTail]
      rw [show 2 + budget = (1 + budget) + 1 by omega, m.run_succ_silent emptyTail]
      rw [Nat.add_comm 1 budget, m.run_succ_silent returnPacket]

/-- A caller supplies its existing evaluator depth; it need not rewrite the
whole saved state into the induction's canonical arithmetic expression. -/
theorem numeric_arguments_at_depth (space : Space) (dispatch : GroundedDispatch)
    (policy : TypePolicy) (numeric : NumericPolicy policy) (numbers : List Int)
    (bindings : Bindings) (fuel : Nat) (enough : numbers.length + 3 ≤ fuel)
    (live : List Atom) (stack : List Frame) (emitted : ResultSet) (budget : Nat) :
    (Checked.machine dispatch policy).run (8 * numbers.length + 1 + budget)
      ⟨space, .work (.args (numbers.map num) (List.replicate numbers.length number)
        bindings fuel live), stack, emitted⟩ =
      (Checked.machine dispatch policy).run budget
        ⟨space, .returning [(argumentPacket (numbers.map num), bindings)], stack, emitted⟩ := by
  have exactDepth : fuel - (numbers.length + 3) + numbers.length + 3 = fuel := by omega
  simpa only [exactDepth] using numeric_arguments space dispatch policy numeric numbers bindings
    (fuel - (numbers.length + 3)) live stack emitted budget

theorem one_argument (space : Space) (dispatch : GroundedDispatch)
    (policy : TypePolicy) (numeric : NumericPolicy policy) (n : Int)
    (bindings : Bindings) (fuel : Nat) (enough : 4 ≤ fuel)
    (live : List Atom) (stack : List Frame) (emitted : ResultSet) (budget : Nat) :
    (Checked.machine dispatch policy).run (9 + budget)
      ⟨space, .work (.args [num n] [number] bindings fuel live), stack, emitted⟩ =
      (Checked.machine dispatch policy).run budget
        ⟨space, .returning [(argumentPacket [num n], bindings)], stack, emitted⟩ :=
  numeric_arguments_at_depth space dispatch policy numeric [n] bindings fuel enough live stack emitted budget

theorem two_arguments (space : Space) (dispatch : GroundedDispatch)
    (policy : TypePolicy) (numeric : NumericPolicy policy) (first second : Int)
    (bindings : Bindings) (fuel : Nat) (enough : 5 ≤ fuel)
    (live : List Atom) (stack : List Frame) (emitted : ResultSet) (budget : Nat) :
    (Checked.machine dispatch policy).run (17 + budget)
      ⟨space, .work (.args [num first, num second] [number, number] bindings fuel live), stack, emitted⟩ =
      (Checked.machine dispatch policy).run budget
        ⟨space, .returning [(argumentPacket [num first, num second], bindings)], stack, emitted⟩ :=
  numeric_arguments_at_depth space dispatch policy numeric [first, second] bindings fuel enough live stack emitted budget

namespace Controls

def record : Bindings := Bindings.empty.assign "saved" (num 9)
def caller : List Frame := [.prepend [(num 11, record)]]
def history : ResultSet := [(num 12, record)]

theorem distinct_operands_keep_record_and_caller :
    (Checked.machine GroundedDispatch.none scopedTypes).run 17
      ⟨Space.empty, .work (.args [num 2, num (-2)] [number, number] record 8 [num 10]), caller, history⟩ =
        ([], .exhausted ⟨Space.empty,
          .returning [(argumentPacket [num 2, num (-2)], record)], caller, history⟩) := by
  simpa only [Nat.add_zero, Machine.run] using
    two_arguments Space.empty GroundedDispatch.none scopedTypes scoped_numeric 2 (-2) record 8
      (by decide) [num 10] caller history 0

theorem too_little_depth_suspends :
    (Checked.machine GroundedDispatch.none scopedTypes).run 1
      ⟨Space.empty, .work (.args [num 2] [number] record 0 []), caller, history⟩ =
      ([], .suspended RecursiveMachine.Checked.ResourceRequest.evaluationDepth
        ⟨Space.empty, .work (.args [num 2] [number] record 0 []), caller, history⟩) := rfl

theorem wrong_formal_keeps_type_error :
    (Checked.machine GroundedDispatch.none scopedTypes).step
      ⟨Space.empty, .work (.atom (num 2) (.symbol "String") record 4 []), caller, history⟩ =
        some (.silent ⟨Space.empty,
          .returning [(mkError (num 2) (.badType (.symbol "String") number), record)],
          caller, history⟩) := rfl

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HELiteralWorkerDelivery
