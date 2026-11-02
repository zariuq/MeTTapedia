import Mettapedia.Machines.ContextualInvocation

/-!
# Completing retained prepared returns

The array loop appends the type-completion outcomes for each reached value and
binding frame. The reference enumerates the producer's completed frontier and
concatenates its checked answers. A rejected type can produce errors or no
answers, but cannot select another invocation of the producer.

The completion callback is the established dialect value/type service; this
model does not prove its type inference algorithm. Native provenance marks,
compiler argument readiness, C ownership and allocation remain correspondence
obligations. In particular, an unmarked HE-compat expression is not certified
as a completed operand by this result.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PreparedReturnCompletion

open NativeCallReturn

variable {Value Fault Delay Context Answer : Type}

def appendChecked (check : Context → Value → List Answer) (context : Context)
    (answers : List Answer) (value : Value) : List Answer :=
  answers ++ check context value

/-- Ordered source completion, independently stated using list concatenation. -/
def reference (check : Context → Value → List Answer) (context : Context)
    (values : List Value) : List Answer :=
  values.flatMap (check context)

/-- The accumulator loop over the producer-owned array. -/
def loop (check : Context → Value → List Answer) (context : Context)
    (values : Array Value) (answers : List Answer := []) : List Answer :=
  values.foldl (appendChecked check context) answers

private theorem fold_checked (check : Context → Value → List Answer) (context : Context)
    (values : List Value) (answers : List Answer) :
    values.foldl (appendChecked check context) answers =
      answers ++ reference check context values := by
  induction values generalizing answers with
  | nil => simp [reference]
  | cons first later ih =>
      simp only [List.foldl_cons, appendChecked, ih, reference,
        List.flatMap_cons, List.append_assoc]

theorem loop_refines (check : Context → Value → List Answer) (context : Context)
    (values : Array Value) (answers : List Answer) :
    loop check context values answers = answers ++ reference check context values.toList := by
  rw [loop, ← Array.foldl_toList]
  exact fold_checked check context values.toList answers

theorem split_completion (check : Context → Value → List Answer) (context : Context)
    (first later : Array Value) (answers : List Answer) :
    loop check context later (loop check context first answers) =
      loop check context (first ++ later) answers := by
  simp [loop_refines, reference, List.flatMap_append, List.append_assoc]

/-- Completion consumes an entered packet, rather than inferring admission
from how many checked outcomes happen to survive. -/
def complete (check : Context → Value → List Answer) (context : Context) :
    Source Value Fault Delay → Except Stop (List Answer)
  | .one (.value .completed value) => .ok (check context value)
  | .frontier .completed values => .ok (loop check context values)
  | .failure => .ok []
  | .interrupted => .error .cancelled
  | _ => .error .hostFailure

private def packetAnswers (check : Context → Value → List Answer) :
    Returned Value Fault Delay Context → List Answer
  | (context, .value .completed value) => check context value
  | _ => []

/-- The completion loop joins the existing tagged frontier observer. -/
theorem frontier_completion_refines (check : Context → Value → List Answer)
    (context : Context) (values : Array Value) :
    complete (Fault := Fault) (Delay := Delay) check context (.frontier .completed values) =
      .ok ((meaning (Fault := Fault) (Delay := Delay) (.frontier .completed values) context).1.flatMap (packetAnswers check)) := by
  simp [complete, loop_refines, reference, meaning, packetAnswers, List.flatMap_map]

/-- Duplicate returned occurrences keep duplicate checked outcomes. -/
theorem duplicate_completion (check : Context → Value → List Answer)
    (context : Context) (value : Value) :
    complete (Fault := Fault) (Delay := Delay) check context
        (.frontier .completed #[value, value]) =
      .ok (check context value ++ check context value) := by
  simp [complete, loop_refines, reference]

theorem empty_completion_is_entered (check : Context → Value → List Answer)
    (context : Context) :
    complete (Fault := Fault) (Delay := Delay) check context (.frontier .completed #[]) = .ok [] := by
  simp [complete, loop_refines, reference]

theorem expression_is_not_completed (check : Context → Value → List Answer)
    (context : Context) (value : Value) :
    complete (Fault := Fault) (Delay := Delay) check context (.one (.value .expression value)) =
      .error .hostFailure := rfl

variable {Input Call World : Type}

/-- A saved caller consumes only its actual result and reached context.
There is no source-expression fallback after this phase. -/
def finishEntered (check : World → Context → Value → List Answer) (context : Context)
    (frame : Invocation.Frame Input Call World Value Fault Delay) :
    Option (World × Except Stop (List Answer) × Nat × Nat) :=
  match frame.control with
  | .deliver returned => some (frame.world, complete (check frame.world) context returned,
      frame.nativeEntries, frame.authoredEntries)
  | _ => none

/-- Even if every value is rejected by its type check, producer work and
committed effects occur once, with no authored retry. -/
theorem entry_completion_once (program : Invocation.Program Input Call World Value Fault Delay)
    (check : World → Context → Value → List Answer) (world : World) (input : Input)
    (context : Context) (call : Call) (admitted : program.admission world input = some call) :
    finishEntered check context
        (Invocation.step program (Invocation.step program (Invocation.initial world input))) =
      some ((program.invoke world call).1,
        complete (check (program.invoke world call).1) context (program.invoke world call).2,
        1, 0) := by
  rw [Invocation.entered_call_exact program world input call admitted]
  rfl

namespace ReadyArguments

open ContextualInvocation.ArgumentWorklist

variable {Scope Continuation : Type}

def completed (slot : Operand Scope) : Operand Scope :=
  {slot with demanded := false}

/-- The existing ordinary lowering enters the saved callee directly when
all argument visits have already completed. Their lexical fields are retained. -/
theorem ready_lowering (slots : List (Operand Scope)) (continuation : Continuation)
    (older : List (Goal Scope Continuation)) :
    lower false (slots.map completed) continuation older = .resume continuation :: older := by
  rw [lowering_refines]
  simp [source, operandProgram, completed]

/-- Interpretation callbacks cannot affect this schedule: ready operands
introduce no computation visit, only the actual pending continuation. -/
theorem ready_contextual_lowering
    {Call Effect Delay Suspension : Type}
    (compute otherCompute : Scope → Nat → ContextualCBPV.Code Value Call Effect Fault Delay Suspension)
    (check : Nat → ContextualCBPV.Code Value Call Effect Fault Delay Suspension)
    (resume : Continuation → ContextualCBPV.Code Value Call Effect Fault Delay Suspension)
    (slots : List (Operand Scope)) (continuation : Continuation)
    (finish : ContextualCBPV.Code Value Call Effect Fault Delay Suspension) :
    Contextual.interpret compute check resume
        (lower false (slots.map completed) continuation []) finish =
      Contextual.interpret otherCompute check resume
        (lower false (slots.map completed) continuation []) finish := by
  simp [ready_lowering, Contextual.interpret]

end ReadyArguments

namespace Controls

def checker (_ : Unit) (value : Nat) : List (Nat ⊕ Nat) :=
  if value = 7 then [.inr 99] else [.inl value]

theorem type_errors_preserve_occurrences :
    complete (Fault := Unit) (Delay := Unit) checker () (.frontier .completed #[7, 7, 9]) =
      .ok [.inr 99, .inr 99, .inl 9] := by decide +kernel

theorem rejected_value_does_not_retry :
    let program : Invocation.Program Unit Unit Nat Nat Unit Unit :=
      ⟨fun _ _ => some (), fun world _ => (world + 1, .one (.value .completed 7))⟩
    finishEntered (fun _ => checker) ()
      (Invocation.step program (Invocation.step program (Invocation.initial 0 ()))) =
        some (1, .ok [.inr 99], 1, 0) := by decide +kernel

theorem interruption_is_not_empty_success :
    complete (Fault := Unit) (Delay := Unit) checker () .interrupted ≠
      complete (Fault := Unit) (Delay := Unit) checker () .failure := by decide +kernel

end Controls
end Mettapedia.Machines.PreparedReturnCompletion
