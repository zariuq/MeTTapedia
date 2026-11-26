import Mettapedia.Languages.MeTTa.HE.RecursiveTasks
import Mettapedia.Languages.MeTTa.HE.TypedApplyEncoding

/-!
# Data of contextual HE values and activations

The same printed expression at two different readiness statuses can
enter evaluation differently. A transport of retained work therefore
encodes the annotated value, not just its erased atom. An activation
retains both its logical bindings and its annotated environment; reading
those fields does not grant the proof of their logical compatibility.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.ContextualData

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval
open Spec.Eval.Completed (ArgumentRequest Boundary Frame Result)
open Spec.Eval.Steps (EquationWork)
open RecursiveTasks.Contextual (Task Continuation)

def statusData : Entry.Status → Atom
  | .active => .grounded (.bool false)
  | .held => .grounded (.bool true)

theorem statusData_injective : Function.Injective statusData := by
  intro a b same
  cases a <;> cases b <;> first | rfl | cases same

def valueData : Entry.Value → Atom
  | .symbol name => .symbol name
  | .var name => .var name
  | .grounded value => .grounded value
  | .expression status children => .expression (statusData status :: children.map valueData)

theorem valueData_injective : Function.Injective valueData := by
  intro first
  induction first using Entry.Value.rec (motive_2 := fun first =>
      ∀ {second : List Entry.Value}, first.map valueData = second.map valueData → first = second) with
  | symbol name => intro b same; cases b <;> simp_all [valueData]
  | var name => intro b same; cases b <;> simp_all [valueData]
  | grounded value => intro b same; cases b <;> simp_all [valueData]
  | expression status children ih =>
    intro b same
    cases b with
    | symbol | var | grounded => simp [valueData] at same
    | expression secondStatus secondChildren =>
      have fields := List.cons.inj (Atom.expression.inj
        (show Atom.expression (statusData status :: children.map valueData) =
          Atom.expression (statusData secondStatus :: secondChildren.map valueData) by
          simpa only [valueData] using same))
      exact congrArg₂ Entry.Value.expression (statusData_injective fields.1) (ih fields.2)
  | nil same =>
    rename_i b
    cases b with
    | nil => rfl
    | cons => cases same
  | cons value tail headIH tailIH same =>
    rename_i b
    cases b with
    | nil => cases same
    | cons value' tail' =>
      have fields := List.cons.inj same
      exact congrArg₂ List.cons (headIH fields.1) (tailIH fields.2)

def sequence {A : Type} (encode : A → Atom) (entries : List A) : Atom :=
  .expression (entries.map encode)

theorem sequence_injective {A : Type} {encode : A → Atom} (injective : Function.Injective encode) :
    Function.Injective (sequence encode) :=
  fun _ _ same => (List.map_injective_iff.mpr injective) (Atom.expression.inj same)

def optional {A : Type} (encode : A → Atom) (entry : Option A) : Atom :=
  sequence encode entry.toList

theorem optional_injective {A : Type} {encode : A → Atom} (injective : Function.Injective encode) :
    Function.Injective (optional encode) := by
  intro a b same
  have lists := sequence_injective injective same
  cases a <;> cases b <;> simp_all

def pair {A B : Type} (encodeA : A → Atom) (encodeB : B → Atom) (entry : A × B) : Atom :=
  .expression [encodeA entry.1, encodeB entry.2]

theorem pair_injective {A B : Type} {encodeA : A → Atom} {encodeB : B → Atom}
    (first : Function.Injective encodeA) (second : Function.Injective encodeB) :
    Function.Injective (pair encodeA encodeB) := by
  intro a b equal
  have fields := List.cons.inj (Atom.expression.inj equal)
  exact Prod.ext (first fields.1) (second (List.cons.inj fields.2).1)

def environmentData : Entry.Value.Environment → Atom :=
  sequence (pair Atom.symbol valueData)

theorem environmentData_injective : Function.Injective environmentData :=
  sequence_injective (pair_injective (fun _ _ => Atom.symbol.inj) valueData_injective)

theorem bindingsData_injective : Function.Injective TypedApplyEncoding.bindingsData := by
  intro first second same
  have read := congrArg TypedApplyEncoding.readBindings same
  simpa only [TypedApplyEncoding.readBindings_bindingsData, Option.some.injEq] using read

def frameData (frame : Frame) : Atom :=
  .expression [TypedApplyEncoding.bindingsData frame.bindings, environmentData frame.environment]

theorem frameData_injective : Function.Injective frameData := by
  intro first second same
  cases first with
  | mk bindings environment evidence =>
    cases second with
    | mk nextBindings nextEnvironment nextEvidence =>
      have fields := List.cons.inj (Atom.expression.inj same)
      obtain rfl : bindings = nextBindings := bindingsData_injective fields.1
      obtain rfl : environment = nextEnvironment := environmentData_injective (List.cons.inj fields.2).1
      rfl

def resultData : Result → Atom := pair valueData frameData

theorem resultData_injective : Function.Injective resultData :=
  pair_injective valueData_injective frameData_injective

def resultsData : List Result → Atom := sequence resultData

theorem resultsData_injective : Function.Injective resultsData :=
  sequence_injective resultData_injective

def namesData : List String → Atom := sequence Atom.symbol

theorem namesData_injective : Function.Injective namesData :=
  sequence_injective (fun _ _ => Atom.symbol.inj)

def callerData : Option Atom → Atom := optional id

theorem callerData_injective : Function.Injective callerData :=
  optional_injective (fun _ _ same => same)

def valuesData : List Entry.Value → Atom := sequence valueData

theorem valuesData_injective : Function.Injective valuesData :=
  sequence_injective valueData_injective

def requestsData : List ArgumentRequest → Atom := sequence (pair valueData id)

theorem requestsData_injective : Function.Injective requestsData :=
  sequence_injective (pair_injective valueData_injective (fun _ _ same => same))

def framesData : List Frame → Atom := sequence frameData

theorem framesData_injective : Function.Injective framesData :=
  sequence_injective frameData_injective

def signatureData (chosen : SelectedTypePolicy) : Atom :=
  .expression [chosen.functionType, .expression chosen.argumentTypes, chosen.returnType]

theorem signatureData_injective : Function.Injective signatureData := by
  intro first second same
  cases first
  cases second
  simp_all [signatureData]

def equationWorkData (work : EquationWork) : Atom :=
  .expression [TypedApplyEncoding.index work.position, work.left, work.right, work.pattern,
    work.body, TypedApplyEncoding.bindingsData work.bindings]

private theorem index_injective : Function.Injective TypedApplyEncoding.index := by
  intro first second same
  have read := congrArg TypedApplyEncoding.readIndex same
  simpa only [TypedApplyEncoding.readIndex_index, Option.some.injEq] using read

theorem equationWorkData_injective : Function.Injective equationWorkData := by
  intro first second same
  cases first
  cases second
  simp_all only [equationWorkData, Atom.expression.injEq, List.cons.injEq, and_true,
    index_injective.eq_iff, bindingsData_injective.eq_iff]

def equationsData : List EquationWork → Atom := sequence equationWorkData

theorem equationsData_injective : Function.Injective equationsData :=
  sequence_injective equationWorkData_injective

def provenanceData : NativeValueProvenance → Atom
  | .emitted => .grounded (.bool false)
  | .completed => .grounded (.bool true)

theorem provenanceData_injective : Function.Injective provenanceData := by
  intro a b same
  cases a <;> cases b <;> first | rfl | cases same

def boundaryData : Boundary → Atom
  | .chain name template => .expression [.symbol "he-boundary-chain", .symbol name, valueData template]
  | .body => .expression [.symbol "he-boundary-body"]
  | .functionDone => .expression [.symbol "he-boundary-function-done"]
  | .producer => .expression [.symbol "he-boundary-producer"]
  | .returned original expected => .expression [.symbol "he-boundary-returned", valueData original, expected]
  | .native original expected provenance =>
    .expression [.symbol "he-boundary-native", valueData original, callerData expected, provenanceData provenance]

theorem boundaryData_injective : Function.Injective boundaryData := by
  intro first second same
  cases first <;> cases second <;> simp_all [boundaryData,
    valueData_injective.eq_iff, callerData_injective.eq_iff, provenanceData_injective.eq_iff]

/-- Each task constructor has its own data form. In particular, a selected
definition's work is retained, not reconstructed by another lookup. -/
def taskData : Task → Atom
  | .atom live scope value expected frame =>
    .expression [.symbol "he-task-atom", .expression live, namesData scope, valueData value, expected, frameData frame]
  | .tuple live scope values frame =>
    .expression [.symbol "he-task-tuple", .expression live, namesData scope, valuesData values, frameData frame]
  | .branches live scope tail heads =>
    .expression [.symbol "he-task-branches", .expression live, namesData scope, valuesData tail, resultsData heads]
  | .arguments live scope requests frame =>
    .expression [.symbol "he-task-arguments", .expression live, namesData scope, requestsData requests, frameData frame]
  | .argumentBranches live scope original requests heads =>
    .expression [.symbol "he-task-argument-branches", .expression live, namesData scope, valueData original,
      requestsData requests, resultsData heads]
  | .function live scope expected signature head arguments frame =>
    .expression [.symbol "he-task-function", .expression live, namesData scope, expected,
      signatureData signature, valueData head, valuesData arguments, frameData frame]
  | .functionBranches live scope requests heads =>
    .expression [.symbol "he-task-function-branches", .expression live, namesData scope,
      requestsData requests, resultsData heads]
  | .invocations live scope expected signature head arguments frames =>
    .expression [.symbol "he-task-invocations", .expression live, namesData scope, expected,
      signatureData signature, valueData head, valuesData arguments, framesData frames]
  | .minimal live scope caller value frame =>
    .expression [.symbol "he-task-minimal", .expression live, namesData scope, callerData caller,
      valueData value, frameData frame]
  | .body live scope caller value frame =>
    .expression [.symbol "he-task-body", .expression live, namesData scope, callerData caller,
      valueData value, frameData frame]
  | .invocation live scope caller value frame =>
    .expression [.symbol "he-task-invocation", .expression live, namesData scope, callerData caller,
      valueData value, frameData frame]
  | .invocationEquations live scope original frame works =>
    .expression [.symbol "he-task-invocation-equations", .expression live, namesData scope,
      valueData original, frameData frame, equationsData works]
  | .boundary live scope caller boundary value frame =>
    .expression [.symbol "he-task-boundary", .expression live, namesData scope, callerData caller,
      boundaryData boundary, valueData value, frameData frame]
  | .boundaryBatch live scope caller boundary answers =>
    .expression [.symbol "he-task-boundary-batch", .expression live, namesData scope,
      callerData caller, boundaryData boundary, resultsData answers]
  | .calls live scope expected answers =>
    .expression [.symbol "he-task-calls", .expression live, namesData scope, expected, resultsData answers]
  | .call live scope value expected frame =>
    .expression [.symbol "he-task-call", .expression live, namesData scope, valueData value, expected, frameData frame]
  | .equations live scope original expected frame works =>
    .expression [.symbol "he-task-equations", .expression live, namesData scope, valueData original, expected,
      frameData frame, equationsData works]
  | .returned live scope original expected value frame =>
    .expression [.symbol "he-task-returned", .expression live, namesData scope, valueData original, expected,
      valueData value, frameData frame]
  | .capture answers saved frame =>
    .expression [.symbol "he-task-capture", resultsData answers, valuesData saved, frameData frame]
  | .restore pairs saved frame =>
    .expression [.symbol "he-task-restore", valuesData pairs, resultsData saved, frameData frame]

set_option maxHeartbeats 600000 in
theorem taskData_injective : Function.Injective taskData := by
  intro first second same
  cases first <;> cases second <;> simp_all [taskData,
    namesData_injective.eq_iff, valueData_injective.eq_iff, valuesData_injective.eq_iff,
    callerData_injective.eq_iff, boundaryData_injective.eq_iff, resultsData_injective.eq_iff,
    requestsData_injective.eq_iff, frameData_injective.eq_iff, framesData_injective.eq_iff,
    signatureData_injective.eq_iff, equationsData_injective.eq_iff]

def continuationData : Continuation → Atom
  | .publish original => .expression [.symbol "he-continuation-publish", original]
  | .singleton => .expression [.symbol "he-continuation-singleton"]
  | .branches live scope tail =>
    .expression [.symbol "he-continuation-branches", .expression live, namesData scope, valuesData tail]
  | .tupleTail head => .expression [.symbol "he-continuation-tuple-tail", valueData head]
  | .arguments live scope original requests =>
    .expression [.symbol "he-continuation-arguments", .expression live, namesData scope,
      valueData original, requestsData requests]
  | .argumentTail head => .expression [.symbol "he-continuation-argument-tail", valueData head]
  | .functionHeads live scope requests =>
    .expression [.symbol "he-continuation-function-heads", .expression live, namesData scope, requestsData requests]
  | .functionAssemble head => .expression [.symbol "he-continuation-function-assemble", valueData head]
  | .diagnostics errors frame =>
    .expression [.symbol "he-continuation-diagnostics", .expression errors, frameData frame]
  | .boundaryBatch live scope caller boundary =>
    .expression [.symbol "he-continuation-boundary", .expression live, namesData scope,
      callerData caller, boundaryData boundary]
  | .calls live scope expected =>
    .expression [.symbol "he-continuation-calls", .expression live, namesData scope, expected]
  | .append task => .expression [.symbol "he-continuation-append", taskData task]
  | .prepend answers => .expression [.symbol "he-continuation-prepend", resultsData answers]
  | .collect frame => .expression [.symbol "he-continuation-collect", frameData frame]

set_option maxHeartbeats 400000 in
theorem continuationData_injective : Function.Injective continuationData := by
  intro first second same
  cases first <;> cases second <;> simp_all [continuationData,
    namesData_injective.eq_iff, valueData_injective.eq_iff, valuesData_injective.eq_iff,
    requestsData_injective.eq_iff, taskData_injective.eq_iff, frameData_injective.eq_iff,
    callerData_injective.eq_iff, boundaryData_injective.eq_iff, resultsData_injective.eq_iff]

def stackData : List Continuation → Atom := sequence continuationData

theorem stackData_injective : Function.Injective stackData :=
  sequence_injective continuationData_injective

/-! ## Controls -/

private def unmarked : Entry.Value :=
  .expression .active [.expression .active [.symbol "answer"]]

private def markedChild : Entry.Value :=
  .expression .active [.expression .held [.symbol "answer"]]

theorem same_print_separates_retained_values :
    unmarked.erase = markedChild.erase ∧ valueData unmarked ≠ valueData markedChild := by
  constructor
  · simp [unmarked, markedChild, Entry.Value.erase]
  · intro equal
    have same := valueData_injective equal
    simp [unmarked, markedChild] at same

theorem positive_result_duplicate_count (result : Result) :
    resultsData [result, result] = .expression [resultData result, resultData result] := rfl

theorem dropping_equal_results_changes_data (result : Result) :
    resultsData [result, result] ≠ resultsData [result] := by
  intro same
  have lengths := congrArg List.length (resultsData_injective same)
  cases lengths

end Mettapedia.Languages.MeTTa.HE.ContextualData
