import Mettapedia.Languages.MM0.MeTTa.Admission.SpecificationMatching
import Mettapedia.Languages.MM0.MeTTa.Admission.AdmissionStep
import Mettapedia.Languages.MM0.Kernel.SpecificationChecking

/-!
# Specification steps and completion in the retained MM0 source

The source checks pending specification consumption before theory admission.
Returned capabilities are paired with their earned physical table invariant;
they do not identify an arbitrary logical theory. Refused pending checks
perform no admission call. End-of-file completion requires an empty pending
list and preserves the store.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.SpecificationStep

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open NamedSpaces (Handle)
open Kernel (Theory Admission SpecificationEntry ProofDeclaration)
open SessionInitialization (Spaces theoryValue stateValue)
open SpecificationMatching (pendingValue declarationValue)
open AdmissionChecks (admissionValue TableReady Ready)
open TableAccess (tableValue)
open ListAccess (listValue optionValue viewValue)

/-- Encoding of the represented logical result, with its physical theory
snapshot supplied by the table invariant. -/
def resultValue (spaces : Spaces) (result : Option Kernel.SpecificationAdmission.State) : Atom :=
  optionValue (result.map fun state => stateValue spaces (pendingValue state.pending))

private def casesOf (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def stepEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 128)[127]'(by decide +kernel)
private def stepCases := casesOf stepEquation.body
private def stepEnvironment (valueInput valueInputValue : Atom) : Subst := [("valueInputValue", valueInputValue), ("valueInput", valueInput)]
private theorem step_unique : program.equations.filter (fun row => row.head == "mm0:spec-step") = [stepEquation] := by decide +kernel
private theorem step_formals : stepEquation.arguments = [.var "valueInput", .var "valueInputValue"] := by decide +kernel
private theorem step_clause (valueInput valueInputValue : Atom) :
    clauses program "mm0:spec-step" [valueInput, valueInputValue] = [.evaluate (stepEnvironment valueInput valueInputValue) stepEquation.body] := by
  rw [clauses_use_only_the_named_equations, step_unique]
  simp [step_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, stepEnvironment]
private theorem step_captured_of_body (bindings : Subst) (before after : State)
    (valueInput valueInputValue : Atom) (valueInputName valueInputValueName : String) (answer : Atom)
    (capture_valueInput : applySubst bindings (.var valueInputName) = valueInput) (capture_valueInputValue : applySubst bindings (.var valueInputValueName) = valueInputValue)
    (computed : PureReturns program (stepEnvironment valueInput valueInputValue) before stepEquation.body after answer) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:spec-step", .var valueInputName, .var valueInputValueName]) after answer := by
  apply authored_variable_call_returns program bindings (stepEnvironment valueInput valueInputValue) before after
    "mm0:spec-step" [valueInputName, valueInputValueName] stepEquation.body answer
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ computed (by decide +kernel)
  simpa [capture_valueInput, capture_valueInputValue] using step_clause valueInput valueInputValue

private def permittedEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 129)[128]'(by decide +kernel)
private def permittedCases := casesOf permittedEquation.body
private def permittedEnvironment (valueInput theory admission : Atom) : Subst := [("admission", admission), ("theory", theory), ("valueInput", valueInput)]
private theorem permitted_unique : program.equations.filter (fun row => row.head == "mm0:spec-permitted") = [permittedEquation] := by decide +kernel
private theorem permitted_formals : permittedEquation.arguments = [.var "valueInput", .var "theory", .var "admission"] := by decide +kernel
private theorem permitted_clause (valueInput theory admission : Atom) :
    clauses program "mm0:spec-permitted" [valueInput, theory, admission] = [.evaluate (permittedEnvironment valueInput theory admission) permittedEquation.body] := by
  rw [clauses_use_only_the_named_equations, permitted_unique]
  simp [permitted_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, permittedEnvironment]
private theorem permitted_captured_of_body (bindings : Subst) (before after : State)
    (valueInput theory admission : Atom) (valueInputName theoryName admissionName : String) (answer : Atom)
    (capture_valueInput : applySubst bindings (.var valueInputName) = valueInput) (capture_theory : applySubst bindings (.var theoryName) = theory) (capture_admission : applySubst bindings (.var admissionName) = admission)
    (computed : PureReturns program (permittedEnvironment valueInput theory admission) before permittedEquation.body after answer) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:spec-permitted", .var valueInputName, .var theoryName, .var admissionName]) after answer := by
  apply authored_variable_call_returns program bindings (permittedEnvironment valueInput theory admission) before after
    "mm0:spec-permitted" [valueInputName, theoryName, admissionName] permittedEquation.body answer
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ computed (by decide +kernel)
  simpa [capture_valueInput, capture_theory, capture_admission] using permitted_clause valueInput theory admission

private def admittedEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 130)[129]'(by decide +kernel)
private def admittedCases := casesOf admittedEquation.body
private def admittedEnvironment (valueInput pending : Atom) : Subst := [("pending", pending), ("valueInput", valueInput)]
private theorem admitted_unique : program.equations.filter (fun row => row.head == "mm0:spec-admitted") = [admittedEquation] := by decide +kernel
private theorem admitted_formals : admittedEquation.arguments = [.var "valueInput", .var "pending"] := by decide +kernel
private theorem admitted_clause (valueInput pending : Atom) :
    clauses program "mm0:spec-admitted" [valueInput, pending] = [.evaluate (admittedEnvironment valueInput pending) admittedEquation.body] := by
  rw [clauses_use_only_the_named_equations, admitted_unique]
  simp [admitted_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, admittedEnvironment]
private theorem admitted_captured_of_body (bindings : Subst) (before after : State)
    (valueInput pending : Atom) (valueInputName pendingName : String) (answer : Atom)
    (capture_valueInput : applySubst bindings (.var valueInputName) = valueInput) (capture_pending : applySubst bindings (.var pendingName) = pending)
    (computed : PureReturns program (admittedEnvironment valueInput pending) before admittedEquation.body after answer) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:spec-admitted", .var valueInputName, .var pendingName]) after answer := by
  apply authored_variable_call_returns program bindings (admittedEnvironment valueInput pending) before after
    "mm0:spec-admitted" [valueInputName, pendingName] admittedEquation.body answer
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ computed (by decide +kernel)
  simpa [capture_valueInput, capture_pending] using admitted_clause valueInput pending

private def finishEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 131)[130]'(by decide +kernel)
private def finishCases := casesOf finishEquation.body
private def finishEnvironment (valueInput : Atom) : Subst := [("valueInput", valueInput)]
private theorem finish_unique : program.equations.filter (fun row => row.head == "mm0:spec-finish") = [finishEquation] := by decide +kernel
private theorem finish_formals : finishEquation.arguments = [.var "valueInput"] := by decide +kernel
private theorem finish_clause (valueInput : Atom) :
    clauses program "mm0:spec-finish" [valueInput] = [.evaluate (finishEnvironment valueInput) finishEquation.body] := by
  rw [clauses_use_only_the_named_equations, finish_unique]
  simp [finish_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, finishEnvironment]
private theorem finish_captured_of_body (bindings : Subst) (before after : State)
    (valueInput : Atom) (valueInputName : String) (answer : Atom)
    (capture_valueInput : applySubst bindings (.var valueInputName) = valueInput)
    (computed : PureReturns program (finishEnvironment valueInput) before finishEquation.body after answer) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:spec-finish", .var valueInputName]) after answer := by
  apply authored_variable_call_returns program bindings (finishEnvironment valueInput) before after
    "mm0:spec-finish" [valueInputName] finishEquation.body answer
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ computed (by decide +kernel)
  simpa [capture_valueInput] using finish_clause valueInput

private def finishedEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 132)[131]'(by decide +kernel)
private def finishedCases := casesOf finishedEquation.body
private def finishedEnvironment (valueInput theory : Atom) : Subst := [("theory", theory), ("valueInput", valueInput)]
private theorem finished_unique : program.equations.filter (fun row => row.head == "mm0:spec-finished") = [finishedEquation] := by decide +kernel
private theorem finished_formals : finishedEquation.arguments = [.var "valueInput", .var "theory"] := by decide +kernel
private theorem finished_clause (valueInput theory : Atom) :
    clauses program "mm0:spec-finished" [valueInput, theory] = [.evaluate (finishedEnvironment valueInput theory) finishedEquation.body] := by
  rw [clauses_use_only_the_named_equations, finished_unique]
  simp [finished_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, finishedEnvironment]
private theorem finished_captured_of_body (bindings : Subst) (before after : State)
    (valueInput theory : Atom) (valueInputName theoryName : String) (answer : Atom)
    (capture_valueInput : applySubst bindings (.var valueInputName) = valueInput) (capture_theory : applySubst bindings (.var theoryName) = theory)
    (computed : PureReturns program (finishedEnvironment valueInput theory) before finishedEquation.body after answer) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:spec-finished", .var valueInputName, .var theoryName]) after answer := by
  apply authored_variable_call_returns program bindings (finishedEnvironment valueInput theory) before after
    "mm0:spec-finished" [valueInputName, theoryName] finishedEquation.body answer
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ computed (by decide +kernel)
  simpa [capture_valueInput, capture_theory] using finished_clause valueInput theory

private def stepBody : Atom := (stepCases[0]'(by decide)).2
private def permittedBody : Atom := (permittedCases[1]'(by decide)).2
private def admittedBody : Atom := (admittedCases[1]'(by decide)).2
private def finishBody : Atom := (finishCases[1]'(by decide)).2

private theorem step_shape : stepEquation.body = .expression [.symbol "case",
    .expression [.var "valueInput", .var "valueInputValue"], .expression (stepCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem permitted_shape : permittedEquation.body = .expression [.symbol "case", .var "valueInput",
    .expression (permittedCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem admitted_shape : admittedEquation.body = .expression [.symbol "case", .var "valueInput",
    .expression (admittedCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem finish_shape : finishEquation.body = .expression [.symbol "case", .expression [.var "valueInput"],
    .expression (finishCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem finished_shape : finishedEquation.body = .expression [.symbol "case", .var "valueInput",
    .expression (finishedCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem step_cases : stepCases = [
    (.expression [listValue [.symbol "MM0:SpecificationState", .var "theory", .var "pending"],
      listValue [.symbol "MM0:ProofDeclaration", .var "local", .var "admission"]], stepBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide +kernel
private theorem permitted_cases : permittedCases = [(.symbol "None", .symbol "None"),
    (.expression [.symbol "Some", .var "pending"], permittedBody), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide +kernel
private theorem admitted_cases : admittedCases = [(.symbol "None", .symbol "None"),
    (.expression [.symbol "Some", .var "theory"], admittedBody), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide +kernel
private theorem finish_cases : finishCases = [(.expression [.symbol "None"], .symbol "None"),
    (.expression [.expression [.symbol "Some", listValue [.symbol "MM0:SpecificationState", .var "theory", .var "pending"]]], finishBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide +kernel
private theorem finished_cases : finishedCases = [(.symbol "List:Nil", .expression [.symbol "Some", .var "theory"]),
    (.expression [.symbol "List:Cons", .var "entry", .var "rest"], .symbol "None"),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide +kernel
private theorem step_body_shape : stepBody = .expression [.symbol "let", .var "specPendingResult",
    .expression [.symbol "mm0:spec-pending", .var "local", .var "pending", .var "admission"],
    .expression [.symbol "mm0:spec-permitted", .var "specPendingResult", .var "theory", .var "admission"]] := by decide +kernel
private theorem permitted_body_shape : permittedBody = .expression [.symbol "let", .var "admissionStepResult",
    .expression [.symbol "mm0:admission-step", .var "theory", .var "admission"],
    .expression [.symbol "mm0:spec-admitted", .var "admissionStepResult", .var "pending"]] := by decide +kernel
private theorem admitted_body_shape : admittedBody = .expression [.symbol "let", .var "items",
    listValue [.symbol "MM0:SpecificationState", .var "theory", .var "pending"],
    .expression [.symbol "Some", .var "items"]] := by decide +kernel
private theorem finish_body_shape : finishBody = .expression [.symbol "let", .var "view",
    .expression [.symbol "mm0:list-view", .var "pending"],
    .expression [.symbol "mm0:spec-finished", .var "view", .var "theory"]] := by decide +kernel

private theorem state_constructor_returns (bindings : Subst) (before : State) (spaces : Spaces)
    (entries : List SpecificationEntry)
    (capturedTheory : applySubst bindings (.var "theory") = theoryValue spaces)
    (capturedPending : applySubst bindings (.var "pending") = pendingValue entries) :
    PureReturns program bindings before
      (listValue [.symbol "MM0:SpecificationState", .var "theory", .var "pending"]) before
      (stateValue spaces (pendingValue entries)) := by
  apply unary_constructor_of_returns program bindings before before "MM0:L" _ _ list_is_data_constructor (by decide)
  simpa [listValue, stateValue, capturedTheory, capturedPending] using
    constructor_variables_return program bindings before "MM0:SpecificationState" ["theory", "pending"]
      (by decide +kernel) (by decide)

private theorem admitted_body_returns (spaces : Spaces) (result : Option Theory)
    (entries : List SpecificationEntry) (before : State) :
    PureReturns program (admittedEnvironment (AdmissionStep.resultValue spaces result) (pendingValue entries))
      before admittedEquation.body before
      (resultValue spaces (result.map fun theory => (⟨theory, entries⟩ : Kernel.SpecificationAdmission.State))) := by
  rw [admitted_shape]
  let bindings := admittedEnvironment (AdmissionStep.resultValue spaces result) (pendingValue entries)
  have input : PureReturns program bindings before (.var "valueInput") before (AdmissionStep.resultValue spaces result) := by
    simpa [bindings, admittedEnvironment, applySubst, Subst.lookup] using variable_returns program bindings before "valueInput"
  cases result with
  | none =>
      apply case_returns program bindings bindings before before before (.var "valueInput") (.symbol "None")
        (.symbol "None") _ _ admittedCases (read_cases_encoded _) input
      · simp [admitted_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings before "None"
  | some theory =>
      let bound := ("theory", theoryValue spaces) :: bindings
      apply case_returns program bindings bound before before before (.var "valueInput")
        (optionValue (some (theoryValue spaces))) admittedBody _ _ admittedCases (read_cases_encoded _) input
      · simp [admitted_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bound, bindings, admittedEnvironment, optionValue]
      · rw [admitted_body_shape]
        let built := ("items", stateValue spaces (pendingValue entries)) :: bound
        apply let_returns program bound built before before before (.var "items") _ _
          (stateValue spaces (pendingValue entries)) _
        · exact state_constructor_returns bound before spaces entries rfl rfl
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, built, bound, bindings, admittedEnvironment]
        · simpa [resultValue, optionValue, built, applySubst, Subst.lookup] using
            unary_constructor_returns program built before "Some" "items" some_is_data_constructor (by decide)

theorem admitted_captured_returns (bindings : Subst) (before : State) (spaces : Spaces)
    (result : Option Theory) (entries : List SpecificationEntry) (resultName pendingName : String)
    (capturedResult : applySubst bindings (.var resultName) = AdmissionStep.resultValue spaces result)
    (capturedPending : applySubst bindings (.var pendingName) = pendingValue entries) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:spec-admitted", .var resultName, .var pendingName]) before
      (resultValue spaces (result.map fun theory => (⟨theory, entries⟩ : Kernel.SpecificationAdmission.State))) :=
  admitted_captured_of_body bindings before before (AdmissionStep.resultValue spaces result) (pendingValue entries)
    resultName pendingName _ capturedResult capturedPending (admitted_body_returns spaces result entries before)

private theorem permitted_none_body_returns (spaces : Spaces) (admission : Admission) (before : State) :
    PureReturns program (permittedEnvironment (.symbol "None") (theoryValue spaces) (admissionValue admission))
      before permittedEquation.body before (.symbol "None") := by
  rw [permitted_shape]
  let bindings := permittedEnvironment (.symbol "None") (theoryValue spaces) (admissionValue admission)
  apply case_returns program bindings bindings before before before (.var "valueInput") (.symbol "None")
    (.symbol "None") _ _ permittedCases (read_cases_encoded _)
  · simpa [bindings, permittedEnvironment, applySubst, Subst.lookup] using variable_returns program bindings before "valueInput"
  · simp [permitted_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
  · exact symbol_returns program bindings before "None"

theorem permitted_none_returns (bindings : Subst) (before : State) (spaces : Spaces) (admission : Admission)
    (resultName theoryName admissionName : String)
    (capturedResult : applySubst bindings (.var resultName) = .symbol "None")
    (capturedTheory : applySubst bindings (.var theoryName) = theoryValue spaces)
    (capturedAdmission : applySubst bindings (.var admissionName) = admissionValue admission) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:spec-permitted", .var resultName, .var theoryName, .var admissionName]) before (.symbol "None") :=
  permitted_captured_of_body bindings before before (.symbol "None") (theoryValue spaces) (admissionValue admission)
    resultName theoryName admissionName _ capturedResult capturedTheory capturedAdmission
    (permitted_none_body_returns spaces admission before)

private theorem permitted_some_body_returns (spaces : Spaces) (admission : Admission) (theory : Theory)
    (entries : List SpecificationEntry) (before after : State)
    (returned : AdmissionStep.Call spaces admission before after (Theory.step? theory admission)) :
    PureReturns program (permittedEnvironment (optionValue (some (pendingValue entries)))
      (theoryValue spaces) (admissionValue admission)) before permittedEquation.body after
      (resultValue spaces ((Theory.step? theory admission).map fun theory =>
        (⟨theory, entries⟩ : Kernel.SpecificationAdmission.State))) := by
  rw [permitted_shape]
  let bindings := permittedEnvironment (optionValue (some (pendingValue entries))) (theoryValue spaces) (admissionValue admission)
  let bound := ("pending", pendingValue entries) :: bindings
  apply case_returns program bindings bound before before after (.var "valueInput")
    (optionValue (some (pendingValue entries))) permittedBody _ _ permittedCases (read_cases_encoded _)
  · simpa [bindings, permittedEnvironment, applySubst, Subst.lookup] using variable_returns program bindings before "valueInput"
  · simp [permitted_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, optionValue, bound, bindings, permittedEnvironment, Subst.lookup]
  · rw [permitted_body_shape]
    let admitted := ("admissionStepResult", AdmissionStep.resultValue spaces (Theory.step? theory admission)) :: bound
    apply let_returns program bound admitted before after after (.var "admissionStepResult") _ _
      (AdmissionStep.resultValue spaces (Theory.step? theory admission)) _
    · exact returned bound "theory" "admission" rfl rfl
    · simp [SpaceSemantics.matchValue, matchAtom, admitted, bound, bindings, permittedEnvironment, Subst.lookup]
    · exact admitted_captured_returns admitted after spaces (Theory.step? theory admission) entries
        "admissionStepResult" "pending" rfl rfl

theorem permitted_some_returns (bindings : Subst) (before after : State) (spaces : Spaces)
    (admission : Admission) (theory : Theory) (entries : List SpecificationEntry)
    (returned : AdmissionStep.Call spaces admission before after (Theory.step? theory admission))
    (resultName theoryName admissionName : String)
    (capturedResult : applySubst bindings (.var resultName) = optionValue (some (pendingValue entries)))
    (capturedTheory : applySubst bindings (.var theoryName) = theoryValue spaces)
    (capturedAdmission : applySubst bindings (.var admissionName) = admissionValue admission) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:spec-permitted", .var resultName, .var theoryName, .var admissionName]) after
      (resultValue spaces ((Theory.step? theory admission).map fun theory =>
        (⟨theory, entries⟩ : Kernel.SpecificationAdmission.State))) :=
  permitted_captured_of_body bindings before after (optionValue (some (pendingValue entries)))
    (theoryValue spaces) (admissionValue admission) resultName theoryName admissionName _
    capturedResult capturedTheory capturedAdmission (permitted_some_body_returns spaces admission theory entries before after returned)


private def stepBindings (spaces : Spaces) (state : Kernel.SpecificationAdmission.State)
    (declaration : ProofDeclaration) : Subst :=
  stepEnvironment (stateValue spaces (pendingValue state.pending)) (declarationValue declaration)

private def stepBound (spaces : Spaces) (state : Kernel.SpecificationAdmission.State)
    (declaration : ProofDeclaration) : Subst :=
  [("admission", admissionValue declaration.admission), ("local", boolean declaration.isLocal),
    ("pending", pendingValue state.pending), ("theory", theoryValue spaces)] ++
    stepBindings spaces state declaration

private theorem step_of_handler (spaces : Spaces) (state : Kernel.SpecificationAdmission.State)
    (declaration : ProofDeclaration) (before after : State)
    (handled : ∀ (bindings : Subst) (pendingName theoryName admissionName : String),
      applySubst bindings (.var pendingName) =
        optionValue ((Kernel.SpecificationAdmission.pending? state.pending declaration).map pendingValue) →
      applySubst bindings (.var theoryName) = theoryValue spaces →
      applySubst bindings (.var admissionName) = admissionValue declaration.admission →
      PureReturns program bindings before
        (.expression [.symbol "mm0:spec-permitted", .var pendingName, .var theoryName, .var admissionName])
        after (resultValue spaces (Kernel.SpecificationAdmission.step? state declaration))) :
    PureReturns program (stepBindings spaces state declaration) before stepEquation.body after
      (resultValue spaces (Kernel.SpecificationAdmission.step? state declaration)) := by
  rw [step_shape]
  let bindings := stepBindings spaces state declaration
  let bound := stepBound spaces state declaration
  apply case_returns program bindings bound before before after
    (.expression [.var "valueInput", .var "valueInputValue"])
    (.expression [stateValue spaces (pendingValue state.pending), declarationValue declaration])
    stepBody _ _ stepCases (read_cases_encoded _)
  · simpa [bindings, stepBindings, stepEnvironment, applySubst, Subst.lookup] using
      tuple_variables_return program bindings before ["valueInput", "valueInputValue"]
  · simp [step_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, bound, bindings, stepBound,
      stepBindings, stepEnvironment, stateValue, declarationValue, listValue, Subst.lookup]
  · rw [step_body_shape]
    let consumed := ("specPendingResult",
      optionValue ((Kernel.SpecificationAdmission.pending? state.pending declaration).map pendingValue)) :: bound
    apply let_returns program bound consumed before before after (.var "specPendingResult") _ _
      (optionValue ((Kernel.SpecificationAdmission.pending? state.pending declaration).map pendingValue)) _
    · exact SpecificationMatching.pending_captured_returns bound before state.pending declaration
        "local" "pending" "admission" rfl rfl rfl
    · simp [SpaceSemantics.matchValue, matchAtom, consumed, bound, stepBound,
        stepBindings, stepEnvironment, Subst.lookup]
    · exact handled consumed "specPendingResult" "theory" "admission" rfl rfl rfl

/-- A captured call to the retained specification step. The logical snapshot
is tracked by the earned table relation, separately from capability bytes. -/
def Call (spaces : Spaces) (state : Kernel.SpecificationAdmission.State)
    (declaration : ProofDeclaration) (before after : State)
    (result : Option Kernel.SpecificationAdmission.State) : Prop :=
  ∀ (bindings : Subst) (stateName declarationName : String),
    applySubst bindings (.var stateName) = stateValue spaces (pendingValue state.pending) →
    applySubst bindings (.var declarationName) = declarationValue declaration →
    PureReturns program bindings before
      (.expression [.symbol "mm0:spec-step", .var stateName, .var declarationName]) after (resultValue spaces result)

private theorem captured_of_handler (spaces : Spaces) (state : Kernel.SpecificationAdmission.State)
    (declaration : ProofDeclaration) (before after : State)
    (handled : ∀ (bindings : Subst) (pendingName theoryName admissionName : String),
      applySubst bindings (.var pendingName) =
        optionValue ((Kernel.SpecificationAdmission.pending? state.pending declaration).map pendingValue) →
      applySubst bindings (.var theoryName) = theoryValue spaces →
      applySubst bindings (.var admissionName) = admissionValue declaration.admission →
      PureReturns program bindings before
        (.expression [.symbol "mm0:spec-permitted", .var pendingName, .var theoryName, .var admissionName])
        after (resultValue spaces (Kernel.SpecificationAdmission.step? state declaration))) :
    Call spaces state declaration before after (Kernel.SpecificationAdmission.step? state declaration) := by
  intro bindings stateName declarationName capturedState capturedDeclaration
  exact step_captured_of_body bindings before after _ _ stateName declarationName _
    capturedState capturedDeclaration (step_of_handler spaces state declaration before after handled)

private theorem step_after_pending (state : Kernel.SpecificationAdmission.State)
    (declaration : ProofDeclaration) (entries : List SpecificationEntry)
    (consumed : Kernel.SpecificationAdmission.pending? state.pending declaration = some entries) :
    Kernel.SpecificationAdmission.step? state declaration =
      (Theory.step? state.theory declaration.admission).map fun theory =>
        (⟨theory, entries⟩ : Kernel.SpecificationAdmission.State) := by
  rw [Kernel.SpecificationAdmission.step?, consumed]
  cases Theory.step? state.theory declaration.admission <;> rfl

/-- Pending refusal leaves the complete store alone. If consumption succeeds,
admission supplies its checked cache frame and publication trace. A successful
term publication preserves the preceding cache scope until the driver resets it. -/
structure EffectFrame (spaces : Spaces) (state : Kernel.SpecificationAdmission.State)
    (declaration : ProofDeclaration) (before after : State) : Prop where
  tables : TableReady spaces ((Kernel.SpecificationAdmission.step? state declaration).getD state).theory after
  cache : InferenceCache.Ready state.theory.termSignature (tableValue spaces.terms) spaces.cache after
  cells : after.cells = before.cells
  proofs : after.read spaces.proofs = before.read spaces.proofs
  other : ∀ handle, handle ≠ spaces.cache → handle ∉ AdmissionPublication.targets spaces declaration.admission →
    after.read handle = before.read handle
  blocked : Kernel.SpecificationAdmission.pending? state.pending declaration = none → after = before
  admission : ∀ entries, Kernel.SpecificationAdmission.pending? state.pending declaration = some entries →
    ∃ checked bound, AdmissionStep.EffectFrame spaces state.theory declaration.admission before checked after bound

theorem EffectFrame.tables_of_step {spaces : Spaces} {state next : Kernel.SpecificationAdmission.State}
    {declaration : ProofDeclaration} {before after : State}
    (frame : EffectFrame spaces state declaration before after)
    (stepped : Kernel.SpecificationAdmission.step? state declaration = some next) :
    TableReady spaces next.theory after := by
  simpa only [stepped, Option.getD_some] using frame.tables

theorem EffectFrame.refused_ready {spaces : Spaces} {state : Kernel.SpecificationAdmission.State}
    {declaration : ProofDeclaration} {before after : State}
    (frame : EffectFrame spaces state declaration before after)
    (refused : Kernel.SpecificationAdmission.step? state declaration = none) :
    Ready spaces state.theory after := by
  exact ⟨by simpa only [refused, Option.getD_none] using frame.tables, frame.cache⟩

/-- The retained source consumes the specification in order, then invokes the
independent admission check in the actual preceding theory. -/
theorem captured_returns (spaces : Spaces) (state : Kernel.SpecificationAdmission.State)
    (declaration : ProofDeclaration) (before : State) (ready : Ready spaces state.theory before) :
    ∃ after, Call spaces state declaration before after (Kernel.SpecificationAdmission.step? state declaration) ∧
      EffectFrame spaces state declaration before after := by
  cases consumed : Kernel.SpecificationAdmission.pending? state.pending declaration with
  | none =>
      refine ⟨before, ?_, ?_⟩
      · apply captured_of_handler spaces state declaration before before
        intro bindings pendingName theoryName admissionName capturedPending capturedTheory capturedAdmission
        simpa [Kernel.SpecificationAdmission.step?, consumed, resultValue, optionValue] using
          permitted_none_returns bindings before spaces declaration.admission pendingName theoryName admissionName
            (by simpa only [consumed, Option.map_none, optionValue] using capturedPending) capturedTheory capturedAdmission
      · refine ⟨?_, ready.cache, rfl, rfl, fun _ _ _ => rfl, fun _ => rfl, ?_⟩
        · simpa [Kernel.SpecificationAdmission.step?, consumed] using ready.toTableReady
        · intro entries impossible
          rw [consumed] at impossible
          cases impossible
  | some entries =>
      obtain ⟨checked, after, bound, returned, frame⟩ :=
        AdmissionStep.captured_returns spaces state.theory declaration.admission before ready
      have stepShape := step_after_pending state declaration entries consumed
      refine ⟨after, ?_, ?_⟩
      · apply captured_of_handler spaces state declaration before after
        intro bindings pendingName theoryName admissionName capturedPending capturedTheory capturedAdmission
        simpa only [stepShape] using
          permitted_some_returns bindings before after spaces declaration.admission state.theory entries returned
            pendingName theoryName admissionName
            (by simpa only [consumed, Option.map_some] using capturedPending) capturedTheory capturedAdmission
      · refine ⟨?_, frame.cache, frame.cells, frame.proofs, frame.other, ?_, ?_⟩
        · rw [stepShape]
          cases admitted : Theory.step? state.theory declaration.admission <;>
            simpa only [admitted, Option.map_none, Option.map_some, Option.getD_none, Option.getD_some] using frame.tables
        · intro impossible
          rw [consumed] at impossible
          cases impossible
        · intro _ _
          exact ⟨checked, bound, frame⟩


private theorem finished_body_returns (spaces : Spaces) (entries : List SpecificationEntry) (before : State) :
    PureReturns program (finishedEnvironment (viewValue (entries.map SpecificationMatching.entryValue)) (theoryValue spaces))
      before finishedEquation.body before
      (optionValue (if entries.isEmpty then some (theoryValue spaces) else none)) := by
  rw [finished_shape]
  let bindings := finishedEnvironment (viewValue (entries.map SpecificationMatching.entryValue)) (theoryValue spaces)
  have input : PureReturns program bindings before (.var "valueInput") before
      (viewValue (entries.map SpecificationMatching.entryValue)) := by
    simpa [bindings, finishedEnvironment, applySubst, Subst.lookup] using variable_returns program bindings before "valueInput"
  cases entries with
  | nil =>
      apply case_returns program bindings bindings before before before (.var "valueInput") (.symbol "List:Nil")
        (.expression [.symbol "Some", .var "theory"]) _ _ finishedCases (read_cases_encoded _) input
      · simp [finished_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · simpa [bindings, finishedEnvironment, optionValue, applySubst, Subst.lookup] using
          unary_constructor_returns program bindings before "Some" "theory" some_is_data_constructor (by decide)
  | cons entry rest =>
      let bound := ("rest", pendingValue rest) :: ("entry", SpecificationMatching.entryValue entry) :: bindings
      apply case_returns program bindings bound before before before (.var "valueInput")
        (viewValue ((entry :: rest).map SpecificationMatching.entryValue)) (.symbol "None") _ _
        finishedCases (read_cases_encoded _) input
      · simp [finished_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, viewValue, pendingValue, bound,
          bindings, finishedEnvironment, Subst.lookup]
      · exact symbol_returns program bound before "None"

theorem finished_captured_returns (bindings : Subst) (before : State) (spaces : Spaces)
    (entries : List SpecificationEntry) (viewName theoryName : String)
    (capturedView : applySubst bindings (.var viewName) = viewValue (entries.map SpecificationMatching.entryValue))
    (capturedTheory : applySubst bindings (.var theoryName) = theoryValue spaces) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:spec-finished", .var viewName, .var theoryName]) before
      (optionValue (if entries.isEmpty then some (theoryValue spaces) else none)) :=
  finished_captured_of_body bindings before before _ _ viewName theoryName _ capturedView capturedTheory
    (finished_body_returns spaces entries before)

private theorem finish_body_returns (spaces : Spaces) (result : Option Kernel.SpecificationAdmission.State)
    (before : State) :
    PureReturns program (finishEnvironment (resultValue spaces result)) before finishEquation.body before
      (AdmissionStep.resultValue spaces (result.bind fun state =>
        if state.pending.isEmpty then some state.theory else none)) := by
  rw [finish_shape]
  let bindings := finishEnvironment (resultValue spaces result)
  have input : PureReturns program bindings before (.expression [.var "valueInput"]) before
      (.expression [resultValue spaces result]) := by
    simpa [bindings, finishEnvironment, applySubst, Subst.lookup] using
      tuple_variables_return program bindings before ["valueInput"]
  cases result with
  | none =>
      apply case_returns program bindings bindings before before before (.expression [.var "valueInput"])
        (.expression [.symbol "None"]) (.symbol "None") _ _ finishCases (read_cases_encoded _) input
      · simp [finish_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom]
      · exact symbol_returns program bindings before "None"
  | some state =>
      let bound := ("pending", pendingValue state.pending) :: ("theory", theoryValue spaces) :: bindings
      apply case_returns program bindings bound before before before (.expression [.var "valueInput"])
        (.expression [resultValue spaces (some state)]) finishBody _ _ finishCases (read_cases_encoded _) input
      · simp [finish_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, resultValue, optionValue, stateValue,
          listValue, bound, bindings, finishEnvironment, Subst.lookup]
      · rw [finish_body_shape]
        let viewed := ("view", viewValue (state.pending.map SpecificationMatching.entryValue)) :: bound
        apply let_returns program bound viewed before before before (.var "view") _ _
          (viewValue (state.pending.map SpecificationMatching.entryValue)) _
        · exact ListAccess.view_captured_returns bound before "pending" (state.pending.map SpecificationMatching.entryValue) rfl
        · simp [SpaceSemantics.matchValue, matchAtom, viewed, bound, bindings, finishEnvironment, Subst.lookup]
        · have computed := finished_captured_returns viewed before spaces state.pending "view" "theory" rfl rfl
          cases state.pending <;> simpa [AdmissionStep.resultValue, optionValue] using computed

/-- End-of-file checks the same empty-pending predicate used by the existing
kernel verifier. Earlier failure and incomplete specifications both refuse;
all completion paths preserve the entire store. -/
theorem finish_captured_returns (bindings : Subst) (before : State) (spaces : Spaces)
    (result : Option Kernel.SpecificationAdmission.State) (name : String)
    (captured : applySubst bindings (.var name) = resultValue spaces result) :
    PureReturns program bindings before (.expression [.symbol "mm0:spec-finish", .var name]) before
      (AdmissionStep.resultValue spaces (result.bind fun state =>
        if state.pending.isEmpty then some state.theory else none)) :=
  finish_captured_of_body bindings before before _ name _ captured (finish_body_returns spaces result before)


def requestConfiguration (before : State) (spaces : Spaces)
    (state : Kernel.SpecificationAdmission.State) (declaration : ProofDeclaration) : Configuration :=
  { state := before, control := .evaluate (stepBindings spaces state declaration)
      (.expression [.symbol "mm0:spec-step", .var "valueInput", .var "valueInputValue"]) }

theorem sufficient_fuel (spaces : Spaces) (state : Kernel.SpecificationAdmission.State)
    (declaration : ProofDeclaration) (before : State) (ready : Ready spaces state.theory before) :
    ∃ after fuel,
      (∀ extra, run program (fuel + extra) (requestConfiguration before spaces state declaration) =
        .complete after [resultValue spaces (Kernel.SpecificationAdmission.step? state declaration)] [] []) ∧
      EffectFrame spaces state declaration before after := by
  obtain ⟨after, returned, frame⟩ := captured_returns spaces state declaration before ready
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program (stepBindings spaces state declaration)
    before after _ _ (returned _ "valueInput" "valueInputValue" rfl rfl)
  exact ⟨after, fuel, fun extra => completed_run_more_fuel program fuel extra _ after _ [] [] completed, frame⟩

/-- Equality of native return values is qualified independently of logical
theory identity; successful theory identity comes from the table frame. -/
theorem result_iff_source_returns (spaces : Spaces) (state : Kernel.SpecificationAdmission.State)
    (declaration : ProofDeclaration) (before : State) (ready : Ready spaces state.theory before) (answer : Atom) :
    resultValue spaces (Kernel.SpecificationAdmission.step? state declaration) = answer ↔
      ∃ after fuel, run program fuel (requestConfiguration before spaces state declaration) = .complete after [answer] [] [] := by
  obtain ⟨reference, referenceFuel, completed, _⟩ := sufficient_fuel spaces state declaration before ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro same
    exact ⟨reference, referenceFuel, by simpa only [same] using referenceCompleted⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
    exact List.singleton_inj.mp same.2.1

theorem refusal_iff_source_refuses (spaces : Spaces) (state : Kernel.SpecificationAdmission.State)
    (declaration : ProofDeclaration) (before : State) (ready : Ready spaces state.theory before) :
    Kernel.SpecificationAdmission.step? state declaration = none ↔
      ∃ after fuel, run program fuel (requestConfiguration before spaces state declaration) = .complete after [.symbol "None"] [] [] := by
  rw [← result_iff_source_returns spaces state declaration before ready]
  cases Kernel.SpecificationAdmission.step? state declaration <;> simp [resultValue, optionValue, stateValue, listValue]

/-- Acceptance corresponds to a real logical step. Capability equality alone
is not asserted to identify a caller-proposed theory. -/
theorem step_iff_source_advances (spaces : Spaces) (state : Kernel.SpecificationAdmission.State)
    (declaration : ProofDeclaration) (before : State) (ready : Ready spaces state.theory before) :
    (∃ next, Kernel.SpecificationAdmission.Step state declaration next) ↔
      ∃ after remaining fuel, run program fuel (requestConfiguration before spaces state declaration) =
        .complete after [.expression [.symbol "Some", stateValue spaces (pendingValue remaining)]] [] [] := by
  constructor
  · rintro ⟨next, stepped⟩
    have accepted := (Kernel.SpecificationAdmission.step_eq_some_iff state next declaration).mpr stepped
    obtain ⟨after, fuel, returned⟩ := (result_iff_source_returns spaces state declaration before ready
      (.expression [.symbol "Some", stateValue spaces (pendingValue next.pending)])).mp
      (by simp [accepted, resultValue, optionValue])
    exact ⟨after, next.pending, fuel, returned⟩
  · rintro ⟨after, remaining, fuel, returned⟩
    have encoded := (result_iff_source_returns spaces state declaration before ready _).mpr ⟨after, fuel, returned⟩
    cases nextResult : Kernel.SpecificationAdmission.step? state declaration with
    | none => simp [nextResult, resultValue, optionValue] at encoded
    | some next => exact ⟨next, (Kernel.SpecificationAdmission.step_eq_some_iff state next declaration).mp nextResult⟩

theorem step_iff_gslt_path (spaces : Spaces) (state : Kernel.SpecificationAdmission.State)
    (declaration : ProofDeclaration) (before : State) (ready : Ready spaces state.theory before) :
    (∃ next, Kernel.SpecificationAdmission.Step state declaration next) ↔
      ∃ after remaining, (theory program).MultiStep (requestConfiguration before spaces state declaration)
        (finished after [.expression [.symbol "Some", stateValue spaces (pendingValue remaining)]] [] []) := by
  rw [step_iff_source_advances spaces state declaration before ready]
  exact exists_congr fun after => exists_congr fun remaining => completed_run_iff_path program _ after _ [] []

theorem step_iff_judgment (spaces : Spaces) (state : Kernel.SpecificationAdmission.State)
    (declaration : ProofDeclaration) (before : State) (ready : Ready spaces state.theory before) :
    (∃ next, Kernel.SpecificationAdmission.Step state declaration next) ↔
      ∃ after remaining, DeclarativeSpec.Runs program (requestConfiguration before spaces state declaration)
        (.complete after [.expression [.symbol "Some", stateValue spaces (pendingValue remaining)]] [] []) := by
  rw [step_iff_source_advances spaces state declaration before ready]
  exact exists_congr fun after => exists_congr fun remaining => completed_run_iff_derivation program _ after _ [] []

theorem completed_frame (spaces : Spaces) (state : Kernel.SpecificationAdmission.State)
    (declaration : ProofDeclaration) (before : State) (ready : Ready spaces state.theory before)
    (after : State) (fuel : Nat) (answers : List Atom)
    (returned : run program fuel (requestConfiguration before spaces state declaration) = .complete after answers [] []) :
    answers = [resultValue spaces (Kernel.SpecificationAdmission.step? state declaration)] ∧
      EffectFrame spaces state declaration before after := by
  obtain ⟨reference, referenceFuel, completed, frame⟩ := sufficient_fuel spaces state declaration before ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
  rw [← same.1]
  exact ⟨same.2.1.symm, frame⟩

theorem source_acceptance_tables (spaces : Spaces) (state : Kernel.SpecificationAdmission.State)
    (declaration : ProofDeclaration) (before after : State) (remaining : List SpecificationEntry) (fuel : Nat)
    (ready : Ready spaces state.theory before)
    (accepted : run program fuel (requestConfiguration before spaces state declaration) =
      .complete after [.expression [.symbol "Some", stateValue spaces (pendingValue remaining)]] [] []) :
    ∃ next, Kernel.SpecificationAdmission.Step state declaration next ∧ next.pending = remaining ∧
      TableReady spaces next.theory after ∧
      InferenceCache.Ready state.theory.termSignature (tableValue spaces.terms) spaces.cache after ∧
      after.cells = before.cells ∧ after.read spaces.proofs = before.read spaces.proofs := by
  obtain ⟨observed, frame⟩ := completed_frame spaces state declaration before ready after fuel _ accepted
  cases nextResult : Kernel.SpecificationAdmission.step? state declaration with
  | none => simp [nextResult, resultValue, optionValue] at observed
  | some next =>
      have encoded : pendingValue next.pending = pendingValue remaining := by
        simpa [nextResult, resultValue, optionValue, stateValue, listValue] using
          (List.singleton_inj.mp observed).symm
      exact ⟨next, (Kernel.SpecificationAdmission.step_eq_some_iff state next declaration).mp nextResult,
        SpecificationMatching.pendingValue_injective encoded, frame.tables_of_step nextResult,
        frame.cache, frame.cells, frame.proofs⟩

def finishRequestConfiguration (before : State) (spaces : Spaces)
    (result : Option Kernel.SpecificationAdmission.State) : Configuration :=
  { state := before, control := .evaluate (finishEnvironment (resultValue spaces result))
      (.expression [.symbol "mm0:spec-finish", .var "valueInput"]) }

theorem finish_sufficient_fuel (spaces : Spaces) (result : Option Kernel.SpecificationAdmission.State) (before : State) :
    ∃ fuel, ∀ extra, run program (fuel + extra) (finishRequestConfiguration before spaces result) =
      .complete before [AdmissionStep.resultValue spaces (result.bind fun state =>
        if state.pending.isEmpty then some state.theory else none)] [] [] := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program (finishEnvironment (resultValue spaces result))
    before before _ _ (finish_captured_returns _ before spaces result "valueInput" rfl)
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ before _ [] [] completed⟩

theorem finish_result_iff (spaces : Spaces) (result : Option Kernel.SpecificationAdmission.State)
    (before : State) (answer : Atom) :
    AdmissionStep.resultValue spaces (result.bind fun state =>
      if state.pending.isEmpty then some state.theory else none) = answer ↔
      ∃ fuel, run program fuel (finishRequestConfiguration before spaces result) = .complete before [answer] [] [] := by
  obtain ⟨referenceFuel, completed⟩ := finish_sufficient_fuel spaces result before
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro same
    exact ⟨referenceFuel, by simpa only [same] using referenceCompleted⟩
  · rintro ⟨fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ before before _ [] [] _ [] [] referenceCompleted returned
    exact List.singleton_inj.mp same.2.1

theorem finish_acceptance_iff (spaces : Spaces) (result : Option Kernel.SpecificationAdmission.State) (before : State) :
    (∃ state, result = some state ∧ state.pending = []) ↔
      ∃ fuel, run program fuel (finishRequestConfiguration before spaces result) =
        .complete before [optionValue (some (theoryValue spaces))] [] [] := by
  rw [← finish_result_iff spaces result before]
  cases result with
  | none => simp [AdmissionStep.resultValue, optionValue]
  | some state =>
      rcases state with ⟨logicalTheory, pending⟩
      cases pending <;> simp [AdmissionStep.resultValue, optionValue]

theorem finish_refusal_iff (spaces : Spaces) (result : Option Kernel.SpecificationAdmission.State) (before : State) :
    (result = none ∨ ∃ state, result = some state ∧ state.pending ≠ []) ↔
      ∃ fuel, run program fuel (finishRequestConfiguration before spaces result) = .complete before [.symbol "None"] [] [] := by
  rw [← finish_result_iff spaces result before]
  cases result with
  | none => simp [AdmissionStep.resultValue, optionValue]
  | some state =>
      rcases state with ⟨logicalTheory, pending⟩
      cases pending <;> simp [AdmissionStep.resultValue, optionValue]

theorem completed_finish_preserves_store (spaces : Spaces) (result : Option Kernel.SpecificationAdmission.State)
    (before after : State) (fuel : Nat) (answers : List Atom)
    (returned : run program fuel (finishRequestConfiguration before spaces result) = .complete after answers [] []) :
    after = before ∧ answers = [AdmissionStep.resultValue spaces (result.bind fun state =>
      if state.pending.isEmpty then some state.theory else none)] := by
  obtain ⟨referenceFuel, completed⟩ := finish_sufficient_fuel spaces result before
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  have same := completed_result_unique program referenceFuel fuel _ before after _ [] [] _ [] [] referenceCompleted returned
  exact ⟨same.1.symm, same.2.1.symm⟩

/-- The EOF predicate is the one already used in the independent kernel
verifier, applied to its resolved logical session result. -/
theorem finish_matches_verifier (bindings : Subst) (before : State) (spaces : Spaces)
    (specification : List SpecificationEntry) (declarations : List ProofDeclaration) (name : String)
    (captured : applySubst bindings (.var name) =
      resultValue spaces (Kernel.SpecificationAdmission.run? ⟨{}, specification⟩ declarations)) :
    PureReturns program bindings before (.expression [.symbol "mm0:spec-finish", .var name]) before
      (AdmissionStep.resultValue spaces (Kernel.SpecificationAdmission.verify? specification declarations)) := by
  have completed := finish_captured_returns bindings before spaces _ name captured
  cases evaluated : Kernel.SpecificationAdmission.run? ⟨{}, specification⟩ declarations <;>
    simpa [Kernel.SpecificationAdmission.verify?, evaluated] using completed

namespace Controls

/-- A public sort matching the next entry reaches real admission and publishes
from the actual empty session tables. -/
theorem start_sort_source_advances (before : State) (index : Nat) (info : Kernel.SortInfo) :
    ∃ after fuel, run program fuel
      (requestConfiguration (SessionInitialization.startState before (pendingValue [.sort index info]))
        (SessionInitialization.allocatedSpaces before) ⟨{}, [.sort index info]⟩ ⟨.sort index info, false⟩) =
      .complete after [.expression [.symbol "Some", stateValue (SessionInitialization.allocatedSpaces before) (pendingValue [])]] [] [] := by
  obtain ⟨after, fuel, completed, _⟩ := sufficient_fuel (SessionInitialization.allocatedSpaces before)
    ⟨{}, [.sort index info]⟩ ⟨.sort index info, false⟩
    (SessionInitialization.startState before (pendingValue [.sort index info]))
    (AdmissionChecks.start_ready before (pendingValue [.sort index info]))
  have returned := completed 0
  simp only [Nat.add_zero] at returned
  refine ⟨after, fuel, ?_⟩
  simpa [Kernel.SpecificationAdmission.step?, Kernel.SpecificationAdmission.pending?, Kernel.SpecificationEntry.checkMatch,
    Theory.step?, Admission.check, Theory.sortSignature, List.lookup, resultValue, optionValue] using returned

/-- A mismatched next specification entry refuses before any admission,
so neither checking nor publication changes any part of the store. -/
theorem mismatched_entry_preserves_store (spaces : Spaces) (state : Kernel.SpecificationAdmission.State)
    (declaration : ProofDeclaration) (before : State) (ready : Ready spaces state.theory before)
    (refused : Kernel.SpecificationAdmission.pending? state.pending declaration = none) :
    Call spaces state declaration before before none := by
  obtain ⟨after, returned, frame⟩ := captured_returns spaces state declaration before ready
  rw [frame.blocked refused] at returned
  simpa [Kernel.SpecificationAdmission.step?, refused] using returned

theorem empty_pending_finish_accepts (spaces : Spaces) (logicalTheory : Theory) (before : State) :
    ∃ fuel, run program fuel (finishRequestConfiguration before spaces (some ⟨logicalTheory, []⟩)) =
      .complete before [optionValue (some (theoryValue spaces))] [] [] :=
  (finish_acceptance_iff spaces (some ⟨logicalTheory, []⟩) before).mp ⟨⟨logicalTheory, []⟩, rfl, rfl⟩

theorem incomplete_pending_finish_refuses (spaces : Spaces) (logicalTheory : Theory)
    (entry : SpecificationEntry) (remaining : List SpecificationEntry) (before : State) :
    ∃ fuel, run program fuel (finishRequestConfiguration before spaces (some ⟨logicalTheory, entry :: remaining⟩)) =
      .complete before [.symbol "None"] [] [] :=
  (finish_refusal_iff spaces (some ⟨logicalTheory, entry :: remaining⟩) before).mp
    (Or.inr ⟨⟨logicalTheory, entry :: remaining⟩, rfl, by simp⟩)

theorem earlier_failure_finish_refuses (spaces : Spaces) (before : State) :
    ∃ fuel, run program fuel (finishRequestConfiguration before spaces none) = .complete before [.symbol "None"] [] [] :=
  (finish_refusal_iff spaces none before).mp (Or.inl rfl)

end Controls

end Mettapedia.Languages.MM0.MeTTa.SpecificationStep
