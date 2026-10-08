import Mettapedia.Languages.MM0.MeTTa.Admission.AdmissionPublication

/-!
# Checking before publication in the retained MM0 source

The admission step runs the independent payload checks against the preceding
theory, publishes only after a successful check, and returns the actual native
table handles. The logical snapshot represented by those handles is established
by the physical publication proof. Publication preserves the cache's preceding
signature scope; checking in an extended signature requires a driver reset.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.AdmissionStep

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open NamedSpaces (Handle)
open Kernel (Theory Admission)
open ListAccess (optionValue)
open TableAccess (tableValue)
open SessionInitialization (Spaces theoryValue)
open AdmissionChecks (admissionValue TableReady Ready)

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 119)[118]'(by decide +kernel)

private def checkedEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 120)[119]'(by decide +kernel)

private def checkedCases : SpaceSemantics.Cases :=
  match checkedEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def environment (spaces : Spaces) (admission : Admission) : Subst :=
  [("admission", admissionValue admission), ("theory", theoryValue spaces)]

private def checkedEnvironment (spaces : Spaces) (admission : Admission) (answer : Bool) : Subst :=
  [("admission", admissionValue admission), ("theory", theoryValue spaces), ("conditionInput", boolean answer)]

private theorem unique :
    program.equations.filter (fun row => row.head == "mm0:admission-step") = [equation] := by
  decide +kernel

private theorem checked_unique :
    program.equations.filter (fun row => row.head == "mm0:admission-checked") = [checkedEquation] := by
  decide +kernel

private theorem formals : equation.arguments = [.var "theory", .var "admission"] := by
  decide +kernel

private theorem checked_formals :
    checkedEquation.arguments = [.var "conditionInput", .var "theory", .var "admission"] := by
  decide +kernel

private theorem shape : equation.body =
    .expression [.symbol "let", .var "admissionCheckResult",
      .expression [.symbol "mm0:admission-check", .var "theory", .var "admission"],
      .expression [.symbol "mm0:admission-checked", .var "admissionCheckResult", .var "theory", .var "admission"]] := by
  decide +kernel

private theorem checked_shape : checkedEquation.body =
    .expression [.symbol "case", .var "conditionInput",
      .expression (checkedCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem checked_cases_shape : checkedCases =
    [(boolean false, .symbol "None"),
      (boolean true, .expression [.symbol "mm0:admission-publish", .var "theory", .var "admission"]),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by
  decide +kernel

private theorem clause (spaces : Spaces) (admission : Admission) :
    clauses program "mm0:admission-step" [theoryValue spaces, admissionValue admission] =
      [.evaluate (environment spaces admission) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, environment]

private theorem checked_clause (spaces : Spaces) (admission : Admission) (answer : Bool) :
    clauses program "mm0:admission-checked" [boolean answer, theoryValue spaces, admissionValue admission] =
      [.evaluate (checkedEnvironment spaces admission answer) checkedEquation.body] := by
  rw [clauses_use_only_the_named_equations, checked_unique]
  simp [checked_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, checkedEnvironment]

/-- Native results carry handles. Their logical snapshot is recorded separately
in the earned post-state table invariant. -/
def resultValue (spaces : Spaces) (result : Option Theory) : Atom :=
  optionValue (result.map fun _ => theoryValue spaces)

def Call (spaces : Spaces) (admission : Admission) (before after : State) (result : Option Theory) : Prop :=
  ∀ bindings theoryName admissionName,
    applySubst bindings (.var theoryName) = theoryValue spaces →
    applySubst bindings (.var admissionName) = admissionValue admission →
    PureReturns program bindings before
      (.expression [.symbol "mm0:admission-step", .var theoryName, .var admissionName]) after
      (resultValue spaces result)

private theorem checked_false_body_returns (spaces : Spaces) (admission : Admission) (state : State) :
    PureReturns program (checkedEnvironment spaces admission false) state checkedEquation.body state (.symbol "None") := by
  rw [checked_shape]
  let bindings := checkedEnvironment spaces admission false
  apply case_returns program bindings bindings state state state (.var "conditionInput")
    (boolean false) (.symbol "None") _ _ checkedCases (read_cases_encoded _)
  · simpa [bindings, checkedEnvironment, applySubst, Subst.lookup] using
      variable_returns program bindings state "conditionInput"
  · simp [checked_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
  · exact symbol_returns program bindings state "None"

private theorem checked_captured_of_body (spaces : Spaces) (admission : Admission) (answer : Bool)
    (before after : State) (result : Atom)
    (computed : PureReturns program (checkedEnvironment spaces admission answer) before checkedEquation.body after result)
    (bindings : Subst) (answerName theoryName admissionName : String)
    (capturedAnswer : applySubst bindings (.var answerName) = boolean answer)
    (capturedTheory : applySubst bindings (.var theoryName) = theoryValue spaces)
    (capturedAdmission : applySubst bindings (.var admissionName) = admissionValue admission) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:admission-checked", .var answerName, .var theoryName, .var admissionName]) after result := by
  apply authored_variable_call_returns program bindings (checkedEnvironment spaces admission answer) before after
    "mm0:admission-checked" [answerName, theoryName, admissionName] checkedEquation.body _
    (by decide) (by decide) (by decide +kernel) _ computed (by decide)
  simpa [capturedAnswer, capturedTheory, capturedAdmission] using checked_clause spaces admission answer

/-- A refused check returns immediately without a native publication, even
when no publication table is allocated. -/
theorem checked_false_returns (spaces : Spaces) (admission : Admission) (state : State)
    (bindings : Subst) (answerName theoryName admissionName : String)
    (capturedAnswer : applySubst bindings (.var answerName) = boolean false)
    (capturedTheory : applySubst bindings (.var theoryName) = theoryValue spaces)
    (capturedAdmission : applySubst bindings (.var admissionName) = admissionValue admission) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:admission-checked", .var answerName, .var theoryName, .var admissionName]) state (.symbol "None") :=
  checked_captured_of_body spaces admission false state state _
    (checked_false_body_returns spaces admission state) bindings answerName theoryName admissionName
    capturedAnswer capturedTheory capturedAdmission

private theorem checked_true_body_of_path (spaces : Spaces) (admission : Admission) (before after : State)
    (published : ∀ bindings theoryName admissionName,
      applySubst bindings (.var theoryName) = theoryValue spaces →
      applySubst bindings (.var admissionName) = admissionValue admission →
      PureReturns program bindings before
        (.expression [.symbol "mm0:admission-publish", .var theoryName, .var admissionName]) after
        (optionValue (some (theoryValue spaces)))) :
    PureReturns program (checkedEnvironment spaces admission true) before checkedEquation.body after
      (optionValue (some (theoryValue spaces))) := by
  rw [checked_shape]
  let bindings := checkedEnvironment spaces admission true
  apply case_returns program bindings bindings before before after (.var "conditionInput")
    (boolean true) (.expression [.symbol "mm0:admission-publish", .var "theory", .var "admission"])
    _ _ checkedCases (read_cases_encoded _)
  · simpa [bindings, checkedEnvironment, applySubst, Subst.lookup] using
      variable_returns program bindings before "conditionInput"
  · simp [checked_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
  · exact published bindings "theory" "admission" rfl rfl

private theorem step_captured_of_paths (spaces : Spaces) (admission : Admission)
    (before checked after : State) (answer : Bool) (result : Option Theory)
    (computed : AdmissionChecks.Call spaces admission before checked answer)
    (handled : ∀ bindings answerName theoryName admissionName,
      applySubst bindings (.var answerName) = boolean answer →
      applySubst bindings (.var theoryName) = theoryValue spaces →
      applySubst bindings (.var admissionName) = admissionValue admission →
      PureReturns program bindings checked
        (.expression [.symbol "mm0:admission-checked", .var answerName, .var theoryName, .var admissionName]) after
        (resultValue spaces result)) : Call spaces admission before after result := by
  have body : PureReturns program (environment spaces admission) before equation.body after (resultValue spaces result) := by
    rw [shape]
    let bindings := environment spaces admission
    let bound := ("admissionCheckResult", boolean answer) :: bindings
    apply let_returns program bindings bound before checked after (.var "admissionCheckResult") _ _ (boolean answer) _
    · exact computed bindings "theory" "admission" rfl rfl
    · simp [SpaceSemantics.matchValue, matchAtom, bindings, bound, environment, Subst.lookup]
    · exact handled bound "admissionCheckResult" "theory" "admission" rfl rfl rfl
  intro bindings theoryName admissionName capturedTheory capturedAdmission
  apply authored_variable_call_returns program bindings (environment spaces admission) before after
    "mm0:admission-step" [theoryName, admissionName] equation.body _
    (by decide) (by decide) (by decide +kernel) _ body (by decide)
  simpa [capturedTheory, capturedAdmission] using clause spaces admission

/-- The check may extend its old scoped cache. Successful publication changes
only its target declaration tables; refusal publishes no table at all. -/
structure EffectFrame (spaces : Spaces) (theory : Theory) (admission : Admission)
    (before checked after : State) (bound : Nat) : Prop where
  checkReady : Ready spaces theory checked
  checkFrame : InferenceCache.Frame spaces.cache (tableValue spaces.terms) bound before checked
  refused : Admission.check theory admission = false → after = checked
  published : Admission.check theory admission = true → AdmissionPublication.Writes spaces admission checked after
  tables : TableReady spaces ((Theory.step? theory admission).getD theory) after
  cache : InferenceCache.Ready theory.termSignature (tableValue spaces.terms) spaces.cache after
  cacheRead : after.read spaces.cache = checked.read spaces.cache
  cells : after.cells = before.cells
  proofs : after.read spaces.proofs = before.read spaces.proofs
  other : ∀ handle, handle ≠ spaces.cache → handle ∉ AdmissionPublication.targets spaces admission →
    after.read handle = before.read handle

theorem EffectFrame.tables_of_step {spaces : Spaces} {theory next : Theory} {admission : Admission}
    {before checked after : State} {bound : Nat}
    (frame : EffectFrame spaces theory admission before checked after bound)
    (step : Theory.step? theory admission = some next) : TableReady spaces next after := by
  simpa only [step, Option.getD_some] using frame.tables

theorem EffectFrame.refused_ready {spaces : Spaces} {theory : Theory} {admission : Admission}
    {before checked after : State} {bound : Nat}
    (frame : EffectFrame spaces theory admission before checked after bound)
    (refused : Theory.step? theory admission = none) : Ready spaces theory after := by
  have rejected : Admission.check theory admission = false := by
    cases tested : Admission.check theory admission with
    | false => rfl
    | true => simp [Theory.step?, tested] at refused
  rw [frame.refused rejected]
  exact frame.checkReady

/-- All five source constructors agree with the independent theory step.
The returned snapshot is established by the real physical publication trace. -/
theorem captured_returns (spaces : Spaces) (theory : Theory) (admission : Admission)
    (before : State) (ready : Ready spaces theory before) :
    ∃ checked after bound, Call spaces admission before after (Theory.step? theory admission) ∧
      EffectFrame spaces theory admission before checked after bound := by
  obtain ⟨checked, bound, computed, readyChecked, frame⟩ :=
    AdmissionChecks.captured_returns spaces theory admission before ready
  cases tested : Admission.check theory admission with
  | false =>
      refine ⟨checked, checked, bound, ?_, ?_⟩
      · apply step_captured_of_paths spaces admission before checked checked false (Theory.step? theory admission)
          (by simpa only [tested] using computed)
        intro bindings answerName theoryName admissionName capturedAnswer capturedTheory capturedAdmission
        simpa [resultValue, Theory.step?, tested, optionValue] using
          checked_false_returns spaces admission checked bindings answerName theoryName admissionName
            capturedAnswer capturedTheory capturedAdmission
      · refine ⟨readyChecked, frame, fun _ => rfl, ?_, ?_, readyChecked.cache, rfl, frame.cells, ?_, ?_⟩
        · intro impossible
          rw [tested] at impossible
          cases impossible
        · simpa [Theory.step?, tested] using readyChecked.toTableReady
        · exact frame.other spaces.proofs ready.separate_proof
        · intro handle different _
          exact frame.other handle different
  | true =>
      have authorized := (Admission.check_iff theory admission).mp tested
      obtain ⟨after, published, written⟩ := AdmissionPublication.returns spaces theory admission checked readyChecked.toTableReady
      obtain ⟨cellsPublished, cachePublished, proofsPublished, othersPublished⟩ :=
        AdmissionPublication.writes_frame spaces theory admission checked after readyChecked.toTableReady written
      refine ⟨checked, after, bound, ?_, ?_⟩
      · apply step_captured_of_paths spaces admission before checked after true (Theory.step? theory admission)
          (by simpa only [tested] using computed)
        intro bindings answerName theoryName admissionName capturedAnswer capturedTheory capturedAdmission
        simpa [resultValue, Theory.step?, tested] using
          checked_captured_of_body spaces admission true checked after _
            (checked_true_body_of_path spaces admission checked after published)
            bindings answerName theoryName admissionName capturedAnswer capturedTheory capturedAdmission
      · refine ⟨readyChecked, frame, ?_, fun _ => written, ?_, ?_, cachePublished,
          cellsPublished.trans frame.cells, proofsPublished.trans (frame.other spaces.proofs ready.separate_proof), ?_⟩
        · intro impossible
          rw [tested] at impossible
          cases impossible
        · simpa [Theory.step?, tested] using
            AdmissionPublication.writes_tables spaces theory admission checked after readyChecked.toTableReady authorized written
        · exact AdmissionPublication.writes_frozen_cache spaces theory admission checked after readyChecked written
        · intro handle different untouched
          exact (othersPublished handle untouched).trans (frame.other handle different)

def requestConfiguration (state : State) (spaces : Spaces) (admission : Admission) : Configuration :=
  { state, control := .evaluate (environment spaces admission)
      (.expression [.symbol "mm0:admission-step", .var "theory", .var "admission"]) }

theorem sufficient_fuel (spaces : Spaces) (theory : Theory) (admission : Admission)
    (before : State) (ready : Ready spaces theory before) :
    ∃ checked after bound fuel,
      (∀ extra, run program (fuel + extra) (requestConfiguration before spaces admission) =
        .complete after [resultValue spaces (Theory.step? theory admission)] [] []) ∧
      EffectFrame spaces theory admission before checked after bound := by
  obtain ⟨checked, after, bound, returned, frame⟩ := captured_returns spaces theory admission before ready
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program (environment spaces admission)
    before after _ _ (returned _ "theory" "admission" rfl rfl)
  exact ⟨checked, after, bound, fuel, fun extra => completed_run_more_fuel program fuel extra _ after _ [] [] completed, frame⟩

/-- Observe the native return value separately from the represented logical
snapshot, since successful native theory values contain capabilities. -/
theorem result_iff_source_returns (spaces : Spaces) (theory : Theory) (admission : Admission)
    (before : State) (ready : Ready spaces theory before) (answer : Atom) :
    resultValue spaces (Theory.step? theory admission) = answer ↔
      ∃ after fuel, run program fuel (requestConfiguration before spaces admission) = .complete after [answer] [] [] := by
  obtain ⟨_, reference, _, referenceFuel, completed, _⟩ := sufficient_fuel spaces theory admission before ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro same
    exact ⟨reference, referenceFuel, by simpa only [same] using referenceCompleted⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
    exact List.singleton_inj.mp same.2.1

theorem authorized_iff_source_advances (spaces : Spaces) (theory : Theory) (admission : Admission)
    (before : State) (ready : Ready spaces theory before) :
    Admission.Authorized theory admission ↔
      ∃ after fuel, run program fuel (requestConfiguration before spaces admission) =
        .complete after [optionValue (some (theoryValue spaces))] [] [] := by
  rw [← Admission.check_iff, ← result_iff_source_returns spaces theory admission before ready]
  cases tested : Admission.check theory admission <;> simp [resultValue, Theory.step?, tested, optionValue]

theorem step_iff_source_advances (spaces : Spaces) (theory : Theory) (admission : Admission)
    (before : State) (ready : Ready spaces theory before) :
    Theory.Step theory admission (admission.insert theory) ↔
      ∃ after fuel, run program fuel (requestConfiguration before spaces admission) =
        .complete after [optionValue (some (theoryValue spaces))] [] [] := by
  rw [← authorized_iff_source_advances spaces theory admission before ready]
  exact ⟨fun step => by cases step with | intro authorized => exact authorized,
    fun authorized => .intro authorized⟩

theorem refusal_iff_source_refuses (spaces : Spaces) (theory : Theory) (admission : Admission)
    (before : State) (ready : Ready spaces theory before) :
    Theory.step? theory admission = none ↔
      ∃ after fuel, run program fuel (requestConfiguration before spaces admission) = .complete after [.symbol "None"] [] [] := by
  rw [← result_iff_source_returns spaces theory admission before ready]
  cases tested : Admission.check theory admission <;> simp [resultValue, Theory.step?, tested, optionValue]

theorem step_iff_gslt_path (spaces : Spaces) (kernelTheory : Theory) (admission : Admission)
    (before : State) (ready : Ready spaces kernelTheory before) :
    Theory.Step kernelTheory admission (admission.insert kernelTheory) ↔
      ∃ after, (theory program).MultiStep (requestConfiguration before spaces admission)
        (finished after [optionValue (some (theoryValue spaces))] [] []) := by
  rw [step_iff_source_advances spaces kernelTheory admission before ready]
  exact exists_congr fun after => completed_run_iff_path program _ after _ [] []

theorem step_iff_judgment (spaces : Spaces) (theory : Theory) (admission : Admission)
    (before : State) (ready : Ready spaces theory before) :
    Theory.Step theory admission (admission.insert theory) ↔
      ∃ after, DeclarativeSpec.Runs program (requestConfiguration before spaces admission)
        (.complete after [optionValue (some (theoryValue spaces))] [] []) := by
  rw [step_iff_source_advances spaces theory admission before ready]
  exact exists_congr fun after => completed_run_iff_derivation program _ after _ [] []

/-- Every completed observation inherits the actual pre-publication cache
frame and the publication trace, independent of its supplied fuel. -/
theorem completed_frame (spaces : Spaces) (theory : Theory) (admission : Admission)
    (before : State) (ready : Ready spaces theory before) (after : State) (fuel : Nat) (answers : List Atom)
    (returned : run program fuel (requestConfiguration before spaces admission) = .complete after answers [] []) :
    answers = [resultValue spaces (Theory.step? theory admission)] ∧
      ∃ checked bound, EffectFrame spaces theory admission before checked after bound := by
  obtain ⟨checked, reference, bound, referenceFuel, completed, frame⟩ := sufficient_fuel spaces theory admission before ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
  rw [← same.1]
  exact ⟨same.2.1.symm, checked, bound, frame⟩

/-- Successful observation establishes physical ownership of the extended
theory and checks the declaration in the actual preceding theory. -/
theorem source_acceptance_tables (spaces : Spaces) (theory : Theory) (admission : Admission)
    (before after : State) (fuel : Nat) (ready : Ready spaces theory before)
    (accepted : run program fuel (requestConfiguration before spaces admission) =
      .complete after [optionValue (some (theoryValue spaces))] [] []) :
    Theory.Step theory admission (admission.insert theory) ∧
      TableReady spaces (admission.insert theory) after ∧
      InferenceCache.Ready theory.termSignature (tableValue spaces.terms) spaces.cache after ∧
      after.cells = before.cells ∧ after.read spaces.proofs = before.read spaces.proofs := by
  have step := (step_iff_source_advances spaces theory admission before ready).mpr ⟨after, fuel, accepted⟩
  have authorized : Admission.Authorized theory admission := by
    cases step with | intro authorized => exact authorized
  have allowed := (Admission.check_iff theory admission).mpr authorized
  obtain ⟨_, checked, bound, frame⟩ := completed_frame spaces theory admission before ready after fuel _ accepted
  exact ⟨step, by simpa [Theory.step?, allowed] using frame.tables, frame.cache, frame.cells, frame.proofs⟩

namespace Controls

/-- The actual start state permits a fresh sort, and the source step completes
through native publication. -/
theorem start_sort_source_advances (before : State) (specification : Atom) (index : Nat) (info : Kernel.SortInfo) :
    ∃ after fuel, run program fuel
      (requestConfiguration (SessionInitialization.startState before specification)
        (SessionInitialization.allocatedSpaces before) (.sort index info)) =
      .complete after [optionValue (some (theoryValue (SessionInitialization.allocatedSpaces before)))] [] [] := by
  apply (authorized_iff_source_advances _ ({} : Theory) _ _
    (AdmissionChecks.start_ready before specification)).mp
  exact .sort rfl

/-- A duplicate sort stops at the refused handler. Its source execution does
not publish a second row or change any cache, table or cell. -/
theorem duplicate_sort_source_refuses (spaces : Spaces) (theory : Theory)
    (index : Nat) (info old : Kernel.SortInfo) (state : State) (ready : Ready spaces theory state)
    (present : theory.sortSignature index = some old) :
    Call spaces (.sort index info) state state none := by
  apply step_captured_of_paths spaces (.sort index info) state state state false none
  · simpa only [Admission.check, present, Option.isNone_some] using
      AdmissionChecks.sort_captured_returns spaces theory index info state ready
  · intro bindings answerName theoryName admissionName capturedAnswer capturedTheory capturedAdmission
    exact checked_false_returns spaces (.sort index info) state bindings answerName theoryName admissionName
      capturedAnswer capturedTheory capturedAdmission

end Controls

end Mettapedia.Languages.MM0.MeTTa.AdmissionStep
