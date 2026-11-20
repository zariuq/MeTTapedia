import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralRuleReadoutCache
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralTypedSiteExecution.Traversal
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceLocalCompletion
import Mettapedia.OSLF.NativeTypes.Semantics.Families
import Mettapedia.OSLF.Framework.GeneralCanonicalQueryOccurrences
import Mettapedia.OSLF.MeTTaIL.GeneralRhoFrontierComparison
import Mettapedia.OSLF.MeTTaIL.GeneralRhoDepthOne

/-!
# Ordered scoped programs executed by the authored MeTTa driver

The presentation entry enumerates authorized typed sites and constructs the
original requests inside MeTTa. Each request runs the original premise machine
for its supplied budget and retains the complete resulting state. Successful
readouts are concatenated in request order. Completion bounds refer to the
original expansion trees; finite prefixes expose pending tasks and obligations.

An independently defined target observer reads physical receipt occurrences
from actual PeTTa completion. For equation-free, stratified plans, saturation
identifies these occurrences with the original source GSLT's successors and
transports existential and universal target predicates.
The quoted execution claims require no registered dynamic relations; native
primitive service execution requires its own correspondence proof.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralProgramDriverExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open SpaceSemantics (Program Equation)
open Eval
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_program_driver.metta"
    sha256 "240bf1fca75125a9c2baa1df7fcbabc4d26f92fd866128b13ff4b9882689edf1"

def runtime : Program := GeneralRuleReadoutCache.runtime.append
  (GeneralTypedSiteExecution.source.program.append source.program)

/-- Licensing is a proposition; request data and its budget are the complete
input identity. Evaluation proof terms are not additional occurrences. -/
abbrev LicensedRequest := {request : GeneralRuleJobExecution.Request //
  request.job.Valid request.plan request.bound request.expected request.source}

abbrev Invocation := LicensedRequest × Nat

def requestTerm (request : GeneralRuleJobExecution.Request) : Term :=
  ScopedRuleJobReadoutExecution.requestProjectionTerm request
    (GeneralRuleJobObservation.requestFootprint request)

def invocationTerm (invocation : Invocation) : Term :=
  .application "ProgramJob" [requestTerm invocation.1.val, .natural invocation.2]

def innerState (invocation : Invocation) :
    Execution.State invocation.1.val.environment invocation.1.val.goal :=
  Execution.run invocation.1.val.environment invocation.1.val.goal invocation.2
    (Execution.start invocation.1.val.environment invocation.1.val.goal)

def receipts (invocation : Invocation) : List GeneralRuleJobs.Receipt :=
  ((innerState invocation).answers.filterMap
    (GeneralRuleJobExecution.rootProjection invocation.1.val invocation.1.property)).map Subtype.val

def observationTerm (invocation : Invocation) : Term :=
  .application "ProgramJobObservation"
    [requestTerm invocation.1.val,
     PremiseOperationsExecution.GeneralExecution.stateTerm (innerState invocation),
     encodeList ScopedRuleJobReadoutExecution.receiptTerm (receipts invocation)]

def programObservationTerm (invocations : List Invocation) : Term :=
  .application "ProgramObservation"
    [encodeList observationTerm invocations,
     encodeList ScopedRuleJobReadoutExecution.receiptTerm (invocations.flatMap receipts)]

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term

private inductive Helper where | receipts | job | run | requests | execute

private def Helper.head : Helper → String
  | .receipts => "gslt:program:receipts"
  | .job => "gslt:program:job"
  | .run => "gslt:program:run"
  | .requests => "gslt:program:requests"
  | .execute => "gslt:program:execute"

private def Helper.names : Helper → List String
  | .receipts => ["readouts"]
  | .job => ["request", "budget"]
  | .run => ["jobs"]
  | .requests => ["environment", "permissions", "bound", "expected", "source", "budget", "jobs"]
  | .execute => ["environment", "permissions", "bound", "expected", "source", "rules", "budget"]

private def equation (helper : Helper) : SpaceSemantics.Equation :=
  (source.program.equations.filter (fun equation => equation.head == helper.head))[0]'(by
    cases helper <;> decide +kernel)

private def bindings (helper : Helper) (values : List Atom) : Subst :=
  (helper.names.zip values).reverse

private theorem helper_clause (helper : Helper) (values : List Atom)
    (length : values.length = helper.names.length) :
    clauses runtime helper.head values = [.evaluate (bindings helper values) (equation helper).body] :=
  PureData.named_equation_clause runtime helper.head (equation helper) helper.names values
    (by cases helper <;> rfl) (by cases helper <;> rfl) (by cases helper <;> decide) length

private theorem helper_raw (helper : Helper) (index : Nat) (bounded : index < helper.names.length) :
    argumentIsRaw runtime helper.head index = true := by
  have checked : (List.range helper.names.length).all
      (fun index => argumentIsRaw runtime helper.head index) = true := by
    cases helper <;> decide +kernel
  exact List.all_eq_true.mp checked index (List.mem_range.mpr bounded)

private theorem helper_call (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns runtime (bindings helper values) state (equation helper).body state answer) :
    PureReturns runtime caller state (a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return runtime caller (bindings helper values) state state
    helper.head arguments (equation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide)
  · cases helper <;> decide +kernel
  · intro index bounded
    apply helper_raw helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · rw [captured]
    exact helper_clause helper values length
  · exact returned

private theorem helper_capture (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns runtime [] state (a helper.head values) state answer) :
    PureReturns runtime caller state (a helper.head arguments) state answer := by
  apply PureData.raw_capture_returns runtime [] caller state state helper.head values arguments answer
  · cases helper <;> decide +kernel
  · intro index bounded
    apply helper_raw helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · cases helper <;> decide
  · have unchanged : applySubst [] = id := by
      funext value
      exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
    simpa only [unchanged, List.map_id] using captured.symm
  · exact returned

private theorem branch_returns (caller selected : Subst) (state : State)
    (expression value : Atom) (rows : SpaceSemantics.Cases) (body answer : Atom)
    (computed : PureReturns runtime caller state expression state value)
    (matched : SpaceSemantics.selectCase caller value rows = some (selected, body))
    (continued : PureReturns runtime selected state body state answer) :
    PureReturns runtime caller state
      (a "case" [expression, .expression (rows.map fun row => .expression [row.1, row.2])]) state answer :=
  case_returns runtime caller selected state state state expression value body answer _ rows
    (read_cases_encoded _) computed matched continued

private theorem named_let_returns (caller : Subst) (state : State)
    (name : String) (expression value body answer : Atom)
    (fresh : caller.lookup name = none)
    (computed : PureReturns runtime caller state expression state value)
    (continued : PureReturns runtime ((name, value) :: caller) state body state answer) :
    PureReturns runtime caller state (a "let" [v name, expression, body]) state answer := by
  apply let_returns runtime caller ((name, value) :: caller) state state state
    (v name) expression body value answer computed
  · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, fresh]
  · exact continued

private def dataHeads : List String :=
  ["Some", "LCons", "PremiseState", "RootGoal", "ProgramJob", "ProgramJobObservation", "ProgramObservation",
   "RuleJobRequestProjection"]

private theorem template_constructor (head : String) (arguments : List Atom)
    (constructor : head ∈ dataHeads)
    (children : ∀ child ∈ arguments, PureData.Template runtime child) :
    PureData.Template runtime (a head arguments) := by
  simp only [dataHeads, List.mem_cons, List.not_mem_nil, or_false] at constructor
  rcases constructor with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals exact PureData.Template.constructor _ _ (by decide +kernel) (by decide) children

private def receiptsCons : Atom :=
  a "let" [v "tail", a "gslt:program:receipts" [v "rest"], a "LCons" [v "receipt", v "tail"]]

private def receiptsCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"),
   (a "LCons" [a "Some" [v "receipt"], v "rest"], receiptsCons),
   (a "LCons" [.symbol "None", v "rest"], a "gslt:program:receipts" [v "rest"])]

private theorem receipts_shape : (equation .receipts).body =
    a "case" [v "readouts", .expression (receiptsCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

/-- The actual MeTTa filter removes only explicit refusals, preserving the
physical order and multiplicity of every successful readout. -/
theorem receipts_returns (state : State) (readouts : List (Option Term)) :
    PureReturns runtime [] state
      (a "gslt:program:receipts" [encoded (encodeList (encodeOption id) readouts)]) state
      (encoded (encodeList id (readouts.filterMap id))) := by
  induction readouts with
  | nil =>
      let caller := bindings .receipts [encoded (.symbol "LNil")]
      apply helper_call .receipts [] state _ _ _ rfl (by rfl)
      rw [receipts_shape]
      apply branch_returns caller caller state _ (.symbol "LNil") receiptsCases (.symbol "LNil") _
      · exact variable_returns runtime caller state "readouts"
      · simp [caller, bindings, Helper.names, receiptsCases,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns runtime caller state "LNil"
  | cons readout rest ih =>
      let value := encoded (encodeList (encodeOption id) (readout :: rest))
      let caller := bindings .receipts [value]
      cases readout with
      | none =>
          let selected := ("rest", encoded (encodeList (encodeOption id) rest)) :: caller
          apply helper_call .receipts [] state _ [value] _ rfl (by
            simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]; rfl)
          rw [receipts_shape]
          apply branch_returns caller selected state _ value receiptsCases
            (a "gslt:program:receipts" [v "rest"]) _
          · exact variable_returns runtime caller state "readouts"
          · simp [caller, selected, value, bindings, Helper.names, receiptsCases,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, Subst.lookup, encoded, encodeOption, CettaWireAtom.encode]
          · apply helper_capture .receipts selected state [v "rest"]
              [encoded (encodeList (encodeOption id) rest)] _ rfl
            · simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]
            · exact ih
      | some receipt =>
          let selected := [("rest", encoded (encodeList (encodeOption id) rest)),
            ("receipt", encoded receipt)] ++ caller
          let tail := encoded (encodeList id (rest.filterMap id))
          let continued := ("tail", tail) :: selected
          apply helper_call .receipts [] state _ [value] _ rfl (by
            simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]; rfl)
          rw [receipts_shape]
          apply branch_returns caller selected state _ value receiptsCases receiptsCons _
          · exact variable_returns runtime caller state "readouts"
          · simp [caller, selected, value, bindings, Helper.names, receiptsCases,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, Subst.lookup, encoded, encodeOption, CettaWireAtom.encode, CettaWireAtom.encodeMany]
          · unfold receiptsCons
            apply named_let_returns selected state "tail" _ tail
            · simp [selected, caller, bindings, Helper.names, Subst.lookup]
            · apply helper_capture .receipts selected state [v "rest"]
                [encoded (encodeList (encodeOption id) rest)] _ rfl
              · simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]
              · exact ih
            · have template : PureData.Template runtime (a "LCons" [v "receipt", v "tail"]) := by
                apply template_constructor _ _ (by simp [dataHeads])
                intro child member
                rcases List.mem_cons.mp member with rfl | member
                · exact .captured _
                · rcases List.mem_singleton.mp member with rfl
                  exact .captured _
              simpa [continued, tail, selected, caller, bindings, Helper.names,
                encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                applySubst, applySubst.applySubstList, Subst.lookup] using
                PureData.template_return runtime continued state (a "LCons" [v "receipt", v "tail"]) template

theorem receipts_captured_returns (caller : Subst) (state : State)
    (readouts : List (Option Term)) (argument : Atom)
    (captured : applySubst caller argument = encoded (encodeList (encodeOption id) readouts)) :
    PureReturns runtime caller state (a "gslt:program:receipts" [argument]) state
      (encoded (encodeList id (readouts.filterMap id))) :=
  helper_capture .receipts caller state [argument] _ _ rfl (by simp [captured])
    (receipts_returns state readouts)

private def oldHead (head : String) : Bool :=
  head != "eval" &&
    !((GeneralRuleReadoutCache.source.program.equations.map (·.head)) ++
      (GeneralTypedSiteExecution.source.program.equations.map (·.head)) ++
      (source.program.equations.map (·.head))).contains head

private theorem old_closed : ProgramClosed oldHead RuleExecutionProgram.scopedProgram := by
  constructor
  · decide +kernel
  · intro equation member supported
    have checked : RuleExecutionProgram.scopedProgram.equations.all (fun equation =>
        !oldHead equation.head || codeWithin oldHead equation.body) = true := by decide +kernel
    have row := List.all_eq_true.mp checked equation member
    simpa only [supported, Bool.not_true, Bool.false_or] using row

private theorem old_agreement :
    ProgramAgreementOn oldHead RuleExecutionProgram.scopedProgram runtime := by
  apply programAgreementOn_of_retained_rows
  · rfl
  · rfl

private theorem old_returns {caller : Subst} {before after : State} {code answer : Atom}
    (supported : codeWithin oldHead code = true)
    (returned : PureReturns RuleExecutionProgram.scopedProgram caller before code after answer) :
    PureReturns runtime caller before code after answer :=
  path_of_closed_agreement old_closed old_agreement ⟨supported, rfl⟩ returned

theorem cache_agreement :
    ProgramAgreementOn GeneralRuleReadoutCache.executionHeads GeneralRuleReadoutCache.runtime runtime := by
  apply appended_program_agreement
  · intro equation member
    have checked : (GeneralTypedSiteExecution.source.program.append source.program).equations.all (fun equation =>
        !GeneralRuleReadoutCache.executionHeads equation.head) = true := by decide +kernel
    have row := List.all_eq_true.mp checked equation member
    cases supported : GeneralRuleReadoutCache.executionHeads equation.head with
    | false => rfl
    | true => simp [supported] at row
  · intro name types member
    have checked : (GeneralTypedSiteExecution.source.program.append source.program).declarations.all (fun declaration => match declaration with
        | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] =>
            !GeneralRuleReadoutCache.executionHeads head
        | _ => true) = true := by decide +kernel
    have row := List.all_eq_true.mp checked
      (.expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)]) member
    cases supported : GeneralRuleReadoutCache.executionHeads name with
    | false => rfl
    | true => simp [supported] at row

private theorem start_returns (state : State) (request : GeneralRuleJobExecution.Request) :
    PureReturns runtime [] state
      (a "gslt:premise:machine-start" [encoded (PremiseOperationsExecution.GeneralExecution.goalTerm request.goal)]) state
      (encoded (encodeOption PremiseOperationsExecution.GeneralExecution.stateTerm
        (some (Execution.start request.environment request.goal)))) := by
  have agreement : ProgramAgreementOn PremiseMachineRunExecution.executionHeads
      PremiseMachineRunExecution.referenceRuntime runtime :=
    programAgreementOn_of_retained_rows _ _ _ (by rfl) (by rfl)
  exact PremiseMachineRunExecution.start_returns runtime agreement state request.environment request.goal

private theorem start_captured_returns (caller : Subst) (state : State)
    (request : GeneralRuleJobExecution.Request) (argument : Atom)
    (captured : applySubst caller argument = encoded (PremiseOperationsExecution.GeneralExecution.goalTerm request.goal)) :
    PureReturns runtime caller state (a "gslt:premise:machine-start" [argument]) state
      (encoded (encodeOption PremiseOperationsExecution.GeneralExecution.stateTerm
        (some (Execution.start request.environment request.goal)))) := by
  apply PureData.raw_capture_returns runtime [] caller state state "gslt:premise:machine-start"
    [encoded (PremiseOperationsExecution.GeneralExecution.goalTerm request.goal)] [argument] _
  · decide +kernel
  · intro index bounded
    have : index = 0 := by simpa using bounded
    subst index
    decide +kernel
  · decide
  · simpa using captured.symm
  · exact start_returns state request

/-- The driver continues the original premise machine from any retained state
whose terms stay within the request footprint, not only from the start. -/
theorem machine_run_captured_returns (caller : Subst) (state : State)
    (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = []) (fuel : Nat)
    (machine : Execution.State request.environment request.goal)
    (covered : Execution.stateFreeWithin (GeneralRuleJobObservation.requestFootprint request)
      request.environment request.goal machine)
    (environmentName fuelName stateName : String)
    (inputs : [v environmentName, v fuelName, v stateName].map (applySubst caller) =
      [encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm request.environment
        (request.environment.free.entriesOn (GeneralRuleJobObservation.requestFootprint request))),
       encoded (.natural fuel), encoded (PremiseOperationsExecution.GeneralExecution.stateTerm machine)]) :
    PureReturns runtime caller state (a "gslt:premise:machine-run" [v environmentName, v fuelName, v stateName])
      state (encoded (encodeOption PremiseOperationsExecution.GeneralExecution.stateTerm
        (some (Execution.run request.environment request.goal fuel machine)))) := by
  apply old_returns (by rfl)
  apply (PremiseOperationsExecution.GeneralExecution.CompletedAssembly.captured_machine_run_iff caller state state
    environmentName fuelName stateName _).mp
  exact PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.Machine.run_state_captured_within_returns
    caller state request.environment finiteProvider request.goal fuel machine (GeneralRuleJobObservation.requestFootprint request)
    (fun _ member => List.mem_append_right _ member) covered _ inputs

private def readoutPayloads (invocation : Invocation) : List (Option Term) :=
  (innerState invocation).answers.map fun result =>
    (GeneralRuleJobExecution.rootProjection invocation.1.val invocation.1.property result).map
      (fun answer => ScopedRuleJobReadoutExecution.receiptTerm answer.val)

private theorem readout_payloads_codec (invocation : Invocation) :
    encodeList (encodeOption id) (readoutPayloads invocation) =
      encodeList (GeneralRuleJobObservation.rootReadoutTerm invocation.1.val invocation.1.property)
        (innerState invocation).answers := by
  rw [readoutPayloads, encodeList_map]
  apply congrArg (fun encode => encodeList encode (innerState invocation).answers)
  funext result
  dsimp only [Function.comp_def]
  unfold GeneralRuleJobObservation.rootReadoutTerm
  cases GeneralRuleJobExecution.rootProjection invocation.1.val invocation.1.property result <;> rfl

private theorem successful_payloads_codec (invocation : Invocation) :
    encodeList id ((readoutPayloads invocation).filterMap id) =
      encodeList ScopedRuleJobReadoutExecution.receiptTerm (receipts invocation) := by
  have filtered : (readoutPayloads invocation).filterMap id =
      (receipts invocation).map ScopedRuleJobReadoutExecution.receiptTerm := by
    simp [readoutPayloads, receipts, List.filterMap_map, List.map_filterMap]
  rw [filtered, encodeList_map]
  rfl

private def jobOutput : Atom :=
  a "ProgramJobObservation" [v "request",
    a "PremiseState" [v "agenda", v "answers", v "unresolved", v "work"], v "receipts"]

private def jobReadouts : Atom :=
  a "let" [v "readouts", a "gslt:rule:job-readouts" [v "request", v "answers"],
    a "let" [v "receipts", a "gslt:program:receipts" [v "readouts"], jobOutput]]

private def jobRun : Atom :=
  a "let" [a "Some" [a "PremiseState" [v "agenda", v "answers", v "unresolved", v "work"]],
    a "gslt:premise:machine-run" [v "environment", v "budget", v "initial"], jobReadouts]

private def jobStart : Atom :=
  a "let" [a "Some" [v "initial"],
    a "gslt:premise:machine-start"
      [a "RootGoal" [v "focusBound", v "focusType", v "focus", v "ordinal"]], jobRun]

private def requestPattern : Atom :=
  a "RuleJobRequestProjection" [v "environment", v "permissions", v "bound", v "expected", v "source",
    a "RuleJob" [v "ordinal", v "declaration",
      a "RuleJobSite" [v "address", v "context", v "focus", v "focusBound", v "focusType", v "frames"]]]

private def jobCases : SpaceSemantics.Cases := [(requestPattern, jobStart)]

private theorem job_shape : (equation .job).body =
    a "case" [v "request", .expression (jobCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private def requestBindings (request : GeneralRuleJobExecution.Request) : Subst :=
  [("frames", encoded (encodeList ScopedRuleJobReadoutExecution.typingFrameTerm request.job.site.typingFrames)),
   ("focusType", encoded (InferenceCettaWire.AuthoredRule.typeTerm request.job.site.focusType)),
   ("focusBound", encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm request.job.site.focusBound)),
   ("focus", encoded (InferenceCettaWire.encodePattern request.job.site.focus)),
   ("context", encoded (InferenceCettaWire.ContextObservation.contextTerm request.job.site.context)),
   ("address", encoded (encodeList Term.natural request.job.site.address)),
   ("declaration", encoded (ScopedRuleJobReadoutExecution.rulePlanTerm request.job.declaration)),
   ("ordinal", encoded (.natural request.job.ordinal)),
   ("source", encoded (InferenceCettaWire.encodePattern request.source)),
   ("expected", encoded (InferenceCettaWire.AuthoredRule.typeTerm request.expected)),
   ("bound", encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm request.bound)),
   ("permissions", encoded (InferenceCettaWire.ContextObservation.permissionsTerm request.plan.permissions.sites)),
   ("environment", encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm request.environment
     (request.environment.free.entriesOn (GeneralRuleJobObservation.requestFootprint request))))]

private theorem job_output_template : PureData.Template runtime jobOutput := by
  apply template_constructor _ _ (by simp [dataHeads])
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .captured _
  · apply template_constructor _ _ (by simp [dataHeads])
    intro child member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> exact .captured _
  · exact .captured _

/-- One authored call performs the actual inner run and readout, retaining its
entire finite state even when the supplied work budget leaves pending tasks. -/
theorem job_returns (state : State) (invocation : Invocation)
    (finiteProvider : invocation.1.val.environment.provider.dynamicRelations = []) :
    PureReturns runtime [] state
      (a "gslt:program:job" [encoded (requestTerm invocation.1.val), encoded (.natural invocation.2)]) state
      (encoded (observationTerm invocation)) := by
  let request := invocation.1.val
  let caller := bindings .job [encoded (requestTerm request), encoded (.natural invocation.2)]
  let selected := requestBindings request ++ caller
  let initial := PremiseOperationsExecution.GeneralExecution.stateTerm (Execution.start request.environment request.goal)
  let begun := ("initial", encoded initial) :: selected
  let machine := innerState invocation
  let observed :=
    [("work", encoded (.natural machine.work)),
     ("unresolved", encoded (encodeList PremiseOperationsExecution.GeneralExecution.obligationTerm machine.unresolved)),
     ("answers", encoded (encodeList PremiseOperationsExecution.GeneralExecution.resultTerm machine.answers)),
     ("agenda", encoded (encodeList PremiseOperationsExecution.GeneralExecution.taskTerm machine.agenda))] ++ begun
  let readouts := encoded (encodeList (GeneralRuleJobObservation.rootReadoutTerm request invocation.1.property) machine.answers)
  let read := ("readouts", readouts) :: observed
  let receiptValues := encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm (receipts invocation))
  let finished := ("receipts", receiptValues) :: read
  apply helper_call .job [] state _
    [encoded (requestTerm invocation.1.val), encoded (.natural invocation.2)] _ rfl (by
    simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
  rw [job_shape]
  apply branch_returns caller selected state _ (encoded (requestTerm request)) jobCases jobStart _
  · exact variable_returns runtime caller state "request"
  · simp [selected, caller, requestBindings, bindings, Helper.names, jobCases, requestPattern,
      requestTerm, ScopedRuleJobReadoutExecution.requestProjectionTerm,
      ScopedRuleJobReadoutExecution.jobTerm, ScopedRuleJobReadoutExecution.siteTerm,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  · unfold jobStart
    apply let_returns runtime selected begun state state state
      (a "Some" [v "initial"]) _ jobRun (encoded (encodeOption id (some initial))) _
    · apply start_captured_returns selected state request
      simp [selected, caller, requestBindings, bindings, Helper.names,
        GeneralRuleJobExecution.Request.goal, PremiseOperationsExecution.GeneralExecution.goalTerm,
        applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany]
    · simp [begun, initial, SpaceSemantics.matchBinding, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, selected,
        requestBindings, caller, bindings, Helper.names, encodeOption, encoded,
        CettaWireAtom.encode, CettaWireAtom.encodeMany]
    · unfold jobRun
      apply let_returns runtime begun observed state state state _ _ jobReadouts
        (encoded (encodeOption PremiseOperationsExecution.GeneralExecution.stateTerm (some machine))) _
      · apply old_returns (by rfl)
        apply GeneralRuleJobObservation.job_run_captured_returns begun state request finiteProvider invocation.1.property
          invocation.2 "environment" "budget" "initial"
        simp [begun, selected, caller, requestBindings, bindings, Helper.names,
          initial, applySubst, Subst.lookup]
      · simp [observed, machine, begun, initial, selected, requestBindings, caller, bindings, Helper.names,
          SpaceSemantics.matchBinding, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, encodeOption, encoded, PremiseOperationsExecution.GeneralExecution.stateTerm,
          PremiseSchedulerExecution.schedulerStateTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany]
      · unfold jobReadouts
        apply named_let_returns observed state "readouts" _ readouts
        · simp [observed, begun, selected, caller, requestBindings, bindings, Helper.names, Subst.lookup]
        · apply GeneralRuleReadoutCache.job_readouts_captured_variables_returns_in_extension runtime cache_agreement
            observed state request invocation.1.property invocation.2 machine.answers (fun _ member => member)
            "request" "answers"
          simp [observed, begun, selected, caller, requestBindings, bindings, Helper.names,
            applySubst, Subst.lookup, GeneralRuleReadoutCache.requestTerm, GeneralRuleReadoutCache.resultsTerm, requestTerm]
        · apply named_let_returns read state "receipts" _ receiptValues
          · simp [read, observed, begun, selected, caller, requestBindings, bindings, Helper.names, Subst.lookup]
          · dsimp only [receiptValues]
            rw [← successful_payloads_codec invocation]
            apply receipts_captured_returns read state (readoutPayloads invocation)
            rw [readout_payloads_codec]
            simp [read, readouts, request, machine, applySubst, Subst.lookup]
          · simpa [jobOutput, observationTerm, finished, receiptValues, read, readouts, observed, begun,
              selected, caller, requestBindings, bindings, Helper.names, request,
              PremiseOperationsExecution.GeneralExecution.stateTerm, PremiseSchedulerExecution.schedulerStateTerm,
              CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup]
              using PureData.template_return runtime finished state jobOutput job_output_template

theorem job_captured_returns (caller : Subst) (state : State) (invocation : Invocation)
    (finiteProvider : invocation.1.val.environment.provider.dynamicRelations = [])
    (request budget : Atom)
    (captured : [request, budget].map (applySubst caller) =
      [encoded (requestTerm invocation.1.val), encoded (.natural invocation.2)]) :
    PureReturns runtime caller state (a "gslt:program:job" [request, budget]) state
      (encoded (observationTerm invocation)) :=
  helper_capture .job caller state [request, budget] _ _ rfl captured (job_returns state invocation finiteProvider)

/-- Receipt lists are joined in order, keeping every occurrence. -/
theorem append_returns (caller : Subst) (state : State)
    (left right : List GeneralRuleJobs.Receipt) (leftName rightName : String)
    (captured : [v leftName, v rightName].map (applySubst caller) =
      [encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm left),
       encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm right)]) :
    PureReturns runtime caller state (a "gslt:automata:append" [v leftName, v rightName]) state
      (encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm (left ++ right))) := by
  apply old_returns (by rfl)
  apply path_of_closed_agreement
    PremiseOperationsExecution.GeneralExecution.CompletedAssembly.retained_machine_closed
    PremiseOperationsExecution.GeneralExecution.CompletedAssembly.retained_machine_agreement ⟨by rfl, rfl⟩
  exact PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.PremiseTransitions.Lower.append_encoded_returns
    ScopedRuleJobReadoutExecution.receiptTerm caller state left right (v leftName) (v rightName) captured

private def runOutput : Atom :=
  a "ProgramObservation"
    [a "LCons" [a "ProgramJobObservation" [v "jobRequest", v "state", v "receipts"], v "observations"], v "all"]

private def runAppend : Atom :=
  a "let" [v "all", a "gslt:automata:append" [v "receipts", v "later"], runOutput]

private def runTail : Atom :=
  a "let" [a "ProgramObservation" [v "observations", v "later"],
    a "gslt:program:run" [v "rest"], runAppend]

private def runCons : Atom :=
  a "let" [a "ProgramJobObservation" [v "jobRequest", v "state", v "receipts"],
    a "gslt:program:job" [v "request", v "budget"], runTail]

private def runCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "ProgramObservation" [.symbol "LNil", .symbol "LNil"]),
   (a "LCons" [a "ProgramJob" [v "request", v "budget"], v "rest"], runCons)]

private theorem run_shape : (equation .run).body =
    a "case" [v "jobs", .expression (runCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem run_output_template : PureData.Template runtime runOutput := by
  apply template_constructor _ _ (by simp [dataHeads])
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · apply template_constructor _ _ (by simp [dataHeads])
    intro child member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · apply template_constructor _ _ (by simp [dataHeads])
      intro child member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> exact .captured _
    · exact .captured _
  · exact .captured _

def programQuery (invocations : List Invocation) : Atom :=
  a "gslt:program:run" [encoded (encodeList invocationTerm invocations)]

/-- The actual program driver executes every supplied job and concatenates
its original successful readouts without changing occurrence order. -/
theorem program_returns (state : State) (invocations : List Invocation)
    (finiteProvider : ∀ invocation ∈ invocations, invocation.1.val.environment.provider.dynamicRelations = []) :
    PureReturns runtime [] state (programQuery invocations) state
      (encoded (programObservationTerm invocations)) := by
  revert finiteProvider
  induction invocations with
  | nil =>
      intro finiteProvider
      let caller := bindings .run [encoded (.symbol "LNil")]
      apply helper_call .run [] state _ _ _ rfl (by rfl)
      rw [run_shape]
      apply branch_returns caller caller state _ (.symbol "LNil") runCases
        (a "ProgramObservation" [.symbol "LNil", .symbol "LNil"]) _
      · exact variable_returns runtime caller state "jobs"
      · simp [caller, bindings, Helper.names, runCases,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · have template : PureData.Template runtime (a "ProgramObservation" [.symbol "LNil", .symbol "LNil"]) := by
          apply template_constructor _ _ (by simp [dataHeads])
          intro child member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl <;> exact .symbol _
        exact PureData.template_return runtime caller state _ template
  | cons invocation rest ih =>
      intro finiteProvider
      let value := encoded (encodeList invocationTerm (invocation :: rest))
      let caller := bindings .run [value]
      let selected :=
        [("rest", encoded (encodeList invocationTerm rest)),
         ("budget", encoded (.natural invocation.2)),
         ("request", encoded (requestTerm invocation.1.val))] ++ caller
      let first :=
        [("receipts", encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm (receipts invocation))),
         ("state", encoded (PremiseOperationsExecution.GeneralExecution.stateTerm (innerState invocation))),
         ("jobRequest", encoded (requestTerm invocation.1.val))] ++ selected
      let later :=
        [("later", encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm (rest.flatMap receipts))),
         ("observations", encoded (encodeList observationTerm rest))] ++ first
      let combined := encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm
        (receipts invocation ++ rest.flatMap receipts))
      let finished := ("all", combined) :: later
      apply helper_call .run [] state _ [value] _ rfl (by
        simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]; rfl)
      rw [run_shape]
      apply branch_returns caller selected state _ value runCases runCons _
      · exact variable_returns runtime caller state "jobs"
      · simp [selected, caller, value, invocationTerm, bindings, Helper.names, runCases,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
      · unfold runCons
        apply let_returns runtime selected first state state state _ _ runTail
          (encoded (observationTerm invocation)) _
        · apply job_captured_returns selected state invocation (finiteProvider invocation List.mem_cons_self)
          simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]
        · simp [first, selected, caller, bindings, Helper.names, observationTerm,
            SpaceSemantics.matchBinding, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
            matchAtom, Subst.lookup, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
        · unfold runTail
          apply let_returns runtime first later state state state _ _ runAppend
            (encoded (programObservationTerm rest)) _
          · apply helper_capture .run first state [v "rest"]
              [encoded (encodeList invocationTerm rest)] _ rfl
            · simp [first, selected, caller, bindings, Helper.names, applySubst, Subst.lookup]
            · exact ih (fun item member => finiteProvider item (List.mem_cons_of_mem invocation member))
          · simp [later, first, selected, caller, bindings, Helper.names, programObservationTerm,
              SpaceSemantics.matchBinding, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, Subst.lookup, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
          · unfold runAppend
            apply named_let_returns later state "all" _ combined
            · simp [later, first, selected, caller, bindings, Helper.names, Subst.lookup]
            · apply append_returns later state (receipts invocation) (rest.flatMap receipts) "receipts" "later"
              simp [later, first, selected, caller, bindings, Helper.names, applySubst, Subst.lookup]
            · simpa [runOutput, programObservationTerm, observationTerm, finished, combined,
                later, first, selected, caller, bindings, Helper.names, encodeList,
                CettaWireAtom.encode, CettaWireAtom.encodeMany,
                applySubst, applySubst.applySubstList, Subst.lookup]
                using PureData.template_return runtime finished state runOutput run_output_template

theorem program_completed_iff (state after : State) (invocations : List Invocation)
    (finiteProvider : ∀ invocation ∈ invocations, invocation.1.val.environment.provider.dynamicRelations = [])
    (answers input output : List Atom) :
    (∃ evaluatorFuel, Eval.run runtime evaluatorFuel
      {state, control := .evaluate [] (programQuery invocations)} =
        .complete after answers input output) ↔
      after = state ∧ answers = [encoded (programObservationTerm invocations)] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff runtime [] state state _ _ (program_returns state invocations finiteProvider)
    after answers input output

/-- Original licensed job enumeration, retaining the supplied per-job budget. -/
def invocations (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (budget : GeneralRuleJobs.Job → Nat) : List Invocation :=
  (GeneralRuleJobs.jobs plan bound expected source).attach.map fun item =>
    (⟨⟨plan, bound, expected, source, item.val⟩,
      (GeneralRuleJobs.jobs_spec plan bound expected source item.val).mp item.property⟩, budget item.val)

theorem invocations_finiteProvider (plan : GeneralExecutionAdmission.Plan)
    (finiteProvider : plan.snapshot.provider.dynamicRelations = [])
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (budget : GeneralRuleJobs.Job → Nat) :
    ∀ invocation ∈ invocations plan bound expected source budget,
      invocation.1.val.environment.provider.dynamicRelations = [] := by
  intro invocation present
  obtain ⟨item, _, same⟩ := List.mem_map.mp present
  cases same
  exact finiteProvider

theorem receipts_eq_finishState (invocation : Invocation)
    (saturated : (Execution.treeStart invocation.1.val.environment invocation.1.val.goal).cost ≤ invocation.2) :
    receipts invocation =
      (GeneralRuleJobExecution.finishState invocation.1.val invocation.1.property).answers.map Subtype.val := by
  unfold receipts innerState
  rw [Execution.run_eq_finish_of_cost_le _ _ _ saturated, Execution.finish_answers,
    GeneralRuleJobExecution.finishState_root_readouts]

/-- Draining every original job yields the source's complete ordered receipt
list. This claim is not made for a finite prefix with pending work. -/
theorem saturated_receipts_eq_completed (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (budget : GeneralRuleJobs.Job → Nat)
    (saturated : ∀ job ∈ GeneralRuleJobs.jobs plan bound expected source,
      (Execution.treeStart (GeneralPlanEnvironment.environment plan)
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget job) :
    (invocations plan bound expected source budget).flatMap receipts =
      GeneralRuleJobExecution.completedReceipts plan bound expected source := by
  unfold invocations GeneralRuleJobExecution.completedReceipts
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro item _
  exact receipts_eq_finishState _ (saturated item.val item.property)

/-- The full observed output is fixed by actual PeTTa execution. For budgets
that drain all selected jobs, its flattened receipts are exactly the original
all-job source readout, with every provenance field retained. -/
theorem saturated_program_completed_iff (state after : State)
    (plan : GeneralExecutionAdmission.Plan)
    (finiteProvider : plan.snapshot.provider.dynamicRelations = []) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (budget : GeneralRuleJobs.Job → Nat)
    (saturated : ∀ job ∈ GeneralRuleJobs.jobs plan bound expected source,
      (Execution.treeStart (GeneralPlanEnvironment.environment plan)
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget job)
    (answers input output : List Atom) :
    (∃ evaluatorFuel, Eval.run runtime evaluatorFuel
      {state, control := .evaluate [] (programQuery (invocations plan bound expected source budget))} =
        .complete after answers input output) ↔
      after = state ∧ answers = [encoded (.application "ProgramObservation"
        [encodeList observationTerm (invocations plan bound expected source budget),
         encodeList ScopedRuleJobReadoutExecution.receiptTerm
           (GeneralRuleJobExecution.completedReceipts plan bound expected source)])] ∧
        input = [] ∧ output = [] := by
  rw [program_completed_iff state after _ (invocations_finiteProvider plan finiteProvider bound expected source budget)]
  simp only [programObservationTerm, saturated_receipts_eq_completed plan bound expected source budget saturated]

/-- Packaging retains the original environment, permissions, source and job.
The executable does not replace jobs with a host-prepared request stream. -/
def packagedJob (environment permissions bound expected source budget job : Term) : Term :=
  .application "ProgramJob"
    [.application "RuleJobRequestProjection" [environment, permissions, bound, expected, source, job], budget]

private def requestsOutput : Atom :=
  a "LCons"
    [a "ProgramJob"
      [a "RuleJobRequestProjection"
        [v "environment", v "permissions", v "bound", v "expected", v "source", v "job"], v "budget"],
     v "tail"]

private def requestsCons : Atom :=
  a "let" [v "tail", a "gslt:program:requests"
    [v "environment", v "permissions", v "bound", v "expected", v "source", v "budget", v "rest"],
    requestsOutput]

private def requestsCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "job", v "rest"], requestsCons)]

private theorem requests_shape : (equation .requests).body =
    a "case" [v "jobs", .expression (requestsCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem requests_output_template : PureData.Template runtime requestsOutput := by
  apply template_constructor _ _ (by simp [dataHeads])
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · apply template_constructor _ _ (by simp [dataHeads])
    intro child member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · apply template_constructor _ _ (by simp [dataHeads])
      intro child member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> exact .captured _
    · exact .captured _
  · exact .captured _

theorem requests_returns (state : State) (environment permissions bound expected source budget : Term)
    (jobs : List Term) :
    PureReturns runtime [] state
      (a "gslt:program:requests"
        ([environment, permissions, bound, expected, source, budget, encodeList id jobs].map encoded)) state
      (encoded (encodeList (packagedJob environment permissions bound expected source budget) jobs)) := by
  induction jobs with
  | nil =>
      let caller := bindings .requests
        ([environment, permissions, bound, expected, source, budget, .symbol "LNil"].map encoded)
      apply helper_call .requests [] state _ _ _ rfl (by
        simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]; rfl)
      rw [requests_shape]
      apply branch_returns caller caller state _ (.symbol "LNil") requestsCases (.symbol "LNil") _
      · exact variable_returns runtime caller state "jobs"
      · simp [caller, bindings, Helper.names, requestsCases,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns runtime caller state "LNil"
  | cons job rest ih =>
      let caller := bindings .requests
        ([environment, permissions, bound, expected, source, budget, encodeList id (job :: rest)].map encoded)
      let selected := [("rest", encoded (encodeList id rest)), ("job", encoded job)] ++ caller
      let tail := encoded (encodeList (packagedJob environment permissions bound expected source budget) rest)
      let finished := ("tail", tail) :: selected
      apply helper_call .requests [] state _ _ _ rfl (by
        simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]; rfl)
      rw [requests_shape]
      apply branch_returns caller selected state _ (encoded (encodeList id (job :: rest)))
        requestsCases requestsCons _
      · exact variable_returns runtime caller state "jobs"
      · simp [selected, caller, bindings, Helper.names, requestsCases,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, encoded]
      · unfold requestsCons
        apply named_let_returns selected state "tail" _ tail
        · simp [selected, caller, bindings, Helper.names, Subst.lookup]
        · apply helper_capture .requests selected state _
            ([environment, permissions, bound, expected, source, budget, encodeList id rest].map encoded) _ rfl
          · simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]
          · exact ih
        · simpa [requestsOutput, packagedJob, finished, tail, selected, caller, bindings, Helper.names,
            encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            applySubst, applySubst.applySubstList, Subst.lookup] using
              PureData.template_return runtime finished state requestsOutput requests_output_template

/-- Every generated job shares the same finite free-context footprint. -/
def environmentTerm (plan : GeneralExecutionAdmission.Plan) (source : Pattern) : Term :=
  let environment := GeneralPlanEnvironment.environment plan
  PremiseOperationsExecution.GeneralExecution.environmentTerm environment
    (environment.free.entriesOn (source.freeFvarNames ++ providerFreeNames environment.provider))

theorem packaged_jobs_eq_invocations (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (budget : Nat) :
    encodeList
      (packagedJob (environmentTerm plan source)
        (InferenceCettaWire.ContextObservation.permissionsTerm plan.permissions.sites)
        (encodeList InferenceCettaWire.AuthoredRule.typeTerm bound)
        (InferenceCettaWire.AuthoredRule.typeTerm expected)
        (InferenceCettaWire.encodePattern source) (.natural budget) ∘ ScopedRuleJobReadoutExecution.jobTerm)
      (GeneralRuleJobs.jobs plan bound expected source) =
    encodeList invocationTerm (invocations plan bound expected source (fun _ => budget)) := by
  let package := packagedJob (environmentTerm plan source)
    (InferenceCettaWire.ContextObservation.permissionsTerm plan.permissions.sites)
    (encodeList InferenceCettaWire.AuthoredRule.typeTerm bound)
    (InferenceCettaWire.AuthoredRule.typeTerm expected) (InferenceCettaWire.encodePattern source)
    (.natural budget) ∘ ScopedRuleJobReadoutExecution.jobTerm
  have same : (invocations plan bound expected source (fun _ => budget)).map invocationTerm =
      (GeneralRuleJobs.jobs plan bound expected source).map package := by
    unfold invocations
    rw [List.map_map]
    change (GeneralRuleJobs.jobs plan bound expected source).attach.map (fun item => package item.val) = _
    exact List.attach_map_val
  have encodedSame := congrArg (encodeList id) same
  simpa only [encodeList_map, Function.id_comp] using encodedSame.symm

/-- Actual site enumeration sees the original finite environment footprint. -/
def enumerationQuery (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) : Atom :=
  let environment := GeneralPlanEnvironment.environment plan
  a "gslt:sites:jobs"
    ([PremiseOperationsExecution.DeclarationTyping.declarationsTerm environment.language.terms,
      PremiseOperationsExecution.DeclarationTyping.freeContextTerm
        (environment.free.entriesOn (source.freeFvarNames ++ providerFreeNames environment.provider)),
      InferenceCettaWire.ContextObservation.permissionsTerm plan.permissions.sites,
      encodeList InferenceCettaWire.AuthoredRule.typeTerm bound,
      InferenceCettaWire.AuthoredRule.typeTerm expected, InferenceCettaWire.encodePattern source,
      encodeList ScopedRuleJobReadoutExecution.rulePlanTerm plan.rules].map encoded)

def executeArguments (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (budget : Nat) : List Term :=
  [environmentTerm plan source,
   InferenceCettaWire.ContextObservation.permissionsTerm plan.permissions.sites,
   encodeList InferenceCettaWire.AuthoredRule.typeTerm bound,
   InferenceCettaWire.AuthoredRule.typeTerm expected, InferenceCettaWire.encodePattern source,
   encodeList ScopedRuleJobReadoutExecution.rulePlanTerm plan.rules, .natural budget]

/-- The native entry consumes presentation data and a source term. It finds
and packages the original ordered jobs inside MeTTa before running them. -/
def executeQuery (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (budget : Nat) : Atom :=
  a "gslt:program:execute" ((executeArguments plan bound expected source budget).map encoded)

private def executeRequests : Atom :=
  a "let" [v "requests", a "gslt:program:requests"
    [v "environment", v "permissions", v "bound", v "expected", v "source", v "budget", v "jobs"],
    a "gslt:program:run" [v "requests"]]

private def executeBody : Atom :=
  a "let" [v "jobs", a "gslt:sites:jobs"
    [v "declarations", v "free", v "permissions", v "bound", v "expected", v "source", v "rules"],
    executeRequests]

private def executeCases : SpaceSemantics.Cases :=
  [(a "PremiseEnvironment"
    [v "declarations", v "rewrites", v "specifications", v "provider", v "reflection", v "free"], executeBody)]

private theorem execute_shape : (equation .execute).body =
    a "case" [v "environment", .expression (executeCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem execute_returns_of_enumeration (state : State) (plan : GeneralExecutionAdmission.Plan)
    (finiteProvider : plan.snapshot.provider.dynamicRelations = [])
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) (budget : Nat)
    (enumerated : PureReturns runtime [] state (enumerationQuery plan bound expected source) state
      (encoded (encodeList ScopedRuleJobReadoutExecution.jobTerm
        (GeneralRuleJobs.jobs plan bound expected source)))) :
    PureReturns runtime [] state (executeQuery plan bound expected source budget) state
      (encoded (programObservationTerm (invocations plan bound expected source (fun _ => budget)))) := by
  let environment := GeneralPlanEnvironment.environment plan
  let free := environment.free.entriesOn (source.freeFvarNames ++ providerFreeNames environment.provider)
  let caller := bindings .execute ((executeArguments plan bound expected source budget).map encoded)
  let selected :=
    [("free", encoded (PremiseOperationsExecution.DeclarationTyping.freeContextTerm free)),
     ("reflection", encoded (PremiseOperationsExecution.GeneralExecution.reflectionTerm environment.reflection)),
     ("provider", encoded (PremiseOperationsExecution.GeneralExecution.providerTerm environment.provider)),
     ("specifications", encoded (encodeList PremiseOperationsExecution.GeneralExecution.specificationTerm environment.specifications)),
     ("rewrites", encoded (encodeList InferenceCettaWire.AuthoredRule.rewriteTerm environment.language.rewrites)),
     ("declarations", encoded (PremiseOperationsExecution.DeclarationTyping.declarationsTerm environment.language.terms))] ++ caller
  let jobsValue := encoded (encodeList ScopedRuleJobReadoutExecution.jobTerm
    (GeneralRuleJobs.jobs plan bound expected source))
  let generated := ("jobs", jobsValue) :: selected
  let requestsValue := encoded (encodeList invocationTerm (invocations plan bound expected source (fun _ => budget)))
  let ready := ("requests", requestsValue) :: generated
  apply helper_call .execute [] state _ _ _ rfl (by
    simp only [executeArguments, List.map_cons, List.map_nil,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]; rfl)
  rw [execute_shape]
  apply branch_returns caller selected state _ (encoded (environmentTerm plan source)) executeCases executeBody _
  · exact variable_returns runtime caller state "environment"
  · simp [selected, caller, environment, free, executeArguments, environmentTerm,
      PremiseOperationsExecution.GeneralExecution.environmentTerm,
      PremiseOperationsExecution.DeclarationTyping.declarationsTerm,
      bindings, Helper.names, executeCases,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  · unfold executeBody
    apply named_let_returns selected state "jobs" _ jobsValue
    · simp [selected, caller, bindings, Helper.names, executeArguments, Subst.lookup]
    · apply PureData.raw_capture_returns runtime [] selected state state "gslt:sites:jobs"
        (([PremiseOperationsExecution.DeclarationTyping.declarationsTerm environment.language.terms,
          PremiseOperationsExecution.DeclarationTyping.freeContextTerm free,
          InferenceCettaWire.ContextObservation.permissionsTerm plan.permissions.sites,
          encodeList InferenceCettaWire.AuthoredRule.typeTerm bound,
          InferenceCettaWire.AuthoredRule.typeTerm expected, InferenceCettaWire.encodePattern source,
          encodeList ScopedRuleJobReadoutExecution.rulePlanTerm plan.rules]).map encoded)
        _ jobsValue
      · decide +kernel
      · intro index bounded
        have checked : (List.range 7).all (fun index => argumentIsRaw runtime "gslt:sites:jobs" index) = true := by
          decide +kernel
        exact List.all_eq_true.mp checked index (List.mem_range.mpr bounded)
      · decide
      · simp [selected, caller, executeArguments, bindings, Helper.names, applySubst, Subst.lookup]
      · exact enumerated
    · unfold executeRequests
      apply named_let_returns generated state "requests" _ requestsValue
      · simp [generated, selected, caller, bindings, Helper.names, executeArguments, Subst.lookup]
      · apply helper_capture .requests generated state _
          ([environmentTerm plan source,
            InferenceCettaWire.ContextObservation.permissionsTerm plan.permissions.sites,
            encodeList InferenceCettaWire.AuthoredRule.typeTerm bound,
            InferenceCettaWire.AuthoredRule.typeTerm expected, InferenceCettaWire.encodePattern source,
            .natural budget,
            encodeList ScopedRuleJobReadoutExecution.jobTerm (GeneralRuleJobs.jobs plan bound expected source)].map encoded)
          _ rfl
        · simp [generated, jobsValue, selected, caller, executeArguments, bindings, Helper.names, applySubst, Subst.lookup]
        · have result := requests_returns state (environmentTerm plan source)
            (InferenceCettaWire.ContextObservation.permissionsTerm plan.permissions.sites)
            (encodeList InferenceCettaWire.AuthoredRule.typeTerm bound)
            (InferenceCettaWire.AuthoredRule.typeTerm expected) (InferenceCettaWire.encodePattern source)
            (.natural budget) ((GeneralRuleJobs.jobs plan bound expected source).map ScopedRuleJobReadoutExecution.jobTerm)
          simpa only [encodeList_map, Function.id_comp, requestsValue, Helper.head,
            packaged_jobs_eq_invocations plan bound expected source budget] using result
      · apply helper_capture .run ready state [v "requests"] [requestsValue] _ rfl
        · simp [ready, generated, selected, caller, executeArguments, bindings, Helper.names, applySubst, Subst.lookup]
        · exact program_returns state _
            (invocations_finiteProvider plan finiteProvider bound expected source (fun _ => budget))

theorem enumeration_agreement :
    ProgramAgreementOn GeneralTypedSiteExecution.executionHeads GeneralTypedSiteExecution.program runtime := by
  apply programAgreementOn_of_retained_rows
  · rfl
  · rfl

theorem enumeration_returns (state : State) (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) :
    PureReturns runtime [] state (enumerationQuery plan bound expected source) state
      (encoded (encodeList ScopedRuleJobReadoutExecution.jobTerm (GeneralRuleJobs.jobs plan bound expected source))) := by
  let environment := GeneralPlanEnvironment.environment plan
  let footprint := source.freeFvarNames ++ providerFreeNames environment.provider
  let values :=
    [PremiseOperationsExecution.DeclarationTyping.declarationsTerm environment.language.terms,
     PremiseOperationsExecution.DeclarationTyping.freeContextTerm (environment.free.entriesOn footprint),
     InferenceCettaWire.ContextObservation.permissionsTerm plan.permissions.sites,
     encodeList InferenceCettaWire.AuthoredRule.typeTerm bound,
     InferenceCettaWire.AuthoredRule.typeTerm expected, InferenceCettaWire.encodePattern source,
     encodeList ScopedRuleJobReadoutExecution.rulePlanTerm plan.rules].map encoded
  let names := ["declarations", "free", "permissions", "bound", "expected", "source", "rules"]
  let caller := (names.zip values).reverse
  let arguments := names.map v
  have captured : arguments.map (applySubst caller) = values := by
    simp [arguments, caller, names, values, applySubst, Subst.lookup]
  have returned := GeneralTypedSiteExecution.jobs_plan_captured_returns_in_extension
    runtime enumeration_agreement caller state plan bound expected source footprint
    (fun _ member => List.mem_append_left _ member) arguments captured (by rfl)
  apply PureData.raw_capture_returns runtime caller [] state state "gslt:sites:jobs" arguments values _
  · decide +kernel
  · intro index bounded
    have checked : (List.range 7).all (fun index => argumentIsRaw runtime "gslt:sites:jobs" index) = true := by
      decide +kernel
    exact List.all_eq_true.mp checked index (List.mem_range.mpr bounded)
  · decide
  · have unchanged : applySubst [] = id := by
      funext value
      exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
    simpa only [unchanged, List.map_id] using captured
  · exact returned

/-- Native typed enumeration, request construction, premise execution and
cached readout compose into the actual presentation-entry call. -/
theorem execute_returns (state : State) (plan : GeneralExecutionAdmission.Plan)
    (finiteProvider : plan.snapshot.provider.dynamicRelations = [])
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) (budget : Nat) :
    PureReturns runtime [] state (executeQuery plan bound expected source budget) state
      (encoded (programObservationTerm (invocations plan bound expected source (fun _ => budget)))) :=
  execute_returns_of_enumeration state plan finiteProvider bound expected source budget
    (enumeration_returns state plan bound expected source)

theorem execute_completed_iff (state after : State) (plan : GeneralExecutionAdmission.Plan)
    (finiteProvider : plan.snapshot.provider.dynamicRelations = [])
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) (budget : Nat)
    (answers input output : List Atom) :
    (∃ evaluatorFuel, Eval.run runtime evaluatorFuel
      {state, control := .evaluate [] (executeQuery plan bound expected source budget)} =
        .complete after answers input output) ↔
      after = state ∧ answers = [encoded (programObservationTerm
        (invocations plan bound expected source (fun _ => budget)))] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff runtime [] state state _ _ (execute_returns state plan finiteProvider bound expected source budget)
    after answers input output

/-! ## Native observations of the assembled driver -/

/-- The target observer recognizes the returned wire shape. Its first field
retains inner states; its second field is an ordered list of receipt data.
No source validity judgment is consulted by this observation. -/
def readProgramReceipts (value : Atom) (receipts : List GeneralRuleJobs.Receipt) : Prop :=
  ∃ observations : Term, value = encoded (.application "ProgramObservation"
    [observations, encodeList ScopedRuleJobReadoutExecution.receiptTerm receipts])

theorem readProgramReceipts_functional (value : Atom) (first second : List GeneralRuleJobs.Receipt)
    (readFirst : readProgramReceipts value first) (readSecond : readProgramReceipts value second) :
    first = second := by
  obtain ⟨firstStates, firstEq⟩ := readFirst
  obtain ⟨secondStates, secondEq⟩ := readSecond
  have same := CettaWireAtom.encode_injective _ _ (firstEq.symm.trans secondEq)
  simp only [Term.application.injEq, List.cons.injEq, and_true, true_and] at same
  exact encodeList_injective ScopedRuleJobReadoutExecution.receiptTerm
    ScopedRuleJobReadoutExecution.receiptTerm_injective same.2

/-- A target occurrence is its physical output ordinal and complete receipt.
Fuel and proof witnesses establish observation without becoming identities. -/
def targetOutput := OperationalGSLT.orderedOutput runtime readProgramReceipts

def program_output_equiv (state : State) (jobs : List Invocation)
    (finiteProvider : ∀ invocation ∈ jobs, invocation.1.val.environment.provider.dynamicRelations = []) :
    {occurrence : Nat × GeneralRuleJobs.Receipt //
      (jobs.flatMap receipts)[occurrence.1]? = some occurrence.2} ≃
    targetOutput.Family {state, control := .evaluate [] (programQuery jobs)} :=
  OperationalGSLT.orderedOutputEquiv runtime readProgramReceipts readProgramReceipts_functional _
    (OperationalGSLT.pureSingleton_of_returns runtime [] state _ _ (program_returns state jobs finiteProvider))
    (jobs.flatMap receipts) ⟨encodeList observationTerm jobs, rfl⟩

/-- Source membership means a successor in the original occurrence GSLT.
Its retained evidence consists of all physical occurrences in the original
completed job readout. Equation-free coverage proves their supports coincide. -/
def sourceOutput (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (empty : plan.equations = [])
    (checked : checkStepStratification (GeneralPlanEnvironment.environment plan).language = true) :
    Mettapedia.OSLF.NativeTypes.Semantics.Families.NativeOutput
      (GeneralOccurrenceSemantics.gslt plan bound expected) where
  predicate := ⟨fun source => ∃ target, (GeneralOccurrenceSemantics.gslt plan bound expected).Step source target,
    by
      intro first second equivalent
      have same := GeneralOccurrenceFrontier.LocalEquationFree.equation_equivalence_is_equality
        (request := ⟨plan, bound, expected, first⟩) empty equivalent
      cases same
      rfl⟩
  Family source := {occurrence : Nat × GeneralRuleJobs.Receipt //
    (GeneralRuleJobExecution.completedReceipts plan bound expected source)[occurrence.1]? = some occurrence.2}
  supportExact source := by
    constructor
    · rintro ⟨⟨⟨index, receipt⟩, present⟩⟩
      exact ⟨receipt.target,
        (GeneralOccurrenceFrontier.LocalEquationFree.completedReceipts_targets_iff_step
          plan bound expected source receipt.target empty checked).mp
          (List.mem_map.mpr ⟨receipt, List.mem_iff_getElem?.mpr ⟨index, present⟩, rfl⟩)⟩
    · rintro ⟨target, step⟩
      obtain ⟨receipt, member, _⟩ := List.mem_map.mp
        ((GeneralOccurrenceFrontier.LocalEquationFree.completedReceipts_targets_iff_step
          plan bound expected source target empty checked).mpr step)
      obtain ⟨index, present⟩ := List.mem_iff_getElem?.mp member
      exact ⟨⟨⟨index, receipt⟩, present⟩⟩

/-- The equivalence is earned from actual driver execution and the original
all-job completion theorem. It retains every receipt field and ordinal. -/
def completed_output_equiv (state : State) (plan : GeneralExecutionAdmission.Plan)
    (finiteProvider : plan.snapshot.provider.dynamicRelations = [])
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (empty : plan.equations = [])
    (checked : checkStepStratification (GeneralPlanEnvironment.environment plan).language = true)
    (budget : GeneralRuleJobs.Job → Nat)
    (saturated : ∀ job ∈ GeneralRuleJobs.jobs plan bound expected source,
      (Execution.treeStart (GeneralPlanEnvironment.environment plan)
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget job) :
    (sourceOutput plan bound expected empty checked).Family source ≃
      targetOutput.Family
        {state, control := .evaluate [] (programQuery (invocations plan bound expected source budget))} := by
  let reindex :
      {occurrence : Nat × GeneralRuleJobs.Receipt //
        (GeneralRuleJobExecution.completedReceipts plan bound expected source)[occurrence.1]? = some occurrence.2} ≃
      {occurrence : Nat × GeneralRuleJobs.Receipt //
        ((invocations plan bound expected source budget).flatMap receipts)[occurrence.1]? = some occurrence.2} :=
    { toFun := fun occurrence => ⟨occurrence.val, by
        rw [saturated_receipts_eq_completed plan bound expected source budget saturated]
        exact occurrence.property⟩
      invFun := fun occurrence => ⟨occurrence.val, by
        rw [← saturated_receipts_eq_completed plan bound expected source budget saturated]
        exact occurrence.property⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  exact reindex.trans (program_output_equiv state _ (invocations_finiteProvider plan finiteProvider bound expected source budget))

@[simp] theorem completed_output_equiv_preserves_occurrence (state : State)
    (plan : GeneralExecutionAdmission.Plan)
    (finiteProvider : plan.snapshot.provider.dynamicRelations = []) (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (empty : plan.equations = [])
    (checked : checkStepStratification (GeneralPlanEnvironment.environment plan).language = true)
    (budget : GeneralRuleJobs.Job → Nat)
    (saturated : ∀ job ∈ GeneralRuleJobs.jobs plan bound expected source,
      (Execution.treeStart (GeneralPlanEnvironment.environment plan)
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget job)
    (occurrence : (sourceOutput plan bound expected empty checked).Family source) :
    (completed_output_equiv state plan finiteProvider bound expected source empty checked budget saturated occurrence).val =
      occurrence.val := rfl

/-- Native membership is preserved and reflected between independently
defined source successors and target operational observations. -/
theorem nativeType_iff (state : State) (plan : GeneralExecutionAdmission.Plan)
    (finiteProvider : plan.snapshot.provider.dynamicRelations = [])
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (empty : plan.equations = [])
    (checked : checkStepStratification (GeneralPlanEnvironment.environment plan).language = true)
    (budget : Pattern → GeneralRuleJobs.Job → Nat)
    (saturated : ∀ source job, job ∈ GeneralRuleJobs.jobs plan bound expected source →
      (Execution.treeStart (GeneralPlanEnvironment.environment plan)
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget source job) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (GeneralOccurrenceSemantics.gslt plan bound expected)).satisfies (S := ()) source
        (sourceOutput plan bound expected empty checked).nativeType.pred ↔
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF (theory runtime)).satisfies (S := ())
      {state, control := .evaluate [] (programQuery (invocations plan bound expected source (budget source)))}
      targetOutput.nativeType.pred :=
  Mettapedia.OSLF.NativeTypes.Semantics.Families.NativeOutput.nativeType_iff
    (sourceOutput plan bound expected empty checked) targetOutput _
    (fun source => completed_output_equiv state plan finiteProvider bound expected source empty checked
      (budget source) (saturated source)) source

/-- The complete target observation contains precisely the successors of the
original source GSLT, with explicit receipt witnesses for each successor. -/
theorem observed_target_iff_step (state : State) (plan : GeneralExecutionAdmission.Plan)
    (finiteProvider : plan.snapshot.provider.dynamicRelations = [])
    (bound : List TypeExpr) (expected : TypeExpr) (source target : Pattern)
    (empty : plan.equations = [])
    (checked : checkStepStratification (GeneralPlanEnvironment.environment plan).language = true)
    (budget : GeneralRuleJobs.Job → Nat)
    (saturated : ∀ job ∈ GeneralRuleJobs.jobs plan bound expected source,
      (Execution.treeStart (GeneralPlanEnvironment.environment plan)
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget job) :
    (∃ occurrence : targetOutput.Family
      {state, control := .evaluate [] (programQuery (invocations plan bound expected source budget))},
      occurrence.val.2.target = target) ↔
      (GeneralOccurrenceSemantics.gslt plan bound expected).Step source target := by
  rw [← GeneralOccurrenceFrontier.LocalEquationFree.completedReceipts_targets_iff_step
    plan bound expected source target empty checked]
  let comparison := completed_output_equiv state plan finiteProvider bound expected source empty checked budget saturated
  constructor
  · rintro ⟨occurrence, endpoint⟩
    obtain ⟨original, rfl⟩ := comparison.surjective occurrence
    exact List.mem_map.mpr ⟨original.val.2,
      List.mem_iff_getElem?.mpr ⟨original.val.1, original.property⟩,
      by simpa only [comparison, completed_output_equiv_preserves_occurrence] using endpoint⟩
  · intro member
    obtain ⟨receipt, present, endpoint⟩ := List.mem_map.mp member
    obtain ⟨index, indexed⟩ := List.mem_iff_getElem?.mp present
    refine ⟨comparison ⟨⟨index, receipt⟩, indexed⟩, ?_⟩
    change receipt.target = target
    exact endpoint

/-- A universal property of returned targets holds exactly for all original
source successors. This theorem requires saturation of every generated job. -/
theorem forall_observed_targets_iff_steps (state : State) (plan : GeneralExecutionAdmission.Plan)
    (finiteProvider : plan.snapshot.provider.dynamicRelations = [])
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (empty : plan.equations = [])
    (checked : checkStepStratification (GeneralPlanEnvironment.environment plan).language = true)
    (budget : GeneralRuleJobs.Job → Nat)
    (saturated : ∀ job ∈ GeneralRuleJobs.jobs plan bound expected source,
      (Execution.treeStart (GeneralPlanEnvironment.environment plan)
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget job)
    (property : Pattern → Prop) :
    (∀ occurrence : targetOutput.Family
      {state, control := .evaluate [] (programQuery (invocations plan bound expected source budget))},
      property occurrence.val.2.target) ↔
      ∀ target, (GeneralOccurrenceSemantics.gslt plan bound expected).Step source target → property target := by
  rw [← GeneralOccurrenceFrontier.LocalEquationFree.forall_completedReceipts_iff
    plan bound expected source empty checked property]
  let comparison := completed_output_equiv state plan finiteProvider bound expected source empty checked budget saturated
  constructor
  · intro universal receipt member
    obtain ⟨index, present⟩ := List.mem_iff_getElem?.mp member
    have result := universal (comparison ⟨⟨index, receipt⟩, present⟩)
    change property receipt.target at result
    exact result
  · intro universal occurrence
    obtain ⟨original, rfl⟩ := comparison.surjective occurrence
    simpa only [comparison, completed_output_equiv_preserves_occurrence] using
      universal original.val.2 (List.mem_iff_getElem?.mpr ⟨original.val.1, original.property⟩)

/-- Native enumeration and supplied-list execution return the same physical
receipt occurrences because both actual calls return the same ordered data. -/
def execute_output_equiv (state : State) (plan : GeneralExecutionAdmission.Plan)
    (finiteProvider : plan.snapshot.provider.dynamicRelations = [])
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) (budget : Nat) :
    targetOutput.Family
      {state, control := .evaluate [] (programQuery (invocations plan bound expected source (fun _ => budget)))} ≃
    targetOutput.Family
      {state, control := .evaluate [] (executeQuery plan bound expected source budget)} :=
  (program_output_equiv state (invocations plan bound expected source (fun _ => budget))
    (invocations_finiteProvider plan finiteProvider bound expected source (fun _ => budget))).symm.trans
    (OperationalGSLT.orderedOutputEquiv runtime readProgramReceipts readProgramReceipts_functional _
      (OperationalGSLT.pureSingleton_of_returns runtime [] state _ _
        (execute_returns state plan finiteProvider bound expected source budget))
      ((invocations plan bound expected source (fun _ => budget)).flatMap receipts)
      ⟨encodeList observationTerm (invocations plan bound expected source (fun _ => budget)), rfl⟩)

/-- Source evidence is retained by the native presentation-entry call itself,
including duplicate physical outputs with equal payloads. -/
def native_output_equiv (state : State) (plan : GeneralExecutionAdmission.Plan)
    (finiteProvider : plan.snapshot.provider.dynamicRelations = [])
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (empty : plan.equations = [])
    (checked : checkStepStratification (GeneralPlanEnvironment.environment plan).language = true)
    (budget : Nat)
    (saturated : ∀ job ∈ GeneralRuleJobs.jobs plan bound expected source,
      (Execution.treeStart (GeneralPlanEnvironment.environment plan)
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget) :
    (sourceOutput plan bound expected empty checked).Family source ≃
      targetOutput.Family {state, control := .evaluate [] (executeQuery plan bound expected source budget)} :=
  (completed_output_equiv state plan finiteProvider bound expected source empty checked (fun _ => budget) saturated).trans
    (execute_output_equiv state plan finiteProvider bound expected source budget)

@[simp] theorem native_output_equiv_preserves_occurrence (state : State)
    (plan : GeneralExecutionAdmission.Plan)
    (finiteProvider : plan.snapshot.provider.dynamicRelations = []) (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (empty : plan.equations = [])
    (checked : checkStepStratification (GeneralPlanEnvironment.environment plan).language = true)
    (budget : Nat)
    (saturated : ∀ job ∈ GeneralRuleJobs.jobs plan bound expected source,
      (Execution.treeStart (GeneralPlanEnvironment.environment plan)
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget)
    (occurrence : (sourceOutput plan bound expected empty checked).Family source) :
    (native_output_equiv state plan finiteProvider bound expected source empty checked budget saturated occurrence).val =
      occurrence.val := rfl

theorem execute_nativeType_iff (state : State) (plan : GeneralExecutionAdmission.Plan)
    (finiteProvider : plan.snapshot.provider.dynamicRelations = [])
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (empty : plan.equations = [])
    (checked : checkStepStratification (GeneralPlanEnvironment.environment plan).language = true)
    (budget : Pattern → Nat)
    (saturated : ∀ source job, job ∈ GeneralRuleJobs.jobs plan bound expected source →
      (Execution.treeStart (GeneralPlanEnvironment.environment plan)
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget source) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (GeneralOccurrenceSemantics.gslt plan bound expected)).satisfies (S := ()) source
        (sourceOutput plan bound expected empty checked).nativeType.pred ↔
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF (theory runtime)).satisfies (S := ())
      {state, control := .evaluate [] (executeQuery plan bound expected source (budget source))}
      targetOutput.nativeType.pred :=
  Mettapedia.OSLF.NativeTypes.Semantics.Families.NativeOutput.nativeType_iff
    (sourceOutput plan bound expected empty checked) targetOutput _
    (fun source => native_output_equiv state plan finiteProvider bound expected source empty checked
      (budget source) (saturated source)) source

theorem execute_observed_target_iff_step (state : State) (plan : GeneralExecutionAdmission.Plan)
    (finiteProvider : plan.snapshot.provider.dynamicRelations = [])
    (bound : List TypeExpr) (expected : TypeExpr) (source target : Pattern)
    (empty : plan.equations = [])
    (checked : checkStepStratification (GeneralPlanEnvironment.environment plan).language = true)
    (budget : Nat)
    (saturated : ∀ job ∈ GeneralRuleJobs.jobs plan bound expected source,
      (Execution.treeStart (GeneralPlanEnvironment.environment plan)
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget) :
    (∃ occurrence : targetOutput.Family
      {state, control := .evaluate [] (executeQuery plan bound expected source budget)},
      occurrence.val.2.target = target) ↔
      (GeneralOccurrenceSemantics.gslt plan bound expected).Step source target := by
  rw [← observed_target_iff_step state plan finiteProvider bound expected source target empty checked (fun _ => budget) saturated]
  let comparison := execute_output_equiv state plan finiteProvider bound expected source budget
  constructor
  · rintro ⟨occurrence, endpoint⟩
    exact ⟨comparison.symm occurrence, endpoint⟩
  · rintro ⟨occurrence, endpoint⟩
    exact ⟨comparison occurrence, endpoint⟩

theorem execute_forall_targets_iff_steps (state : State) (plan : GeneralExecutionAdmission.Plan)
    (finiteProvider : plan.snapshot.provider.dynamicRelations = [])
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (empty : plan.equations = [])
    (checked : checkStepStratification (GeneralPlanEnvironment.environment plan).language = true)
    (budget : Nat)
    (saturated : ∀ job ∈ GeneralRuleJobs.jobs plan bound expected source,
      (Execution.treeStart (GeneralPlanEnvironment.environment plan)
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget)
    (property : Pattern → Prop) :
    (∀ occurrence : targetOutput.Family
      {state, control := .evaluate [] (executeQuery plan bound expected source budget)},
      property occurrence.val.2.target) ↔
      ∀ target, (GeneralOccurrenceSemantics.gslt plan bound expected).Step source target → property target := by
  rw [← forall_observed_targets_iff_steps state plan finiteProvider bound expected source empty checked (fun _ => budget) saturated property]
  let comparison := execute_output_equiv state plan finiteProvider bound expected source budget
  exact ⟨fun universal occurrence => universal (comparison occurrence),
    fun universal occurrence => universal (comparison.symm occurrence)⟩

/-- Existential outgoing observations transport for any declared target
predicate, using exactly the same native entry and physical evidence. -/
theorem execute_may_targets_iff_steps (state : State) (plan : GeneralExecutionAdmission.Plan)
    (finiteProvider : plan.snapshot.provider.dynamicRelations = [])
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
    (empty : plan.equations = [])
    (checked : checkStepStratification (GeneralPlanEnvironment.environment plan).language = true)
    (budget : Nat)
    (saturated : ∀ job ∈ GeneralRuleJobs.jobs plan bound expected source,
      (Execution.treeStart (GeneralPlanEnvironment.environment plan)
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget)
    (property : Pattern → Prop) :
    (∃ occurrence : targetOutput.Family
      {state, control := .evaluate [] (executeQuery plan bound expected source budget)},
      property occurrence.val.2.target) ↔
      ∃ target, (GeneralOccurrenceSemantics.gslt plan bound expected).Step source target ∧ property target := by
  constructor
  · rintro ⟨occurrence, holds⟩
    exact ⟨occurrence.val.2.target,
      (execute_observed_target_iff_step state plan finiteProvider bound expected source _ empty checked budget saturated).mp
        ⟨occurrence, rfl⟩, holds⟩
  · rintro ⟨target, step, holds⟩
    obtain ⟨occurrence, endpoint⟩ :=
      (execute_observed_target_iff_step state plan finiteProvider bound expected source target empty checked budget saturated).mpr step
    exact ⟨occurrence, endpoint.symm ▸ holds⟩


/-! ## The printed reducts are the canonical ones, in order -/

section CanonicalOrder

open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement (QueryProfile rootPlan providerRelEnv
  completedReceipts_targets)

/-- **The driver returns the canonical reducts, in order.** For the root plan of
a query-profile language, a well-sorted source and a budget that drains every
job, the actual PeTTa run of the presentation entry completes with one
observation. The receipts it carries have exactly the canonical engine's reducts
over the provider's own relation environment, one for one and in order. -/
theorem execute_reducts (state : State) {language : LanguageDef}
    {provider : GeneralPremise.ProviderSnapshot} (profile : QueryProfile language provider)
    {bound : List TypeExpr} {type : TypeExpr} {source : Pattern}
    (sourceTyped : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      (GeneralPlanEnvironment.environment (rootPlan language provider)).language
      (GeneralPlanEnvironment.environment (rootPlan language provider)).free bound type source)
    (budget : Nat)
    (saturated : ∀ job ∈ GeneralRuleJobs.jobs (rootPlan language provider) bound type source,
      (Execution.treeStart (GeneralPlanEnvironment.environment (rootPlan language provider))
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget)
    (fuel : Nat) :
    ∃ (evaluatorFuel : Nat) (value : Atom) (receipts : List GeneralRuleJobs.Receipt),
      Eval.run runtime evaluatorFuel
          {state, control := .evaluate [] (executeQuery (rootPlan language provider) bound type source
            budget)} = .complete state [value] [] [] ∧
        readProgramReceipts value receipts ∧
        receipts.map GeneralRuleJobs.Receipt.target =
          ContextualStep.reductsUsing (providerRelEnv provider) language (fuel + 1) source := by
  let jobs := invocations (rootPlan language provider) bound type source (fun _ => budget)
  obtain ⟨evaluatorFuel, completed⟩ :=
    (execute_completed_iff state state (rootPlan language provider) profile.firstOrder.noDynamic bound type source budget
      [encoded (programObservationTerm jobs)] [] []).mpr ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨evaluatorFuel, encoded (programObservationTerm jobs), jobs.flatMap receipts, completed,
    ⟨encodeList observationTerm jobs, rfl⟩, ?_⟩
  rw [saturated_receipts_eq_completed (rootPlan language provider) bound type source (fun _ => budget)
    saturated]
  exact completedReceipts_targets profile sourceTyped fuel

end CanonicalOrder



/-! ## The rho calculus through the PeTTa driver

Three plans share the original COMM declaration and differ only in their reduction contexts.
`GeneralRho.Standard.plan` licenses the positions inside the parallel bag, which are the reduction
contexts of the rho calculus. `GeneralRho.DepthOne.plan` licenses only the root, which suffices on
canonical processes. `GeneralRho.plan` licenses every site: it also fires COMM under an input
binder, inside a sent process and inside a quoted name. -/

section Rho

open Mettapedia.Languages.ProcessCalculi.RhoCalculus (semanticCommSubst)

/-- The selected rho plan is stratified: its only rule, COMM, asks for no child step. -/
theorem rho_stratified :
    checkStepStratification (GeneralPlanEnvironment.environment GeneralRho.plan).language = true := by
  change checkStepStratification
    { GeneralRho.language with
      rewrites := GeneralRho.plan.rules.map GeneralExecutionAdmission.RulePlan.rule } = true
  rw [GeneralRho.compiled_rules]
  rfl

/-- **Rho with every site through the PeTTa driver.** For the all-sites rho plan, with no
equations and a budget that drains every job, the actual PeTTa run of the presentation entry
observes a target exactly when it is a step of that plan's GSLT. -/
theorem rho_execute_observed_target_iff_step (state : State) (bound : List TypeExpr)
    (expected : TypeExpr) (source target : Pattern) (budget : Nat)
    (saturated : ∀ job ∈ GeneralRuleJobs.jobs GeneralRho.plan bound expected source,
      (Execution.treeStart (GeneralPlanEnvironment.environment GeneralRho.plan)
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget) :
    (∃ occurrence : targetOutput.Family
      {state, control := .evaluate [] (executeQuery GeneralRho.plan bound expected source budget)},
      occurrence.val.2.target = target) ↔
      (GeneralOccurrenceSemantics.gslt GeneralRho.plan bound expected).Step source target :=
  execute_observed_target_iff_step state GeneralRho.plan (by rfl) bound expected source target
    GeneralRho.compilation_has_no_equations rho_stratified budget saturated

/-- **Every original COMM is printed with its reduct.** For a closed original rho redex, an
input on a channel in parallel with an output on it and a residual bag, with a quotation-sealed
input body, the actual PeTTa run of the presentation entry observes the COMM reduct. The reduct
is the independent semantic substitution of the payload into the body with its quotations of
drops resolved, beside the residual. -/
theorem rho_original_comm_observed (state : State) {channel body payload : Pattern}
    {rest : List Pattern}
    (channelTyped : DerivedPresentationSyntax.NameWellSorted rhoReflectivePresentation (fun _ => none) []
      channel)
    (bodyTyped : DerivedPresentationSyntax.ProcWellSorted rhoReflectivePresentation (fun _ => none) ["Name"]
      body)
    (sealed : ScopedPattern.binderSafeAt "NQuote" 1 body = true)
    (payloadTyped : DerivedPresentationSyntax.ProcWellSorted rhoReflectivePresentation (fun _ => none) []
      payload)
    (restTyped : DerivedPresentationSyntax.ProcListWellSorted rhoReflectivePresentation (fun _ => none) []
      rest)
    (budget : Nat)
    (saturated : ∀ job ∈ GeneralRuleJobs.jobs GeneralRho.plan [] (.base "Proc")
        (GeneralRho.source channel body payload rest),
      (Execution.treeStart (GeneralPlanEnvironment.environment GeneralRho.plan)
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget) :
    ∃ occurrence : targetOutput.Family
      {state, control := .evaluate [] (executeQuery GeneralRho.plan [] (.base "Proc")
        (GeneralRho.source channel body payload rest) budget)},
      occurrence.val.2.target =
        .collection .hashBag (semanticCommSubst (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.resolveQuotes rhoReflectivePresentation body) payload :: rest) none := by
  have valid := GeneralRho.root_receipt_valid (GeneralRho.derived_name_open channelTyped)
    (GeneralRho.derived_process_open bodyTyped) sealed (GeneralRho.derived_names_admitted bodyTyped sealed)
    (GeneralRho.derived_process_open payloadTyped) (GeneralRho.derived_processes_typed restTyped)
    (GeneralRho.derived_processes_represented restTyped)
  have semantic := GeneralRho.rootReceipt_target_resolved (channel := channel) bodyTyped payloadTyped
    restTyped
  rw [← semantic]
  exact (rho_execute_observed_target_iff_step state [] (.base "Proc") _ _ budget saturated).mpr
    ⟨_, _, .refl _, valid, .refl _⟩

/-- On a body in the literal-quotation fiber, the observed reduct is the
paper-facing semantic substitution of the payload into the body. -/
theorem rho_original_comm_observed_literal (state : State) {channel body payload : Pattern}
    {rest : List Pattern}
    (channelTyped : DerivedPresentationSyntax.NameWellSorted rhoReflectivePresentation (fun _ => none) []
      channel)
    (bodyTyped : DerivedPresentationSyntax.ProcWellSorted rhoReflectivePresentation (fun _ => none) ["Name"]
      body)
    (sealed : ScopedPattern.binderSafeAt "NQuote" 1 body = true)
    (fiber : Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent.quotesLiteral rhoReflectivePresentation body = true)
    (payloadTyped : DerivedPresentationSyntax.ProcWellSorted rhoReflectivePresentation (fun _ => none) []
      payload)
    (restTyped : DerivedPresentationSyntax.ProcListWellSorted rhoReflectivePresentation (fun _ => none) []
      rest)
    (budget : Nat)
    (saturated : ∀ job ∈ GeneralRuleJobs.jobs GeneralRho.plan [] (.base "Proc")
        (GeneralRho.source channel body payload rest),
      (Execution.treeStart (GeneralPlanEnvironment.environment GeneralRho.plan)
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget) :
    ∃ occurrence : targetOutput.Family
      {state, control := .evaluate [] (executeQuery GeneralRho.plan [] (.base "Proc")
        (GeneralRho.source channel body payload rest) budget)},
      occurrence.val.2.target = .collection .hashBag (semanticCommSubst body payload :: rest) none := by
  rw [← Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy.semanticCommSubst_resolveQuotes_of_fiber
    bodyTyped fiber payloadTyped]
  exact rho_original_comm_observed state channelTyped bodyTyped sealed payloadTyped restTyped budget saturated

/-- **Standard rho through the PeTTa driver.** With the rho calculus's own reduction contexts and a
budget that drains every job, the actual PeTTa run of the presentation entry observes a target
exactly when it is a COMM step inside the parallel bag of the source. -/
theorem rho_standard_execute_observed_target_iff_step (state : State) (bound : List TypeExpr)
    (expected : TypeExpr) (source target : Pattern) (budget : Nat)
    (saturated : ∀ job ∈ GeneralRuleJobs.jobs GeneralRho.Standard.plan bound expected source,
      (Execution.treeStart (GeneralPlanEnvironment.environment GeneralRho.Standard.plan)
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget) :
    (∃ occurrence : targetOutput.Family
      {state, control := .evaluate [] (executeQuery GeneralRho.Standard.plan bound expected source budget)},
      occurrence.val.2.target = target) ↔
      (GeneralOccurrenceSemantics.gslt GeneralRho.Standard.plan bound expected).Step source target :=
  execute_observed_target_iff_step state GeneralRho.Standard.plan (by rfl) bound expected source target
    GeneralRho.Standard.compilation_has_no_equations GeneralRho.Standard.stratified budget saturated

/-- **Every standard COMM is printed with its reduct.** With the standard reduction contexts, the
actual PeTTa run observes the reduct of every closed original redex at the root of the bag. -/
theorem rho_standard_original_comm_observed (state : State) {channel body payload : Pattern}
    {rest : List Pattern}
    (channelTyped : DerivedPresentationSyntax.NameWellSorted rhoReflectivePresentation (fun _ => none) []
      channel)
    (bodyTyped : DerivedPresentationSyntax.ProcWellSorted rhoReflectivePresentation (fun _ => none) ["Name"]
      body)
    (sealed : ScopedPattern.binderSafeAt "NQuote" 1 body = true)
    (payloadTyped : DerivedPresentationSyntax.ProcWellSorted rhoReflectivePresentation (fun _ => none) []
      payload)
    (restTyped : DerivedPresentationSyntax.ProcListWellSorted rhoReflectivePresentation (fun _ => none) []
      rest)
    (budget : Nat)
    (saturated : ∀ job ∈ GeneralRuleJobs.jobs GeneralRho.Standard.plan [] (.base "Proc")
        (GeneralRho.source channel body payload rest),
      (Execution.treeStart (GeneralPlanEnvironment.environment GeneralRho.Standard.plan)
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget) :
    ∃ occurrence : targetOutput.Family
      {state, control := .evaluate [] (executeQuery GeneralRho.Standard.plan [] (.base "Proc")
        (GeneralRho.source channel body payload rest) budget)},
      occurrence.val.2.target =
        .collection .hashBag (semanticCommSubst (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.resolveQuotes rhoReflectivePresentation body) payload :: rest) none := by
  have valid := GeneralRho.Standard.root_receipt_valid (GeneralRho.derived_name_open channelTyped)
    (GeneralRho.derived_process_open bodyTyped) sealed (GeneralRho.derived_names_admitted bodyTyped sealed)
    (GeneralRho.derived_process_open payloadTyped) (GeneralRho.derived_processes_typed restTyped)
    (GeneralRho.derived_processes_represented restTyped)
  have semantic := GeneralRho.rootReceipt_target_resolved (channel := channel) bodyTyped payloadTyped
    restTyped
  rw [← semantic]
  exact (rho_standard_execute_observed_target_iff_step state [] (.base "Proc") _ _ budget saturated).mpr
    ⟨_, _, .refl _, valid, .refl _⟩

/-- On a body in the literal-quotation fiber, the observed reduct is the
paper-facing semantic substitution of the payload into the body. -/
theorem rho_standard_original_comm_observed_literal (state : State) {channel body payload : Pattern}
    {rest : List Pattern}
    (channelTyped : DerivedPresentationSyntax.NameWellSorted rhoReflectivePresentation (fun _ => none) []
      channel)
    (bodyTyped : DerivedPresentationSyntax.ProcWellSorted rhoReflectivePresentation (fun _ => none) ["Name"]
      body)
    (sealed : ScopedPattern.binderSafeAt "NQuote" 1 body = true)
    (fiber : Mettapedia.OSLF.MeTTaIL.ReflectiveCoherent.quotesLiteral rhoReflectivePresentation body = true)
    (payloadTyped : DerivedPresentationSyntax.ProcWellSorted rhoReflectivePresentation (fun _ => none) []
      payload)
    (restTyped : DerivedPresentationSyntax.ProcListWellSorted rhoReflectivePresentation (fun _ => none) []
      rest)
    (budget : Nat)
    (saturated : ∀ job ∈ GeneralRuleJobs.jobs GeneralRho.Standard.plan [] (.base "Proc")
        (GeneralRho.source channel body payload rest),
      (Execution.treeStart (GeneralPlanEnvironment.environment GeneralRho.Standard.plan)
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget) :
    ∃ occurrence : targetOutput.Family
      {state, control := .evaluate [] (executeQuery GeneralRho.Standard.plan [] (.base "Proc")
        (GeneralRho.source channel body payload rest) budget)},
      occurrence.val.2.target = .collection .hashBag (semanticCommSubst body payload :: rest) none := by
  rw [← Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefAdequacy.semanticCommSubst_resolveQuotes_of_fiber
    bodyTyped fiber payloadTyped]
  exact rho_standard_original_comm_observed state channelTyped bodyTyped sealed payloadTyped restTyped budget saturated

/-- **Canonical rho through the PeTTa driver.** On a closed, quotation-sealed canonical source, with
a budget that drains every job, the actual PeTTa run of the depth-one plan observes a target exactly
when it is an authored depth-one rho step. -/
theorem rho_canonical_observed_iff_step (state : State) {source target : Pattern}
    (typed : DerivedPresentationSyntax.ProcWellSorted rhoReflectivePresentation (fun _ => none) [] source)
    (sealed : ScopedPattern.binderSafeAt "NQuote" 0 source = true)
    (canonical : Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.IsCanonical source) (budget : Nat)
    (saturated : ∀ job ∈ GeneralRuleJobs.jobs GeneralRho.DepthOne.plan [] (.base "Proc") source,
      (Execution.treeStart (GeneralPlanEnvironment.environment GeneralRho.DepthOne.plan)
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget) :
    (∃ occurrence : targetOutput.Family
      {state, control := .evaluate [] (executeQuery GeneralRho.DepthOne.plan [] (.base "Proc") source budget)},
      occurrence.val.2.target = target) ↔
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep.RhoStepAt 1 source target :=
  (execute_observed_target_iff_step state GeneralRho.DepthOne.plan (by rfl) [] (.base "Proc") source target
    GeneralRho.DepthOne.compilation_has_no_equations GeneralRho.DepthOne.stratified budget saturated).trans
    (GeneralRho.DepthOne.step_iff typed sealed (GeneralRho.DepthOne.isCanonical_channelsDecided canonical))

/-- **Rho modulo structural congruence through the PeTTa driver.** Run the depth-one plan on the
canonical form of a closed, quotation-sealed process; that form is structurally congruent to the
process. Every observed target is an authored rho step from the canonical form, and every authored
rho step from the process, at any depth, is observed up to canonical form. -/
theorem rho_observed_on_canonical (state : State) {process : Pattern}
    (typed : DerivedPresentationSyntax.ProcWellSorted rhoReflectivePresentation (fun _ => none) [] process)
    (sealed : ScopedPattern.binderSafeAt "NQuote" 0 process = true) (budget : Nat)
    (saturated : ∀ job ∈ GeneralRuleJobs.jobs GeneralRho.DepthOne.plan [] (.base "Proc")
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize process),
      (Execution.treeStart (GeneralPlanEnvironment.environment GeneralRho.DepthOne.plan)
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence process
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize process) ∧
      (∀ observed, (∃ occurrence : targetOutput.Family
          {state, control := .evaluate [] (executeQuery GeneralRho.DepthOne.plan [] (.base "Proc")
            (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize process) budget)},
          occurrence.val.2.target = observed) →
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep.RhoStep
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize process) observed) ∧
      (∀ target, Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep.RhoStep process target →
        ∃ observed, (∃ occurrence : targetOutput.Family
            {state, control := .evaluate [] (executeQuery GeneralRho.DepthOne.plan [] (.base "Proc")
              (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize process) budget)},
            occurrence.val.2.target = observed) ∧
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize observed =
            Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize target) := by
  obtain ⟨canonicalTyped, canonicalSealed⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness.closed_canonicalize typed sealed
  have exact := fun target => rho_canonical_observed_iff_step state (target := target) canonicalTyped
    canonicalSealed (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize_isCanonical process)
    budget saturated
  refine ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize_sound process,
    fun observed seen => ⟨1, (exact observed).mp seen⟩, fun target step => ?_⟩
  obtain ⟨observed, depthOne, same⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness.canonicalStep_complete_of_rhoStep
      typed step
  exact ⟨observed, (exact observed).mpr depthOne, same⟩

/-- **Rho through the PeTTa driver on lexicographic forms.** Run the depth-one plan on the
lexicographic form of a closed, quotation-sealed process; that form is structurally congruent to the
process and is computed by insertion sort on serializations. Every observed target is an authored rho
step from the form, and every authored rho step from the process, at any depth, is observed up to
canonical form. -/
theorem rho_observed_on_lexCanon (state : State) {process : Pattern}
    (typed : DerivedPresentationSyntax.ProcWellSorted rhoReflectivePresentation (fun _ => none) [] process)
    (sealed : ScopedPattern.binderSafeAt "NQuote" 0 process = true) (budget : Nat)
    (saturated : ∀ job ∈ GeneralRuleJobs.jobs GeneralRho.DepthOne.plan [] (.base "Proc")
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.LexCanonical.lexCanon process),
      (Execution.treeStart (GeneralPlanEnvironment.environment GeneralRho.DepthOne.plan)
        (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost ≤ budget) :
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence process
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.LexCanonical.lexCanon process) ∧
      (∀ observed, (∃ occurrence : targetOutput.Family
          {state, control := .evaluate [] (executeQuery GeneralRho.DepthOne.plan [] (.base "Proc")
            (Mettapedia.Languages.ProcessCalculi.RhoCalculus.LexCanonical.lexCanon process) budget)},
          occurrence.val.2.target = observed) →
        Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep.RhoStep
          (Mettapedia.Languages.ProcessCalculi.RhoCalculus.LexCanonical.lexCanon process) observed) ∧
      (∀ target, Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep.RhoStep process target →
        ∃ observed, (∃ occurrence : targetOutput.Family
            {state, control := .evaluate [] (executeQuery GeneralRho.DepthOne.plan [] (.base "Proc")
              (Mettapedia.Languages.ProcessCalculi.RhoCalculus.LexCanonical.lexCanon process) budget)},
            occurrence.val.2.target = observed) ∧
          Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize observed =
            Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical.canonicalize target) := by
  obtain ⟨lexTyped, lexSealed⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.LexCanonical.closed_lexCanon typed sealed
  have exact := fun target =>
    (execute_observed_target_iff_step state GeneralRho.DepthOne.plan (by rfl) [] (.base "Proc")
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.LexCanonical.lexCanon process) target
      GeneralRho.DepthOne.compilation_has_no_equations GeneralRho.DepthOne.stratified budget saturated).trans
      (GeneralRho.DepthOne.step_iff lexTyped lexSealed
        (Mettapedia.Languages.ProcessCalculi.RhoCalculus.LexCanonical.lexCanon_channelsDecided process))
  refine ⟨Mettapedia.Languages.ProcessCalculi.RhoCalculus.LexCanonical.lexCanon_sound process,
    fun observed seen => ⟨1, (exact observed).mp seen⟩, fun target step => ?_⟩
  obtain ⟨observed, depthOne, same⟩ :=
    Mettapedia.Languages.ProcessCalculi.RhoCalculus.LexCanonical.lexStep_complete typed step
  exact ⟨observed, (exact observed).mpr depthOne, same⟩

end Rho

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralProgramDriverExecution
