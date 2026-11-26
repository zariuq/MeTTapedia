import Mettapedia.Languages.MeTTa.PeTTa.BridgeTransport
import Mettapedia.Languages.MeTTa.PeTTa.AppendAgreement
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralRuleJobExecution

/-!
# Authored scoped rule-driver program and wire operations

The driver advances the original rule-job scheduler. Its data retain the
inner premise agenda, physical answer cursor, emitted receipts and unresolved
obligations. Exhausting a budget retains that complete state for resumption.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralRuleDriverExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program Equation)
open Eval
open scoped ProgramQuotation


def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../../metta/gslt/lib/gslt_execution_driver.metta"
    sha256 "02558b35a3acbd2d18ccb45457bfee24d04e6814afb174e5756746f8cb7db74c"

def program : Program := RuleExecutionProgram.scopedProgram.append source.program

def retainedHead (head : String) : Bool :=
  head != "eval" && !(head.startsWith "gslt:driver:")

theorem retained_closed : ProgramClosed retainedHead RuleExecutionProgram.scopedProgram := by
  exact BridgeKit.closed_of_all _ _ (by decide +kernel) (by decide +kernel)

theorem retained_agreement :
    ProgramAgreementOn retainedHead RuleExecutionProgram.scopedProgram program := by
  exact appended_program_agreement_of_all _ _ _ (by decide +kernel) (by decide +kernel)

theorem retained_returns {caller : Subst} {before after : State} {code answer : Atom}
    (supported : codeWithin retainedHead code = true)
    (returned : PureReturns RuleExecutionProgram.scopedProgram caller before code after answer) :
    PureReturns program caller before code after answer :=
  path_of_closed_agreement retained_closed retained_agreement ⟨supported, rfl⟩ returned

def taskTerm {request : GeneralRuleJobExecution.Request} : GeneralRuleJobExecution.Task request → Term
  | .root frame => .application "RuleJobFrame" [PremiseOperationsExecution.GeneralExecution.stateTerm frame.state, .natural frame.cursor]

def answerTerm {request : GeneralRuleJobExecution.Request} (answer : GeneralRuleJobExecution.Answer request) : Term :=
  ScopedRuleJobReadoutExecution.receiptTerm answer.val

def obligationTerm : GeneralRuleJobExecution.Obligation → Term
  | .premise reason => .application "RuleJobPremise" [PremiseOperationsExecution.GeneralExecution.obligationTerm reason]

def stateTerm {request : GeneralRuleJobExecution.Request} (state : GeneralRuleJobExecution.State request) : Term :=
  PremiseSchedulerExecution.schedulerStateTerm taskTerm answerTerm obligationTerm state

def expansionTerm {request : GeneralRuleJobExecution.Request}
    (expanded : Scheduler.Expansion (GeneralRuleJobExecution.Task request) (GeneralRuleJobExecution.Answer request) GeneralRuleJobExecution.Obligation) : Term :=
  PremiseSchedulerExecution.schedulerExpansionTerm taskTerm answerTerm obligationTerm expanded

def requestTerm (request : GeneralRuleJobExecution.Request) : Term :=
  ScopedRuleJobReadoutExecution.requestProjectionTerm request (GeneralRuleJobObservation.requestFootprint request)

abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
abbrev v (name : String) : Atom := .var name
abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
abbrev number (value : Nat) : Atom := encoded (.natural value)

inductive Helper where
  | obligations | start | expand | tick | run | begin
  deriving DecidableEq

def Helper.head : Helper → String
  | .obligations => "gslt:driver:job-obligations"
  | .start => "gslt:driver:job-start"
  | .expand => "gslt:driver:job-expand"
  | .tick => "gslt:driver:job-tick"
  | .run => "gslt:driver:job-run"
  | .begin => "gslt:driver:job-begin"

def Helper.names : Helper → List String
  | .obligations => ["obligations"]
  | .start => ["request"]
  | .expand => ["request", "task"]
  | .tick => ["request", "state"]
  | .run => ["request", "fuel", "state"]
  | .begin => ["request", "fuel"]

def equations (head : String) : List SpaceSemantics.Equation :=
  program.equations.filter (fun equation => equation.head == head)

def equation (helper : Helper) : SpaceSemantics.Equation :=
  (equations helper.head)[0]'(by cases helper <;> decide +kernel)

def bindings (helper : Helper) (values : List Atom) : Subst :=
  (helper.names.zip values).reverse

theorem helper_clause (helper : Helper) (values : List Atom)
    (length : values.length = helper.names.length) :
    clauses program helper.head values =
      [.evaluate (bindings helper values) (equation helper).body] :=
  PureData.named_equation_clause program helper.head (equation helper) helper.names values
    (by cases helper <;> rfl) (by cases helper <;> decide +kernel)
    (by cases helper <;> decide) length

theorem helper_raw (helper : Helper) (index : Nat) (bounded : index < helper.names.length) :
    argumentIsRaw program helper.head index = true := by
  have checked : (List.range helper.names.length).all
      (fun index => argumentIsRaw program helper.head index) = true := by
    cases helper <;> decide +kernel
  exact List.all_eq_true.mp checked index (List.mem_range.mpr bounded)

theorem helper_call (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program (bindings helper values) state (equation helper).body state answer) :
    PureReturns program caller state (a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return program caller (bindings helper values) state state
    helper.head arguments (equation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide)
    (by cases helper <;> decide +kernel)
  · intro index bounded
    apply helper_raw helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · rw [captured]
    exact helper_clause helper values length
  · exact returned

theorem helper_capture (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program [] state (a helper.head values) state answer) :
    PureReturns program caller state (a helper.head arguments) state answer := by
  apply PureData.raw_capture_returns program [] caller state state helper.head values arguments answer
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

theorem branch_returns (caller selected : Subst) (state : State)
    (expression value : Atom) (rows : SpaceSemantics.Cases) (body answer : Atom)
    (computed : PureReturns program caller state expression state value)
    (matched : SpaceSemantics.selectCase caller value rows = some (selected, body))
    (continued : PureReturns program selected state body state answer) :
    PureReturns program caller state
      (a "case" [expression, .expression (rows.map fun row => .expression [row.1, row.2])]) state answer :=
  case_returns program caller selected state state state expression value body answer _ rows
    (read_cases_encoded _) computed matched continued

def dataHeads : List String :=
  ["Some", "LCons", "RuleJobPremise", "RuleJobFrame", "PremiseState", "PremiseExpansion",
   "RuleJobExpansionInput", "RootGoal"]

theorem named_let_returns (target : Program) (caller : Subst) (state : State)
    (name : String) (expression value body answer : Atom)
    (fresh : caller.lookup name = none)
    (computed : PureReturns target caller state expression state value)
    (continued : PureReturns target ((name, value) :: caller) state body state answer) :
    PureReturns target caller state (a "let" [v name, expression, body]) state answer := by
  apply let_returns target caller ((name, value) :: caller) state state state
    (v name) expression body value answer computed
  · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, fresh]
  · exact continued

theorem template_constructor (head : String) (arguments : List Atom)
    (constructor : head ∈ dataHeads)
    (children : ∀ child ∈ arguments, PureData.Template program child) :
    PureData.Template program (a head arguments) := by
  simp only [dataHeads, List.mem_cons, List.not_mem_nil, or_false] at constructor
  rcases constructor with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals exact PureData.Template.constructor _ _ (by decide +kernel) (by decide) children

def obligationResult : Atom :=
  a "LCons" [a "RuleJobPremise" [v "reason"], v "tail"]

def obligationBody : Atom :=
  a "let" [v "tail", a "gslt:driver:job-obligations" [v "rest"], obligationResult]

def obligationCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", .symbol "LNil"), (a "LCons" [v "reason", v "rest"], obligationBody)]

theorem obligations_shape : (equation .obligations).body =
    a "case" [v "obligations", .expression (obligationCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem obligation_result_template : PureData.Template program obligationResult := by
  apply template_constructor _ _ (by simp [dataHeads])
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · apply template_constructor _ _ (by simp [dataHeads])
    intro child member
    rcases List.mem_singleton.mp member with rfl
    exact .captured _
  · exact .captured _

theorem obligations_returns (state : State) (obligations : List Execution.Obligation) :
    PureReturns program [] state
      (a "gslt:driver:job-obligations"
        [encoded (encodeList PremiseOperationsExecution.GeneralExecution.obligationTerm obligations)]) state
      (encoded (encodeList obligationTerm (obligations.map GeneralRuleJobExecution.Obligation.premise))) := by
  induction obligations with
  | nil =>
      let caller := bindings .obligations [encoded (.symbol "LNil")]
      apply helper_call .obligations [] state _ _ _ rfl (by rfl)
      rw [obligations_shape]
      apply branch_returns caller caller state _ (.symbol "LNil") obligationCases (.symbol "LNil") _
      · exact variable_returns program caller state "obligations"
      · simp [caller, bindings, Helper.names, obligationCases,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program caller state "LNil"
  | cons reason rest ih =>
      let value := encoded (encodeList PremiseOperationsExecution.GeneralExecution.obligationTerm (reason :: rest))
      let caller := bindings .obligations [value]
      let selected := [("rest", encoded (encodeList PremiseOperationsExecution.GeneralExecution.obligationTerm rest)),
        ("reason", encoded (PremiseOperationsExecution.GeneralExecution.obligationTerm reason))] ++ caller
      let tail := encoded (encodeList obligationTerm (rest.map GeneralRuleJobExecution.Obligation.premise))
      let continued := ("tail", tail) :: selected
      apply helper_call .obligations [] state _ [value] _ rfl (by
        simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]; rfl)
      rw [obligations_shape]
      apply branch_returns caller selected state _ value obligationCases obligationBody _
      · exact variable_returns program caller state "obligations"
      · simp [caller, selected, value, bindings, Helper.names, obligationCases,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, encoded]
      · unfold obligationBody
        apply named_let_returns program selected state "tail" _ tail
        · simp [selected, caller, bindings, Helper.names, Subst.lookup]
        · apply helper_capture .obligations selected state [v "rest"]
            [encoded (encodeList PremiseOperationsExecution.GeneralExecution.obligationTerm rest)] _ rfl
          · simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]
          · exact ih
        · simpa [obligationResult, continued, tail, selected, caller, bindings, Helper.names,
            obligationTerm, List.map_cons, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany,
            applySubst, applySubst.applySubstList, Subst.lookup] using
            PureData.template_return program continued state obligationResult obligation_result_template

theorem obligations_captured_returns (caller : Subst) (state : State)
    (obligations : List Execution.Obligation) (argument : Atom)
    (captured : applySubst caller argument =
      encoded (encodeList PremiseOperationsExecution.GeneralExecution.obligationTerm obligations)) :
    PureReturns program caller state (a "gslt:driver:job-obligations" [argument]) state
      (encoded (encodeList obligationTerm (obligations.map GeneralRuleJobExecution.Obligation.premise))) :=
  helper_capture .obligations caller state [argument] _ _ rfl (by simp [captured])
    (obligations_returns state obligations)


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralRuleDriverExecution
