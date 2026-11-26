import Mettapedia.Languages.MeTTa.PeTTa.BridgeTransport
import Mettapedia.Languages.MeTTa.PeTTa.AppendAgreement
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralRuleJobExecution
import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobReadoutCache
import Mettapedia.Languages.MeTTa.PeTTa.OperationalGSLT

/-!
# Pure replacement-decision reuse in the actual rule-job readout

The retained MeTTa program caches one replacement decision and reconstructs
each receipt from the current occurrence. Its key contains the complete
request projection, root goal and local target. Only an actual original
readout can introduce a retained decision.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralRuleReadoutCache

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program Equation)
open Eval
open scoped ProgramQuotation

open GeneralRuleJobExecution.ReadoutCache (target? localTarget reconstruct)

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_rule_readout_cache.metta"
    sha256 "aeec6c4a03d4071e1d4253a0e5093133962b44eceec49b53b4b3de0c4d9ac9a8"

def runtime : Program := RuleExecutionProgram.scopedProgram.append source.program

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
private abbrev number (value : Nat) : Atom := encoded (.natural value)

private inductive Helper where | key | target | rebuild | miss | step | loop | accounted | readouts
private def Helper.head : Helper → String
  | .key => "gslt:rule:job-readout-key"
  | .target => "gslt:rule:job-readout-target"
  | .rebuild => "gslt:rule:job-readout-rebuild"
  | .miss => "gslt:rule:job-readout-cache-miss"
  | .step => "gslt:rule:job-readout-cache-step"
  | .loop => "gslt:rule:job-readouts-loop"
  | .accounted => "gslt:rule:job-readouts-accounted"
  | .readouts => "gslt:rule:job-readouts"

private def Helper.names : Helper → List String
  | .key => ["request", "result"]
  | .target => ["readout"]
  | .rebuild => ["request", "result", "endpoint"]
  | .miss => ["request", "result", "key"]
  | .step => ["request", "result", "cache"]
  | .loop => ["request", "results", "cache"]
  | .accounted => ["request", "results"]
  | .readouts => ["request", "results"]

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
  have small : index = 0 ∨ index = 1 ∨ index = 2 := by
    cases helper <;> simp only [Helper.names, List.length_cons, List.length_nil] at bounded <;> omega
  rcases small with rfl | rfl | rfl <;> cases helper
  all_goals simp only [Helper.names, List.length_cons, List.length_nil] at bounded
  all_goals first | omega | decide +kernel

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
    exact helper_raw helper index (by omega)
  · cases helper <;> decide
  · have unchanged : applySubst [] = id := by
      funext value
      exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
    simpa only [unchanged, List.map_id] using captured.symm
  · exact returned

private theorem original_append_agreement :
    ProgramAgreementOn ScopedRuleJobReadoutExecution.executionHeads RuleExecutionProgram.scopedProgram runtime := by
  exact appended_program_agreement_of_all _ _ _ (by decide +kernel) (by decide +kernel)

theorem original_readout_agreement :
    ProgramAgreementOn ScopedRuleJobReadoutExecution.executionHeads ScopedRuleJobReadoutExecution.runtime runtime := by
  have previous := PremiseOperationsExecution.GeneralExecution.CompletedAssembly.readout_agreement
  exact ⟨fun head supported => (previous.dispatch head supported).trans
      (original_append_agreement.dispatch head supported),
    fun head index supported => (previous.demand head index supported).trans
      (original_append_agreement.demand head index supported),
    fun head values supported => (previous.bodies head values supported).trans
      (original_append_agreement.bodies head values supported)⟩

def requestTerm (request : GeneralRuleJobExecution.Request) : Term :=
  ScopedRuleJobReadoutExecution.requestProjectionTerm request (GeneralRuleJobObservation.requestFootprint request)

def keyTerm (request : Term) (goal localTarget : Term) : Term :=
  .application "ReadoutKey" [request, goal, localTarget]

theorem keyTerm_eq_iff (request goal target request' goal' target' : Term) :
    keyTerm request goal target = keyTerm request' goal' target' ↔
      request = request' ∧ goal = goal' ∧ target = target' := by
  simp [keyTerm]

def resultKey (request : GeneralRuleJobExecution.Request) (localTarget : Pattern) : Term :=
  keyTerm (requestTerm request) (PremiseOperationsExecution.GeneralExecution.goalTerm request.goal)
    (InferenceCettaWire.encodePattern localTarget)

theorem resultKey_injective (request : GeneralRuleJobExecution.Request) :
    Function.Injective (resultKey request) := by
  intro first second same
  have equality := (keyTerm_eq_iff _ _ _ _ _ _).mp same
  exact InferenceCettaWire.encodePattern_injective equality.2.2

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

private theorem bool_if_returns (caller : Subst) (state : State)
    (condition : Atom) (value : Bool) (yes no answer : Atom)
    (tested : PureReturns runtime caller state condition state (Effects.boolean value))
    (continued : PureReturns runtime caller state (if value then yes else no) state answer) :
    PureReturns runtime caller state (a "if" [condition, yes, no]) state answer := by
  apply if_returns runtime caller state state state condition (Effects.boolean value) yes no answer tested
  have boolean_same : (Effects.boolean value == Effects.boolean true) = value := by
    cases value <;> decide +kernel
  simpa only [boolean_same] using continued

private def dataHeads : List String :=
  ["ReadoutKey", "ReadoutUncacheable", "ReadoutRebuild", "ReadoutCache", "ReadoutCached", "ReadoutBatch",
    "Some", "RuleJobReceipt", "LCons"]

private theorem data_template (head : String) (arguments : List Atom) (member : head ∈ dataHeads)
    (children : ∀ child ∈ arguments, PureData.Template runtime child) :
    PureData.Template runtime (a head arguments) := by
  apply PureData.Template.constructor head arguments _ _ children
  · simp only [dataHeads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · simp only [dataHeads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem data_variables_template (head : String) (names : List String) (member : head ∈ dataHeads) :
    PureData.Template runtime (a head (names.map v)) := by
  apply data_template head _ member
  intro child member
  obtain ⟨name, _, rfl⟩ := List.mem_map.mp member
  exact .captured name

private def keyBody : Atom := a "ReadoutKey" [v "request", v "goal", v "localTarget"]
private def keyCases : SpaceSemantics.Cases :=
  [(a "PremiseResult" [v "goal", a "RootAnswer" [v "trace", v "captured", v "completed", v "history", v "localTarget"]], keyBody),
    (v "____________", a "ReadoutUncacheable" [v "request", v "result"])]

private theorem key_shape : (equation .key).body =
    a "case" [v "result", .expression (keyCases.map fun row => .expression [row.1, row.2])] := rfl

theorem key_returns (state : State) (request : GeneralRuleJobExecution.Request)
    (result : GeneralPremise.Execution.Result request.environment request.goal) :
    PureReturns runtime [] state (a Helper.key.head [encoded (requestTerm request),
      encoded (PremiseOperationsExecution.GeneralExecution.resultTerm result)]) state
      (encoded (resultKey request (localTarget result))) := by
  cases result with
  | root trace captured completed history target valid =>
    let values := [encoded (requestTerm request), encoded (PremiseOperationsExecution.GeneralExecution.resultTerm
      (GeneralPremise.Execution.Result.root trace captured completed history target valid))]
    let caller := bindings .key values
    let selected : Subst :=
      [("localTarget", encoded (InferenceCettaWire.encodePattern target)),
       ("history", encoded (PremiseOperationsExecution.GeneralExecution.eventsTerm history)),
       ("completed", encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm completed)),
       ("captured", encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm captured)),
       ("trace", encoded (PremiseOperationsExecution.GeneralExecution.traceTerm trace)),
       ("goal", encoded (PremiseOperationsExecution.GeneralExecution.goalTerm request.goal))] ++ caller
    apply helper_call .key [] state _ values _ rfl (by simp [values]; rfl)
    rw [key_shape]
    apply branch_returns caller selected state _ values[1]! keyCases keyBody
    · simpa [caller, bindings, Helper.names, values, applySubst, Subst.lookup] using
        variable_returns runtime caller state "result"
    · simp [caller, selected, values, bindings, Helper.names, keyCases,
        PremiseOperationsExecution.GeneralExecution.resultTerm, SpaceSemantics.selectCase,
        SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, GeneralRuleJobExecution.Request.goal]
    · simpa [keyBody, selected, caller, bindings, Helper.names, values, resultKey, keyTerm,
        localTarget, applySubst, applySubst.applySubstList, Subst.lookup,
        CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        PureData.template_return runtime selected state keyBody
          (data_variables_template "ReadoutKey" ["request", "goal", "localTarget"] (by simp [dataHeads]))

private def targetCases : SpaceSemantics.Cases :=
  [(a "Some" [a "RuleJobReceipt" [v "job", v "trace", v "captured", v "completed", v "history", v "localTarget", v "target"]],
      a "Some" [v "target"]), (v "____________", .symbol "None")]

private theorem target_shape : (equation .target).body =
    a "case" [v "readout", .expression (targetCases.map fun row => .expression [row.1, row.2])] := rfl

theorem target_returns (state : State) (receipt : Option GeneralRuleJobs.Receipt) :
    PureReturns runtime [] state
      (a Helper.target.head [encoded (encodeOption ScopedRuleJobReadoutExecution.receiptTerm receipt)]) state
      (encoded (encodeOption InferenceCettaWire.encodePattern (receipt.map GeneralRuleJobs.Receipt.target))) := by
  cases receipt with
  | none =>
    let caller := bindings .target [encoded (encodeOption ScopedRuleJobReadoutExecution.receiptTerm none)]
    apply helper_call .target [] state _ [.symbol "None"] _ rfl (by rfl)
    rw [target_shape]
    apply branch_returns caller (("____________", .symbol "None") :: caller) state _ (.symbol "None") targetCases (.symbol "None")
    · simpa [caller, bindings, Helper.names, applySubst, Subst.lookup, encoded, CettaWireAtom.encode] using variable_returns runtime caller state "readout"
    · simp [caller, bindings, Helper.names, targetCases, SpaceSemantics.selectCase,
        SpaceSemantics.matchValue, matchAtom, Subst.lookup]
    · exact symbol_returns runtime _ state "None"
  | some receipt =>
    let value := encoded (encodeOption ScopedRuleJobReadoutExecution.receiptTerm (some receipt))
    let caller := bindings .target [value]
    let selected : Subst :=
      [("target", encoded (InferenceCettaWire.encodePattern receipt.target)),
       ("localTarget", encoded (InferenceCettaWire.encodePattern receipt.localTarget)),
       ("history", encoded (PremiseOperationsExecution.GeneralExecution.eventsTerm receipt.premiseHistory)),
       ("completed", encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm receipt.completed)),
       ("captured", encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm receipt.captured)),
       ("trace", encoded (PremiseOperationsExecution.GeneralExecution.traceTerm receipt.matcherTrace)),
       ("job", encoded (ScopedRuleJobReadoutExecution.jobTerm receipt.job))] ++ caller
    apply helper_call .target [] state _ [value] _ rfl (by simp [value])
    rw [target_shape]
    apply branch_returns caller selected state _ value targetCases (a "Some" [v "target"])
    · simpa [caller, bindings, Helper.names, applySubst, Subst.lookup] using variable_returns runtime caller state "readout"
    · simp [caller, selected, value, bindings, Helper.names, targetCases,
        ScopedRuleJobReadoutExecution.receiptTerm, encodeOption, SpaceSemantics.selectCase,
        SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
        CettaWireAtom.encode, CettaWireAtom.encodeMany]
    · simpa [selected, applySubst, applySubst.applySubstList, Subst.lookup,
        CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        PureData.template_return runtime selected state (a "Some" [v "target"])
          (data_variables_template "Some" ["target"] (by simp [dataHeads]))

def readoutTerm (request : GeneralRuleJobExecution.Request)
    (result : GeneralPremise.Execution.Result request.environment request.goal) (target : Option Pattern) : Term :=
  encodeOption ScopedRuleJobReadoutExecution.receiptTerm (reconstruct request result target)

theorem original_readout_factor (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (result : GeneralPremise.Execution.Result request.environment request.goal) :
    GeneralRuleJobObservation.rootReadoutTerm request licensed result =
      readoutTerm request result (target? request (localTarget result)) := by
  rw [readoutTerm, ← GeneralRuleJobExecution.ReadoutCache.rootProjection_factor request licensed result]
  unfold GeneralRuleJobObservation.rootReadoutTerm
  cases GeneralRuleJobExecution.rootProjection request licensed result <;> rfl

private def rebuildBody : Atom :=
  a "Some" [a "RuleJobReceipt" [v "job", v "trace", v "captured", v "completed", v "history", v "localTarget", v "target"]]
private def rebuildCases : SpaceSemantics.Cases :=
  [(a "ReadoutRebuild"
      [a "RuleJobRequestProjection" [v "environment", v "permissions", v "bound", v "expected", v "source", v "job"],
       a "PremiseResult" [v "goal", a "RootAnswer" [v "trace", v "captured", v "completed", v "history", v "localTarget"]],
       a "Some" [v "target"]], rebuildBody),
    (v "____________", .symbol "None")]
private theorem rebuild_shape : (equation .rebuild).body =
    a "case" [a "ReadoutRebuild" [v "request", v "result", v "endpoint"],
      .expression (rebuildCases.map fun row => .expression [row.1, row.2])] := rfl

private theorem rebuild_template : PureData.Template runtime rebuildBody := by
  apply data_template "Some" _ (by simp [dataHeads])
  intro child member
  simp only [List.mem_singleton] at member
  subst child
  exact data_variables_template "RuleJobReceipt"
    ["job", "trace", "captured", "completed", "history", "localTarget", "target"] (by simp [dataHeads])

theorem rebuild_returns (state : State) (request : GeneralRuleJobExecution.Request)
    (result : GeneralPremise.Execution.Result request.environment request.goal) (endpoint : Option Pattern) :
    PureReturns runtime [] state (a Helper.rebuild.head
      [encoded (requestTerm request), encoded (PremiseOperationsExecution.GeneralExecution.resultTerm result),
       encoded (encodeOption InferenceCettaWire.encodePattern endpoint)]) state
      (encoded (readoutTerm request result endpoint)) := by
  cases result with
  | root trace captured completed history localTarget valid =>
    let result := GeneralPremise.Execution.Result.root trace captured completed history localTarget valid
    let values := [encoded (requestTerm request), encoded (PremiseOperationsExecution.GeneralExecution.resultTerm result),
      encoded (encodeOption InferenceCettaWire.encodePattern endpoint)]
    let caller := bindings .rebuild values
    let value := a "ReadoutRebuild" values
    have input : PureReturns runtime caller state
        (a "ReadoutRebuild" [v "request", v "result", v "endpoint"]) state value := by
      simpa [caller, values, value, bindings, Helper.names, applySubst, applySubst.applySubstList,
        Subst.lookup] using PureData.template_return runtime caller state
          (a "ReadoutRebuild" [v "request", v "result", v "endpoint"])
          (data_variables_template "ReadoutRebuild" ["request", "result", "endpoint"] (by simp [dataHeads]))
    apply helper_call .rebuild [] state _ values _ rfl (by simp [values]; rfl)
    rw [rebuild_shape]
    cases endpoint with
    | none =>
      apply branch_returns caller (("____________", value) :: caller) state _ value rebuildCases (.symbol "None") _ input
      · simp [value, values, caller, bindings, Helper.names, rebuildCases, result, requestTerm,
          ScopedRuleJobReadoutExecution.requestProjectionTerm, PremiseOperationsExecution.GeneralExecution.resultTerm,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany]
      · exact symbol_returns runtime _ state "None"
    | some endpoint =>
      let selected :=
        [("environment", encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm request.environment
            (request.environment.free.entriesOn (GeneralRuleJobObservation.requestFootprint request)))),
         ("permissions", encoded (InferenceCettaWire.ContextObservation.permissionsTerm request.plan.permissions.sites)),
         ("bound", encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm request.bound)),
         ("expected", encoded (InferenceCettaWire.AuthoredRule.typeTerm request.expected)),
         ("source", encoded (InferenceCettaWire.encodePattern request.source)),
         ("job", encoded (ScopedRuleJobReadoutExecution.jobTerm request.job)),
         ("goal", encoded (PremiseOperationsExecution.GeneralExecution.goalTerm request.goal)),
         ("trace", encoded (PremiseOperationsExecution.GeneralExecution.traceTerm trace)),
         ("captured", encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm captured)),
         ("completed", encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm completed)),
         ("history", encoded (PremiseOperationsExecution.GeneralExecution.eventsTerm history)),
         ("localTarget", encoded (InferenceCettaWire.encodePattern localTarget)),
         ("target", encoded (InferenceCettaWire.encodePattern endpoint))].reverse ++ caller
      apply branch_returns caller selected state _ value rebuildCases rebuildBody _ input
      · simp [value, values, caller, selected, bindings, Helper.names, rebuildCases, result, requestTerm,
          ScopedRuleJobReadoutExecution.requestProjectionTerm, PremiseOperationsExecution.GeneralExecution.resultTerm,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          GeneralRuleJobExecution.Request.goal]
      · simpa [rebuildBody, selected, applySubst, applySubst.applySubstList, Subst.lookup,
          CettaWireAtom.encode, CettaWireAtom.encodeMany, readoutTerm, reconstruct, result,
          ScopedRuleJobReadoutExecution.receiptTerm] using
          PureData.template_return runtime selected state rebuildBody rebuild_template

theorem original_returns (caller : Subst) (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (result : GeneralPremise.Execution.Result request.environment request.goal)
    (member : result ∈ (GeneralPremise.Execution.run request.environment request.goal fuel
      (GeneralPremise.Execution.start request.environment request.goal)).answers)
    (requestName resultName : String)
    (captured : [v requestName, v resultName].map (applySubst caller) =
      [encoded (requestTerm request), encoded (PremiseOperationsExecution.GeneralExecution.resultTerm result)]) :
    PureReturns runtime caller state (a "gslt:rule:job-finish-root" [v requestName, v resultName]) state
      (encoded (readoutTerm request result (target? request (localTarget result)))) := by
  rw [← original_readout_factor request licensed result]
  cases result with
  | root trace initial completed history target valid =>
      exact ScopedRuleJobReadoutExecution.finish_root_run_captured_variables_returns_in_extension
        runtime original_readout_agreement caller state request licensed fuel trace initial completed history target
        valid member requestName resultName captured

/-- The original readout earns the independent PeTTa native contract before
its endpoint may be retained. The evidence records its actual output value. -/
def original_native_certificate (caller : Subst) (state : State)
    (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (result : GeneralPremise.Execution.Result request.environment request.goal)
    (member : result ∈ (GeneralPremise.Execution.run request.environment request.goal fuel
      (GeneralPremise.Execution.start request.environment request.goal)).answers)
    (requestName resultName : String)
    (captured : [v requestName, v resultName].map (applySubst caller) =
      [encoded (requestTerm request), encoded (PremiseOperationsExecution.GeneralExecution.resultTerm result)]) :
    (OperationalGSLT.pureSingletonOutput runtime).Family
      { state := state, control := .evaluate caller (a "gslt:rule:job-finish-root" [v requestName, v resultName]) } :=
  OperationalGSLT.pureSingleton_of_returns runtime caller state _ _
    (original_returns caller state request licensed fuel result member requestName resultName captured)

def cacheTerm (request : GeneralRuleJobExecution.Request) :
    Option (List.MemoizedMap.Entry Pattern (Option Pattern)) → Term
  | none => .symbol "None"
  | some entry => .application "ReadoutCache"
      [resultKey request entry.key, encodeOption InferenceCettaWire.encodePattern entry.value]

private def cachedTerm (readout cache : Term) (calls : Nat) : Term :=
  .application "ReadoutCached" [readout, cache, .natural calls]

private def missData : Atom :=
  a "ReadoutCached" [v "readout", a "ReadoutCache" [v "key", v "endpoint"], number 1]
private def missBody : Atom :=
  a "let" [v "readout", a "gslt:rule:job-finish-root" [v "request", v "result"],
    a "let" [v "endpoint", a "gslt:rule:job-readout-target" [v "readout"], missData]]
private theorem miss_shape : (equation .miss).body = missBody := rfl

private theorem miss_template : PureData.Template runtime missData := by
  apply data_template "ReadoutCached" _ (by simp [dataHeads])
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .captured _
  · exact data_variables_template "ReadoutCache" ["key", "endpoint"] (by simp [dataHeads])
  · exact .grounded _

theorem miss_returns (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (result : GeneralPremise.Execution.Result request.environment request.goal)
    (member : result ∈ (GeneralPremise.Execution.run request.environment request.goal fuel
      (GeneralPremise.Execution.start request.environment request.goal)).answers) :
    PureReturns runtime [] state (a Helper.miss.head
      [encoded (requestTerm request), encoded (PremiseOperationsExecution.GeneralExecution.resultTerm result),
       encoded (resultKey request (localTarget result))]) state
      (encoded (cachedTerm (readoutTerm request result (target? request (localTarget result)))
        (cacheTerm request (some ⟨localTarget result, target? request (localTarget result)⟩)) 1)) := by
  let target := target? request (localTarget result)
  let readout := readoutTerm request result target
  let values := [encoded (requestTerm request), encoded (PremiseOperationsExecution.GeneralExecution.resultTerm result),
    encoded (resultKey request (localTarget result))]
  let caller := bindings .miss values
  let next := ("readout", encoded readout) :: caller
  let final := ("endpoint", encoded (encodeOption InferenceCettaWire.encodePattern target)) :: next
  apply helper_call .miss [] state _ values _ rfl (by simp [values])
  rw [miss_shape]
  unfold missBody
  apply named_let_returns caller state "readout" _ (encoded readout) _ _
  · simp [caller, values, bindings, Helper.names, Subst.lookup]
  · exact OperationalGSLT.pureSingleton_returns runtime caller state _
      (original_native_certificate caller state request licensed fuel result member "request" "result"
        (by simp [caller, bindings, Helper.names, values, applySubst, Subst.lookup]))
  · apply named_let_returns next state "endpoint" _
      (encoded (encodeOption InferenceCettaWire.encodePattern target)) _ _
    · simp [next, caller, values, bindings, Helper.names, Subst.lookup]
    · have returned := target_returns state (reconstruct request result target)
      rw [GeneralRuleJobExecution.ReadoutCache.reconstruction_target] at returned
      exact helper_capture .target next state [v "readout"] [encoded readout] _ rfl
        (by simp [next, applySubst, Subst.lookup]) returned
    · simpa [missData, final, next, caller, bindings, Helper.names, values, cacheTerm, cachedTerm,
        readout, target, applySubst, applySubst.applySubstList, Subst.lookup,
        CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        PureData.template_return runtime final state missData miss_template


private def stepMiss : Atom := a Helper.miss.head [v "request", v "result", v "key"]
private def stepHitData : Atom := a "ReadoutCached" [v "readout", v "cache", number 0]
private def stepHit : Atom := a "let" [v "readout",
  a Helper.rebuild.head [v "request", v "result", v "endpoint"], stepHitData]
private def stepChoice : Atom := a "if" [a "==" [v "key", v "oldKey"], stepHit, stepMiss]
private def stepCases : SpaceSemantics.Cases :=
  [(a "ReadoutCache" [v "oldKey", v "endpoint"], stepChoice), (v "_________", stepMiss)]
private theorem step_shape : (equation .step).body =
    a "let" [v "key", a Helper.key.head [v "request", v "result"],
      a "case" [v "cache", .expression (stepCases.map fun row => .expression [row.1, row.2])]] := rfl
private theorem stepHit_template : PureData.Template runtime stepHitData := by
  apply data_template "ReadoutCached" _ (by simp [dataHeads])
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .captured _
  · exact .captured _
  · exact .grounded _

theorem cache_step_returns (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (result : GeneralPremise.Execution.Result request.environment request.goal)
    (member : result ∈ (GeneralPremise.Execution.run request.environment request.goal fuel
      (GeneralPremise.Execution.start request.environment request.goal)).answers)
    (cache : Option (List.MemoizedMap.Entry Pattern (Option Pattern))) :
    PureReturns runtime [] state (a Helper.step.head
      [encoded (requestTerm request), encoded (PremiseOperationsExecution.GeneralExecution.resultTerm result),
       encoded (cacheTerm request cache)]) state
      (encoded (cachedTerm
        (readoutTerm request result (List.MemoizedMap.access (target? request) (localTarget result) cache).1)
        (cacheTerm request (some (List.MemoizedMap.access (target? request) (localTarget result) cache).2.1))
        (List.MemoizedMap.access (target? request) (localTarget result) cache).2.2)) := by
  let values := [encoded (requestTerm request), encoded (PremiseOperationsExecution.GeneralExecution.resultTerm result),
    encoded (cacheTerm request cache)]
  let caller := bindings .step values
  let next := ("key", encoded (resultKey request (localTarget result))) :: caller
  apply helper_call .step [] state _ values _ rfl (by simp [values])
  rw [step_shape]
  apply named_let_returns caller state "key" _ (encoded (resultKey request (localTarget result))) _ _
  · simp [caller, values, bindings, Helper.names, Subst.lookup]
  · exact helper_capture .key caller state [v "request", v "result"] _ _ rfl
      (by simp [caller, values, bindings, Helper.names, applySubst, Subst.lookup])
      (key_returns state request result)
  · have readCache : PureReturns runtime next state (v "cache") state (encoded (cacheTerm request cache)) := by
      simpa [next, caller, values, bindings, Helper.names, applySubst, Subst.lookup]
        using variable_returns runtime next state "cache"
    cases cache with
    | none =>
      let selected := ("_________", encoded (cacheTerm request none)) :: next
      apply branch_returns next selected state _ _ stepCases stepMiss _ readCache
      · simp [selected, next, caller, values, bindings, Helper.names, stepCases, cacheTerm,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, Subst.lookup, CettaWireAtom.encode]
      · exact helper_capture .miss selected state [v "request", v "result", v "key"] _ _ rfl
          (by simp [selected, next, caller, values, bindings, Helper.names, applySubst, Subst.lookup])
          (miss_returns state request licensed fuel result member)
    | some entry =>
      let selected := ("endpoint", encoded (encodeOption InferenceCettaWire.encodePattern entry.value)) ::
        ("oldKey", encoded (resultKey request entry.key)) :: next
      apply branch_returns next selected state _ _ stepCases stepChoice _ readCache
      · simp [selected, next, caller, values, bindings, Helper.names, stepCases, cacheTerm,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany]
      · unfold stepChoice
        apply bool_if_returns selected state _ (decide (resultKey request (localTarget result) = resultKey request entry.key))
        · exact CettaWireAtom.equality_captured_returns runtime selected state _ _ "key" "oldKey"
            (by simp [selected, next, caller, values, bindings, Helper.names, applySubst, Subst.lookup])
            (by simp [selected, next, caller, values, bindings, Helper.names, applySubst, Subst.lookup])
        · by_cases hit : entry.key = localTarget result
          · have same : resultKey request (localTarget result) = resultKey request entry.key := by rw [hit]
            simp only [same, decide_true, ↓reduceIte]
            unfold stepHit
            apply named_let_returns selected state "readout" _ (encoded (readoutTerm request result entry.value)) _ _
            · simp [selected, next, caller, values, bindings, Helper.names, Subst.lookup]
            · exact helper_capture .rebuild selected state [v "request", v "result", v "endpoint"] _ _ rfl
                (by simp [selected, next, caller, values, bindings, Helper.names, applySubst, Subst.lookup])
                (rebuild_returns state request result entry.value)
            · simpa [stepHitData, selected, next, caller, values, bindings, Helper.names, applySubst,
                applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                cachedTerm, List.MemoizedMap.access, hit] using
                PureData.template_return runtime (("readout", encoded (readoutTerm request result entry.value)) :: selected)
                  state stepHitData stepHit_template
          · have different : resultKey request (localTarget result) ≠ resultKey request entry.key := by
              intro same
              exact hit ((resultKey_injective request same).symm)
            simp only [different, decide_false, Bool.false_eq_true, ↓reduceIte]
            simpa only [List.MemoizedMap.access, hit, ↓reduceIte, stepMiss] using
              helper_capture .miss selected state [v "request", v "result", v "key"] _ _ rfl
                (by simp [selected, next, caller, values, bindings, Helper.names, applySubst, Subst.lookup])
                (miss_returns state request licensed fuel result member)


def resultsTerm {request : GeneralRuleJobExecution.Request}
    (results : List (GeneralPremise.Execution.Result request.environment request.goal)) : Term :=
  encodeList PremiseOperationsExecution.GeneralExecution.resultTerm results

def readoutsTerm (readouts : List (Option GeneralRuleJobs.Receipt)) : Term :=
  encodeList (encodeOption ScopedRuleJobReadoutExecution.receiptTerm) readouts

def batchTerm (readouts : List (Option GeneralRuleJobs.Receipt)) (calls : Nat) : Term :=
  .application "ReadoutBatch" [readoutsTerm readouts, .natural calls]

def cachedRun (request : GeneralRuleJobExecution.Request)
    (results : List (GeneralPremise.Execution.Result request.environment request.goal))
    (cache : Option (List.MemoizedMap.Entry Pattern (Option Pattern))) :=
  List.MemoizedMap.run localTarget (target? request) (reconstruct request) results cache

private def loopData : Atom := a "ReadoutBatch" [a "LCons" [v "readout", v "tail"], v "calls"]
private def loopLast : Atom := a "let" [v "calls", a "+" [v "miss", v "later"], loopData]
private def loopMiddle : Atom := a "let" [a "ReadoutBatch" [v "tail", v "later"],
  a Helper.loop.head [v "request", v "rest", v "next"], loopLast]
private def loopBody : Atom := a "let" [a "ReadoutCached" [v "readout", v "next", v "miss"],
  a Helper.step.head [v "request", v "result", v "cache"], loopMiddle]
private def loopCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", a "ReadoutBatch" [.symbol "LNil", number 0]),
   (a "LCons" [v "result", v "rest"], loopBody)]
private theorem loop_shape : (equation .loop).body =
    a "case" [v "results", .expression (loopCases.map fun row => .expression [row.1, row.2])] := rfl

private theorem loopData_template : PureData.Template runtime loopData := by
  apply data_template "ReadoutBatch" _ (by simp [dataHeads])
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact data_variables_template "LCons" ["readout", "tail"] (by simp [dataHeads])
  · exact .captured _

private theorem addition_returns (caller : Subst) (state : State) (left right : Nat)
    (leftName rightName : String)
    (leftCaptured : applySubst caller (v leftName) = number left)
    (rightCaptured : applySubst caller (v rightName) = number right) :
    PureReturns runtime caller state (a "+" [v leftName, v rightName]) state (number (left + right)) := by
  apply native_variable_call_returns runtime caller state state "+" [leftName, rightName] _
    (by decide) (by decide) _ (by decide)
  simp [leftCaptured, rightCaptured, CettaWireAtom.encode, StdLib.integer_addition]

theorem loop_returns (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (results : List (GeneralPremise.Execution.Result request.environment request.goal))
    (members : ∀ result ∈ results, result ∈ (GeneralPremise.Execution.run request.environment request.goal fuel
      (GeneralPremise.Execution.start request.environment request.goal)).answers)
    (cache : Option (List.MemoizedMap.Entry Pattern (Option Pattern))) :
    PureReturns runtime [] state (a Helper.loop.head
      [encoded (requestTerm request), encoded (resultsTerm results), encoded (cacheTerm request cache)]) state
      (encoded (batchTerm (cachedRun request results cache).1 (cachedRun request results cache).2.2)) := by
  induction results generalizing cache with
  | nil =>
    let values := [encoded (requestTerm request), encoded (resultsTerm (request := request) []),
      encoded (cacheTerm request cache)]
    let caller := bindings .loop values
    apply helper_call .loop [] state _ values _ rfl (by simp [values])
    rw [loop_shape]
    apply branch_returns caller caller state _ (.symbol "LNil") loopCases
      (a "ReadoutBatch" [.symbol "LNil", number 0]) _
    · simpa [caller, values, bindings, Helper.names, resultsTerm, applySubst, Subst.lookup,
        CettaWireAtom.encode] using variable_returns runtime caller state "results"
    · simp [loopCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
    · have template : PureData.Template runtime (a "ReadoutBatch" [.symbol "LNil", number 0]) := by
        apply data_template "ReadoutBatch" _ (by simp [dataHeads])
        intro child member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact .symbol _
        · exact .grounded _
      simpa [batchTerm, readoutsTerm, cachedRun, List.MemoizedMap.run, applySubst,
        applySubst.applySubstList, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        PureData.template_return runtime caller state (a "ReadoutBatch" [.symbol "LNil", number 0]) template
  | cons result rest ih =>
    let access := List.MemoizedMap.access (target? request) (localTarget result) cache
    let tail := cachedRun request rest (some access.2.1)
    let values := [encoded (requestTerm request), encoded (resultsTerm (result :: rest)),
      encoded (cacheTerm request cache)]
    let caller := bindings .loop values
    let selected := ("rest", encoded (resultsTerm rest)) ::
      ("result", encoded (PremiseOperationsExecution.GeneralExecution.resultTerm result)) :: caller
    let next := ("miss", number access.2.2) :: ("next", encoded (cacheTerm request (some access.2.1))) ::
      ("readout", encoded (readoutTerm request result access.1)) :: selected
    let later := ("later", number tail.2.2) :: ("tail", encoded (readoutsTerm tail.1)) :: next
    have member := members result (by simp)
    have remaining := ih (fun item present => members item (by simp [present])) (some access.2.1)
    apply helper_call .loop [] state _ values _ rfl (by simp [values])
    rw [loop_shape]
    apply branch_returns caller selected state _ (encoded (resultsTerm (result :: rest))) loopCases loopBody _
    · simpa [caller, values, bindings, Helper.names, applySubst, Subst.lookup]
        using variable_returns runtime caller state "results"
    · simp [loopCases, selected, caller, values, bindings, Helper.names, resultsTerm,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        matchAtom, Subst.lookup, CettaWireAtom.encode]
    · unfold loopBody
      apply let_returns runtime selected next state state state _ _ _
        (encoded (cachedTerm (readoutTerm request result access.1) (cacheTerm request (some access.2.1)) access.2.2)) _
      · exact helper_capture .step selected state [v "request", v "result", v "cache"] _ _ rfl
          (by simp [selected, caller, values, bindings, Helper.names, applySubst, Subst.lookup])
          (cache_step_returns state request licensed fuel result member cache)
      · simp [next, selected, caller, values, bindings, Helper.names, cachedTerm,
          SpaceSemantics.matchBinding, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany]
      · unfold loopMiddle
        apply let_returns runtime next later state state state _ _ _ (encoded (batchTerm tail.1 tail.2.2)) _
        · exact helper_capture .loop next state [v "request", v "rest", v "next"] _ _ rfl
            (by simp [next, selected, caller, values, bindings, Helper.names, applySubst, Subst.lookup]) remaining
        · simp [later, next, selected, caller, values, bindings, Helper.names, batchTerm,
            SpaceSemantics.matchBinding, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
            matchAtom, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany]
        · unfold loopLast
          apply named_let_returns later state "calls" _ (number (access.2.2 + tail.2.2)) _ _
          · simp [later, next, selected, caller, values, bindings, Helper.names, Subst.lookup]
          · exact addition_returns later state _ _ "miss" "later"
              (by simp [later, next, applySubst, Subst.lookup])
              (by simp [later, applySubst, Subst.lookup])
          · simpa [loopData, later, next, selected, caller, values, bindings, Helper.names,
              applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              batchTerm, readoutsTerm, readoutTerm, cachedRun, List.MemoizedMap.run, access, tail] using
              PureData.template_return runtime (("calls", number (access.2.2 + tail.2.2)) :: later)
                state loopData loopData_template


private theorem accounted_shape : (equation .accounted).body =
    a Helper.loop.head [v "request", v "results", .symbol "None"] := rfl
private theorem readouts_shape : (equation .readouts).body =
    a "let" [a "ReadoutBatch" [v "readouts", v "calls"],
      a Helper.accounted.head [v "request", v "results"], v "readouts"] := rfl

theorem accounted_returns (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (results : List (GeneralPremise.Execution.Result request.environment request.goal))
    (members : ∀ result ∈ results, result ∈ (GeneralPremise.Execution.run request.environment request.goal fuel
      (GeneralPremise.Execution.start request.environment request.goal)).answers) :
    PureReturns runtime [] state (a Helper.accounted.head [encoded (requestTerm request), encoded (resultsTerm results)])
      state (encoded (batchTerm (cachedRun request results none).1 (cachedRun request results none).2.2)) := by
  let values := [encoded (requestTerm request), encoded (resultsTerm results)]
  let caller := bindings .accounted values
  apply helper_call .accounted [] state _ values _ rfl (by simp [values])
  rw [accounted_shape]
  exact helper_capture .loop caller state [v "request", v "results", .symbol "None"] _ _ rfl
    (by simp [caller, values, bindings, Helper.names, applySubst, Subst.lookup, cacheTerm, CettaWireAtom.encode])
    (loop_returns state request licensed fuel results members none)

theorem readouts_returns (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (results : List (GeneralPremise.Execution.Result request.environment request.goal))
    (members : ∀ result ∈ results, result ∈ (GeneralPremise.Execution.run request.environment request.goal fuel
      (GeneralPremise.Execution.start request.environment request.goal)).answers) :
    PureReturns runtime [] state (a Helper.readouts.head [encoded (requestTerm request), encoded (resultsTerm results)])
      state (encoded (readoutsTerm (cachedRun request results none).1)) := by
  let values := [encoded (requestTerm request), encoded (resultsTerm results)]
  let caller := bindings .readouts values
  let selected := ("calls", number (cachedRun request results none).2.2) ::
    ("readouts", encoded (readoutsTerm (cachedRun request results none).1)) :: caller
  apply helper_call .readouts [] state _ values _ rfl (by simp [values])
  rw [readouts_shape]
  apply let_returns runtime caller selected state state state _ _ _
    (encoded (batchTerm (cachedRun request results none).1 (cachedRun request results none).2.2)) _
  · exact helper_capture .accounted caller state [v "request", v "results"] _ _ rfl
      (by simp [caller, values, bindings, Helper.names, applySubst, Subst.lookup])
      (accounted_returns state request licensed fuel results members)
  · simp [selected, caller, values, bindings, Helper.names, batchTerm,
      SpaceSemantics.matchBinding, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  · simpa [selected, applySubst, Subst.lookup] using variable_returns runtime selected state "readouts"

theorem cached_readouts_exact (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (results : List (GeneralPremise.Execution.Result request.environment request.goal)) :
    readoutsTerm (cachedRun request results none).1 =
      encodeList (GeneralRuleJobObservation.rootReadoutTerm request licensed) results := by
  change readoutsTerm (GeneralRuleJobExecution.ReadoutCache.run request results).1 = _
  rw [GeneralRuleJobExecution.ReadoutCache.run_exact request licensed results]
  unfold readoutsTerm
  rw [encodeList_map]
  apply congrArg (fun encode => encodeList encode results)
  funext result
  unfold GeneralRuleJobObservation.rootReadoutTerm
  simp only [Function.comp_apply]
  cases GeneralRuleJobExecution.rootProjection request licensed result <;> rfl

theorem job_readouts_returns (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (results : List (GeneralPremise.Execution.Result request.environment request.goal))
    (members : ∀ result ∈ results, result ∈ (GeneralPremise.Execution.run request.environment request.goal fuel
      (GeneralPremise.Execution.start request.environment request.goal)).answers) :
    PureReturns runtime [] state
      (a "gslt:rule:job-readouts" [encoded (requestTerm request), encoded (resultsTerm results)]) state
      (encoded (encodeList (GeneralRuleJobObservation.rootReadoutTerm request licensed) results)) := by
  rw [← cached_readouts_exact request licensed results]
  exact readouts_returns state request licensed fuel results members

theorem job_readouts_accounted_returns (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (results : List (GeneralPremise.Execution.Result request.environment request.goal))
    (members : ∀ result ∈ results, result ∈ (GeneralPremise.Execution.run request.environment request.goal fuel
      (GeneralPremise.Execution.start request.environment request.goal)).answers) :
    PureReturns runtime [] state
      (a "gslt:rule:job-readouts-accounted" [encoded (requestTerm request), encoded (resultsTerm results)]) state
      (encoded (.application "ReadoutBatch"
        [encodeList (GeneralRuleJobObservation.rootReadoutTerm request licensed) results,
         .natural (cachedRun request results none).2.2])) := by
  rw [← cached_readouts_exact request licensed results]
  exact accounted_returns state request licensed fuel results members

def executionHeadNames : List String :=
  ScopedRuleJobReadoutExecution.executionHeadNames ++ dataHeads ++
    (source.program.equations.map (·.head)) ++ ["+"]

def executionHeads (head : String) : Bool := executionHeadNames.contains head

theorem runtime_closed : ProgramClosed executionHeads runtime := by
  exact BridgeKit.closed_of_all _ _ (by decide +kernel) (by decide +kernel)

theorem job_readouts_captured_variables_returns_in_extension (targetProgram : Program)
    (agreement : ProgramAgreementOn executionHeads runtime targetProgram)
    (caller : Subst) (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (results : List (GeneralPremise.Execution.Result request.environment request.goal))
    (members : ∀ result ∈ results, result ∈ (GeneralPremise.Execution.run request.environment request.goal fuel
      (GeneralPremise.Execution.start request.environment request.goal)).answers)
    (requestName resultsName : String)
    (captured : [v requestName, v resultsName].map (applySubst caller) =
      [encoded (requestTerm request), encoded (resultsTerm results)]) :
    PureReturns targetProgram caller state
      (a "gslt:rule:job-readouts" [v requestName, v resultsName]) state
      (encoded (encodeList (GeneralRuleJobObservation.rootReadoutTerm request licensed) results)) := by
  apply path_of_closed_agreement runtime_closed agreement ⟨by rfl, rfl⟩
  exact helper_capture .readouts caller state [v requestName, v resultsName] _ _ rfl captured
    (job_readouts_returns state request licensed fuel results members)


/-- The replacement cache cannot turn the readout into an effectful or
multi-answer operation. This characterizes every completed target run. -/
theorem job_readouts_completed_iff (state after : State)
    (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (results : List (GeneralPremise.Execution.Result request.environment request.goal))
    (members : ∀ result ∈ results, result ∈ (GeneralPremise.Execution.run request.environment request.goal fuel
      (GeneralPremise.Execution.start request.environment request.goal)).answers)
    (answers input output : List Atom) :
    (∃ targetFuel, Eval.run runtime targetFuel
      { state := state, control := .evaluate [] (a "gslt:rule:job-readouts" [encoded (requestTerm request), encoded (resultsTerm results)]) } =
        .complete after answers input output) ↔
      after = state ∧
      answers = [encoded (encodeList (GeneralRuleJobObservation.rootReadoutTerm request licensed) results)] ∧
      input = [] ∧ output = [] :=
  pure_returns_completed_iff runtime [] state state _ _
    (job_readouts_returns state request licensed fuel results members) after answers input output

/-- Cache comparisons include the complete request projection, rather than
only its endpoint. A changed projected snapshot or permission cannot hit. -/
theorem key_changed_request (request request' goal target goal' target' : Term)
    (changed : request ≠ request') :
    keyTerm request goal target ≠ keyTerm request' goal' target' := by
  intro same
  exact changed ((keyTerm_eq_iff _ _ _ _ _ _).mp same).1

theorem cached_run_calls_bound (request : GeneralRuleJobExecution.Request)
    (results : List (GeneralPremise.Execution.Result request.environment request.goal)) :
    (cachedRun request results none).2.2 ≤ results.length :=
  List.MemoizedMap.calls_le_length _ _ _ _ _

/-- Two different source witnesses with the same endpoint share one actual
replacement-decision call. Their receipt reconstruction remains independent. -/
theorem two_results_one_decision (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (first second : GeneralPremise.Execution.Result request.environment request.goal)
    (members : ∀ result ∈ [first, second], result ∈
      (GeneralPremise.Execution.run request.environment request.goal fuel
        (GeneralPremise.Execution.start request.environment request.goal)).answers)
    (same : localTarget first = localTarget second) :
    PureReturns runtime [] state
      (a "gslt:rule:job-readouts-accounted"
        [encoded (requestTerm request), encoded (resultsTerm [first, second])]) state
      (encoded (.application "ReadoutBatch"
        [encodeList (GeneralRuleJobObservation.rootReadoutTerm request licensed) [first, second], .natural 1])) := by
  have calls : (cachedRun request [first, second] none).2.2 = 1 :=
    List.MemoizedMap.adjacent_same_key_calls _ _ _ first second same
  simpa only [calls] using job_readouts_accounted_returns state request licensed fuel [first, second] members


/-- The cached execution inhabits the same independently stated native
purity-and-termination family as the original readout. -/
def cached_native_certificate (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (results : List (GeneralPremise.Execution.Result request.environment request.goal))
    (members : ∀ result ∈ results, result ∈ (GeneralPremise.Execution.run request.environment request.goal fuel
      (GeneralPremise.Execution.start request.environment request.goal)).answers) :
    (OperationalGSLT.pureSingletonOutput runtime).Family
      { state := state, control := .evaluate [] (a "gslt:rule:job-readouts" [encoded (requestTerm request), encoded (resultsTerm results)]) } :=
  OperationalGSLT.pureSingleton_of_returns runtime [] state _ _
    (job_readouts_returns state request licensed fuel results members)

/-- Every retained native output witness contains the complete ordered receipt
list. Native support alone is not used to identify its payload occurrences. -/
theorem cached_native_evidence_exact (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (fuel : Nat) (results : List (GeneralPremise.Execution.Result request.environment request.goal))
    (members : ∀ result ∈ results, result ∈ (GeneralPremise.Execution.run request.environment request.goal fuel
      (GeneralPremise.Execution.start request.environment request.goal)).answers)
    (witness : (OperationalGSLT.pureSingletonOutput runtime).Family
      { state := state, control := .evaluate [] (a "gslt:rule:job-readouts" [encoded (requestTerm request), encoded (resultsTerm results)]) }) :
    witness.val = encoded (encodeList (GeneralRuleJobObservation.rootReadoutTerm request licensed) results) := by
  have same := (OperationalGSLT.pureSingleton_family_subsingleton runtime _).elim witness
    (cached_native_certificate state request licensed fuel results members)
  exact congrArg Subtype.val same

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralRuleReadoutCache
