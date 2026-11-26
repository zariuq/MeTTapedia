import Mettapedia.Languages.MeTTa.PeTTa.BridgeTransport
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralRuleDriverExecution.Program

/-!
# Execution of the original scoped rule-job scheduler

The authored driver retains pending work and physical answer cursors.
The quoted execution claims require no registered dynamic relations; native
primitive service execution requires its own correspondence proof.
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


private theorem machine_run_agreement :
    ProgramAgreementOn PremiseMachineRunExecution.executionHeads
      PremiseMachineRunExecution.referenceRuntime program :=
  programAgreementOn_of_retained_rows _ _ _ (by rfl) (by rfl)

private theorem scheduler_agreement :
    ProgramAgreementOn PremiseSchedulerExecution.executionHeads
      PremiseSchedulerExecution.runtime program :=
  programAgreementOn_of_retained_rows _ _ _ (by rfl) (by rfl)

private theorem readout_agreement :
    ProgramAgreementOn ScopedRuleJobReadoutExecution.executionHeads
      ScopedRuleJobReadoutExecution.runtime program :=
  programAgreementOn_of_retained_rows _ _ _ (by rfl) (by rfl)

private def rowHeads (head : String) : Bool :=
  ["gslt:rule:row-at", "Some", "LNil", "LCons", "None", "==", "-", "if", "let", "case"].contains head

private theorem row_closed : ProgramClosed rowHeads RuleExecutionProgram.program := by
  exact BridgeKit.closed_of_all _ _ (by decide +kernel) (by decide +kernel)

private theorem row_agreement : ProgramAgreementOn rowHeads RuleExecutionProgram.program program :=
  programAgreementOn_of_retained_rows _ _ _ (by rfl) (by rfl)

private theorem row_captured_returns {α : Type} (encoder : α → Term)
    (caller : Subst) (state : State) (index : Nat) (rows : List α) (one two : String)
    (captured : [v one, v two].map (applySubst caller) =
      [number index, encoded (encodeList encoder rows)]) :
    PureReturns program caller state (a "gslt:rule:row-at" [v one, v two]) state
      (encoded (encodeOption encoder rows[index]?)) := by
  have returned := RuleInstantiationExecution.RowLookup.row_at_captured_returns caller state index
    (rows.map encoder) (v one) (v two)
    (by simpa only [encodeList_map, Function.id_comp] using captured)
  have transported := path_of_closed_agreement row_closed row_agreement
    (show configurationWithin rowHeads
      {state, control := .evaluate caller (a "gslt:rule:row-at" [v one, v two])} from by
        constructor <;> rfl) returned
  cases found : rows[index]? <;>
    simpa [List.getElem?_map, found, MatchAutomataBindingExecution.payloadOptionTerm, encodeOption]
      using transported

local macro "driver_template" : tactic => `(tactic|
  repeat' first
  | exact PureData.Template.captured _
  | exact PureData.Template.grounded _
  | exact PureData.Template.symbol _
  | (apply template_constructor _ _ (by decide)
     intro child member
     simp only [List.mem_cons, List.not_mem_nil, or_false] at member)
  | (rcases member with rfl | member)
  | subst child)

private theorem machine_start_captured_returns (caller : Subst) (state : State)
    (environment : Environment) (goal : Execution.Goal) (argument : Atom)
    (captured : applySubst caller argument =
      encoded (PremiseOperationsExecution.GeneralExecution.goalTerm goal)) :
    PureReturns program caller state (a "gslt:premise:machine-start" [argument]) state
      (encoded (encodeOption PremiseOperationsExecution.GeneralExecution.stateTerm
        (some (Execution.start environment goal)))) := by
  apply PureData.raw_capture_returns program [] caller state state "gslt:premise:machine-start"
    [encoded (PremiseOperationsExecution.GeneralExecution.goalTerm goal)] [argument]
  · decide +kernel
  · intro index bounded
    have zero : index = 0 := by simpa using bounded
    subst index
    decide +kernel
  · decide
  · simp only [List.map_cons, List.map_nil, captured,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]
  · exact PremiseMachineRunExecution.start_returns program machine_run_agreement state environment goal

private def startResult : Atom :=
  a "Some" [a "PremiseState"
    [a "LCons" [a "RuleJobFrame" [v "inner", number 0], .symbol "LNil"],
     .symbol "LNil", .symbol "LNil", number 0]]

private def startInnerCases : SpaceSemantics.Cases :=
  [(a "Some" [v "inner"], startResult), (v "____________", .symbol "None")]

private def startInner : Atom :=
  a "case" [a "gslt:premise:machine-start"
      [a "RootGoal" [v "focusBound", v "focusType", v "focus", v "ordinal"]],
    .expression (startInnerCases.map fun row => .expression [row.1, row.2])]

private def requestPattern : Atom :=
  a "RuleJobRequestProjection"
    [v "environment", v "permissions", v "bound", v "expected", v "source",
      a "RuleJob" [v "ordinal", v "declaration",
        a "RuleJobSite" [v "address", v "context", v "focus", v "focusBound", v "focusType", v "frames"]]]

private def requestBindings (request : GeneralRuleJobExecution.Request) : Subst :=
  [("environment", encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm request.environment
      (request.environment.free.entriesOn (GeneralRuleJobObservation.requestFootprint request)))),
   ("permissions", encoded (InferenceCettaWire.ContextObservation.permissionsTerm request.plan.permissions.sites)),
   ("bound", encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm request.bound)),
   ("expected", encoded (InferenceCettaWire.AuthoredRule.typeTerm request.expected)),
   ("source", encoded (InferenceCettaWire.encodePattern request.source)),
   ("ordinal", number request.job.ordinal),
   ("declaration", encoded (ScopedRuleJobReadoutExecution.rulePlanTerm request.job.declaration)),
   ("address", encoded (encodeList Term.natural request.job.site.address)),
   ("context", encoded (InferenceCettaWire.ContextObservation.contextTerm request.job.site.context)),
   ("focus", encoded (InferenceCettaWire.encodePattern request.job.site.focus)),
   ("focusBound", encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm request.job.site.focusBound)),
   ("focusType", encoded (InferenceCettaWire.AuthoredRule.typeTerm request.job.site.focusType)),
   ("frames", encoded (encodeList ScopedRuleJobReadoutExecution.typingFrameTerm request.job.site.typingFrames))].reverse

private def startCases : SpaceSemantics.Cases :=
  [(requestPattern, startInner), (v "_____________", .symbol "None")]

private theorem start_shape : (equation .start).body =
    a "case" [v "request", .expression (startCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem start_returns (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source) :
    PureReturns program [] state (a "gslt:driver:job-start" [encoded (requestTerm request)]) state
      (encoded (encodeOption stateTerm (some (GeneralRuleJobExecution.start request licensed)))) := by
  let caller := bindings .start [encoded (requestTerm request)]
  let selected := requestBindings request ++ caller
  let inner := Execution.start request.environment request.goal
  let found := ("inner", encoded (PremiseOperationsExecution.GeneralExecution.stateTerm inner)) :: selected
  apply helper_call .start [] state _ [encoded (requestTerm request)] _ rfl (by
    simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
  rw [start_shape]
  apply branch_returns caller selected state _ (encoded (requestTerm request)) startCases startInner _
  · exact variable_returns program caller state "request"
  · simp [startCases, requestPattern, selected, caller, bindings, Helper.names, requestBindings,
      requestTerm, ScopedRuleJobReadoutExecution.requestProjectionTerm,
      ScopedRuleJobReadoutExecution.jobTerm, ScopedRuleJobReadoutExecution.siteTerm,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  · unfold startInner
    apply branch_returns selected found state _
      (encoded (encodeOption PremiseOperationsExecution.GeneralExecution.stateTerm (some inner)))
      startInnerCases startResult _
    · apply machine_start_captured_returns
      simp [requestBindings, selected, caller, bindings, Helper.names,
        GeneralRuleJobExecution.Request.goal, PremiseOperationsExecution.GeneralExecution.goalTerm,
        applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany]
    · simp [startInnerCases, found, selected, requestBindings, caller, bindings, Helper.names,
        SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        matchAtom, Subst.lookup, encodeOption, CettaWireAtom.encode, CettaWireAtom.encodeMany]
    · have templated : PureData.Template program startResult := by unfold startResult; driver_template
      simpa [startResult, found, inner, stateTerm, taskTerm, GeneralRuleJobExecution.start,
        PremiseSchedulerExecution.schedulerStateTerm, encodeOption, encodeList,
        applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany]
        using PureData.template_return program found state startResult templated

private theorem machine_tick_captured_returns (caller : Subst) (state : State)
    (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (machine : Execution.State request.environment request.goal)
    (covered : Execution.stateFreeWithin (GeneralRuleJobObservation.requestFootprint request)
      request.environment request.goal machine) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm request.environment
         (request.environment.free.entriesOn (GeneralRuleJobObservation.requestFootprint request))),
       encoded (PremiseOperationsExecution.GeneralExecution.stateTerm machine)]) :
    PureReturns program caller state (a "gslt:premise:machine-tick" arguments) state
      (encoded (encodeOption PremiseOperationsExecution.GeneralExecution.stateTerm
        (some (Execution.tick request.environment request.goal machine)))) := by
  apply PremiseMachineRunExecution.tick_captured_returns program machine_run_agreement caller state
    (PremiseOperationsExecution.GeneralExecution.environmentTerm request.environment
      (request.environment.free.entriesOn (GeneralRuleJobObservation.requestFootprint request)))
    PremiseOperationsExecution.GeneralExecution.taskTerm PremiseOperationsExecution.GeneralExecution.resultTerm
    PremiseOperationsExecution.GeneralExecution.obligationTerm (Execution.expand request.environment request.goal)
    machine arguments captured
  intro current member callee inputs
  apply retained_returns (by
    simp only [codeWithin, expressionHeadWithin, atomsWithin, Bool.and_true]
    decide +kernel)
  apply path_of_closed_agreement
    PremiseOperationsExecution.GeneralExecution.CompletedAssembly.retained_machine_closed
    PremiseOperationsExecution.GeneralExecution.CompletedAssembly.retained_machine_agreement
    (by constructor <;> rfl)
  exact PremiseOperationsExecution.GeneralExecution.EnvironmentExecution.Tasks.expand_captured_within_returns
    callee state request.environment finiteProvider request.goal current (GeneralRuleJobObservation.requestFootprint request)
    (fun _ member => List.mem_append_right _ member) (covered.1 current member)
    (v "environment") (v "task") inputs

private theorem finish_captured_returns (caller : Subst) (state : State)
    (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (result : Execution.Result request.environment request.goal)
    (covered : Execution.resultFreeWithin (GeneralRuleJobObservation.requestFootprint request)
      result) (one two : String)
    (captured : [v one, v two].map (applySubst caller) =
      [encoded (requestTerm request), encoded (PremiseOperationsExecution.GeneralExecution.resultTerm result)]) :
    PureReturns program caller state (a "gslt:rule:job-finish-root" [v one, v two]) state
      (encoded (encodeOption answerTerm (GeneralRuleJobExecution.rootProjection request licensed result))) := by
  cases result with
  | root trace original completed history target valid =>
    apply path_of_closed_agreement ScopedRuleJobReadoutExecution.runtime_closed readout_agreement
      (by
        constructor
        · change codeWithin ScopedRuleJobReadoutExecution.executionHeads (a "gslt:rule:job-finish-root" [v one, v two]) = true
          simp only [codeWithin, expressionHeadWithin, atomsWithin, Bool.and_true]
          decide +kernel
        · rfl)
    exact ScopedRuleJobReadoutExecution.finish_root_finite_captured_returns caller state request licensed
      (GeneralRuleJobObservation.requestFootprint request) trace original completed history target valid
      (GeneralRuleJobExecution.licensed_fill_free_within _ _ _ _ _ _ _ _ licensed.2 target
        (fun _ member => List.mem_append_left _ member) covered.2.2.2)
      (v one) (v two) captured

private theorem successor_returns (caller : Subst) (state : State) (value : Nat) (name : String)
    (captured : applySubst caller (v name) = number value) :
    PureReturns program caller state (a "+" [v name, number 1]) state (number (value + 1)) := by
  apply native_binary_call_returns program caller state state state state "+"
    (v name) (number 1) (number value) (number 1) (number (value + 1))
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  · simpa only [captured] using variable_returns program caller state name
  · exact grounded_returns program caller state (.int 1)
  · change (Except.ok (state, [Atom.grounded (.int ((value : Int) + 1))]) : Effects.Result) =
      Except.ok (state, [Atom.grounded (.int ((value + 1 : Nat) : Int))])
    simp
  · decide

private def expansionInnerState : Atom :=
  a "PremiseState" [v "agenda", v "answers", v "unresolved", v "work"]

private def expansionTail : Atom :=
  a "LCons" [a "RuleJobFrame" [expansionInnerState, v "next"], .symbol "LNil"]

private def expansionReceipt : Atom :=
  a "Some" [a "PremiseExpansion" [v "tail", a "LCons" [v "receipt", .symbol "LNil"], .symbol "LNil"]]

private def expansionRefusal : Atom :=
  a "Some" [a "PremiseExpansion" [v "tail", .symbol "LNil", .symbol "LNil"]]

private def expansionReadoutCases : SpaceSemantics.Cases :=
  [(a "Some" [v "receipt"], expansionReceipt), (.symbol "None", expansionRefusal)]

private def expansionReadout : Atom :=
  a "case" [a "gslt:rule:job-finish-root" [v "request", v "result"],
    .expression (expansionReadoutCases.map fun row => .expression [row.1, row.2])]

private def expansionFound : Atom :=
  a "let" [v "next", a "+" [v "cursor", number 1],
    a "let" [v "tail", expansionTail, expansionReadout]]

private def expansionPending : Atom :=
  a "Some" [a "PremiseExpansion" [.symbol "LNil", .symbol "LNil", v "pending"]]

private def expansionSettled : Atom :=
  a "let" [v "pending", a "gslt:driver:job-obligations" [v "unresolved"], expansionPending]

private def expansionAdvanced : Atom :=
  a "Some" [a "PremiseExpansion"
    [a "LCons" [a "RuleJobFrame" [v "advanced", v "cursor"], .symbol "LNil"],
     .symbol "LNil", .symbol "LNil"]]

private def expansionAdvanceCases : SpaceSemantics.Cases :=
  [(a "Some" [v "advanced"], expansionAdvanced), (v "____________", .symbol "None")]

private def expansionAdvance : Atom :=
  a "case" [a "gslt:premise:machine-tick" [v "environment", expansionInnerState],
    .expression (expansionAdvanceCases.map fun row => .expression [row.1, row.2])]

private def expansionAgendaCases : SpaceSemantics.Cases :=
  [(.symbol "LNil", expansionSettled), (a "LCons" [v "current", v "remaining"], expansionAdvance)]

private def expansionUnread : Atom :=
  a "case" [v "agenda", .expression (expansionAgendaCases.map fun row => .expression [row.1, row.2])]

private def expansionRowCases : SpaceSemantics.Cases :=
  [(a "Some" [v "result"], expansionFound), (.symbol "None", expansionUnread)]

private def expansionRow : Atom :=
  a "case" [a "gslt:rule:row-at" [v "cursor", v "answers"],
    .expression (expansionRowCases.map fun row => .expression [row.1, row.2])]

private def expansionPattern : Atom :=
  a "RuleJobExpansionInput"
    [a "RuleJobRequestProjection" [v "environment", v "permissions", v "bound", v "expected", v "source", v "job"],
     a "RuleJobFrame" [expansionInnerState, v "cursor"]]

private def expansionBindings (request : GeneralRuleJobExecution.Request)
    (frame : GeneralRuleJobExecution.Frame request) : Subst :=
  [("environment", encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm request.environment
      (request.environment.free.entriesOn (GeneralRuleJobObservation.requestFootprint request)))),
   ("permissions", encoded (InferenceCettaWire.ContextObservation.permissionsTerm request.plan.permissions.sites)),
   ("bound", encoded (encodeList InferenceCettaWire.AuthoredRule.typeTerm request.bound)),
   ("expected", encoded (InferenceCettaWire.AuthoredRule.typeTerm request.expected)),
   ("source", encoded (InferenceCettaWire.encodePattern request.source)),
   ("job", encoded (ScopedRuleJobReadoutExecution.jobTerm request.job)),
   ("agenda", encoded (encodeList PremiseOperationsExecution.GeneralExecution.taskTerm frame.state.agenda)),
   ("answers", encoded (encodeList PremiseOperationsExecution.GeneralExecution.resultTerm frame.state.answers)),
   ("unresolved", encoded (encodeList PremiseOperationsExecution.GeneralExecution.obligationTerm frame.state.unresolved)),
   ("work", number frame.state.work), ("cursor", number frame.cursor)].reverse

private def expansionCases : SpaceSemantics.Cases :=
  [(expansionPattern, expansionRow), (v "_____________", .symbol "None")]

private theorem expand_shape : (equation .expand).body =
    a "case" [a "RuleJobExpansionInput" [v "request", v "task"],
      .expression (expansionCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem expansion_frame_returns (state : State) (request : GeneralRuleJobExecution.Request)
    (frame : GeneralRuleJobExecution.Frame request) (answer : Atom)
    (continued : PureReturns program
      (expansionBindings request frame ++ bindings .expand
        [encoded (requestTerm request), encoded (taskTerm (.root frame))]) state expansionRow state answer) :
    PureReturns program [] state
      (a "gslt:driver:job-expand" [encoded (requestTerm request), encoded (taskTerm (.root frame))]) state answer := by
  let caller := bindings .expand [encoded (requestTerm request), encoded (taskTerm (.root frame))]
  let selected := expansionBindings request frame ++ caller
  apply helper_call .expand [] state _ [encoded (requestTerm request), encoded (taskTerm (.root frame))] _ rfl (by
    simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
  rw [expand_shape]
  apply branch_returns caller selected state _
    (a "RuleJobExpansionInput" [encoded (requestTerm request), encoded (taskTerm (.root frame))])
    expansionCases expansionRow _
  · have templated : PureData.Template program (a "RuleJobExpansionInput" [v "request", v "task"]) := by
      driver_template
    simpa [caller, bindings, Helper.names, applySubst, applySubst.applySubstList, Subst.lookup]
      using PureData.template_return program caller state _ templated
  · simp [expansionCases, expansionPattern, expansionInnerState, selected, caller, expansionBindings,
      bindings, Helper.names, requestTerm, ScopedRuleJobReadoutExecution.requestProjectionTerm,
      taskTerm, PremiseOperationsExecution.GeneralExecution.stateTerm, PremiseSchedulerExecution.schedulerStateTerm,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  · exact continued

theorem expand_returns (state : State) (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (task : GeneralRuleJobExecution.Task request)
    (covered : GeneralRuleJobExecution.jobTaskFreeWithin
      (GeneralRuleJobObservation.requestFootprint request) task) :
    PureReturns program [] state
      (a "gslt:driver:job-expand" [encoded (requestTerm request), encoded (taskTerm task)]) state
      (encoded (encodeOption expansionTerm (some (GeneralRuleJobExecution.expand request task)))) := by
  cases task with
  | root frame =>
    let caller := bindings .expand [encoded (requestTerm request), encoded (taskTerm (.root frame))]
    let selected := expansionBindings request frame ++ caller
    apply expansion_frame_returns state request frame
    have lookup := row_captured_returns PremiseOperationsExecution.GeneralExecution.resultTerm
      selected state frame.cursor frame.state.answers "cursor" "answers" (by
        simp [selected, expansionBindings, caller, bindings, Helper.names, applySubst, Subst.lookup])
    unfold expansionRow
    cases row : frame.state.answers[frame.cursor]? with
    | none =>
      apply branch_returns selected selected state _ (.symbol "None") expansionRowCases expansionUnread _
      · simpa only [row, encodeOption, CettaWireAtom.encode] using lookup
      · simp [expansionRowCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · unfold expansionUnread
        cases agenda : frame.state.agenda with
        | nil =>
          apply branch_returns selected selected state _ (.symbol "LNil") expansionAgendaCases expansionSettled _
          · simpa [selected, expansionBindings, caller, bindings, Helper.names, applySubst, Subst.lookup,
              agenda, encodeList, CettaWireAtom.encode] using variable_returns program selected state "agenda"
          · simp [expansionAgendaCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
          · let pending := encoded (encodeList obligationTerm (frame.state.unresolved.map GeneralRuleJobExecution.Obligation.premise))
            let done := ("pending", pending) :: selected
            unfold expansionSettled
            apply named_let_returns program selected state "pending" _ pending
            · simp [selected, expansionBindings, caller, bindings, Helper.names, Subst.lookup]
            · apply obligations_captured_returns
              simp [selected, expansionBindings, caller, bindings, Helper.names, applySubst, Subst.lookup]
            · have templated : PureData.Template program expansionPending := by
                unfold expansionPending; driver_template
              simpa [expansionPending, done, pending, GeneralRuleJobExecution.expand, row, Scheduler.settled, agenda,
                expansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm, encodeOption, encodeList,
                applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany]
                using PureData.template_return program done state expansionPending templated
        | cons current remaining =>
          let active := [("remaining", encoded (encodeList PremiseOperationsExecution.GeneralExecution.taskTerm remaining)),
            ("current", encoded (PremiseOperationsExecution.GeneralExecution.taskTerm current))] ++ selected
          let advanced := Execution.tick request.environment request.goal frame.state
          let done := ("advanced", encoded (PremiseOperationsExecution.GeneralExecution.stateTerm advanced)) :: active
          apply branch_returns selected active state _
            (encoded (encodeList PremiseOperationsExecution.GeneralExecution.taskTerm (current :: remaining)))
            expansionAgendaCases expansionAdvance _
          · simpa [selected, expansionBindings, caller, bindings, Helper.names, applySubst, Subst.lookup, agenda]
              using variable_returns program selected state "agenda"
          · simp [active, expansionAgendaCases, selected, expansionBindings, caller, bindings, Helper.names,
              SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
              matchAtom, Subst.lookup, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany]
          · unfold expansionAdvance
            apply branch_returns active done state _
              (encoded (encodeOption PremiseOperationsExecution.GeneralExecution.stateTerm (some advanced)))
              expansionAdvanceCases expansionAdvanced _
            · apply machine_tick_captured_returns active state request finiteProvider frame.state covered
              simp [expansionInnerState, active, selected, expansionBindings, caller, bindings, Helper.names,
                PremiseOperationsExecution.GeneralExecution.stateTerm, PremiseSchedulerExecution.schedulerStateTerm,
                applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany]
            · simp [done, active, expansionAdvanceCases, selected, expansionBindings, caller, bindings, Helper.names,
                SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                matchAtom, Subst.lookup, encodeOption, CettaWireAtom.encode, CettaWireAtom.encodeMany]
            · have templated : PureData.Template program expansionAdvanced := by
                unfold expansionAdvanced; driver_template
              simpa [expansionAdvanced, done, active, selected, expansionBindings, caller, bindings, Helper.names,
                advanced, GeneralRuleJobExecution.expand, row, Scheduler.settled, agenda,
                expansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm, taskTerm, encodeOption, encodeList,
                applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany]
                using PureData.template_return program done state expansionAdvanced templated
    | some result =>
      let found := ("result", encoded (PremiseOperationsExecution.GeneralExecution.resultTerm result)) :: selected
      let counted := ("next", number (frame.cursor + 1)) :: found
      let tail := encoded (encodeList taskTerm [GeneralRuleJobExecution.Task.root {frame with cursor := frame.cursor + 1}])
      let tailed := ("tail", tail) :: counted
      apply branch_returns selected found state _
        (encoded (encodeOption PremiseOperationsExecution.GeneralExecution.resultTerm (some result)))
        expansionRowCases expansionFound _
      · simpa only [row] using lookup
      · simp [found, expansionRowCases, selected, expansionBindings, caller, bindings, Helper.names,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, encodeOption, CettaWireAtom.encode, CettaWireAtom.encodeMany]
      · unfold expansionFound
        apply named_let_returns program found state "next" _ (number (frame.cursor + 1))
        · simp [found, selected, expansionBindings, caller, bindings, Helper.names, Subst.lookup]
        · exact successor_returns found state frame.cursor "cursor" (by
            simp [found, selected, expansionBindings, caller, bindings, Helper.names, applySubst, Subst.lookup])
        · apply named_let_returns program counted state "tail" _ tail
          · simp [counted, found, selected, expansionBindings, caller, bindings, Helper.names, Subst.lookup]
          · have templated : PureData.Template program expansionTail := by
              unfold expansionTail expansionInnerState; driver_template
            simpa [expansionTail, expansionInnerState, counted, found, selected, expansionBindings, caller, bindings, Helper.names,
              tail, taskTerm, PremiseOperationsExecution.GeneralExecution.stateTerm, PremiseSchedulerExecution.schedulerStateTerm, encodeList,
              applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany]
              using PureData.template_return program counted state expansionTail templated
          · have resultCovered := covered.2 result (List.mem_of_getElem? row)
            have readout := finish_captured_returns tailed state request frame.licensed result resultCovered
              "request" "result" (by
                simp [tailed, counted, found, selected, expansionBindings, caller, bindings, Helper.names,
                  applySubst, Subst.lookup])
            unfold expansionReadout
            cases produced : GeneralRuleJobExecution.rootProjection request frame.licensed result with
            | none =>
              apply branch_returns tailed tailed state _ (.symbol "None")
                expansionReadoutCases expansionRefusal _
              · simpa only [produced, encodeOption, CettaWireAtom.encode] using readout
              · simp [expansionReadoutCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
              · have templated : PureData.Template program expansionRefusal := by
                  unfold expansionRefusal; driver_template
                cases result with
                | root trace original completed history target valid =>
                  simp only [GeneralRuleJobExecution.rootProjection] at produced
                  simpa [expansionRefusal, tailed, tail, GeneralRuleJobExecution.expand, row,
                    expansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm, taskTerm, encodeOption, encodeList,
                    applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                    produced] using PureData.template_return program tailed state expansionRefusal templated
            | some receipt =>
              let done := ("receipt", encoded (answerTerm receipt)) :: tailed
              apply branch_returns tailed done state _ (encoded (encodeOption answerTerm (some receipt)))
                expansionReadoutCases expansionReceipt _
              · simpa only [produced] using readout
              · simp [done, expansionReadoutCases, tailed, counted, found, selected, expansionBindings, caller, bindings, Helper.names,
                  SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
                  matchAtom, Subst.lookup, encodeOption, CettaWireAtom.encode, CettaWireAtom.encodeMany]
              · have templated : PureData.Template program expansionReceipt := by
                  unfold expansionReceipt; driver_template
                cases result with
                | root trace original completed history target valid =>
                  simp only [GeneralRuleJobExecution.rootProjection] at produced
                  simpa [expansionReceipt, done, tailed, tail, GeneralRuleJobExecution.expand, row,
                    expansionTerm, PremiseSchedulerExecution.schedulerExpansionTerm, taskTerm, encodeOption, encodeList,
                    applySubst, applySubst.applySubstList, Subst.lookup, CettaWireAtom.encode, CettaWireAtom.encodeMany,
                    produced] using PureData.template_return program done state expansionReceipt templated

theorem expand_captured_returns (caller : Subst) (state : State) (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (task : GeneralRuleJobExecution.Task request)
    (covered : GeneralRuleJobExecution.jobTaskFreeWithin
      (GeneralRuleJobObservation.requestFootprint request) task) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) = [encoded (requestTerm request), encoded (taskTerm task)]) :
    PureReturns program caller state (a "gslt:driver:job-expand" arguments) state
      (encoded (encodeOption expansionTerm (some (GeneralRuleJobExecution.expand request task)))) :=
  helper_capture .expand caller state arguments _ _ rfl captured (expand_returns state request finiteProvider task covered)

private def tickBody : Atom :=
  a "let" [v "expanded", a "gslt:driver:job-expand" [v "request", v "task"],
    a "gslt:premise:machine-commit" [v "state", v "expanded"]]

private def tickCases : SpaceSemantics.Cases :=
  [(a "PremiseState" [.symbol "LNil", v "answers", v "unresolved", v "work"], a "Some" [v "state"]),
   (a "PremiseState" [a "LCons" [v "task", v "rest"], v "answers", v "unresolved", v "work"], tickBody),
   (v "___________", .symbol "None")]

private theorem tick_shape : (equation .tick).body =
    a "case" [v "state", .expression (tickCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem tick_returns (state : State) (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (machine : GeneralRuleJobExecution.State request)
    (covered : GeneralRuleJobExecution.jobStateFreeWithin
      (GeneralRuleJobObservation.requestFootprint request) request machine) :
    PureReturns program [] state
      (a "gslt:driver:job-tick" [encoded (requestTerm request), encoded (stateTerm machine)]) state
      (encoded (encodeOption stateTerm (some (GeneralRuleJobExecution.tick request machine)))) := by
  let value := encoded (stateTerm machine)
  let caller := bindings .tick [encoded (requestTerm request), value]
  apply helper_call .tick [] state _ [encoded (requestTerm request), value] _ rfl (by
    simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]; rfl)
  rw [tick_shape]
  cases agenda : machine.agenda with
  | nil =>
    let selected := [("work", number machine.work),
      ("unresolved", encoded (encodeList obligationTerm machine.unresolved)),
      ("answers", encoded (encodeList answerTerm machine.answers))] ++ caller
    apply branch_returns caller selected state _ value tickCases (a "Some" [v "state"]) _
    · exact variable_returns program caller state "state"
    · simp [value, stateTerm, PremiseSchedulerExecution.schedulerStateTerm, agenda, tickCases, selected, caller,
        bindings, Helper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, CettaWireAtom.encode,
        CettaWireAtom.encodeMany, encodeList, Subst.lookup]
    · have templated : PureData.Template program (a "Some" [v "state"]) := by driver_template
      simpa [GeneralRuleJobExecution.tick, Scheduler.tick, agenda, encodeOption,
        value, selected, caller, bindings, Helper.names,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList, Subst.lookup]
        using PureData.template_return program selected state _ templated
  | cons current rest =>
    let selected := [("work", number machine.work),
      ("unresolved", encoded (encodeList obligationTerm machine.unresolved)),
      ("answers", encoded (encodeList answerTerm machine.answers)),
      ("rest", encoded (encodeList taskTerm rest)), ("task", encoded (taskTerm current))] ++ caller
    let expansion := encoded (encodeOption expansionTerm (some (GeneralRuleJobExecution.expand request current)))
    let continued := ("expanded", expansion) :: selected
    apply branch_returns caller selected state _ value tickCases tickBody _
    · exact variable_returns program caller state "state"
    · simp [value, stateTerm, PremiseSchedulerExecution.schedulerStateTerm, agenda, tickCases, selected, caller,
        bindings, Helper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, CettaWireAtom.encode,
        CettaWireAtom.encodeMany, encodeList, Subst.lookup]
    · unfold tickBody
      apply named_let_returns program selected state "expanded" _ expansion
      · simp [selected, caller, bindings, Helper.names, Subst.lookup]
      · apply expand_captured_returns selected state request finiteProvider current (covered.1 current (by simp [agenda]))
        simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]
      · apply PremiseSchedulerExecution.returns_in_extension program scheduler_agreement (by decide +kernel)
        apply PremiseSchedulerExecution.commit_captured_returns continued state taskTerm answerTerm obligationTerm
          (GeneralRuleJobExecution.expand request) machine [v "state", v "expanded"]
        simp [continued, expansion, selected, caller, bindings, Helper.names, applySubst, Subst.lookup,
          agenda, value, stateTerm, expansionTerm]

theorem tick_captured_returns (caller : Subst) (state : State) (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (machine : GeneralRuleJobExecution.State request)
    (covered : GeneralRuleJobExecution.jobStateFreeWithin
      (GeneralRuleJobObservation.requestFootprint request) request machine) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) = [encoded (requestTerm request), encoded (stateTerm machine)]) :
    PureReturns program caller state (a "gslt:driver:job-tick" arguments) state
      (encoded (encodeOption stateTerm (some (GeneralRuleJobExecution.tick request machine)))) :=
  helper_capture .tick caller state arguments _ _ rfl captured (tick_returns state request finiteProvider machine covered)

private theorem bool_if_returns (caller : Subst) (state : State)
    (condition : Atom) (value : Bool) (yes no answer : Atom)
    (tested : PureReturns program caller state condition state (Effects.boolean value))
    (continued : PureReturns program caller state (if value then yes else no) state answer) :
    PureReturns program caller state (a "if" [condition, yes, no]) state answer := by
  apply if_returns program caller state state state condition (Effects.boolean value) yes no answer tested
  have boolean_same : (Effects.boolean value == Effects.boolean true) = value := by
    cases value <;> decide +kernel
  simpa only [boolean_same] using continued

private def runContinue : Atom :=
  a "let" [v "remaining", a "-" [v "fuel", number 1],
    a "gslt:driver:job-run" [v "request", v "remaining", v "next"]]

private def runCases : SpaceSemantics.Cases :=
  [(a "Some" [v "next"], runContinue), (v "__________", .symbol "None")]

private def runBody : Atom :=
  a "case" [a "gslt:driver:job-tick" [v "request", v "state"],
    .expression (runCases.map fun row => .expression [row.1, row.2])]

private theorem run_shape : (equation .run).body =
    a "if" [a "==" [v "fuel", number 0], a "Some" [v "state"], runBody] := by
  decide +kernel

theorem run_returns (state : State) (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = []) (fuel : Nat)
    (machine : GeneralRuleJobExecution.State request)
    (covered : GeneralRuleJobExecution.jobStateFreeWithin
      (GeneralRuleJobObservation.requestFootprint request) request machine) :
    PureReturns program [] state
      (a "gslt:driver:job-run" [encoded (requestTerm request), number fuel, encoded (stateTerm machine)]) state
      (encoded (encodeOption stateTerm (some (GeneralRuleJobExecution.run request fuel machine)))) := by
  induction fuel generalizing machine with
  | zero =>
    let value := encoded (stateTerm machine)
    let caller := bindings .run [encoded (requestTerm request), number 0, value]
    apply helper_call .run [] state _ [encoded (requestTerm request), number 0, value] _ rfl (by
      simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]; rfl)
    rw [run_shape]
    have tested := CettaWireAtom.equality_evaluated_returns program caller state (.natural 0) (.natural 0)
      (v "fuel") (number 0) (by decide +kernel) (by decide +kernel)
      (by simpa [caller, bindings, Helper.names, applySubst, Subst.lookup] using variable_returns program caller state "fuel")
      (grounded_returns program caller state (.int 0))
    simp only [decide_true] at tested
    apply bool_if_returns caller state _ true _ _ _ tested
    have templated : PureData.Template program (a "Some" [v "state"]) := by driver_template
    simpa [GeneralRuleJobExecution.run, Scheduler.run, caller, bindings, Helper.names,
      applySubst, applySubst.applySubstList, Subst.lookup, encodeOption, CettaWireAtom.encode, CettaWireAtom.encodeMany]
      using PureData.template_return program caller state _ templated
  | succ fuel ih =>
    let value := encoded (stateTerm machine)
    let caller := bindings .run [encoded (requestTerm request), number (fuel + 1), value]
    let nextMachine := GeneralRuleJobExecution.tick request machine
    let nextValue := encoded (stateTerm nextMachine)
    let selected := ("next", nextValue) :: caller
    let remaining := ("remaining", number fuel) :: selected
    apply helper_call .run [] state _ [encoded (requestTerm request), number (fuel + 1), value] _ rfl (by
      simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]; rfl)
    rw [run_shape]
    have tested := CettaWireAtom.equality_evaluated_returns program caller state (.natural (fuel + 1)) (.natural 0)
      (v "fuel") (number 0) (by decide +kernel) (by decide +kernel)
      (by simpa [caller, bindings, Helper.names, applySubst, Subst.lookup] using variable_returns program caller state "fuel")
      (grounded_returns program caller state (.int 0))
    simp only [Term.natural.injEq, Nat.add_one_ne_zero, decide_false] at tested
    apply bool_if_returns caller state _ false _ _ _ tested
    unfold runBody
    apply branch_returns caller selected state _ (a "Some" [nextValue]) runCases runContinue _
    · apply tick_captured_returns caller state request finiteProvider machine covered
      simp [caller, bindings, Helper.names, applySubst, Subst.lookup, value]
    · simp [runCases, selected, caller, bindings, Helper.names, SpaceSemantics.selectCase,
        SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · unfold runContinue
      apply named_let_returns program selected state "remaining" _ (number fuel)
      · simp [selected, caller, bindings, Helper.names, Subst.lookup]
      · apply native_binary_call_returns program selected state state state state "-"
          (v "fuel") (number 1) (number (fuel + 1)) (number 1) (number fuel)
          (by decide) (by decide) (by decide +kernel) (by decide +kernel)
        · simpa [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]
            using variable_returns program selected state "fuel"
        · exact grounded_returns program selected state (.int 1)
        · change (Except.ok (state, [Atom.grounded (.int (((fuel + 1 : Nat) : Int) - 1))]) : Effects.Result) =
            Except.ok (state, [Atom.grounded (.int (fuel : Int))])
          simp
        · decide
      · apply helper_capture .run remaining state [v "request", v "remaining", v "next"]
          [encoded (requestTerm request), number fuel, nextValue] _ rfl
        · simp [remaining, selected, caller, bindings, Helper.names, applySubst, Subst.lookup]
        · apply ih nextMachine
          apply GeneralRuleJobExecution.job_tick_free_within
            (GeneralRuleJobObservation.requestFootprint request) request
            (fun _ member => List.mem_append_left _ member) _ machine covered
          exact provider_coverage_mono _ _ _ (fun _ member => List.mem_append_right _ member)
            (provider_covered_by_own_names request.environment.provider)

theorem run_captured_returns (caller : Subst) (state : State) (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (fuel : Nat) (machine : GeneralRuleJobExecution.State request)
    (covered : GeneralRuleJobExecution.jobStateFreeWithin
      (GeneralRuleJobObservation.requestFootprint request) request machine) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (requestTerm request), number fuel, encoded (stateTerm machine)]) :
    PureReturns program caller state (a "gslt:driver:job-run" arguments) state
      (encoded (encodeOption stateTerm (some (GeneralRuleJobExecution.run request fuel machine)))) :=
  helper_capture .run caller state arguments _ _ rfl captured (run_returns state request finiteProvider fuel machine covered)

theorem start_captured_returns (caller : Subst) (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (argument : Atom) (captured : applySubst caller argument = encoded (requestTerm request)) :
    PureReturns program caller state (a "gslt:driver:job-start" [argument]) state
      (encoded (encodeOption stateTerm (some (GeneralRuleJobExecution.start request licensed)))) :=
  helper_capture .start caller state [argument] _ _ rfl (by simp only [List.map_cons, List.map_nil, captured])
    (start_returns state request licensed)

private def beginBody : Atom :=
  a "gslt:driver:job-run" [v "request", v "fuel", v "state"]

private def beginCases : SpaceSemantics.Cases :=
  [(a "Some" [v "state"], beginBody), (v "________", .symbol "None")]

private theorem begin_shape : (equation .begin).body =
    a "case" [a "gslt:driver:job-start" [v "request"],
      .expression (beginCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

theorem begin_returns (state : State) (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (licensed : request.job.Valid request.plan request.bound request.expected request.source) (fuel : Nat) :
    PureReturns program [] state
      (a "gslt:driver:job-begin" [encoded (requestTerm request), number fuel]) state
      (encoded (encodeOption stateTerm (some (GeneralRuleJobExecution.run request fuel
        (GeneralRuleJobExecution.start request licensed))))) := by
  let caller := bindings .begin [encoded (requestTerm request), number fuel]
  let initial := GeneralRuleJobExecution.start request licensed
  let selected := ("state", encoded (stateTerm initial)) :: caller
  apply helper_call .begin [] state _ [encoded (requestTerm request), number fuel] _ rfl (by
    simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
  rw [begin_shape]
  apply branch_returns caller selected state _ (encoded (encodeOption stateTerm (some initial))) beginCases beginBody _
  · apply start_captured_returns caller state request licensed
    simp [caller, bindings, Helper.names, applySubst, Subst.lookup]
  · simp [beginCases, selected, caller, bindings, Helper.names, SpaceSemantics.selectCase,
      SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
      encodeOption, CettaWireAtom.encode, CettaWireAtom.encodeMany]
  · apply run_captured_returns selected state request finiteProvider fuel initial
    · exact GeneralRuleJobExecution.job_start_free_within _ request licensed
        (fun _ member => List.mem_append_left _ member)
    · simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]

/-- Completed target runs expose the complete source cursor state and perform
no input, output or store mutation. Finite fuel can still leave pending work. -/
theorem run_completed_iff (caller : Subst) (state : State) (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (fuel : Nat) (machine : GeneralRuleJobExecution.State request)
    (covered : GeneralRuleJobExecution.jobStateFreeWithin
      (GeneralRuleJobObservation.requestFootprint request) request machine) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (requestTerm request), number fuel, encoded (stateTerm machine)])
    (after : State) (answers input output : List Atom) :
    (∃ evaluatorFuel, Eval.run program evaluatorFuel
      {state, control := .evaluate caller (a "gslt:driver:job-run" arguments)} =
        .complete after answers input output) ↔
      after = state ∧ answers = [encoded (encodeOption stateTerm
        (some (GeneralRuleJobExecution.run request fuel machine)))] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program caller state state _ _
    (run_captured_returns caller state request finiteProvider fuel machine covered arguments captured) after answers input output

theorem begin_completed_iff (state : State) (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (licensed : request.job.Valid request.plan request.bound request.expected request.source) (fuel : Nat)
    (after : State) (answers input output : List Atom) :
    (∃ evaluatorFuel, Eval.run program evaluatorFuel
      {state, control := .evaluate [] (a "gslt:driver:job-begin" [encoded (requestTerm request), number fuel])} =
        .complete after answers input output) ↔
      after = state ∧ answers = [encoded (encodeOption stateTerm
        (some (GeneralRuleJobExecution.run request fuel (GeneralRuleJobExecution.start request licensed))))] ∧
        input = [] ∧ output = [] :=
  pure_returns_completed_iff program [] state state _ _ (begin_returns state request finiteProvider licensed fuel)
    after answers input output

/-- Resumption consumes the retained cursor state. It preserves the entire
observation of the corresponding uninterrupted execution. -/
theorem resume_returns (state : State) (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (first second : Nat) :
    PureReturns program [] state
      (a "gslt:driver:job-run" [encoded (requestTerm request), number second,
        encoded (stateTerm (GeneralRuleJobExecution.run request first
          (GeneralRuleJobExecution.start request licensed)))]) state
      (encoded (encodeOption stateTerm (some (GeneralRuleJobExecution.run request (first + second)
        (GeneralRuleJobExecution.start request licensed))))) := by
  rw [GeneralRuleJobExecution.run_add]
  exact run_returns state request finiteProvider second _
    (GeneralRuleJobExecution.job_run_finite_free_within request licensed first)

theorem finish_returns (state : State) (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (licensed : request.job.Valid request.plan request.bound request.expected request.source) :
    PureReturns program [] state
      (a "gslt:driver:job-begin" [encoded (requestTerm request),
        number (GeneralRuleJobExecution.workBound request licensed)]) state
      (encoded (encodeOption stateTerm (some (GeneralRuleJobExecution.finishState request licensed)))) :=
  begin_returns state request finiteProvider licensed (GeneralRuleJobExecution.workBound request licensed)

/-- A completed observation is stated directly using the target evaluator.
The observed receipt list is independent data; it is not defined by source replay. -/
def FinishedObservation (state : State) (request : GeneralRuleJobExecution.Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (agenda : Term) (receipts : List GeneralRuleJobs.Receipt) (unresolved : Term) (work : Nat) : Prop :=
  ∃ evaluatorFuel, Eval.run program evaluatorFuel
    {state, control := .evaluate []
      (a "gslt:driver:job-begin" [encoded (requestTerm request),
        number (GeneralRuleJobExecution.workBound request licensed)])} =
    .complete state [encoded (.application "Some" [.application "PremiseState"
      [agenda, encodeList ScopedRuleJobReadoutExecution.receiptTerm receipts, unresolved, .natural work]])] [] []

theorem finished_observation_iff (state : State) (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (agenda : Term) (receipts : List GeneralRuleJobs.Receipt) (unresolved : Term) (work : Nat) :
    FinishedObservation state request licensed agenda receipts unresolved work ↔
      agenda = encodeList taskTerm (GeneralRuleJobExecution.finishState request licensed).agenda ∧
      receipts = (GeneralRuleJobExecution.finishState request licensed).answers.map Subtype.val ∧
      unresolved = encodeList obligationTerm (GeneralRuleJobExecution.finishState request licensed).unresolved ∧
      work = (GeneralRuleJobExecution.finishState request licensed).work := by
  let finished := GeneralRuleJobExecution.finishState request licensed
  have receiptEncoding : encodeList answerTerm finished.answers =
      encodeList ScopedRuleJobReadoutExecution.receiptTerm (finished.answers.map Subtype.val) := by
    rw [encodeList_map]
    rfl
  unfold FinishedObservation
  rw [begin_completed_iff state request finiteProvider licensed (GeneralRuleJobExecution.workBound request licensed)]
  change (state = state ∧
    [encoded (.application "Some" [.application "PremiseState"
      [agenda, encodeList ScopedRuleJobReadoutExecution.receiptTerm receipts, unresolved, .natural work]])] =
    [encoded (encodeOption stateTerm (some finished))] ∧ ([] : List Atom) = [] ∧ ([] : List Atom) = []) ↔ _
  simp only [true_and, and_true, List.cons.injEq, CettaWireAtom.encode_eq_encode, encodeOption,
    stateTerm, PremiseSchedulerExecution.schedulerStateTerm, Term.application.injEq,
    List.cons.injEq, Term.natural.injEq, receiptEncoding,
    (encodeList_injective ScopedRuleJobReadoutExecution.receiptTerm
      ScopedRuleJobReadoutExecution.receiptTerm_injective).eq_iff]
  rfl

/-- The actual completed cursor driver contains precisely the valid receipts
of its selected original job. This includes refused replacements and duplicate
physical answer occurrences through the ordered list theorem above. -/
theorem finished_receipt_iff (state : State) (request : GeneralRuleJobExecution.Request)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (checked : GeneralPremise.checkStepStratification request.environment.language = true)
    (receipt : GeneralRuleJobs.Receipt) :
    (∃ agenda receipts unresolved work,
      FinishedObservation state request licensed agenda receipts unresolved work ∧ receipt ∈ receipts) ↔
      receipt.Valid request.plan request.bound request.expected request.source ∧ receipt.job = request.job := by
  constructor
  · rintro ⟨agenda, receipts, unresolved, work, observed, member⟩
    have same := (finished_observation_iff state request finiteProvider licensed agenda receipts unresolved work).mp observed
    apply (GeneralRuleJobExecution.finishState_receipt_iff request licensed checked receipt).mp
    simpa only [same.2.1] using member
  · intro valid
    let finished := GeneralRuleJobExecution.finishState request licensed
    refine ⟨encodeList taskTerm finished.agenda, finished.answers.map Subtype.val,
      encodeList obligationTerm finished.unresolved, finished.work, ?_, ?_⟩
    · exact (finished_observation_iff state request finiteProvider licensed _ _ _ _).mpr ⟨rfl, rfl, rfl, rfl⟩
    · exact (GeneralRuleJobExecution.finishState_receipt_iff request licensed checked receipt).mpr valid

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralRuleDriverExecution
