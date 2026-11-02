import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseSchedulerExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralPremiseMachineExecution.Core
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecution

/-! Execution of retained premise-machine scheduling through actual MeTTa calls. -/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseMachineRunExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open SpaceSemantics (Program Equation)
open Eval
open Mettapedia.OSLF.MeTTaIL.GeneralPremise
open PremiseSchedulerExecution (schedulerStateTerm schedulerExpansionTerm)
open scoped ProgramQuotation

def sourceProgram : Program := RuleExecutionProgram.premiseMachineRunProgram
def referenceRuntime : Program := PremiseSchedulerExecution.runtime.append sourceProgram

def executionHeadNames : List String :=
  PremiseSchedulerExecution.executionHeadNames ++
    ["-", "==", "if", "PremiseEvaluate", "PremiseDone",
     "gslt:premise:machine-start", "gslt:premise:machine-tick", "gslt:premise:machine-run"]

def executionHeads (head : String) : Bool := executionHeadNames.contains head

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
private abbrev number (value : Nat) : Atom := encoded (.natural value)

private inductive Helper where | start | tick | run
private def Helper.head : Helper → String
  | .start => "gslt:premise:machine-start"
  | .tick => "gslt:premise:machine-tick"
  | .run => "gslt:premise:machine-run"
private def Helper.names : Helper → List String
  | .start => ["goal"]
  | .tick => ["environment", "state"]
  | .run => ["environment", "fuel", "state"]
private def equations (head : String) : List Equation :=
  referenceRuntime.equations.filter (fun equation => equation.head == head)
private def equation (helper : Helper) : Equation :=
  (equations helper.head)[0]'(by cases helper <;> decide +kernel)
private def bindings (helper : Helper) (values : List Atom) : Subst :=
  (helper.names.zip values).reverse

private theorem helper_supported (helper : Helper) : executionHeads helper.head = true := by
  cases helper <;> decide +kernel

private theorem helper_clause (target : Program)
    (agreement : ProgramAgreementOn executionHeads referenceRuntime target)
    (helper : Helper) (values : List Atom) (length : values.length = helper.names.length) :
    clauses target helper.head values =
      [.evaluate (bindings helper values) (equation helper).body] := by
  apply PureData.selected_clause_agreement agreement (helper_supported helper)
  exact PureData.named_equation_clause referenceRuntime helper.head (equation helper)
    helper.names values (by cases helper <;> rfl) (by cases helper <;> decide +kernel)
    (by cases helper <;> decide) length

private theorem helper_raw (target : Program)
    (agreement : ProgramAgreementOn executionHeads referenceRuntime target)
    (helper : Helper) (index : Nat) (bounded : index < helper.names.length) :
    argumentIsRaw target helper.head index = true := by
  rw [← agreement.demand helper.head index (helper_supported helper)]
  have small : index = 0 ∨ index = 1 ∨ index = 2 := by
    cases helper <;> simp only [Helper.names, List.length_cons, List.length_nil] at bounded <;> omega
  rcases small with rfl | rfl | rfl <;> cases helper
  all_goals simp only [Helper.names, List.length_cons, List.length_nil] at bounded
  all_goals first | omega | decide +kernel

private theorem helper_call (target : Program)
    (agreement : ProgramAgreementOn executionHeads referenceRuntime target)
    (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns target (bindings helper values) state (equation helper).body state answer) :
    PureReturns target caller state (a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return target caller (bindings helper values) state state
    helper.head arguments (equation helper).body answer
    (by cases helper <;> decide) (by cases helper <;> decide) (by cases helper <;> decide)
  · rw [← agreement.dispatch helper.head (helper_supported helper)]
    cases helper <;> decide +kernel
  · intro index bounded
    apply helper_raw target agreement helper index
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    omega
  · rw [captured]
    exact helper_clause target agreement helper values length
  · exact returned

private theorem helper_capture (target : Program)
    (agreement : ProgramAgreementOn executionHeads referenceRuntime target)
    (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns target [] state (a helper.head values) state answer) :
    PureReturns target caller state (a helper.head arguments) state answer := by
  apply PureData.raw_capture_returns target [] caller state state helper.head values arguments answer
  · rw [← agreement.dispatch helper.head (helper_supported helper)]
    cases helper <;> decide +kernel
  · intro index bounded
    exact helper_raw target agreement helper index (by omega)
  · cases helper <;> decide
  · have unchanged : applySubst [] = id := by
      funext value; exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
    simpa only [unchanged, List.map_id] using captured.symm
  · exact returned

private theorem scheduler_reference_agreement :
    ProgramAgreementOn PremiseSchedulerExecution.executionHeads
      PremiseSchedulerExecution.runtime referenceRuntime := by
  apply appended_program_agreement
  · intro equation member
    have checked : sourceProgram.equations.all (fun equation =>
        !PremiseSchedulerExecution.executionHeads equation.head) = true := by decide +kernel
    have row := List.all_eq_true.mp checked equation member
    cases selected : PremiseSchedulerExecution.executionHeads equation.head with
    | false => rfl
    | true => simp [selected] at row
  · intro name types member
    have checked : sourceProgram.declarations.all (fun declaration => match declaration with
        | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] =>
            !PremiseSchedulerExecution.executionHeads head
        | _ => true) = true := by decide +kernel
    have row := List.all_eq_true.mp checked
      (.expression [.symbol ":", .symbol name, .expression (.symbol "->" :: types)]) member
    cases selected : PremiseSchedulerExecution.executionHeads name with
    | false => rfl
    | true => simp [selected] at row

private theorem scheduler_target_agreement (target : Program)
    (agreement : ProgramAgreementOn executionHeads referenceRuntime target) :
    ProgramAgreementOn PremiseSchedulerExecution.executionHeads
      PremiseSchedulerExecution.runtime target := by
  have included (head : String) (supported : PremiseSchedulerExecution.executionHeads head = true) :
      executionHeads head = true := by
    unfold executionHeads executionHeadNames
    rw [List.contains_append]
    change PremiseSchedulerExecution.executionHeadNames.contains head = true at supported
    simp only [supported, Bool.true_or]
  constructor
  · intro head supported
    exact (scheduler_reference_agreement.dispatch head supported).trans
      (agreement.dispatch head (included head supported))
  · intro head index supported
    exact (scheduler_reference_agreement.demand head index supported).trans
      (agreement.demand head index (included head supported))
  · intro head values supported
    exact (scheduler_reference_agreement.bodies head values supported).trans
      (agreement.bodies head values (included head supported))

private def dataHeads : List String :=
  ["Some", "None", "PremiseState", "PremiseEvaluate", "PremiseDone", "LCons", "LNil"]

private theorem data_inert (target : Program)
    (agreement : ProgramAgreementOn executionHeads referenceRuntime target)
    (head : String) (member : head ∈ dataHeads) :
    (ioHead head || StdLib.known head || target.equations.any (·.head == head)) = false := by
  have supported : executionHeads head = true := by
    simp only [dataHeads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  rw [← agreement.dispatch head supported]
  simp only [dataHeads, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem template_constructor (target : Program)
    (agreement : ProgramAgreementOn executionHeads referenceRuntime target)
    (head : String) (arguments : List Atom) (member : head ∈ dataHeads)
    (children : ∀ child ∈ arguments, PureData.Template target child) :
    PureData.Template target (a head arguments) := by
  apply PureData.Template.constructor head arguments (data_inert target agreement head member)
  · simp only [dataHeads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact children

private theorem branch_returns (target : Program) (caller selected : Subst) (state : State)
    (expression value : Atom) (rows : SpaceSemantics.Cases) (body answer : Atom)
    (computed : PureReturns target caller state expression state value)
    (matched : SpaceSemantics.selectCase caller value rows = some (selected, body))
    (continued : PureReturns target selected state body state answer) :
    PureReturns target caller state
      (a "case" [expression, .expression (rows.map fun row => .expression [row.1, row.2])]) state answer :=
  case_returns target caller selected state state state expression value body answer _ rows
    (read_cases_encoded _) computed matched continued

private theorem named_let_returns (target : Program) (caller : Subst) (state : State)
    (name : String) (expression value body answer : Atom)
    (fresh : caller.lookup name = none)
    (computed : PureReturns target caller state expression state value)
    (continued : PureReturns target ((name, value) :: caller) state body state answer) :
    PureReturns target caller state (a "let" [v name, expression, body]) state answer := by
  apply let_returns target caller ((name, value) :: caller) state state state
    (v name) expression body value answer computed
  · simp [SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, fresh]
  · exact continued

private theorem bool_if_returns (target : Program) (caller : Subst) (state : State)
    (condition : Atom) (value : Bool) (yes no answer : Atom)
    (tested : PureReturns target caller state condition state (Effects.boolean value))
    (continued : PureReturns target caller state (if value then yes else no) state answer) :
    PureReturns target caller state (a "if" [condition, yes, no]) state answer := by
  apply if_returns target caller state state state condition (Effects.boolean value) yes no answer tested
  have boolean_same : (Effects.boolean value == Effects.boolean true) = value := by
    cases value <;> decide +kernel
  simpa only [boolean_same] using continued

private def startBody : Atom :=
  a "Some" [a "PremiseState"
    [a "LCons" [a "PremiseEvaluate" [v "goal", a "PremiseDone" [v "goal"]], .symbol "LNil"],
      .symbol "LNil", .symbol "LNil", number 0]]

private theorem start_shape : (equation .start).body = startBody := by rfl

private theorem start_template (target : Program)
    (agreement : ProgramAgreementOn executionHeads referenceRuntime target) :
    PureData.Template target startBody := by
  unfold startBody
  apply template_constructor target agreement "Some" _ (by simp [dataHeads])
  intro child member
  simp only [List.mem_singleton] at member; subst child
  apply template_constructor target agreement "PremiseState" _ (by simp [dataHeads])
  intro child member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · apply template_constructor target agreement "LCons" _ (by simp [dataHeads])
    intro child member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · apply template_constructor target agreement "PremiseEvaluate" _ (by simp [dataHeads])
      intro child member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact .captured _
      · apply template_constructor target agreement "PremiseDone" _ (by simp [dataHeads])
        intro child member
        simp only [List.mem_singleton] at member; subst child
        exact .captured _
    · exact .symbol _
  · exact .symbol _
  · exact .symbol _
  · exact .grounded _

theorem start_returns (target : Program)
    (agreement : ProgramAgreementOn executionHeads referenceRuntime target)
    (state : State) (environment : Environment) (goal : Execution.Goal) :
    PureReturns target [] state
      (a "gslt:premise:machine-start" [encoded (PremiseOperationsExecution.GeneralExecution.goalTerm goal)])
      state (encoded (encodeOption PremiseOperationsExecution.GeneralExecution.stateTerm
        (some (Execution.start environment goal)))) := by
  let caller := bindings .start [encoded (PremiseOperationsExecution.GeneralExecution.goalTerm goal)]
  apply helper_call target agreement .start [] state _
    [encoded (PremiseOperationsExecution.GeneralExecution.goalTerm goal)] _ rfl
    (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
  rw [start_shape]
  simpa [startBody, caller, bindings, Helper.names, Execution.start,
    PremiseOperationsExecution.GeneralExecution.stateTerm, schedulerStateTerm,
    PremiseOperationsExecution.GeneralExecution.taskTerm,
    PremiseOperationsExecution.GeneralExecution.continuationTerm, encodeOption, encodeList,
    encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany, applySubst, applySubst.applySubstList,
    Subst.lookup] using PureData.template_return target caller state startBody
      (start_template target agreement)

#print axioms start_returns

private def tickBody : Atom :=
  a "let" [v "expanded", a "gslt:premise:machine-expand-in" [v "environment", v "task"],
    a "gslt:premise:machine-commit" [v "state", v "expanded"]]

private def tickCases : SpaceSemantics.Cases :=
  [(a "PremiseState" [.symbol "LNil", v "answers", v "unresolved", v "work"],
      a "Some" [v "state"]),
   (a "PremiseState" [a "LCons" [v "task", v "rest"], v "answers", v "unresolved", v "work"],
      tickBody),
   (v "bad", .symbol "None")]

private theorem tick_shape : (equation .tick).body =
    a "case" [v "state", .expression (tickCases.map fun row => .expression [row.1, row.2])] := by
  rfl

theorem tick_returns {Task Answer Obligation : Type} (target : Program)
    (agreement : ProgramAgreementOn executionHeads referenceRuntime target)
    (state : State) (environment : Term)
    (task : Task → Term) (answer : Answer → Term) (obligation : Obligation → Term)
    (expand : Task → Scheduler.Expansion Task Answer Obligation)
    (scheduler : Scheduler.State Task Answer Obligation)
    (expanded : ∀ current ∈ scheduler.agenda, ∀ caller : Subst,
      [v "environment", v "task"].map (applySubst caller) = [encoded environment, encoded (task current)] →
      PureReturns target caller state
        (a "gslt:premise:machine-expand-in" [v "environment", v "task"])
        state (encoded (encodeOption (schedulerExpansionTerm task answer obligation) (some (expand current))))) :
    PureReturns target [] state
      (a "gslt:premise:machine-tick" [encoded environment,
        encoded (schedulerStateTerm task answer obligation scheduler)])
      state (encoded (encodeOption (schedulerStateTerm task answer obligation)
        (some (Scheduler.tick expand scheduler)))) := by
  let value := encoded (schedulerStateTerm task answer obligation scheduler)
  let caller := bindings .tick [encoded environment, value]
  apply helper_call target agreement .tick [] state _ [encoded environment, value] _ rfl
    (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]; rfl)
  rw [tick_shape]
  cases agenda : scheduler.agenda with
  | nil =>
      let selected := [("work", number scheduler.work),
        ("unresolved", encoded (encodeList obligation scheduler.unresolved)),
        ("answers", encoded (encodeList answer scheduler.answers))] ++ caller
      apply branch_returns target caller selected state _ value tickCases (a "Some" [v "state"]) _
      · simpa [caller, bindings, Helper.names, applySubst, Subst.lookup] using
          variable_returns target caller state "state"
      · simp [value, schedulerStateTerm, agenda, tickCases, selected, caller,
          bindings, Helper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, encodeList, Subst.lookup, encoded]
      · have templated : PureData.Template target (a "Some" [v "state"]) :=
          template_constructor target agreement _ _ (by simp [dataHeads]) (by
            intro child member
            simp only [List.mem_singleton] at member
            subst child
            exact .captured _)
        simpa [Scheduler.tick, agenda, encodeOption, schedulerStateTerm, value, selected, caller,
          bindings, Helper.names, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          applySubst, applySubst.applySubstList, Subst.lookup] using
          PureData.template_return target selected state _ templated
  | cons current rest =>
      let selected := [("work", number scheduler.work),
        ("unresolved", encoded (encodeList obligation scheduler.unresolved)),
        ("answers", encoded (encodeList answer scheduler.answers)),
        ("rest", encoded (encodeList task rest)), ("task", encoded (task current))] ++ caller
      let expansion := encoded (encodeOption (schedulerExpansionTerm task answer obligation) (some (expand current)))
      let continued := ("expanded", expansion) :: selected
      apply branch_returns target caller selected state _ value tickCases tickBody _
      · simpa [caller, bindings, Helper.names, applySubst, Subst.lookup] using
          variable_returns target caller state "state"
      · simp [value, schedulerStateTerm, agenda, tickCases, selected, caller,
          bindings, Helper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, encodeList, Subst.lookup, encoded]
      · unfold tickBody
        apply named_let_returns target selected state "expanded" _ expansion
        · simp [selected, caller, bindings, Helper.names, Subst.lookup]
        · apply expanded current (by simp [agenda]) selected
          simp [selected, caller, bindings, Helper.names, applySubst, Subst.lookup]
        · apply PremiseSchedulerExecution.returns_in_extension target
            (scheduler_target_agreement target agreement) (by decide +kernel)
          apply PremiseSchedulerExecution.commit_captured_returns continued state
            task answer obligation expand scheduler [v "state", v "expanded"]
          simp [continued, expansion, selected, caller, bindings, Helper.names,
            applySubst, Subst.lookup, agenda, value]

theorem tick_captured_returns {Task Answer Obligation : Type} (target : Program)
    (agreement : ProgramAgreementOn executionHeads referenceRuntime target)
    (caller : Subst) (state : State) (environment : Term)
    (task : Task → Term) (answer : Answer → Term) (obligation : Obligation → Term)
    (expand : Task → Scheduler.Expansion Task Answer Obligation)
    (scheduler : Scheduler.State Task Answer Obligation) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded environment, encoded (schedulerStateTerm task answer obligation scheduler)])
    (expanded : ∀ current ∈ scheduler.agenda, ∀ callee : Subst,
      [v "environment", v "task"].map (applySubst callee) = [encoded environment, encoded (task current)] →
      PureReturns target callee state
        (a "gslt:premise:machine-expand-in" [v "environment", v "task"])
        state (encoded (encodeOption (schedulerExpansionTerm task answer obligation) (some (expand current))))) :
    PureReturns target caller state (a "gslt:premise:machine-tick" arguments)
      state (encoded (encodeOption (schedulerStateTerm task answer obligation)
        (some (Scheduler.tick expand scheduler)))) :=
  helper_capture target agreement .tick caller state arguments _ _ rfl captured
    (tick_returns target agreement state environment task answer obligation expand scheduler expanded)

private theorem native_demanded (target : Program)
    (agreement : ProgramAgreementOn executionHeads referenceRuntime target)
    (head : String) (member : head ∈ ["-", "=="]) (index : Nat) (bounded : index < 2) :
    argumentIsRaw target head index = false := by
  have supported : executionHeads head = true := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide +kernel
  rw [← agreement.demand head index supported]
  have small : index = 0 ∨ index = 1 := by omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rcases small with rfl | rfl <;> decide +kernel

private def runContinue : Atom :=
  a "let" [v "remaining", a "-" [v "fuel", number 1],
    a "gslt:premise:machine-run" [v "environment", v "remaining", v "next-state"]]
private def runCases : SpaceSemantics.Cases :=
  [(a "Some" [v "next-state"], runContinue), (v "unavailable", .symbol "None")]
private def runBody : Atom :=
  a "let" [v "next", a "gslt:premise:machine-tick" [v "environment", v "state"],
    a "case" [v "next", .expression (runCases.map fun row => .expression [row.1, row.2])]]
private theorem run_shape : (equation .run).body =
    a "if" [a "==" [v "fuel", number 0], a "Some" [v "state"], runBody] := by rfl

/-- Fuel advances exactly the original scheduler. Expansion is required only for
frames actually present at an executed source prefix, rather than arbitrary tasks. -/
theorem run_returns {Task Answer Obligation : Type} (target : Program)
    (agreement : ProgramAgreementOn executionHeads referenceRuntime target)
    (state : State) (environment : Term)
    (task : Task → Term) (answer : Answer → Term) (obligation : Obligation → Term)
    (expand : Task → Scheduler.Expansion Task Answer Obligation)
    (fuel : Nat) (scheduler : Scheduler.State Task Answer Obligation)
    (expanded : ∀ index < fuel, ∀ current ∈ (Scheduler.run expand index scheduler).agenda,
      ∀ caller : Subst,
      [v "environment", v "task"].map (applySubst caller) = [encoded environment, encoded (task current)] →
      PureReturns target caller state
        (a "gslt:premise:machine-expand-in" [v "environment", v "task"])
        state (encoded (encodeOption (schedulerExpansionTerm task answer obligation) (some (expand current))))) :
    PureReturns target [] state
      (a "gslt:premise:machine-run" [encoded environment, number fuel,
        encoded (schedulerStateTerm task answer obligation scheduler)])
      state (encoded (encodeOption (schedulerStateTerm task answer obligation)
        (some (Scheduler.run expand fuel scheduler)))) := by
  induction fuel generalizing scheduler with
  | zero =>
      let value := encoded (schedulerStateTerm task answer obligation scheduler)
      let caller := bindings .run [encoded environment, number 0, value]
      apply helper_call target agreement .run [] state _ [encoded environment, number 0, value] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]; rfl)
      rw [run_shape]
      have tested := CettaWireAtom.equality_evaluated_returns target caller state (.natural 0) (.natural 0)
        (v "fuel") (number 0)
        (native_demanded target agreement _ (by simp) 0 (by decide))
        (native_demanded target agreement _ (by simp) 1 (by decide))
        (by simpa [caller, bindings, Helper.names, applySubst, Subst.lookup] using variable_returns target caller state "fuel")
        (grounded_returns target caller state (.int 0))
      simp only [decide_true] at tested
      apply bool_if_returns target caller state _ true _ _ _ tested
      have templated : PureData.Template target (a "Some" [v "state"]) :=
        template_constructor target agreement _ _ (by simp [dataHeads]) (by
          intro child member; simp only [List.mem_singleton] at member; subst child; exact .captured _)
      simpa [Scheduler.run, caller, bindings, Helper.names, applySubst, applySubst.applySubstList,
        Subst.lookup, encodeOption, CettaWireAtom.encode, CettaWireAtom.encodeMany] using
        PureData.template_return target caller state _ templated
  | succ fuel ih =>
      let value := encoded (schedulerStateTerm task answer obligation scheduler)
      let caller := bindings .run [encoded environment, number (fuel + 1), value]
      let nextScheduler := Scheduler.tick expand scheduler
      let nextValue := encoded (schedulerStateTerm task answer obligation nextScheduler)
      let next := ("next", a "Some" [nextValue]) :: caller
      let selected := ("next-state", nextValue) :: next
      let remaining := ("remaining", number fuel) :: selected
      apply helper_call target agreement .run [] state _ [encoded environment, number (fuel + 1), value] _ rfl
        (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]; rfl)
      rw [run_shape]
      have tested := CettaWireAtom.equality_evaluated_returns target caller state (.natural (fuel + 1)) (.natural 0)
        (v "fuel") (number 0)
        (native_demanded target agreement _ (by simp) 0 (by decide))
        (native_demanded target agreement _ (by simp) 1 (by decide))
        (by simpa [caller, bindings, Helper.names, applySubst, Subst.lookup] using variable_returns target caller state "fuel")
        (grounded_returns target caller state (.int 0))
      simp only [Term.natural.injEq, Nat.add_one_ne_zero, decide_false] at tested
      apply bool_if_returns target caller state _ false _ _ _ tested
      unfold runBody
      apply named_let_returns target caller state "next" _ (a "Some" [nextValue])
      · simp [caller, bindings, Helper.names, Subst.lookup]
      · apply tick_captured_returns target agreement caller state environment task answer obligation expand scheduler
          [v "environment", v "state"]
        · simp [caller, bindings, Helper.names, applySubst, Subst.lookup, value]
        · intro current member callee captured
          apply expanded 0 (by omega) current
          · simpa only [Scheduler.run] using member
          · exact captured
      · apply branch_returns target next selected state (v "next") (a "Some" [nextValue]) runCases runContinue _
        · simpa [next, caller, bindings, Helper.names, applySubst, Subst.lookup] using variable_returns target next state "next"
        · simp [runCases, selected, next, caller, bindings, Helper.names, SpaceSemantics.selectCase,
            SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
        · unfold runContinue
          apply named_let_returns target selected state "remaining" _ (number fuel)
          · simp [selected, next, caller, bindings, Helper.names, Subst.lookup]
          · apply native_binary_call_returns target selected state state state state "-"
              (v "fuel") (number 1) (number (fuel + 1)) (number 1) (number fuel)
              (by decide) (by decide)
              (native_demanded target agreement _ (by simp) 0 (by decide))
              (native_demanded target agreement _ (by simp) 1 (by decide))
            · simpa [selected, next, caller, bindings, Helper.names, applySubst, Subst.lookup] using variable_returns target selected state "fuel"
            · exact grounded_returns target selected state (.int 1)
            · change (Except.ok (state, [Atom.grounded (.int (((fuel + 1 : Nat) : Int) - 1))]) : Effects.Result) =
                  Except.ok (state, [.grounded (.int (fuel : Int))])
              simp
            · decide
          · apply helper_capture target agreement .run remaining state
              [v "environment", v "remaining", v "next-state"]
              [encoded environment, number fuel, nextValue] _ rfl
            · simp [remaining, selected, next, caller, bindings, Helper.names, applySubst, Subst.lookup]
            · apply ih nextScheduler
              intro index bounded current member callee captured
              apply expanded (index + 1) (by omega) current
              · simpa only [Scheduler.run] using member
              · exact captured

#print axioms tick_returns
#print axioms tick_captured_returns
#print axioms run_returns

theorem run_captured_returns {Task Answer Obligation : Type} (target : Program)
    (agreement : ProgramAgreementOn executionHeads referenceRuntime target)
    (caller : Subst) (state : State) (environment : Term)
    (task : Task → Term) (answer : Answer → Term) (obligation : Obligation → Term)
    (expand : Task → Scheduler.Expansion Task Answer Obligation)
    (fuel : Nat) (scheduler : Scheduler.State Task Answer Obligation) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) = [encoded environment, number fuel,
      encoded (schedulerStateTerm task answer obligation scheduler)])
    (expanded : ∀ index < fuel, ∀ current ∈ (Scheduler.run expand index scheduler).agenda,
      ∀ callee : Subst,
      [v "environment", v "task"].map (applySubst callee) = [encoded environment, encoded (task current)] →
      PureReturns target callee state
        (a "gslt:premise:machine-expand-in" [v "environment", v "task"])
        state (encoded (encodeOption (schedulerExpansionTerm task answer obligation) (some (expand current))))) :
    PureReturns target caller state (a "gslt:premise:machine-run" arguments)
      state (encoded (encodeOption (schedulerStateTerm task answer obligation)
        (some (Scheduler.run expand fuel scheduler)))) :=
  helper_capture target agreement .run caller state arguments _ _ rfl captured
    (run_returns target agreement state environment task answer obligation expand fuel scheduler expanded)

/-- Completed target runs return exactly the original scheduler observation,
including the pending frames and unresolved obligations retained at this fuel. -/
theorem run_completed_iff {Task Answer Obligation : Type} (target : Program)
    (agreement : ProgramAgreementOn executionHeads referenceRuntime target)
    (caller : Subst) (state : State) (environment : Term)
    (task : Task → Term) (answer : Answer → Term) (obligation : Obligation → Term)
    (expand : Task → Scheduler.Expansion Task Answer Obligation)
    (fuel : Nat) (scheduler : Scheduler.State Task Answer Obligation) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) = [encoded environment, number fuel,
      encoded (schedulerStateTerm task answer obligation scheduler)])
    (expanded : ∀ index < fuel, ∀ current ∈ (Scheduler.run expand index scheduler).agenda,
      ∀ callee : Subst,
      [v "environment", v "task"].map (applySubst callee) = [encoded environment, encoded (task current)] →
      PureReturns target callee state
        (a "gslt:premise:machine-expand-in" [v "environment", v "task"])
        state (encoded (encodeOption (schedulerExpansionTerm task answer obligation) (some (expand current)))))
    (after : State) (answers input output : List Atom) :
    (∃ evaluatorFuel, Eval.run target evaluatorFuel
        { state := state, control := .evaluate caller (a "gslt:premise:machine-run" arguments) } =
      .complete after answers input output) ↔
      after = state ∧ answers = [encoded (encodeOption (schedulerStateTerm task answer obligation)
        (some (Scheduler.run expand fuel scheduler)))] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff target caller state state _ _
    (run_captured_returns target agreement caller state environment task answer obligation
      expand fuel scheduler arguments captured expanded) after answers input output

theorem run_derivation_iff {Task Answer Obligation : Type} (target : Program)
    (agreement : ProgramAgreementOn executionHeads referenceRuntime target)
    (caller : Subst) (state : State) (environment : Term)
    (task : Task → Term) (answer : Answer → Term) (obligation : Obligation → Term)
    (expand : Task → Scheduler.Expansion Task Answer Obligation)
    (fuel : Nat) (scheduler : Scheduler.State Task Answer Obligation) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) = [encoded environment, number fuel,
      encoded (schedulerStateTerm task answer obligation scheduler)])
    (expanded : ∀ index < fuel, ∀ current ∈ (Scheduler.run expand index scheduler).agenda,
      ∀ callee : Subst,
      [v "environment", v "task"].map (applySubst callee) = [encoded environment, encoded (task current)] →
      PureReturns target callee state
        (a "gslt:premise:machine-expand-in" [v "environment", v "task"])
        state (encoded (encodeOption (schedulerExpansionTerm task answer obligation) (some (expand current)))))
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs target
      { state := state, control := .evaluate caller (a "gslt:premise:machine-run" arguments) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [encoded (encodeOption (schedulerStateTerm task answer obligation)
        (some (Scheduler.run expand fuel scheduler)))] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff target caller state state _ _
    (run_captured_returns target agreement caller state environment task answer obligation
      expand fuel scheduler arguments captured expanded) after answers input output

theorem run_resumed_derivation_iff {Task Answer Obligation : Type} (target : Program)
    (agreement : ProgramAgreementOn executionHeads referenceRuntime target)
    (state : State) (environment : Term)
    (task : Task → Term) (answer : Answer → Term) (obligation : Obligation → Term)
    (expand : Task → Scheduler.Expansion Task Answer Obligation)
    (first second : Nat) (scheduler : Scheduler.State Task Answer Obligation)
    (expanded : ∀ index < first + second, ∀ current ∈ (Scheduler.run expand index scheduler).agenda,
      ∀ callee : Subst,
      [v "environment", v "task"].map (applySubst callee) = [encoded environment, encoded (task current)] →
      PureReturns target callee state
        (a "gslt:premise:machine-expand-in" [v "environment", v "task"])
        state (encoded (encodeOption (schedulerExpansionTerm task answer obligation) (some (expand current)))))
    (after : State) (answers input output : List Atom) :
    DeclarativeSpec.Runs target
      { state := state, control := .evaluate [] (a "gslt:premise:machine-run"
        [encoded environment, number (first + second),
         encoded (schedulerStateTerm task answer obligation scheduler)]) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [encoded (encodeOption (schedulerStateTerm task answer obligation)
        (some (Scheduler.run expand second (Scheduler.run expand first scheduler))))] ∧
        input = [] ∧ output = [] := by
  have returned := run_derivation_iff target agreement [] state environment task answer obligation
    expand (first + second) scheduler
    [encoded environment, number (first + second), encoded (schedulerStateTerm task answer obligation scheduler)]
    (by simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil])
    expanded after answers input output
  simpa only [Scheduler.run_add] using returned

#print axioms run_captured_returns
#print axioms run_completed_iff
#print axioms run_derivation_iff
#print axioms run_resumed_derivation_iff

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseMachineRunExecution
