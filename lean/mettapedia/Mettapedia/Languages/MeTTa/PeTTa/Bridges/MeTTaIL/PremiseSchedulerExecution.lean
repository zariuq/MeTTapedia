import Mettapedia.Languages.MeTTa.PeTTa.BridgeTransport
import Mettapedia.Languages.MeTTa.PeTTa.AppendAgreement
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleInstantiationExecution
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseScheduler

/-! Exact execution of the original premise scheduler's commit and completion operations. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseSchedulerExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open SpaceSemantics (Program Equation)
open Eval
open Mettapedia.OSLF.MeTTaIL.GeneralPremise
open scoped ProgramQuotation

def sourceProgram : Program := RuleExecutionProgram.premiseSchedulerProgram

def runtime : Program := RuleExecutionProgram.program.append sourceProgram

private def retainedHead (head : String) : Bool :=
  head != "eval" && head != "gslt:premise:machine-commit" && head != "gslt:premise:machine-complete"

private theorem retained_closed : ProgramClosed retainedHead RuleExecutionProgram.program := by
  exact BridgeKit.closed_of_all _ _ (by decide +kernel) (by decide +kernel)

private theorem retained_agreement : ProgramAgreementOn retainedHead RuleExecutionProgram.program runtime := by
  exact appended_program_agreement_of_all _ _ _ (by decide +kernel) (by decide +kernel)

private theorem retained_returns {caller : Subst} {state : State} {code answer : Atom}
    (supported : codeWithin retainedHead code = true)
    (returned : PureReturns RuleExecutionProgram.program caller state code state answer) :
    PureReturns runtime caller state code state answer :=
  path_of_closed_agreement retained_closed retained_agreement ⟨supported, rfl⟩ returned

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
private abbrev number (value : Nat) : Atom := encoded (.natural value)
private abbrev listValue (terms : List Term) : Atom := encoded (encodeList id terms)

def schedulerStateTerm {Task Answer Obligation : Type}
    (task : Task → Term) (answer : Answer → Term) (obligation : Obligation → Term)
    (state : Scheduler.State Task Answer Obligation) : Term :=
  .application "PremiseState" [encodeList task state.agenda, encodeList answer state.answers,
    encodeList obligation state.unresolved, .natural state.work]

def schedulerExpansionTerm {Task Answer Obligation : Type}
    (task : Task → Term) (answer : Answer → Term) (obligation : Obligation → Term)
    (expansion : Scheduler.Expansion Task Answer Obligation) : Term :=
  .application "PremiseExpansion" [encodeList task expansion.tasks, encodeList answer expansion.answers,
    encodeList obligation expansion.unresolved]

private inductive Helper where | commit | complete
private def Helper.head : Helper → String
  | .commit => "gslt:premise:machine-commit"
  | .complete => "gslt:premise:machine-complete"
private def Helper.names : Helper → List String
  | .commit => ["state", "expanded"]
  | .complete => ["state"]
private def equations (head : String) : List Equation :=
  runtime.equations.filter (fun equation => equation.head == head)
private def equation (helper : Helper) : Equation :=
  (equations helper.head)[0]'(by cases helper <;> decide +kernel)
private def environment (helper : Helper) (values : List Atom) : Subst :=
  (helper.names.zip values).reverse

private theorem helper_clause (helper : Helper) (values : List Atom)
    (length : values.length = helper.names.length) :
    clauses runtime helper.head values =
      [.evaluate (environment helper values) (equation helper).body] :=
  PureData.named_equation_clause runtime helper.head (equation helper) helper.names values
    (by cases helper <;> rfl) (by cases helper <;> decide +kernel)
    (by cases helper <;> decide) length

private theorem helper_raw (helper : Helper) (index : Nat) (bounded : index < helper.names.length) :
    argumentIsRaw runtime helper.head index = true := by
  cases helper <;> simp only [Helper.names, List.length_cons, List.length_nil] at bounded
  all_goals
    have small : index = 0 ∨ index = 1 := by omega
    rcases small with rfl | rfl <;> first | omega | decide +kernel

private theorem helper_call (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns runtime (environment helper values) state (equation helper).body state answer) :
    PureReturns runtime caller state (a helper.head arguments) state answer := by
  apply PureData.raw_authored_call_return runtime caller (environment helper values) state state
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

private theorem captured_closed (values : List Atom) : values.map (applySubst []) = values := by
  have unchanged : applySubst [] = id := by
    funext value; exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
  simp only [unchanged, List.map_id]

private theorem branch_returns (caller selected : Subst) (state : State)
    (expression value : Atom) (rows : SpaceSemantics.Cases) (body answer : Atom)
    (computed : PureReturns runtime caller state expression state value)
    (matched : SpaceSemantics.selectCase caller value rows = some (selected, body))
    (continued : PureReturns runtime selected state body state answer) :
    PureReturns runtime caller state
      (a "case" [expression, .expression (rows.map fun row => .expression [row.1, row.2])]) state answer :=
  case_returns runtime caller selected state state state expression value body answer _ rows
    (read_cases_encoded _) computed matched continued

private def completeCases : SpaceSemantics.Cases :=
  [(a "PremiseState" [.symbol "LNil", v "answers", .symbol "LNil", v "work"], Effects.boolean true),
   (v "pending", Effects.boolean false)]
private theorem complete_shape : (equation .complete).body =
    a "case" [v "state", .expression (completeCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

private theorem append_encoded_returns {α β : Type} (leftEncoder : α → Term)
    (rightEncoder : β → Term) (caller : Subst) (state : State)
    (left : List α) (right : List β) (one two : String)
    (captured : [v one, v two].map (applySubst caller) =
      [encoded (encodeList leftEncoder left), encoded (encodeList rightEncoder right)]) :
    PureReturns runtime caller state (a "gslt:automata:append" [v one, v two]) state
      (encoded (encodeList id (left.map leftEncoder ++ right.map rightEncoder))) := by
  have checked := MatchAutomataSourceExecution.append_captured_returns caller state
    (left.map leftEncoder) (right.map rightEncoder) (v one) (v two) (by
      simpa only [MatchAutomataSourceExecution.listValue, CettaWire.encodeList_map,
        Function.id_comp] using captured)
  exact retained_returns (by rfl)
    (RuleExecutionProgram.automata_captured_returns (by
      simp only [codeWithin, atomsWithin, expressionHeadWithin, Bool.and_true]
      decide +kernel) checked)

private theorem append_list_returns {α : Type} (encoder : α → Term)
    (caller : Subst) (state : State) (left right : List α) (one two : String)
    (captured : [v one, v two].map (applySubst caller) =
      [encoded (encodeList encoder left), encoded (encodeList encoder right)]) :
    PureReturns runtime caller state (a "gslt:automata:append" [v one, v two]) state
      (encoded (encodeList encoder (left ++ right))) := by
  simpa only [← List.map_append, CettaWire.encodeList_map, Function.id_comp] using
    append_encoded_returns encoder encoder caller state left right one two captured

private theorem add_one_returns (caller : Subst) (state : State) (value : Nat)
    (captured : applySubst caller (v "work") = number value) :
    PureReturns runtime caller state (a "+" [v "work", number 1]) state (number (value + 1)) := by
  apply native_binary_call_returns runtime caller state state state state "+"
    (v "work") (number 1) (number value) (number 1) _
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
  · simpa only [captured] using variable_returns runtime caller state "work"
  · exact grounded_returns runtime caller state (.int 1)
  · simpa only [number, encoded, CettaWireAtom.encode, Int.natCast_add, Int.natCast_one] using
      StdLib.integer_addition state (value : Int) 1

private theorem template_constructor (head : String) (arguments : List Atom)
    (constructor : head ∈ ["Some", "PremiseState"])
    (children : ∀ child ∈ arguments, PureData.Template runtime child) :
    PureData.Template runtime (a head arguments) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at constructor
  rcases constructor with (rfl | rfl)
  all_goals exact PureData.Template.constructor _ _ (by decide +kernel) (by decide) children

private def commitResult : Atom :=
  a "Some" [a "PremiseState" [v "agenda", v "all-answers", v "all-unresolved", v "next-work"]]
private def commitPairs : List (Atom × Atom) :=
  [(v "agenda", a "gslt:automata:append" [v "tasks", v "rest"]),
   (v "all-answers", a "gslt:automata:append" [v "answers", v "new-answers"]),
   (v "all-unresolved", a "gslt:automata:append" [v "unresolved", v "new-unresolved"]),
   (v "next-work", a "+" [v "work", number 1])]
private def commitExpansionBody : Atom :=
  a "let*" [.expression (commitPairs.map fun pair => .expression [pair.1, pair.2]), commitResult]
private def commitExpansionCases : SpaceSemantics.Cases :=
  [(a "Some" [a "PremiseExpansion" [v "tasks", v "new-answers", v "new-unresolved"]],
      commitExpansionBody), (v "pending", .symbol "None")]
private def commitCases : SpaceSemantics.Cases :=
  [(a "PremiseState" [.symbol "LNil", v "answers", v "unresolved", v "work"],
      a "Some" [v "state"]),
   (a "PremiseState" [a "LCons" [v "task", v "rest"], v "answers", v "unresolved", v "work"],
      a "case" [v "expanded", .expression (commitExpansionCases.map fun row => .expression [row.1, row.2])]),
   (v "bad", .symbol "None")]
private theorem commit_shape : (equation .commit).body =
    a "case" [v "state", .expression (commitCases.map fun row => .expression [row.1, row.2])] := by
  decide +kernel

/-- The native operation commits precisely one expansion of the original scheduler.
No answer, obligation or pending frame is erased or reordered. -/
theorem commit_returns {Task Answer Obligation : Type} (state : State)
    (task : Task → Term) (answer : Answer → Term) (obligation : Obligation → Term)
    (expand : Task → Scheduler.Expansion Task Answer Obligation)
    (scheduler : Scheduler.State Task Answer Obligation) :
    PureReturns runtime [] state
      (a "gslt:premise:machine-commit" [encoded (schedulerStateTerm task answer obligation scheduler),
        encoded (encodeOption (schedulerExpansionTerm task answer obligation)
          (scheduler.agenda.head?.map expand))])
      state (encoded (encodeOption (schedulerStateTerm task answer obligation)
        (some (Scheduler.tick expand scheduler)))) := by
  let value := encoded (schedulerStateTerm task answer obligation scheduler)
  let expanded := encoded (encodeOption (schedulerExpansionTerm task answer obligation)
    (scheduler.agenda.head?.map expand))
  let caller := environment .commit [value, expanded]
  apply helper_call .commit [] state _ _ _ rfl (captured_closed _)
  rw [commit_shape]
  change PureReturns runtime caller state
    (a "case" [v "state", .expression (commitCases.map fun row => .expression [row.1, row.2])]) state _
  cases agenda : scheduler.agenda with
  | nil =>
      let selected := [("work", number scheduler.work),
        ("unresolved", encoded (encodeList obligation scheduler.unresolved)),
        ("answers", encoded (encodeList answer scheduler.answers))] ++ caller
      apply branch_returns caller selected state _ value commitCases (a "Some" [v "state"]) _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns runtime caller state "state"
      · simp [value, schedulerStateTerm, agenda, commitCases, selected, caller,
          environment, Helper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, encodeList, Subst.lookup, encoded]
      · have templated : PureData.Template runtime (a "Some" [v "state"]) :=
          template_constructor _ _ (by simp) (by
            intro child member
            simp only [List.mem_singleton] at member
            subst child
            exact .captured _)
        simpa [Scheduler.tick, agenda, encodeOption, schedulerStateTerm, value, selected, caller,
          environment, Helper.names, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany,
          applySubst, applySubst.applySubstList, Subst.lookup] using
          PureData.template_return runtime selected state _ templated
  | cons current rest =>
      let next := expand current
      let selected := [("work", number scheduler.work),
        ("unresolved", encoded (encodeList obligation scheduler.unresolved)),
        ("answers", encoded (encodeList answer scheduler.answers)),
        ("rest", encoded (encodeList task rest)), ("task", encoded (task current))] ++ caller
      let framed := [("new-unresolved", encoded (encodeList obligation next.unresolved)),
        ("new-answers", encoded (encodeList answer next.answers)),
        ("tasks", encoded (encodeList task next.tasks))] ++ selected
      let agendaBound := ("agenda", encoded (encodeList task (next.tasks ++ rest))) :: framed
      let answersBound := ("all-answers", encoded (encodeList answer (scheduler.answers ++ next.answers))) :: agendaBound
      let unresolvedBound := ("all-unresolved", encoded (encodeList obligation
        (scheduler.unresolved ++ next.unresolved))) :: answersBound
      let final := ("next-work", number (scheduler.work + 1)) :: unresolvedBound
      apply branch_returns caller selected state _ value commitCases
        (a "case" [v "expanded", .expression (commitExpansionCases.map fun row => .expression [row.1, row.2])]) _
      · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
          variable_returns runtime caller state "state"
      · simp [value, schedulerStateTerm, agenda, commitCases, selected, caller,
          environment, Helper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, CettaWireAtom.encode,
          CettaWireAtom.encodeMany, encodeList, Subst.lookup, encoded]
      · apply branch_returns selected framed state _ expanded commitExpansionCases commitExpansionBody _
        · simpa [selected, caller, environment, Helper.names, applySubst, Subst.lookup] using
            variable_returns runtime selected state "expanded"
        · simp [expanded, agenda, next, schedulerExpansionTerm, encodeOption, commitExpansionCases,
            framed, selected, caller, environment, Helper.names, SpaceSemantics.selectCase,
            SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
            CettaWireAtom.encode, CettaWireAtom.encodeMany, Subst.lookup, encoded]
        · unfold commitExpansionBody
          apply PureData.let_bindings_return (pairs := commitPairs) (final := final)
          · unfold commitPairs
            apply PureData.BindingsReturn.cons (bound := agendaBound)
            · exact append_list_returns task framed state next.tasks rest "tasks" "rest" (by
                simp [framed, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
            · simp [agendaBound, framed, selected, SpaceSemantics.matchBinding,
                SpaceSemantics.matchValue, matchAtom, Subst.lookup, caller, environment, Helper.names]
            · apply PureData.BindingsReturn.cons (bound := answersBound)
              · exact append_list_returns answer agendaBound state scheduler.answers next.answers
                  "answers" "new-answers" (by
                    simp [agendaBound, framed, selected, caller, environment, Helper.names, applySubst, Subst.lookup])
              · simp [answersBound, agendaBound, framed, selected, SpaceSemantics.matchBinding,
                  SpaceSemantics.matchValue, matchAtom, Subst.lookup, caller, environment, Helper.names]
              · apply PureData.BindingsReturn.cons (bound := unresolvedBound)
                · exact append_list_returns obligation answersBound state scheduler.unresolved next.unresolved
                    "unresolved" "new-unresolved" (by
                      simp [answersBound, agendaBound, framed, selected, caller, environment,
                        Helper.names, applySubst, Subst.lookup])
                · simp [unresolvedBound, answersBound, agendaBound, framed, selected,
                    SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup, caller, environment, Helper.names]
                · apply PureData.BindingsReturn.cons (bound := final)
                  · exact add_one_returns unresolvedBound state scheduler.work (by
                      simp [unresolvedBound, answersBound, agendaBound, framed, selected, caller,
                        environment, Helper.names, applySubst, Subst.lookup])
                  · simp [final, unresolvedBound, answersBound, agendaBound, framed, selected,
                      SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup, caller, environment, Helper.names]
                  · exact .nil _ _
          · have templated : PureData.Template runtime commitResult := by
              unfold commitResult
              apply template_constructor _ _ (by simp)
              intro child member
              simp only [List.mem_singleton] at member
              subst child
              apply template_constructor _ _ (by simp)
              intro child member
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with rfl | rfl | rfl | rfl <;> exact .captured _
            simpa [commitResult, Scheduler.tick, agenda, next, schedulerStateTerm, encodeOption,
              final, unresolvedBound, answersBound, agendaBound, framed, selected, caller,
              environment, Helper.names, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany,
              applySubst, applySubst.applySubstList, Subst.lookup] using
              PureData.template_return runtime final state _ templated

theorem commit_derivation_iff {Task Answer Obligation : Type} (state after : State)
    (task : Task → Term) (answer : Answer → Term) (obligation : Obligation → Term)
    (expand : Task → Scheduler.Expansion Task Answer Obligation)
    (scheduler : Scheduler.State Task Answer Obligation)
    (answers input output : List Atom) :
    DeclarativeSpec.Runs runtime
      { state := state, control := .evaluate []
          (a "gslt:premise:machine-commit" [encoded (schedulerStateTerm task answer obligation scheduler),
            encoded (encodeOption (schedulerExpansionTerm task answer obligation)
              (scheduler.agenda.head?.map expand))]) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [encoded (encodeOption (schedulerStateTerm task answer obligation)
        (some (Scheduler.tick expand scheduler)))] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff runtime [] state state _ _
    (commit_returns state task answer obligation expand scheduler) after answers input output

theorem complete_returns {Task Answer Obligation : Type} (state : State)
    (task : Task → Term) (answer : Answer → Term) (obligation : Obligation → Term)
    (scheduler : Scheduler.State Task Answer Obligation) :
    PureReturns runtime [] state
      (a "gslt:premise:machine-complete" [encoded (schedulerStateTerm task answer obligation scheduler)])
      state (Effects.boolean (Scheduler.complete scheduler)) := by
  let value := encoded (schedulerStateTerm task answer obligation scheduler)
  let caller := environment .complete [value]
  apply helper_call .complete [] state _ _ _ rfl (captured_closed _)
  rw [complete_shape]
  cases agenda : scheduler.agenda with
  | nil =>
      cases unresolved : scheduler.unresolved with
      | nil =>
          let selected := [("work", number scheduler.work),
            ("answers", encoded (encodeList answer scheduler.answers))] ++ caller
          apply branch_returns caller selected state _ value completeCases (Effects.boolean true) _
          · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
              variable_returns runtime caller state "state"
          · simp [value, schedulerStateTerm, agenda, unresolved, completeCases, selected, caller,
              environment, Helper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, CettaWireAtom.encode,
              CettaWireAtom.encodeMany, encodeList, Subst.lookup, encoded]
          · simpa [Scheduler.complete, agenda, unresolved, Effects.boolean] using
              grounded_returns runtime selected state (.bool true)
      | cons pending rest =>
          let selected := ("pending", value) :: caller
          apply branch_returns caller selected state _ value completeCases (Effects.boolean false) _
          · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
              variable_returns runtime caller state "state"
          · simp [value, schedulerStateTerm, agenda, unresolved, completeCases, selected, caller,
              environment, Helper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, CettaWireAtom.encode,
              CettaWireAtom.encodeMany, encodeList, Subst.lookup, encoded]
          · simpa [Scheduler.complete, agenda, unresolved, Effects.boolean] using
              grounded_returns runtime selected state (.bool false)
  | cons next rest =>
      cases unresolved : scheduler.unresolved
      all_goals
        let selected := ("pending", value) :: caller
        apply branch_returns caller selected state _ value completeCases (Effects.boolean false) _
        · simpa [caller, environment, Helper.names, applySubst, Subst.lookup] using
            variable_returns runtime caller state "state"
        · simp [value, schedulerStateTerm, agenda, unresolved, completeCases, selected, caller,
            environment, Helper.names, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
            SpaceSemantics.matchValue.matchValues, matchAtom, CettaWireAtom.encode,
            CettaWireAtom.encodeMany, encodeList, Subst.lookup, encoded]
        · simpa [Scheduler.complete, agenda, Effects.boolean] using
            grounded_returns runtime selected state (.bool false)

theorem complete_derivation_iff {Task Answer Obligation : Type} (state after : State)
    (task : Task → Term) (answer : Answer → Term) (obligation : Obligation → Term)
    (scheduler : Scheduler.State Task Answer Obligation)
    (answers input output : List Atom) :
    DeclarativeSpec.Runs runtime
      { state := state, control := .evaluate []
          (a "gslt:premise:machine-complete" [encoded (schedulerStateTerm task answer obligation scheduler)]) }
      (.complete after answers input output) ↔
      after = state ∧ answers = [Effects.boolean (Scheduler.complete scheduler)] ∧ input = [] ∧ output = [] :=
  pure_returns_derivation_iff runtime [] state state _ _
    (complete_returns state task answer obligation scheduler) after answers input output

theorem unresolved_refused {Task Answer Obligation : Type} (state : State)
    (task : Task → Term) (answer : Answer → Term) (obligation : Obligation → Term)
    (scheduler : Scheduler.State Task Answer Obligation)
    (pending : scheduler.unresolved ≠ []) :
    PureReturns runtime [] state
      (a "gslt:premise:machine-complete" [encoded (schedulerStateTerm task answer obligation scheduler)])
      state (Effects.boolean false) := by
  simpa only [Scheduler.unresolved_not_complete scheduler pending] using
    complete_returns state task answer obligation scheduler

theorem pending_refused {Task Answer Obligation : Type} (state : State)
    (task : Task → Term) (answer : Answer → Term) (obligation : Obligation → Term)
    (scheduler : Scheduler.State Task Answer Obligation)
    (pending : scheduler.agenda ≠ []) :
    PureReturns runtime [] state
      (a "gslt:premise:machine-complete" [encoded (schedulerStateTerm task answer obligation scheduler)])
      state (Effects.boolean false) := by
  simpa only [Scheduler.pending_not_complete scheduler pending] using
    complete_returns state task answer obligation scheduler

namespace Controls

private abbrev label (name : String) : Term := .application name []
private def states : List (String × Scheduler.State Term Term Term) :=
  [("empty", {}),
   ("answers-retain-duplicates", { answers := [label "AnswerA", label "AnswerA", label "AnswerB"], work := 8 }),
   ("unresolved", { unresolved := [label "NeedsGuard"], work := 3 }),
   ("pending", { agenda := [label "TaskA"] }),
   ("paused-with-answers", { agenda := [label "TaskA", label "TaskB"], answers := [label "AnswerA"], work := 4 }),
   ("pending-and-unresolved", { agenda := [label "TaskA"], unresolved := [label "NeedsGuard"], work := 2 })]

private def expansions : List (String × Scheduler.Expansion Term Term Term) :=
  [("empty-expansion", {}),
   ("duplicate-answers", { answers := [label "AnswerA", label "AnswerA", label "AnswerB"] }),
   ("new-tasks-first", { tasks := [label "TaskC", label "TaskD"] }),
   ("unresolved-is-retained", { unresolved := [label "NeedsGuard", label "NeedsType"] })]

def nativeControls : List (String × String × String) :=
  let completion := states.map fun (name, state) =>
    ("complete-" ++ name,
     (Term.application "gslt:premise:machine-complete" [schedulerStateTerm id id id state]).render,
     if Scheduler.complete state then "True" else "False")
  let committed := expansions.flatMap fun (name, expansion) => states.map fun (stateName, state) =>
    let call := Term.application "gslt:premise:machine-commit"
      [schedulerStateTerm id id id state,
       encodeOption (schedulerExpansionTerm id id id) (state.agenda.head?.map fun _ => expansion)]
    let result := encodeOption (schedulerStateTerm id id id)
      (some (Scheduler.tick (fun _ => expansion) state))
    ("commit-" ++ name ++ "-" ++ stateName, call.render, result.render)
  completion ++ committed ++
    [("unexpanded-task-is-refused", "(gslt:premise:machine-commit (PremiseState (LCons (TaskA) LNil) LNil LNil 0) None)", "None"),
     ("malformed-expansion-is-refused", "(gslt:premise:machine-commit (PremiseState (LCons (TaskA) LNil) LNil LNil 0) (Some (Other)))", "None"),
     ("malformed-state-is-refused", "(gslt:premise:machine-commit (Other) None)", "None"),
     ("malformed-state-is-incomplete", "(gslt:premise:machine-complete (Other))", "False"),
     ("idle-expansion-is-not-consumed", "(gslt:premise:machine-commit (PremiseState LNil (LCons (AnswerA) LNil) LNil 8) (Some (PremiseExpansion (LCons (TaskC) LNil) (LCons (AnswerB) LNil) (LCons (NeedsGuard) LNil))))",
       "(Some (PremiseState LNil (LCons (AnswerA) LNil) LNil 8))")]

def renderNativeControls : String := String.intercalate "\n" (nativeControls.map fun (name, call, expected) =>
  "!(let $actual " ++ call ++ " (println! (PremiseSchedulerControl " ++ reprStr name ++
    " (== $actual (quote " ++ expected ++ ")))))")

end Controls

#print axioms complete_returns
#print axioms complete_derivation_iff
#print axioms commit_returns
#print axioms commit_derivation_iff
#print axioms unresolved_refused
#print axioms pending_refused

#eval IO.println Controls.renderNativeControls

private theorem helper_capture (helper : Helper) (caller : Subst) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = helper.names.length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns runtime [] state (a helper.head values) state answer) :
    PureReturns runtime caller state (a helper.head arguments) state answer := by
  apply PureData.raw_capture_returns runtime [] caller state state helper.head values arguments answer
    (by cases helper <;> decide +kernel) _ (by cases helper <;> decide) _ returned
  · intro index bounded
    exact helper_raw helper index (by omega)
  · have unchanged : applySubst [] = id := by
      funext value; exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
    simpa only [unchanged, List.map_id] using captured.symm

theorem commit_captured_returns {Task Answer Obligation : Type} (caller : Subst) (state : State)
    (task : Task → Term) (answer : Answer → Term) (obligation : Obligation → Term)
    (expand : Task → Scheduler.Expansion Task Answer Obligation)
    (scheduler : Scheduler.State Task Answer Obligation) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (schedulerStateTerm task answer obligation scheduler),
       encoded (encodeOption (schedulerExpansionTerm task answer obligation)
         (scheduler.agenda.head?.map expand))]) :
    PureReturns runtime caller state (a "gslt:premise:machine-commit" arguments)
      state (encoded (encodeOption (schedulerStateTerm task answer obligation)
        (some (Scheduler.tick expand scheduler)))) :=
  helper_capture .commit caller state arguments _ _ rfl captured
    (commit_returns state task answer obligation expand scheduler)

theorem complete_captured_returns {Task Answer Obligation : Type} (caller : Subst) (state : State)
    (task : Task → Term) (answer : Answer → Term) (obligation : Obligation → Term)
    (scheduler : Scheduler.State Task Answer Obligation) (arguments : List Atom)
    (captured : arguments.map (applySubst caller) =
      [encoded (schedulerStateTerm task answer obligation scheduler)]) :
    PureReturns runtime caller state (a "gslt:premise:machine-complete" arguments)
      state (Effects.boolean (Scheduler.complete scheduler)) :=
  helper_capture .complete caller state arguments _ _ rfl captured
    (complete_returns state task answer obligation scheduler)

#print axioms commit_captured_returns
#print axioms complete_captured_returns

/-- Exactly the heads inspected by scheduler commit and completion. Encoded tasks,
answers and obligations are captured data and need not belong to this set. -/
def executionHeadNames : List String :=
  ["+", "LCons", "LNil", "None", "Some", "PremiseState", "PremiseExpansion",
   "case", "let", "let*", "gslt:automata:append",
   "gslt:premise:machine-commit", "gslt:premise:machine-complete"]

def executionHeads (head : String) : Bool := executionHeadNames.contains head

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem runtime_closed : ProgramClosed executionHeads runtime := by
  exact BridgeKit.closed_of_all _ _ (by decide +kernel) (by decide +kernel)

theorem returns_in_extension (target : Program)
    (agreement : ProgramAgreementOn executionHeads runtime target)
    {caller : Subst} {state : State} {code answer : Atom}
    (supported : codeWithin executionHeads code = true)
    (returned : PureReturns runtime caller state code state answer) :
    PureReturns target caller state code state answer :=
  path_of_closed_agreement runtime_closed agreement ⟨supported, rfl⟩ returned

#print axioms runtime_closed
#print axioms returns_in_extension

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseSchedulerExecution
