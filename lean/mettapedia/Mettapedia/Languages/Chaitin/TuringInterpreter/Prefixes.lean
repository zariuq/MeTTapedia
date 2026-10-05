import Mettapedia.Languages.Chaitin.TuringInterpreter.Environment

/-!
# One iteration of the ordinary Lisp tape interpreter

Row search and tape motion are evaluated by the already checked Lisp
procedures. The prefixes stop either at the returned configuration or at the
next recursive call, retaining its actual dynamic environment and caller.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Chaitin.TuringInterpreter

open TuringPrograms PureEvaluation Expressions

def selectionExpression : SExpr :=
  call "find-row" [.symbol "table", fieldExpr 0 (.symbol "configuration"),
    fieldExpr 2 (.symbol "configuration")]

def continuationExpression : SExpr :=
  ifExpr (equalExpr (.symbol "selected") (.symbol "nil")) (.symbol "configuration")
    (call "run-table" [.symbol "table",
      call "move-row" [.symbol "selected", .symbol "configuration"]])

def iterationEnvironment (environment : Environment) (machine : TuringMachine.Machine)
    (configuration : TuringMachine.Configuration) (selected : SExpr) : Environment :=
  selectedScope (loopScope environment (encodeTable machine.transitions)
    (encodeConfiguration configuration)) selected

theorem EnvironmentContract.iterationEnvironment {environment : Environment}
    (contract : EnvironmentContract environment) (machine : TuringMachine.Machine)
    (configuration : TuringMachine.Configuration) (selected : SExpr) :
    EnvironmentContract (iterationEnvironment environment machine configuration selected) :=
  (contract.loopScope _ _).selectedScope _

theorem iteration_table (environment : Environment) (machine : TuringMachine.Machine)
    (configuration : TuringMachine.Configuration) (selected : SExpr) :
    lookup (iterationEnvironment environment machine configuration selected) (.symbol "table") =
      encodeTable machine.transitions :=
  (selectedScope_preserves _ _ _ (by decide)).trans (loopScope_table _ _ _)

theorem iteration_configuration (environment : Environment) (machine : TuringMachine.Machine)
    (configuration : TuringMachine.Configuration) (selected : SExpr) :
    lookup (iterationEnvironment environment machine configuration selected) (.symbol "configuration") =
      encodeConfiguration configuration :=
  (selectedScope_preserves _ _ _ (by decide)).trans (loopScope_configuration _ _ _)

theorem selection_eval (machine : TuringMachine.Machine)
    (configuration : TuringMachine.Configuration) (environment : Environment)
    (contract : EnvironmentContract environment) :
    PureEval (loopScope environment (encodeTable machine.transitions) (encodeConfiguration configuration))
      selectionExpression (((machine.entryFor configuration).map encodeTransition).getD SExpr.nil) := by
  let scope := loopScope environment (encodeTable machine.transitions) (encodeConfiguration configuration)
  have localContract := contract.loopScope (encodeTable machine.transitions) (encodeConfiguration configuration)
  have configurationRun := eval_word (loopScope_configuration environment
    (encodeTable machine.transitions) (encodeConfiguration configuration))
  have stateRun : PureEval scope (fieldExpr 0 (.symbol "configuration"))
      (.number configuration.state) :=
    eval_field localContract.car localContract.cdr 0 configurationRun
  have scannedRun : PureEval scope (fieldExpr 2 (.symbol "configuration"))
      (.number configuration.scanned) :=
    eval_field localContract.car localContract.cdr 2 configurationRun
  exact PureEval.application (eval_word localContract.findRow)
    (by intro same; cases same) (by intro same; cases same)
    (.cons (eval_word (loopScope_table _ _ _)) (.cons stateRun (.cons scannedRun (.nil scope))))
    (lookup_encoded_apply machine.transitions configuration.state configuration.scanned
      scope localContract.rowLookup)

theorem body_halted (machine : TuringMachine.Machine)
    (configuration : TuringMachine.Configuration) (environment : Environment)
    (contract : EnvironmentContract environment) (stopped : machine.entryFor configuration = none) :
    PureEval (loopScope environment (encodeTable machine.transitions) (encodeConfiguration configuration))
      interpreterBody (encodeConfiguration configuration) := by
  let scope := loopScope environment (encodeTable machine.transitions) (encodeConfiguration configuration)
  have localContract := contract.loopScope (encodeTable machine.transitions) (encodeConfiguration configuration)
  have selectedRun : PureEval scope selectionExpression SExpr.nil := by
    simpa only [stopped, Option.map_none, Option.getD_none] using
      selection_eval machine configuration environment contract
  apply eval_letValue localContract.quote selectedRun
  change PureEval (iterationEnvironment environment machine configuration SExpr.nil)
    continuationExpression (encodeConfiguration configuration)
  have finalContract := contract.iterationEnvironment machine configuration SExpr.nil
  apply eval_if finalContract.conditional
    (eval_equal finalContract.equal (eval_word (selectedScope_selected _ _)) (eval_word finalContract.nil))
  simpa only [SExpr.truth_boolean, decide_true, ↓reduceIte] using
    eval_word (iteration_configuration environment machine configuration SExpr.nil)

theorem body_next_prefix (machine : TuringMachine.Machine)
    (configuration : TuringMachine.Configuration) (entry : TuringMachine.Transition)
    (environment : Environment) (contract : EnvironmentContract environment)
    (found : machine.entryFor configuration = some entry) (context : State) :
    InternalSteps
      { context with control := (.eval interpreterBody
        (loopScope environment (encodeTable machine.transitions) (encodeConfiguration configuration))
        .unlimited) }
      { context with control := (.apply loopFunction
        [encodeTable machine.transitions, encodeConfiguration (configuration.after entry)]
        (iterationEnvironment environment machine configuration (encodeTransition entry)) .unlimited) } := by
  let scope := loopScope environment (encodeTable machine.transitions) (encodeConfiguration configuration)
  let nextScope := iterationEnvironment environment machine configuration (encodeTransition entry)
  have localContract := contract.loopScope (encodeTable machine.transitions) (encodeConfiguration configuration)
  have nextContract := contract.iterationEnvironment machine configuration (encodeTransition entry)
  have selectedRun : PureEval scope selectionExpression (encodeTransition entry) := by
    simpa only [found, Option.map_some, Option.getD_some] using
      selection_eval machine configuration environment contract
  have selectedValue : PureEval nextScope (.symbol "selected") (encodeTransition entry) :=
    eval_word (selectedScope_selected _ _)
  have configurationRun := eval_word (iteration_configuration environment machine configuration
    (encodeTransition entry))
  have notNil : encodeTransition entry ≠ SExpr.nil := by
    simp [encodeTransition, SExpr.nil]
  have branch := conditional_prefix (yes := .symbol "configuration")
    (no := call "run-table" [.symbol "table",
      call "move-row" [.symbol "selected", .symbol "configuration"]])
    nextContract.conditional (eval_equal nextContract.equal selectedValue (eval_word nextContract.nil)) context
  have moveRun : PureEval nextScope
      (call "move-row" [.symbol "selected", .symbol "configuration"])
      (encodeConfiguration (configuration.after entry)) :=
    .application (eval_word nextContract.moveRow)
      (by intro same; cases same) (by intro same; cases same)
      (.cons selectedValue (.cons configurationRun (.nil nextScope)))
      (transition_encoded_apply entry configuration nextScope nextContract.toMoveEnvironment)
  have recurse := application_prefix (eval_word nextContract.runTable)
    (by intro same; cases same) (by intro same; cases same)
    (.cons (eval_word (iteration_table environment machine configuration (encodeTransition entry)))
      (.cons moveRun (.nil nextScope))) context
  have branchPrefix : InternalSteps
      { context with control := .eval continuationExpression nextScope .unlimited }
      { context with control := (.eval (call "run-table" [.symbol "table",
        call "move-row" [.symbol "selected", .symbol "configuration"]]) nextScope .unlimited) } := by
    simpa only [continuationExpression, nextScope, SExpr.truth_boolean, notNil,
      decide_false, Bool.false_eq_true, ↓reduceIte]
      using branch
  exact (let_prefix localContract.quote selectedRun context).trans
    (branchPrefix.trans recurse)

theorem closed_program_prefix (machine : TuringMachine.Machine)
    (configuration : TuringMachine.Configuration) (context : State) :
    InternalSteps
      { context with control := .eval (machineProgram machine configuration) cleanEnvironment .unlimited }
      { context with control := (.apply loopFunction
        [encodeTable machine.transitions, encodeConfiguration configuration] baseEnvironment .unlimited) } := by
  have findPrefix := let_prefix (environment := cleanEnvironment) (name := "find-row")
    (body := letValue "move-row" transitionProgram
      (letValue "run-table" loopProgram
        (call "run-table" [quote (encodeTable machine.transitions), quote (encodeConfiguration configuration)])))
    (by rfl) (eval_quote (by rfl) lookupFunction) context
  have movePrefix := let_prefix (environment := rowBaseEnvironment) (name := "move-row")
    (body := letValue "run-table" loopProgram
      (call "run-table" [quote (encodeTable machine.transitions), quote (encodeConfiguration configuration)]))
    rowBase_quote (eval_quote rowBase_quote transitionFunction) context
  have loopPrefix := let_prefix (environment := moveBaseEnvironment) (name := "run-table")
    (body := call "run-table" [quote (encodeTable machine.transitions), quote (encodeConfiguration configuration)])
    moveBase_quote (eval_quote moveBase_quote loopFunction) context
  have callPrefix := application_prefix (eval_word baseEnvironment_contract.runTable)
    (by intro same; cases same) (by intro same; cases same)
    (.cons (eval_quote baseEnvironment_contract.quote (encodeTable machine.transitions))
      (.cons (eval_quote baseEnvironment_contract.quote (encodeConfiguration configuration))
        (.nil baseEnvironment))) context
  exact findPrefix.trans (movePrefix.trans (loopPrefix.trans callPrefix))

end Mettapedia.Languages.Chaitin.TuringInterpreter
