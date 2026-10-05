import Mettapedia.Languages.Chaitin.TuringPrograms
import Mettapedia.Languages.Chaitin.EnvironmentLaws
import Mettapedia.Languages.Chaitin.ExpressionLaws

/-!
# Semantic correctness of the Lisp write-and-move procedure

The ordinary Lisp expression manipulates both half-tapes through `car`, `cdr`,
and `cons`. The comparison preserves represented trailing blanks and agrees
with writing the symbol before moving the head.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Chaitin.TuringPrograms

open PureEvaluation Expressions

def transitionFunction : SExpr := lambda ["entry", "configuration"] transitionBody

structure MoveEnvironment (environment : Environment) : Prop where
  conditional : lookup environment (.symbol "if") = .symbol "if"
  car : lookup environment (.symbol "car") = .symbol "car"
  cdr : lookup environment (.symbol "cdr") = .symbol "cdr"
  cons : lookup environment (.symbol "cons") = .symbol "cons"
  equal : lookup environment (.symbol "=") = .symbol "="
  quote : lookup environment (.symbol "'") = .symbol "'"
  nil : lookup environment (.symbol "nil") = SExpr.nil

def moveScope (environment : Environment) (entry configuration : SExpr) : Environment :=
  bindNames [.symbol "entry", .symbol "configuration"] [entry, configuration] environment

theorem moveScope_preserves (environment : Environment) (entry configuration : SExpr)
    (name : String)
    (absent : SExpr.symbol name ∉ ([.symbol "entry", .symbol "configuration"] : List SExpr)) :
    lookup (moveScope environment entry configuration) (.symbol name) =
      lookup environment (.symbol name) :=
  EnvironmentLaws.lookup_bindNames_of_not_mem _ _ _ _ absent

theorem MoveEnvironment.moveScope {environment : Environment}
    (bindings : MoveEnvironment environment) (entry configuration : SExpr) :
    MoveEnvironment (moveScope environment entry configuration) := by
  exact ⟨
    (moveScope_preserves environment entry configuration "if" (by decide)).trans
      bindings.conditional,
    (moveScope_preserves environment entry configuration "car" (by decide)).trans bindings.car,
    (moveScope_preserves environment entry configuration "cdr" (by decide)).trans bindings.cdr,
    (moveScope_preserves environment entry configuration "cons" (by decide)).trans bindings.cons,
    (moveScope_preserves environment entry configuration "=" (by decide)).trans bindings.equal,
    (moveScope_preserves environment entry configuration "'" (by decide)).trans bindings.quote,
    (moveScope_preserves environment entry configuration "nil" (by decide)).trans bindings.nil⟩

theorem moveScope_entry (environment : Environment) (entry configuration : SExpr) :
    lookup (moveScope environment entry configuration) (.symbol "entry") = entry :=
  EnvironmentLaws.lookup_bindNames_index 0 _ _ _ _ rfl (by decide)

theorem moveScope_configuration (environment : Environment) (entry configuration : SExpr) :
    lookup (moveScope environment entry configuration) (.symbol "configuration") = configuration :=
  EnvironmentLaws.lookup_bindNames_index 1 _ _ _ _ rfl (by decide)

theorem blankHead_eval {environment : Environment} (bindings : MoveEnvironment environment)
    {expression value : SExpr} (argument : PureEval environment expression value) :
    PureEval environment (blankHeadExpr expression) (headOrBlank value) := by
  exact eval_if_equal_branches bindings.conditional bindings.equal argument
    (eval_word bindings.nil) (eval_number environment 0) (eval_car bindings.car argument)

/-- The actual Lisp procedure agrees with the data operation for arbitrary
historical values; encoded tapes are a special case. -/
theorem transition_apply (entry configuration : SExpr) (environment : Environment)
    (bindings : MoveEnvironment environment) :
    PureApply environment transitionFunction [entry, configuration] (moveData entry configuration) := by
  apply PureEvaluation.apply_lambda _ _ _
  change PureEval (moveScope environment entry configuration) transitionBody
    (moveData entry configuration)
  let scope := moveScope environment entry configuration
  have localBindings : MoveEnvironment scope := bindings.moveScope entry configuration
  have entryRun : PureEval scope (.symbol "entry") entry :=
    eval_word (moveScope_entry environment entry configuration)
  have configurationRun : PureEval scope (.symbol "configuration") configuration :=
    eval_word (moveScope_configuration environment entry configuration)
  have leftRun := eval_field localBindings.car localBindings.cdr 1 configurationRun
  have rightRun := eval_field localBindings.car localBindings.cdr 3 configurationRun
  have writeRun := eval_field localBindings.car localBindings.cdr 2 entryRun
  have nextRun := eval_field localBindings.car localBindings.cdr 4 entryRun
  have directionRun := eval_field localBindings.car localBindings.cdr 3 entryRun
  have rightBranch := eval_listExpr localBindings.cons localBindings.nil
    (.cons nextRun (.cons (eval_cons localBindings.cons writeRun leftRun)
      (.cons (blankHead_eval localBindings rightRun)
        (.cons (eval_cdr localBindings.cdr rightRun) (.nil scope)))))
  have leftBranch := eval_listExpr localBindings.cons localBindings.nil
    (.cons nextRun (.cons (eval_cdr localBindings.cdr leftRun)
      (.cons (blankHead_eval localBindings leftRun)
        (.cons (eval_cons localBindings.cons writeRun rightRun) (.nil scope)))))
  exact eval_if_equal_branches localBindings.conditional localBindings.equal directionRun
    (eval_quote localBindings.quote (.symbol "right")) rightBranch leftBranch

theorem transition_encoded_apply (entry : TuringMachine.Transition)
    (configuration : TuringMachine.Configuration) (environment : Environment)
    (bindings : MoveEnvironment environment) :
    PureApply environment transitionFunction
      [encodeTransition entry, encodeConfiguration configuration]
      (encodeConfiguration (configuration.after entry)) := by
  simpa only [moveData_encode] using
    transition_apply (encodeTransition entry) (encodeConfiguration configuration) environment bindings

theorem MoveEnvironment.clean : MoveEnvironment cleanEnvironment := by
  constructor <;> decide

/-- Apply the ordinary quoted procedure to two quoted data values. -/
def transitionApplication (entry configuration : SExpr) : SExpr :=
  .list [transitionProgram, quote entry, quote configuration]

theorem transitionApplication_eval (entry configuration : SExpr) :
    PureEval cleanEnvironment (transitionApplication entry configuration)
      (moveData entry configuration) := by
  exact PureEval.application (eval_quote (by decide) transitionFunction)
    (by intro same; cases same) (by intro same; cases same)
    (.cons (eval_quote (by decide) entry)
      (.cons (eval_quote (by decide) configuration) (.nil cleanEnvironment)))
    (transition_apply entry configuration cleanEnvironment MoveEnvironment.clean)

theorem transitionApplication_evaluates (entry : TuringMachine.Transition)
    (configuration : TuringMachine.Configuration) (input : List Bool) :
    Evaluates (transitionApplication (encodeTransition entry) (encodeConfiguration configuration))
      input ⟨.success (encodeConfiguration (configuration.after entry)), [], []⟩ input := by
  simpa only [moveData_encode] using
    (transitionApplication_eval (encodeTransition entry) (encodeConfiguration configuration)).evaluates input

theorem transitionApplication_executable (entry : TuringMachine.Transition)
    (configuration : TuringMachine.Configuration) (input : List Bool) :
    ∃ fuel, execute fuel
      (transitionApplication (encodeTransition entry) (encodeConfiguration configuration)) input =
      some (⟨.success (encodeConfiguration (configuration.after entry)), [], []⟩, input) :=
  evaluates_iff_execute.mp (transitionApplication_evaluates entry configuration input)

/-- Moving past the finite right half-tape supplies blank zero and retains
the just-written cell in the left half-tape. -/
theorem right_edge_runtime (input : List Bool) :
    Evaluates (transitionApplication (encodeTransition ⟨3, 7, 9, .right, 4⟩)
      (encodeConfiguration ⟨3, [8], 7, []⟩)) input
      ⟨.success (encodeConfiguration ⟨4, [9, 8], 0, []⟩), [], []⟩ input :=
  transitionApplication_evaluates _ _ input

theorem written_cell_cannot_be_dropped (input rest : List Bool) :
    ¬ Evaluates (transitionApplication (encodeTransition ⟨3, 7, 9, .right, 4⟩)
      (encodeConfiguration ⟨3, [8], 7, []⟩)) input
      ⟨.success (encodeConfiguration ⟨4, [8], 0, []⟩), [], []⟩ rest := by
  intro run
  have same := run.deterministic (right_edge_runtime input)
  have result := Result.success.inj (congrArg Observation.result same.1)
  have configuration := encodeConfiguration_injective result
  cases configuration

end Mettapedia.Languages.Chaitin.TuringPrograms
