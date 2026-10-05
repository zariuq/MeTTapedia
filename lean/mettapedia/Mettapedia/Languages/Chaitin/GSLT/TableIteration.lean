import Mettapedia.Languages.Chaitin.GSLT.PureReturns
import Mettapedia.Languages.Chaitin.TuringInterpreter.Prefixes

/-!
# One complete table iteration as an ordinary historical Lisp program

The program uses the existing recursive row search and list-based tape
procedure. It returns an empty list when no row applies, or a singleton
containing the complete next configuration. It does not recurse into the
next machine iteration. These explicit boundaries give an executable block
semantics for comparing languages with different elementary step counts.

The optional result distinguishes an absent transition from a transition
back to the same configuration. Every invocation terminates, including on
finite non-deterministic tables; choosing the first row is historical Lisp's
policy. Agreement with all authored table rewrites requires determinism.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Chaitin.GSLT.TableIteration

open TuringPrograms TuringInterpreter PureEvaluation Expressions

def body : SExpr :=
  letValue "selected" selectionExpression
    (ifExpr (equalExpr (.symbol "selected") (.symbol "nil")) (.symbol "nil")
      (listExpr [call "move-row" [.symbol "selected", .symbol "configuration"]]))

def function : SExpr := lambda ["table", "configuration"] body

/-- The helpers are installed by the same historical `let` expansion as the
recursive machine interpreter. No table lookup is a host operation. -/
def program (machine : TuringMachine.Machine) (configuration : TuringMachine.Configuration) : SExpr :=
  letValue "find-row" lookupProgram
    (letValue "move-row" transitionProgram
      (letValue "run-table" loopProgram
        (.list [quote function, quote (encodeTable machine.transitions),
          quote (TuringPrograms.encodeConfiguration configuration)])))

def outcome : Option TuringMachine.Configuration → SExpr
  | none => SExpr.nil
  | some configuration => .list [TuringPrograms.encodeConfiguration configuration]

@[simp] theorem outcome_none : outcome none = SExpr.nil := rfl
@[simp] theorem outcome_some (configuration : TuringMachine.Configuration) :
    outcome (some configuration) = .list [TuringPrograms.encodeConfiguration configuration] := rfl

theorem outcome_injective : Function.Injective outcome := by
  intro first second same
  cases first with
  | none => cases second <;> simp_all [outcome, SExpr.nil]
  | some first =>
      cases second with
      | none => simp [outcome, SExpr.nil] at same
      | some second =>
          have dataSame : TuringPrograms.encodeConfiguration first =
              TuringPrograms.encodeConfiguration second := by simpa [outcome] using same
          exact congrArg some (TuringPrograms.encodeConfiguration_injective dataSame)

theorem body_evaluates (machine : TuringMachine.Machine)
    (configuration : TuringMachine.Configuration) (environment : Environment)
    (contract : EnvironmentContract environment) :
    PureEval (loopScope environment (encodeTable machine.transitions)
      (TuringPrograms.encodeConfiguration configuration)) body (outcome (machine.next? configuration)) := by
  let scope := loopScope environment (encodeTable machine.transitions)
    (TuringPrograms.encodeConfiguration configuration)
  have localContract := contract.loopScope (encodeTable machine.transitions)
    (TuringPrograms.encodeConfiguration configuration)
  cases found : machine.entryFor configuration with
  | none =>
      have selection : PureEval scope selectionExpression SExpr.nil := by
        simpa only [found, Option.map_none, Option.getD_none] using
          selection_eval machine configuration environment contract
      apply eval_letValue localContract.quote selection
      let nextScope := iterationEnvironment environment machine configuration SExpr.nil
      have nextContract := contract.iterationEnvironment machine configuration SExpr.nil
      have selected := eval_word (selectedScope_selected scope SExpr.nil)
      have nilRun := eval_word nextContract.nil
      have branch := eval_if (yes := .symbol "nil")
        (no := listExpr [call "move-row" [.symbol "selected", .symbol "configuration"]])
        nextContract.conditional
        (eval_equal nextContract.equal selected nilRun) nilRun
      simpa only [body, nextScope, iterationEnvironment, selectedScope, bind, SExpr.elements,
        TuringMachine.Machine.next?, found, Option.map_none,
        outcome, SExpr.truth_boolean, decide_true, ↓reduceIte] using branch
  | some entry =>
      have selection : PureEval scope selectionExpression (encodeTransition entry) := by
        simpa only [found, Option.map_some, Option.getD_some] using
          selection_eval machine configuration environment contract
      apply eval_letValue localContract.quote selection
      let nextScope := iterationEnvironment environment machine configuration (encodeTransition entry)
      have nextContract := contract.iterationEnvironment machine configuration (encodeTransition entry)
      have selected := eval_word (selectedScope_selected scope (encodeTransition entry))
      have configurationRun := eval_word
        (iteration_configuration environment machine configuration (encodeTransition entry))
      have moveRun : PureEval nextScope
          (call "move-row" [.symbol "selected", .symbol "configuration"])
          (TuringPrograms.encodeConfiguration (configuration.after entry)) :=
        .application (eval_word nextContract.moveRow)
          (by intro same; cases same) (by intro same; cases same)
          (.cons selected (.cons configurationRun (.nil nextScope)))
          (transition_encoded_apply entry configuration nextScope nextContract.toMoveEnvironment)
      have singletonRun := eval_cons nextContract.cons moveRun (eval_word nextContract.nil)
      have notNil : encodeTransition entry ≠ SExpr.nil := by simp [encodeTransition, SExpr.nil]
      have branch := eval_if (yes := .symbol "nil")
        (no := listExpr [call "move-row" [.symbol "selected", .symbol "configuration"]])
        nextContract.conditional
        (eval_equal nextContract.equal selected (eval_word nextContract.nil)) singletonRun
      simpa only [body, nextScope, iterationEnvironment, selectedScope, bind, SExpr.elements,
        listExpr, TuringMachine.Machine.next?, found, Option.map_some,
        outcome, SExpr.truth_boolean, notNil, decide_false, Bool.false_eq_true, ↓reduceIte,
        SExpr.cons, SExpr.nil] using branch

/-- Totality is proved compositionally, without evaluating a closed machine
or relying on the eventual answer of its unbounded run. -/
theorem program_evaluates (machine : TuringMachine.Machine)
    (configuration : TuringMachine.Configuration) :
    PureEval cleanEnvironment (program machine configuration) (outcome (machine.next? configuration)) := by
  apply eval_letValue (by rfl) (eval_quote (by rfl) lookupFunction)
  apply eval_letValue rowBase_quote (eval_quote rowBase_quote transitionFunction)
  apply eval_letValue moveBase_quote (eval_quote moveBase_quote loopFunction)
  exact .application (eval_quote baseEnvironment_contract.quote function)
    (by intro same; cases same) (by intro same; cases same)
    (.cons (eval_quote baseEnvironment_contract.quote (encodeTable machine.transitions))
      (.cons (eval_quote baseEnvironment_contract.quote (TuringPrograms.encodeConfiguration configuration))
        (.nil baseEnvironment)))
    (apply_lambda _ _ _ (body_evaluates machine configuration baseEnvironment baseEnvironment_contract))

/-- Every generated return is the calculated optional successor. -/
theorem returns_iff (machine : TuringMachine.Machine)
    (configuration : TuringMachine.Configuration) (value : SExpr) :
    theory.MultiStep (start (program machine configuration)) (result value) ↔
      value = outcome (machine.next? configuration) :=
  pureEval_returns_iff (program_evaluates machine configuration) value

end Mettapedia.Languages.Chaitin.GSLT.TableIteration
