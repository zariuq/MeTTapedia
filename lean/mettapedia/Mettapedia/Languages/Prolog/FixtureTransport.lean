import Lean.Elab.Command
import Lean.Meta.AppBuilder
import Mettapedia.Logic.Prolog.Eval
import Mettapedia.Languages.Prolog.Eval

set_option autoImplicit false

namespace Mettapedia.Languages.Prolog.SharedFixtures

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Keep the independently declared goal constructors and their nesting. -/
def goal : Mettapedia.Logic.Prolog.PrologGoal → PrologGoal
  | .succeed => .succeed
  | .fail => .fail
  | .cut => .cut
  | .conj first second => .conj (goal first) (goal second)
  | .disj first second => .disj (goal first) (goal second)
  | .ite cond yes no => .ite (goal cond) (goal yes) (goal no)
  | .once body => .once (goal body)
  | .neg body => .neg (goal body)
  | .isVar pat => .isVar pat
  | .unify left right => .unify left right
  | .notUnify left right => .notUnify left right
  | .findall name body => .findall name (goal body)
  | .spaceMatch pat template => .spaceMatch pat template
  | .reduceCall args => .reduceCall args

/-- Ordered environments and the cut signal both survive transport. -/
def result : Mettapedia.Logic.Prolog.PrologEvalResult → PrologEvalResult
  | .normal answers => .normal answers
  | .cutThrown answers => .cutThrown answers

theorem result_answers (r : Mettapedia.Logic.Prolog.PrologEvalResult) :
    (result r).answers = r.answers := by
  cases r <;> rfl

theorem list_payload (values : List Pattern) :
    Mettapedia.Logic.Prolog.Pattern.mkList values = Pattern.mkList values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    simp only [Mettapedia.Logic.Prolog.Pattern.mkList_cons, Pattern.mkList_cons, ih]

theorem insert_binding (env : PEnv) (name : String) (value : Pattern) :
    Mettapedia.Logic.Prolog.PEnv.insert env name value = PEnv.insert env name value := rfl

def sourceOracle (oracle : EvalOracle) : Mettapedia.Logic.Prolog.EvalOracle where
  space := ⟨oracle.space.matchFacts⟩
  call := oracle.call
  matchEval := oracle.matchEval

/-- Transport an actual derivation, including the witnesses for all
conjunction branches and the first-answer tests for cut barriers. -/
theorem evaluation (oracle : EvalOracle)
    {g : Mettapedia.Logic.Prolog.PrologGoal} {env : PEnv}
    {r : Mettapedia.Logic.Prolog.PrologEvalResult}
    (h : Mettapedia.Logic.Prolog.PrologEval (sourceOracle oracle) g env r) :
    PrologEval oracle (goal g) env (result r) := by
  induction h with
  | succeed_eval env => exact .succeed_eval env
  | fail_eval env => exact .fail_eval env
  | cut_eval env => exact .cut_eval env
  | conj_normal first second env answers pairs _ domain _ firstIH eachIH =>
    exact .conj_normal (goal first) (goal second) env answers pairs firstIH domain eachIH
  | conj_g2_cut first second env answers pref start out suff _ split _ _ leftIH prefIH cutIH =>
    exact .conj_g2_cut (goal first) (goal second) env answers pref start out suff leftIH split prefIH cutIH
  | conj_g1_cut first second env answers pairs _ domain _ firstIH eachIH =>
    exact .conj_g1_cut (goal first) (goal second) env answers pairs firstIH domain eachIH
  | conj_g1_cut_g2_cut first second env answers pref start out suff _ split _ _ leftIH prefIH cutIH =>
    exact .conj_g1_cut_g2_cut (goal first) (goal second) env answers pref start out suff leftIH split prefIH cutIH
  | disj_g1_cut first second env answers _ leftIH =>
    exact .disj_g1_cut (goal first) (goal second) env answers leftIH
  | disj_normal first second env lhs rhs _ _ leftIH rightIH =>
    exact .disj_normal (goal first) (goal second) env lhs rhs leftIH rightIH
  | disj_g2_cut first second env lhs rhs _ _ leftIH rightIH =>
    exact .disj_g2_cut (goal first) (goal second) env lhs rhs leftIH rightIH
  | ite_then cond yes no env first rest condition outcome _ firstRead _ condIH thenIH =>
    exact .ite_then (goal cond) (goal yes) (goal no) env first rest
      (result condition) (result outcome) condIH (by rw [result_answers]; exact firstRead) thenIH
  | ite_else cond yes no env condition outcome _ emptyRead _ condIH elseIH =>
    exact .ite_else (goal cond) (goal yes) (goal no) env (result condition) (result outcome)
      condIH (by rw [result_answers]; exact emptyRead) elseIH
  | once_some body env before first rest _ firstRead ih =>
    exact .once_some (goal body) env (result before) first rest ih (by rw [result_answers]; exact firstRead)
  | once_none body env before _ emptyRead ih =>
    exact .once_none (goal body) env (result before) ih (by rw [result_answers]; exact emptyRead)
  | neg_succ body env before _ emptyRead ih =>
    exact .neg_succ (goal body) env (result before) ih (by rw [result_answers]; exact emptyRead)
  | neg_fail body env before first rest _ firstRead ih =>
    exact .neg_fail (goal body) env (result before) first rest ih (by rw [result_answers]; exact firstRead)
  | isVar_succ pat env name read => exact .isVar_succ pat env name read
  | isVar_fail pat env read => exact .isVar_fail pat env read
  | unify_succ left right env bindings matched => exact .unify_succ left right env bindings matched
  | unify_fail left right env matched => exact .unify_fail left right env matched
  | notUnify_succ left right env matched => exact .notUnify_succ left right env matched
  | notUnify_fail left right env bindings rest matched => exact .notUnify_fail left right env bindings rest matched
  | findall_eval name body env before vals _ read ih =>
    simpa only [goal, result, list_payload, insert_binding] using
      PrologEval.findall_eval name (goal body) env (result before) vals ih
        (by rw [result_answers]; exact read)
  | spaceMatch_eval pat template env outs read => exact .spaceMatch_eval pat template env outs read
  | reduceCall_eval args env outs read => exact .reduceCall_eval args env outs read

#print axioms evaluation

end Mettapedia.Languages.Prolog.SharedFixtures

namespace Mettapedia.Languages.Prolog.SharedFixtures

open Lean Meta Elab Command

private def logicFixture (fixture : Name) : Name :=
  `Mettapedia.Logic.Prolog.FixtureCorpus ++ fixture

private def languageFixture (fixture : Name) : Name :=
  `Mettapedia.Languages.Prolog.FixtureCorpus ++ fixture

private def langType (source : Expr) : Expr :=
  source.replace fun node =>
    match node with
    | .const name levels =>
      let target := name.replacePrefix `Mettapedia.Logic.Prolog `Mettapedia.Languages.Prolog
      if target == name then none else some (.const target levels)
    | _ => none

/-- Check the requested new theorem at the transported form of the
canonical declaration's exact type. The fixture names are retained. -/
private def fixtureDeclaration (fixture : Name) : MetaM Declaration := do
  let sourceName := logicFixture fixture
  let .thmInfo source ← getConstInfo sourceName
    | throwError "{sourceName} is not a theorem"
  let type := langType source.type
  let value ← forallTelescope type fun locals conclusion => do
    withTransparency .all do
      let parameters ← locals.mapM fun binder => do
        if (← inferType binder).isConstOf ``EvalOracle then
          pure (mkApp (mkConst ``sourceOracle) binder)
        else
          pure binder
      let witness := mkAppN (mkConst sourceName (source.levelParams.map Level.param)) parameters
      let proof ← if conclusion.getAppFn.isConstOf ``PrologEval then do
        let some oracle := conclusion.getAppArgs[0]?
          | throwError "{sourceName} has no evaluation oracle"
        mkAppM ``evaluation #[oracle, witness]
      else
        pure witness
      unless ← isDefEq (← inferType proof) conclusion do
        throwError "Proof of {sourceName} cannot be read at {conclusion}"
      instantiateMVars (← mkLambdaFVars locals proof)
  pure (.thmDecl {
    name := languageFixture fixture
    levelParams := source.levelParams
    type
    value })

syntax (name := transportPrologFixtures)
  "transport_prolog_fixtures" "[" ident,* "]" : command

elab_rules : command
  | `(transport_prolog_fixtures [$names:ident,*]) => do
    for name in names.getElems do
      withRef name do
        let declaration ← liftTermElabM (fixtureDeclaration name.getId)
        liftCoreM do
          addDecl declaration
          addInheritedDocString (languageFixture name.getId) (logicFixture name.getId)

end Mettapedia.Languages.Prolog.SharedFixtures
