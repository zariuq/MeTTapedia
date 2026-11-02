import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternFiring
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFunctionInstantiation
import Mettapedia.Languages.OCaml.PatternProperties

/-! Pattern-rule observations agree with source let/function entry and
ordered clause selection. Earlier clause failures remain explicit evidence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match

theorem match_one_rule_source (pattern : OCaml.MatchPattern) (index : Nat) (actual : OCaml.Value)
    (body : OCaml.Code) (captured : OCaml.Environment) (continuation : OCaml.Continuation)
    (pool : List OCaml.MatchPattern) (encodedContinuation target : Pattern) (assignment : Bindings)
    (resolved : continuation? pool continuation = some encodedContinuation)
    (input : applyBindings assignment ((patternRules index pattern)[0]'(by simp [patternRules])).left =
      node "MlMatchOne" [patternId index, value actual, code body, environment captured, encodedContinuation])
    (output : applyBindings assignment ((patternRules index pattern)[0]'(by simp [patternRules])).right = target) :
    state? pool (OCaml.enterBody pattern actual body captured continuation) = some target := by
  obtain ⟨boundValues, matched, actualTarget⟩ := match_one_rule_readback pattern index actual body captured
    encodedContinuation assignment input
  rw [← output, actualTarget]
  exact enter_body_encoding body captured continuation resolved matched

theorem let_source_success (program : OCaml.Program) (pattern : OCaml.MatchPattern) (actual : OCaml.Value)
    (body : OCaml.Code) (captured : OCaml.Environment) (bindings : List OCaml.Value) (continuation : OCaml.Continuation)
    (matched : OCaml.matchPattern pattern actual = some bindings) :
    OCaml.machineStep program (.returned actual (.letValue pattern body captured :: continuation)) =
      .ok (some (.evaluate body (OCaml.extend captured bindings) continuation)) := by
  simp only [OCaml.machineStep, OCaml.returnValue, OCaml.enterBody, matched, Except.map]
  rfl

theorem clause_rule_source (program : OCaml.Program) (index : Nat) (actual : OCaml.Value)
    (before : List OCaml.Clause) (clause : OCaml.Clause) (after : List OCaml.Clause)
    (captured : OCaml.Environment) (continuation : OCaml.Continuation) (pool : List OCaml.MatchPattern)
    (encodedContinuation later target : Pattern) (assignment : Bindings)
    (resolved : continuation? pool continuation = some encodedContinuation)
    (earlierFailed : ∀ earlier ∈ before, OCaml.matchPattern earlier.pattern actual = none)
    (input : applyBindings assignment ((patternRules index clause.pattern)[1]'(by simp [patternRules])).left =
      node "MlTryClause" [patternId index, value actual, code clause.body, later, environment captured, encodedContinuation])
    (output : applyBindings assignment ((patternRules index clause.pattern)[1]'(by simp [patternRules])).right = target) :
    ∃ next, OCaml.machineStep program
      (.returned actual (.matchValue (before ++ clause :: after) captured :: continuation)) = .ok (some next) ∧
      state? pool next = some target := by
  obtain ⟨boundValues, matched, actualTarget⟩ := try_clause_rule_readback clause.pattern index actual clause.body later
    captured encodedContinuation assignment input
  have selected := OCaml.selectClause_of_first before clause after actual boundValues earlierFailed matched
  refine ⟨.evaluate clause.body (OCaml.extend captured boundValues) continuation, ?_, ?_⟩
  · simp only [OCaml.machineStep, OCaml.returnValue, selected, Except.map]
    rfl
  · rw [← output, actualTarget]
    simpa only [OCaml.enterBody, matched] using
      enter_body_encoding clause.body captured continuation resolved matched

theorem failed_pattern_no_rule (pattern : OCaml.MatchPattern) (index : Nat) (actual : OCaml.Value)
    (body : OCaml.Code) (captured : OCaml.Environment) (continuation target : Pattern)
    (failed : OCaml.matchPattern pattern actual = none) :
    ¬ ∃ assignment : Bindings,
      applyBindings assignment ((patternRules index pattern)[0]'(by simp [patternRules])).left =
        node "MlMatchOne" [patternId index, value actual, code body, environment captured, continuation] ∧
      applyBindings assignment ((patternRules index pattern)[0]'(by simp [patternRules])).right = target := by
  rw [match_one_rule_iff]
  simp [failed]

#print axioms match_one_rule_source
#print axioms clause_rule_source
#print axioms failed_pattern_no_rule

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
