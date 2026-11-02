import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternCoverage

/-! Both emitted pattern-rule forms preserve the source match and its
environment extension. Clause priority and failed-match service execution
remain separate controller obligations.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match

theorem apply_patternId (assignment : Bindings) (index : Nat) :
    applyBindings assignment (patternId index) = patternId index := by
  simp only [patternId, apply_node, List.map_cons, List.map_nil, apply_digits]

theorem match_one_rule_readback (pattern : OCaml.MatchPattern) (index : Nat) (actual : OCaml.Value)
    (body : OCaml.Code) (captured : OCaml.Environment) (continuation : Pattern) (assignment : Bindings)
    (input : applyBindings assignment ((patternRules index pattern)[0]'(by simp [patternRules])).left =
      node "MlMatchOne" [patternId index, value actual, code body, environment captured, continuation]) :
    ∃ boundValues, OCaml.matchPattern pattern actual = some boundValues ∧
      applyBindings assignment ((patternRules index pattern)[0]'(by simp [patternRules])).right =
        node "MlEvaluate" [code body, environment (OCaml.extend captured boundValues), continuation] := by
  change applyBindings assignment (node "MlMatchOne"
    [patternId index, (patternAt pattern 0).term, hole "body", hole "environment", hole "continuation"]) = _ at input
  simp only [apply_node, List.map_cons, List.map_nil, apply_patternId] at input
  have arguments := (Pattern.apply.inj input).2
  have matching := (List.cons.inj (List.cons.inj arguments).2).1
  have bodySame := (List.cons.inj (List.cons.inj (List.cons.inj arguments).2).2).1
  have capturedSame := (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj arguments).2).2).2).1
  have continuationSame := (List.cons.inj
    (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj arguments).2).2).2).2).1
  obtain ⟨boundValues, matched, bindingsSame⟩ := pattern_instance_readback pattern 0 actual assignment matching
  refine ⟨boundValues, matched, ?_⟩
  change applyBindings assignment (node "MlEvaluate"
    [hole "body", extend (patternAt pattern 0).bindings (hole "environment"), hole "continuation"]) = _
  simp only [apply_node, List.map_cons, List.map_nil, apply_extend,
    bodySame, capturedSame, continuationSame, bindingsSame, environment_extend]

theorem try_clause_rule_readback (pattern : OCaml.MatchPattern) (index : Nat) (actual : OCaml.Value)
    (body : OCaml.Code) (later : Pattern) (captured : OCaml.Environment) (continuation : Pattern) (assignment : Bindings)
    (input : applyBindings assignment ((patternRules index pattern)[1]'(by simp [patternRules])).left =
      node "MlTryClause" [patternId index, value actual, code body, later, environment captured, continuation]) :
    ∃ boundValues, OCaml.matchPattern pattern actual = some boundValues ∧
      applyBindings assignment ((patternRules index pattern)[1]'(by simp [patternRules])).right =
        node "MlEvaluate" [code body, environment (OCaml.extend captured boundValues), continuation] := by
  change applyBindings assignment (node "MlTryClause"
    [patternId index, (patternAt pattern 0).term, hole "body", hole "later",
      hole "environment", hole "continuation"]) = _ at input
  simp only [apply_node, List.map_cons, List.map_nil, apply_patternId] at input
  have arguments := (Pattern.apply.inj input).2
  have matching := (List.cons.inj (List.cons.inj arguments).2).1
  have bodySame := (List.cons.inj (List.cons.inj (List.cons.inj arguments).2).2).1
  have capturedSame := (List.cons.inj
    (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj arguments).2).2).2).2).1
  have continuationSame := (List.cons.inj
    (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj (List.cons.inj arguments).2).2).2).2).2).1
  obtain ⟨boundValues, matched, bindingsSame⟩ := pattern_instance_readback pattern 0 actual assignment matching
  refine ⟨boundValues, matched, ?_⟩
  change applyBindings assignment (node "MlEvaluate"
    [hole "body", extend (patternAt pattern 0).bindings (hole "environment"), hole "continuation"]) = _
  simp only [apply_node, List.map_cons, List.map_nil, apply_extend,
    bodySame, capturedSame, continuationSame, bindingsSame, environment_extend]

#print axioms match_one_rule_readback
#print axioms try_clause_rule_readback

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
