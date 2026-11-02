import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlVariableLookup
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFreeNames

/-! An instantiated lookup prefix selects exactly its source environment
position. The value returned by a compiled lookup is the value stored there;
short environments cannot match the prefix.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match

theorem extend_reverse_readback (skipped : List Pattern) (wanted suffix : Pattern) (items : List OCaml.Value)
    (same : extend skipped.reverse (node "MlEnvironmentCons" [wanted, suffix]) = environment items) :
    ∃ actual, items[skipped.length]? = some actual ∧ wanted = value actual := by
  induction skipped generalizing items with
  | nil =>
      cases items with
      | nil => simp [extend, environment, node] at same
      | cons actual rest =>
          have arguments := List.cons.inj (Pattern.apply.inj same).2
          exact ⟨actual, rfl, arguments.1⟩
  | cons first rest ih =>
      have shape : extend (first :: rest).reverse (node "MlEnvironmentCons" [wanted, suffix]) =
          node "MlEnvironmentCons" [first, extend rest.reverse (node "MlEnvironmentCons" [wanted, suffix])] := by
        simp only [extend, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [shape] at same
      cases items with
      | nil => simp [environment, node] at same
      | cons head tail =>
          have arguments := List.cons.inj (Pattern.apply.inj same).2
          have tailSame := (List.cons.inj arguments.2).1
          obtain ⟨actual, found, valueSame⟩ := ih tail tailSame
          exact ⟨actual, found, valueSame⟩

theorem variable_rule_readback (pool : List OCaml.MatchPattern) (reference index : Nat) (items : OCaml.Environment)
    (rest : Pattern) (row : RewriteRule) (assignment : Bindings)
    (formed : compileInstruction? pool reference (.variable index) = some row)
    (input : applyBindings assignment row.left = node "MlEvaluate" [code reference, environment items, rest]) :
    ∃ actual, items[index]? = some actual ∧ applyBindings assignment row.right = node "MlReturn" [value actual, rest] := by
  simp only [compileInstruction?, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at formed
  cases formed
  simp only [rule, apply_node, List.map_cons, List.map_nil, apply_code] at input
  have arguments := List.cons.inj (Pattern.apply.inj input).2
  have environmentSame := (List.cons.inj arguments.2).1
  have continuationSame := (List.cons.inj (List.cons.inj arguments.2).2).1
  simp only [apply_extend, List.map_reverse, apply_node, List.map_cons, List.map_nil] at environmentSame
  obtain ⟨actual, found, valueSame⟩ := extend_reverse_readback
    (((List.range index).map fun skip => hole ("skip:" ++ toString skip)).map (applyBindings assignment))
    (applyBindings assignment (hole "variable")) (applyBindings assignment (hole "tail")) items environmentSame
  simp only [List.length_map, List.length_range] at found
  refine ⟨actual, found, ?_⟩
  simp only [rule, apply_node, List.map_cons, List.map_nil, valueSame, continuationSame]

#print axioms variable_rule_readback

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
