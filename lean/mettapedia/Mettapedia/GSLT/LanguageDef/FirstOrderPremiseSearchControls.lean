import Mettapedia.GSLT.LanguageDef.FirstOrderPremiseSearch

/-! Positive and separating controls for premise output threading, fresh rule
variables, occurs checks, explicit seeds and bounded completion outcomes. -/

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.FirstOrderPremiseSearch.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open FirstOrderRules InferenceChecker

private def a : Pattern := .apply "a" []
private def b : Pattern := .apply "b" []
private def v (name : String) : Pattern := .fvar name
private def app (name : String) (arguments : List Pattern) : Pattern := .apply name arguments
private def limits : Limits := ⟨1000, 20, 128⟩

private def rules : List FORule := [
  ⟨"join", ["x", "middle", "z"],
    [app "edge" [v "x", v "middle"], app "edge" [v "middle", v "z"]], app "path" [v "x", v "z"]⟩,
  ⟨"ab", [], [], app "edge" [a, b]⟩,
  ⟨"ba", [], [], app "edge" [b, a]⟩]

private def status : Outcome → String
  | .candidate _ => "candidate"
  | .noCandidate => "no-candidate"
  | .exhausted _ => "exhausted"
  | .fault _ => "fault"

private def rootArguments (report : Report) : List Pattern :=
  match report.outcome with | .candidate (.node application _) => application.arguments | _ => []

private def childRules (report : Report) : List String :=
  match report.outcome with
  | .candidate (.node _ children) => children.map fun child => match child with | .node application _ => application.ruleId.value
  | _ => []

theorem premise_outputs_threaded :
    rootArguments (search rules (app "path" [a, a]) none limits) = [a, b, a] := by decide +kernel

theorem ordered_children_retained :
    childRules (search rules (app "path" [a, a]) none limits) = ["ab", "ba"] := by decide +kernel

theorem repeated_holes_disagree :
    status (search [⟨"same", ["x"], [], app "same" [v "x", v "x"]⟩]
      (app "same" [a, b]) none limits).outcome = "no-candidate" := by decide +kernel

theorem occurs_check_refuses_cycle :
    (match Mettapedia.TypeTheory.PromotionAdmission.unify 32
      [((.var 0 : UTerm), .app "cycle" [.var 0])] with
    | .fail => true | _ => false) = true := by decide +kernel

private def freshRules : List FORule := [
  ⟨"use-twice", [], [app "id" [a], app "id" [b]], app "ok" []⟩,
  ⟨"id", ["x"], [], app "id" [v "x"]⟩]

private def childArguments (report : Report) : List (List Pattern) :=
  match report.outcome with
  | .candidate (.node _ children) => children.map fun child => match child with | .node application _ => application.arguments
  | _ => []

theorem invocations_have_fresh_variables :
    childArguments (search freshRules (app "ok" []) none limits) = [[a], [b]] := by decide +kernel

theorem step_exhaustion_is_explicit :
    status (search rules (app "path" [a, a]) none ⟨0, 20, 128⟩).outcome = "exhausted" := by decide +kernel

theorem depth_exhaustion_is_explicit :
    status (search rules (app "path" [a, a]) none ⟨1000, 0, 128⟩).outcome = "exhausted" := by decide +kernel

theorem unifier_exhaustion_is_explicit :
    status (search rules (app "path" [a, a]) none ⟨1000, 20, 0⟩).outcome = "exhausted" := by decide +kernel

theorem bad_seed_argument_arity :
    status (search rules (app "path" [a, a]) (some (.node "join" [] [none, none])) limits).outcome =
      "fault" := by decide +kernel

theorem bad_seed_premise_arity :
    status (search rules (app "path" [a, a]) (some (.node "join" [a, b, a] [])) limits).outcome =
      "fault" := by decide +kernel

theorem undeclared_variable_fault :
    status (search [⟨"bad", [], [app "missing" [v "ghost"]], app "ok" []⟩]
      (app "ok" []) none limits).outcome = "fault" := by decide +kernel

theorem duplicate_rule_identity_fault :
    status (search (rules ++ rules) (app "path" [a, a]) none limits).outcome = "fault" := by decide +kernel

theorem unused_variable_not_invented :
    status (search [⟨"undetermined", ["x"], [], app "ok" []⟩]
      (app "ok" []) none limits).outcome = "no-candidate" := by decide +kernel

theorem repeated_calls_do_not_mutate_inputs :
    rootArguments (search rules (app "path" [a, a]) none limits) = [a, b, a] ∧
    rootArguments (search rules (app "path" [b, b]) none limits) = [b, a, b] := by decide +kernel

theorem deep_left_branch_does_not_hide_base :
    status (search [⟨"recursive", [], [app "goal" []], app "goal" []⟩,
        ⟨"base", [], [], app "goal" []⟩]
      (app "goal" []) none ⟨1000, 4, 128⟩).outcome = "candidate" := by decide +kernel

end Mettapedia.GSLT.LanguageDef.FirstOrderPremiseSearch.Controls
