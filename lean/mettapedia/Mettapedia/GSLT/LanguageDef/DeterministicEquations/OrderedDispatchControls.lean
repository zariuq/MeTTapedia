import Mettapedia.GSLT.LanguageDef.DeterministicEquations.OrderedDispatch

/-!
# Ordered-dispatch controls

These use the actual source matching and body evaluator. They exercise
overlap, source occurrences, all-arity grouping, data bindings and committed
failure/exhaustion. They do not assert concrete MeTTa execution or the
left-linear profile of an arbitrary source pattern.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.OrderedDispatch.Controls

private def equation (name head : String) (parameters : List Term) (body : Term) : Equation :=
  { name, head, params := parameters, body }

private def specific : Equation := equation "specific" "choose" [.sym "a"] (.sym "specific-answer")
private def wildcard : Equation := equation "wildcard" "choose" [.var "x"] (.sym "fallback-answer")
private def overlap : Program := [specific, wildcard]
private def pureHost : Host := { primitive := fun _ _ => .unhandled }

theorem overlapping_patterns_select_first :
    (selectCase (compileHead overlap "choose") [.sym "a"]).map (fun hit => hit.1.sourceIndex) =
      some 0 := rfl

theorem reversing_overlap_changes_selected_body :
    dispatchCaseWith (eval [wildcard, specific] pureHost 1)
      (compileHead [wildcard, specific] "choose") [.sym "a"] =
      .value (.sym "fallback-answer") := rfl

theorem specific_body_is_executed :
    dispatchCaseWith (eval overlap pureHost 1) (compileHead overlap "choose") [.sym "a"] =
      .value (.sym "specific-answer") := rfl

theorem unmatched_specific_uses_later_pattern :
    dispatchCaseWith (eval overlap pureHost 1) (compileHead overlap "choose") [.sym "b"] =
      .value (.sym "fallback-answer") := rfl

theorem source_occurrences_are_not_deduplicated :
    (compileHead [specific, specific] "choose").map (·.sourceIndex) = [0, 1] := rfl

theorem identical_duplicate_selects_first_occurrence :
    (selectCase (compileHead [specific, specific] "choose") [.sym "a"]).map
      (fun hit => hit.1.sourceIndex) = some 0 := rfl

theorem foreign_head_does_not_renumber_occurrences :
    (compileHead [specific, equation "foreign" "other" [] (.sym "other-answer"), wildcard]
      "choose").map (·.sourceIndex) = [0, 2] := rfl

private def allArities : Program :=
  [equation "zero" "arity" [] (.sym "zero-answer"),
   equation "one" "arity" [.var "x"] (.sym "one-answer"),
   equation "two" "arity" [.var "x", .var "y"] (.sym "two-answer")]

theorem grouping_keeps_all_arities :
    (compileHead allArities "arity").map (fun row => row.equation.params.length) = [0, 1, 2] := rfl

theorem zero_arity_selects_its_vector :
    (selectCase (compileHead allArities "arity") []).map (fun hit => hit.1.sourceIndex) = some 0 := rfl

theorem two_arity_selects_its_vector :
    (selectCase (compileHead allArities "arity") [.sym "a", .sym "b"]).map
      (fun hit => hit.1.sourceIndex) = some 2 := rfl

theorem wrong_arity_refuses :
    dispatchCaseWith (eval allArities pureHost 1) (compileHead allArities "arity")
      [.sym "a", .sym "b", .sym "c"] = .failure := rfl

theorem declared_unmatched_pattern_refuses :
    dispatchCaseWith (eval [specific] pureHost 1) (compileHead [specific] "choose") [.sym "b"] =
      .failure := rfl

private def faultHost : Host :=
  { primitive := fun head _ => if head = "faulting-primitive" then .fault else .unhandled }

private def failing : Equation :=
  equation "first-fails" "choose" [.sym "a"] (.expr [.sym "faulting-primitive"])

theorem selected_primitive_failure_is_not_rescued :
    dispatchCaseWith (eval [failing, wildcard] faultHost 2)
      (compileHead [failing, wildcard] "choose") [.sym "a"] = .failure := rfl

theorem later_body_would_succeed_after_failure :
    dispatchCaseWith (eval [failing, wildcard] faultHost 2)
      (compileHead [wildcard] "choose") [.sym "a"] = .value (.sym "fallback-answer") := rfl

private def demanding : Equation :=
  equation "first-needs-more-fuel" "choose" [.sym "a"] (.expr [.sym "helper"])
private def helper : Equation := equation "helper" "helper" [] (.sym "helper-answer")

theorem selected_body_exhaustion_is_not_rescued :
    dispatchCaseWith (eval [demanding, wildcard, helper] pureHost 1)
      (compileHead [demanding, wildcard, helper] "choose") [.sym "a"] = .exhausted := rfl

theorem later_body_would_succeed_after_exhaustion :
    dispatchCaseWith (eval [demanding, wildcard, helper] pureHost 1)
      (compileHead [wildcard] "choose") [.sym "a"] = .value (.sym "fallback-answer") := rfl

theorem sufficient_fuel_executes_original_selected_body :
    dispatchCaseWith (eval [demanding, wildcard, helper] pureHost 2)
      (compileHead [demanding, wildcard, helper] "choose") [.sym "a"] =
      .value (.sym "helper-answer") := rfl

theorem completed_failure_is_distinct_from_exhaustion :
    dispatchCaseWith (eval [failing, wildcard] faultHost 2)
      (compileHead [failing, wildcard] "choose") [.sym "a"] ≠ .exhausted := by
  rw [selected_primitive_failure_is_not_rescued]
  intro equal
  cases equal

theorem bindings_keep_argument_order :
    (selectCase (compileHead
      [equation "bindings" "bind" [.var "left", .var "right"] (.var "left")] "bind")
      [.sym "b", .sym "a"]).map Prod.snd = some [("left", .sym "b"), ("right", .sym "a")] := rfl

theorem bound_active_looking_data_is_not_executed :
    dispatchCaseWith (eval
      [equation "identity" "identity" [.var "x"] (.var "x")] faultHost 1)
      (compileHead [equation "identity" "identity" [.var "x"] (.var "x")] "identity")
      [.expr [.sym "faulting-primitive"]] = .value (.expr [.sym "faulting-primitive"]) := rfl

theorem vector_matching_preserves_list_expression_distinction :
    selectCase (compileHead
      [equation "nested-list" "nested" [.list [.sym "a"]] (.sym "list-answer")] "nested")
      [.expr [.sym "a"]] = none := rfl

theorem literal_spelling_is_not_numeric_equality :
    selectCase (compileHead
      [equation "spelling" "spelling" [.lit "01"] (.sym "matched")] "spelling")
      [.lit "1"] = none := rfl

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.OrderedDispatch.Controls
