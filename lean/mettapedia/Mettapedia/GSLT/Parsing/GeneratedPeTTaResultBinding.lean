import Mettapedia.GSLT.Parsing.SourceSExprPatternMatching

/-!
# Ground result binding in generated PeTTa

Actual dollar-variable templates use the existing Pattern matcher and ground
S-expression codec. This is the result-binding boundary of generated `let`,
not another rule evaluator. The `once` law requires at most one completed
answer occurrence; equality of distinct answer values is insufficient.

The ignored anonymous binder is supported at the result root; nested anonymous
binders are outside this selected generated-template profile.
The laws concern finite, pure, ground answer streams. They do not assert full
PeTTa execution, early stopping of an infinite generator, or that a particular
generated callee has the required cardinality.
-/

namespace Mettapedia.GSLT.Parsing.GeneratedPeTTaResultBinding

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open SourceSExprPatternCodec (encode encodeList)

def variableToken (token : String) : Bool :=
  token.startsWith "$" && token != "$" && token != "$_"

mutual
  /-- Dollar names are schema variables; substituted SExpr values remain data. -/
  def template : SExpr → Pattern
    | .atom token => if variableToken token then .fvar token else encode (.atom token)
    | .list values => .apply "source-sexpr-list-v1" (templates values)

  def templates : List SExpr → List Pattern
    | [] => []
    | value :: values => template value :: templates values
end

mutual
  theorem template_match_correct (schema : SExpr) :
      Pattern.isMatchCorrect (template schema) = true := by
    cases schema with
    | atom token =>
        simp only [template]
        split <;> rfl
    | list values => exact templates_match_correct values
  termination_by sizeOf schema

  theorem templates_match_correct (schemas : List SExpr) :
      isMatchCorrectListAux (templates schemas) = true := by
    cases schemas with
    | nil => rfl
    | cons schema schemas =>
        change (Pattern.isMatchCorrect (template schema) &&
          isMatchCorrectListAux (templates schemas)) = true
        rw [template_match_correct schema, templates_match_correct schemas]
        rfl
  termination_by sizeOf schemas
end

private theorem empty_or_singleton {α : Type} (values : List α)
    (small : values.length ≤ 1) : values = [] ∨ ∃ value, values = [value] := by
  cases values with
  | nil => exact Or.inl rfl
  | cons value rest =>
      right
      refine ⟨value, ?_⟩
      cases rest with
      | nil => rfl
      | cons next tail => simp at small

private theorem filterMap_small {α β : Type} (values : List α)
    (small : values.length ≤ 1) (f : α → Option β) :
    (values.filterMap f).length ≤ 1 := by
  rcases empty_or_singleton values small with rfl | ⟨value, rfl⟩
  · simp
  · cases result : f value <;> simp [result]

private theorem combine_small {α β γ : Type} (left : List α) (right : List β)
    (smallLeft : left.length ≤ 1) (smallRight : right.length ≤ 1)
    (f : α → β → Option γ) :
    (left.flatMap fun x => right.filterMap (f x)).length ≤ 1 := by
  rcases empty_or_singleton left smallLeft with rfl | ⟨value, rfl⟩
  · simp
  · simpa using filterMap_small right smallRight (f value)

mutual
  theorem template_match_small (schema value : SExpr) :
      (matchPattern (template schema) (encode value)).length ≤ 1 := by
    cases schema with
    | atom token =>
        cases isVariable : variableToken token with
        | true => simp [template, isVariable, matchPattern]
        | false =>
            cases value with
            | atom other =>
                simp only [template, isVariable, Bool.false_eq_true, ↓reduceIte,
                  encode, matchPattern, matchArgs, List.length_cons, List.length_nil,
                  beq_self_eq_true, Bool.and_self, List.filterMap_nil,
                  List.filterMap_cons]
                split <;> simp_all [mergeBindings]
            | list values => simp [template, isVariable, encode, matchPattern]
    | list schemas =>
        cases value with
        | atom token => simp [template, encode, matchPattern]
        | list values =>
            simp only [template, encode, matchPattern]
            split
            · exact templates_match_small schemas values
            · simp
  termination_by sizeOf schema

  theorem templates_match_small (schemas values : List SExpr) :
      (matchArgs (templates schemas) (encodeList values)).length ≤ 1 := by
    cases schemas with
    | nil => cases values <;> simp [templates, encodeList, matchArgs]
    | cons schema schemas =>
        cases values with
        | nil => simp [templates, encodeList, matchArgs]
        | cons value values =>
            simpa only [templates, encodeList, matchArgs] using
              combine_small _ _ (template_match_small schema value)
                (templates_match_small schemas values) mergeBindings
  termination_by sizeOf schemas
end

/-- Bind one completed ground result consistently with the caller environment.
The generated ignored-result binder is handled without creating a named cell. -/
def bindResult (env : Bindings) (schema value : SExpr) : List Bindings :=
  if schema = .atom "$_" then [env]
  else (matchPattern (template schema) (encode value)).filterMap (mergeBindings env)

def bindAnswers (env : Bindings) (schema : SExpr) (answers : List SExpr) : List Bindings :=
  answers.flatMap (bindResult env schema)

theorem bindResult_small (env : Bindings) (schema value : SExpr) :
    (bindResult env schema value).length ≤ 1 := by
  unfold bindResult
  split
  · simp
  · exact filterMap_small _ (template_match_small schema value) _

theorem bindResult_preserves_frame (env : Bindings) (schema value : SExpr)
    (next : Bindings) (returned : next ∈ bindResult env schema value)
    (name : String) (before : Pattern)
    (bound : env.find? (·.1 == name) = some (name, before)) :
    next.find? (·.1 == name) = some (name, before) := by
  unfold bindResult at returned
  split at returned
  · simpa using (List.mem_singleton.mp returned ▸ bound)
  · obtain ⟨matched, _, merged⟩ := List.mem_filterMap.mp returned
    exact mergeBindings_subsumed_left merged bound

theorem bindAnswers_preserves_frame (env : Bindings) (schema : SExpr)
    (answers : List SExpr) (next : Bindings)
    (returned : next ∈ bindAnswers env schema answers)
    (name : String) (before : Pattern)
    (bound : env.find? (·.1 == name) = some (name, before)) :
    next.find? (·.1 == name) = some (name, before) := by
  obtain ⟨value, _, matched⟩ := List.mem_flatMap.mp returned
  exact bindResult_preserves_frame env schema value next matched name before bound

/-- A named/structured result template reconstructs the exact ground result
under the merged environment; preserving the frame does not lose the match. -/
theorem bindResult_reconstructs (env : Bindings) (schema value : SExpr)
    (named : schema ≠ .atom "$_") (next : Bindings)
    (returned : next ∈ bindResult env schema value) :
    applyBindings next (template schema) = encode value := by
  simp only [bindResult, named, ↓reduceIte] at returned
  obtain ⟨matched, matchedResult, merged⟩ := List.mem_filterMap.mp returned
  exact matchRel_correct_of_extends (matchPattern_sound matchedResult)
    (template_match_correct schema)
    (fun _ _ bound => mergeBindings_subsumed_right merged bound)

private theorem take_one_of_small {α : Type} (values : List α)
    (small : values.length ≤ 1) : values.take 1 = values := by
  rcases empty_or_singleton values small with rfl | ⟨value, rfl⟩ <;> rfl

/-- Moving finite result constraints across `once` is safe for zero-or-one
answer occurrences, including constrained failure and caller bindings. -/
theorem semidet_binding_once (env : Bindings) (schema : SExpr)
    (answers : List SExpr) (semidet : answers.length ≤ 1) :
    bindAnswers env schema (answers.take 1) =
      (bindAnswers env schema answers).take 1 := by
  rw [take_one_of_small answers semidet]
  symm
  apply take_one_of_small
  rcases empty_or_singleton answers semidet with rfl | ⟨value, rfl⟩
  · simp [bindAnswers]
  · simpa [bindAnswers] using bindResult_small env schema value

/-- The whole continuation's ordered result list is preserved, not only its
set of values. The call's completion/cardinality premise remains explicit. -/
theorem semidet_let_continuation (env : Bindings) (schema : SExpr)
    (answers : List SExpr) (semidet : answers.length ≤ 1)
    (body : Bindings → List SExpr) :
    (bindAnswers env schema (answers.take 1)).flatMap body =
      ((bindAnswers env schema answers).take 1).flatMap body := by
  rw [semidet_binding_once env schema answers semidet]

theorem ignored_result_retains_occurrences (env : Bindings) (answers : List SExpr) :
    bindAnswers env (.atom "$_") answers = answers.map (fun _ => env) := by
  induction answers with
  | nil => rfl
  | cons value rest ih => simpa [bindAnswers, bindResult] using congrArg (List.cons env) ih

theorem equal_values_do_not_license_once (value : SExpr) :
    bindAnswers [] (.atom "$_") [value, value] ≠
      (bindAnswers [] (.atom "$_") [value, value]).take 1 := by
  simp [ignored_result_retains_occurrences]

theorem constraint_before_once_can_select_second :
    bindAnswers [] (.atom "second") ([.atom "first", .atom "second"].take 1) = [] ∧
      (bindAnswers [] (.atom "second") [.atom "first", .atom "second"]).take 1 = [[]] := by
  simp [bindAnswers, bindResult, template, variableToken, encode, matchPattern,
    matchArgs, mergeBindings]

theorem caller_binding_cannot_be_overwritten :
    bindResult [("$x", encode (.atom "old"))] (.atom "$x") (.atom "new") = [] := by
  simp [bindResult, template, variableToken, encode, matchPattern, mergeBindings]

theorem caller_binding_can_be_reused :
    bindResult [("$x", encode (.atom "same"))] (.atom "$x") (.atom "same") =
      [[("$x", encode (.atom "same"))]] := by
  simp [bindResult, template, variableToken, encode, matchPattern, mergeBindings]

theorem dollar_payload_is_not_a_new_variable :
    bindResult [] (.atom "$x") (.atom "$y") = [[("$x", encode (.atom "$y"))]] := by
  simp [bindResult, template, variableToken, matchPattern, mergeBindings]

theorem callable_payload_stays_data :
    bindResult [] (.atom "$x") (.list [.atom "f", .atom "$y"]) =
      [[("$x", encode (.list [.atom "f", .atom "$y"]))]] := by
  simp [bindResult, template, variableToken, matchPattern, mergeBindings]

end Mettapedia.GSLT.Parsing.GeneratedPeTTaResultBinding
