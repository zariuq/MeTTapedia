import Mettapedia.GSLT.Parsing.GeneratedPeTTaResultBinding
import Mettapedia.GSLT.Parsing.PlainBnfGeneratedPeTTaSyntax

/-!
# Instantiation of actual generated PeTTa templates

The existing Pattern substitution and exact S-expression codec determine
instantiation. Dollar names occur in templates; bound values remain inert
encoded data. A missing binding or a value outside the codec image yields
`none`, not an empty answer stream. The result-root `$_` wildcard belongs to
`bindResult`; it is not an expression variable here.

These laws describe substitution and compatible frames, not generated-body
execution or full PeTTa evaluation. No target syntax or evaluator is added.
-/

namespace Mettapedia.GSLT.Parsing.GeneratedPeTTaTemplateInstantiation

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open SourceSExprPatternCodec (encode encodeList decode decodeList decode_encode)
open GeneratedPeTTaResultBinding (variableToken template templates bindResult bindAnswers)

def instantiate? (env : Bindings) (schema : SExpr) : Option SExpr :=
  decode (applyBindings env (template schema))

def instantiateList? (env : Bindings) (schemas : List SExpr) : Option (List SExpr) :=
  decodeList ((templates schemas).map (applyBindings env))

/-- Exact closed-result characterization, including arbitrary noncanonical
binding values: success is precisely membership in the ground-data image. -/
theorem instantiate_eq_some_iff (env : Bindings) (schema value : SExpr) :
    instantiate? env schema = some value ↔
      applyBindings env (template schema) = encode value := by
  rw [instantiate?, SourceSExprPatternCodec.decode_eq_some_iff, eq_comm]

theorem instantiate_atom (env : Bindings) (token : String) :
    instantiate? env (.atom token) =
      if variableToken token then
        (env.find? (·.1 == token)).bind (fun entry => decode entry.2)
      else some (.atom token) := by
  cases classified : variableToken token with
  | false => simp [instantiate?, template, classified, applyBindings, encode, decode]
  | true =>
      simp only [instantiate?, template, classified, ↓reduceIte, applyBindings]
      cases found : env.find? (·.1 == token) <;> rfl

@[simp] theorem instantiate_list (env : Bindings) (schemas : List SExpr) :
    instantiate? env (.list schemas) = SExpr.list <$> instantiateList? env schemas := by
  simp only [instantiate?, template, applyBindings, decode, instantiateList?]

@[simp] theorem instantiateList_nil (env : Bindings) :
    instantiateList? env [] = some [] := rfl

@[simp] theorem instantiateList_cons (env : Bindings) (schema : SExpr) (schemas : List SExpr) :
    instantiateList? env (schema :: schemas) =
      (do return (← instantiate? env schema) :: (← instantiateList? env schemas)) := rfl

theorem instantiate_variable {env : Bindings} {token : String} {value : SExpr}
    (classified : variableToken token = true)
    (bound : env.find? (·.1 == token) = some (token, encode value)) :
    instantiate? env (.atom token) = some value := by
  rw [instantiate_atom, classified, if_pos rfl, bound]
  exact decode_encode value

theorem instantiate_missing {env : Bindings} {token : String}
    (classified : variableToken token = true)
    (missing : env.find? (·.1 == token) = none) :
    instantiate? env (.atom token) = none := by
  simp [instantiate_atom, classified, missing]

/-- Supplying a bound value does not recursively interpret variable-looking
or callable-looking data inside that value. -/
theorem bound_value_is_inert (env : Bindings) (token : String) (value : SExpr)
    (classified : variableToken token = true) :
    instantiate? ((token, encode value) :: env) (.atom token) = some value := by
  apply instantiate_variable classified
  simp

theorem ignored_token_is_expression_data (env : Bindings) :
    instantiate? env (.atom "$_") = some (.atom "$_") := by
  simp [instantiate_atom, variableToken]

theorem bindResult_instantiates (env : Bindings) (schema value : SExpr)
    (named : schema ≠ .atom "$_") (next : Bindings)
    (returned : next ∈ bindResult env schema value) :
    instantiate? next schema = some value :=
  (instantiate_eq_some_iff next schema value).mpr
    (GeneratedPeTTaResultBinding.bindResult_reconstructs env schema value named next returned)

private theorem find_key {env : Bindings} {name key : String} {value : Pattern}
    (found : env.find? (·.1 == name) = some (key, value)) : key = name := by
  have matched := List.find?_some found
  simpa only [beq_iff_eq] using matched

mutual
  /-- Compatible extension preserves every already completed instantiation.
  Missing-variable failures need not survive an extension that supplies them. -/
  theorem instantiate_of_extends (env next : Bindings)
      (extension : BindingsExtends env next) (schema value : SExpr)
      (before : instantiate? env schema = some value) :
      instantiate? next schema = some value := by
    cases schema with
    | atom token =>
        cases classified : variableToken token with
        | false =>
            simpa only [instantiate_atom, classified, Bool.false_eq_true, ↓reduceIte] using before
        | true =>
            rw [instantiate_atom, classified, if_pos rfl] at before ⊢
            cases found : env.find? (·.1 == token) with
            | none => simp [found] at before
            | some entry =>
                rcases entry with ⟨key, term⟩
                have same := find_key found
                subst key
                rw [extension token term found]
                simpa [found] using before
    | list schemas =>
        rw [instantiate_list] at before ⊢
        cases result : instantiateList? env schemas with
        | none => simp [result] at before
        | some values =>
            have same : SExpr.list values = value := by simpa [result] using before
            rw [instantiateList_of_extends env next extension schemas values result, ← same]
            rfl
  termination_by sizeOf schema

  theorem instantiateList_of_extends (env next : Bindings)
      (extension : BindingsExtends env next) (schemas values : List SExpr)
      (before : instantiateList? env schemas = some values) :
      instantiateList? next schemas = some values := by
    cases schemas with
    | nil => simpa using before
    | cons schema schemas =>
        rw [instantiateList_cons] at before ⊢
        cases first : instantiate? env schema with
        | none => simp [first] at before
        | some value =>
            cases rest : instantiateList? env schemas with
            | none => simp [first, rest] at before
            | some tail =>
                have same : value :: tail = values := by simpa [first, rest] using before
                rw [instantiate_of_extends env next extension schema value first,
                  instantiateList_of_extends env next extension schemas tail rest, ← same]
                rfl
  termination_by sizeOf schemas
end

theorem instantiate_preserved_by_bindResult
    (env next : Bindings) (resultSchema resultValue schema value : SExpr)
    (returned : next ∈ bindResult env resultSchema resultValue)
    (before : instantiate? env schema = some value) :
    instantiate? next schema = some value :=
  instantiate_of_extends env next
    (GeneratedPeTTaResultBinding.bindResult_preserves_frame env resultSchema resultValue next returned)
    schema value before

theorem instantiate_preserved_by_bindAnswers
    (env next : Bindings) (resultSchema : SExpr) (answers : List SExpr)
    (schema value : SExpr) (returned : next ∈ bindAnswers env resultSchema answers)
    (before : instantiate? env schema = some value) :
    instantiate? next schema = some value :=
  instantiate_of_extends env next
    (GeneratedPeTTaResultBinding.bindAnswers_preserves_frame env resultSchema answers next returned)
    schema value before

/-- Result binding cannot contradict a template already closed by the caller. -/
theorem bound_result_agrees_with_caller (env next : Bindings) (schema beforeValue resultValue : SExpr)
    (named : schema ≠ .atom "$_")
    (before : instantiate? env schema = some beforeValue)
    (returned : next ∈ bindResult env schema resultValue) : beforeValue = resultValue := by
  exact Option.some.inj
    ((instantiate_preserved_by_bindResult env next schema resultValue schema beforeValue returned before).symm.trans
      (bindResult_instantiates env schema resultValue named next returned))

/-- Common unsigiled names are projected into the source namespace without
changing payloads, list order or repeated bindings. -/
def sourceEnv (values : List (String × SExpr)) : SourceSExprPatternInstantiation.Env :=
  values.map fun (name, value) => ("?" ++ name, value)

def targetEnv (values : List (String × SExpr)) : Bindings :=
  values.map fun (name, value) => ("$" ++ name, encode value)

private theorem find_prefixed {α β : Type} (sigil : String) (f : α → β)
    (values : List (String × α)) (name : String) :
    ((values.map fun (key, value) => (sigil ++ key, f value)).find?
      (·.1 == sigil ++ name)) =
    (values.find? (·.1 == name)).map (fun (key, value) => (sigil ++ key, f value)) := by
  induction values with
  | nil => rfl
  | cons entry values ih =>
      rcases entry with ⟨key, value⟩
      have same : (sigil ++ key == sigil ++ name) = (key == name) := by
        apply Bool.eq_iff_iff.mpr
        simpa only [beq_iff_eq] using (String.append_right_inj sigil (t₁ := key) (t₂ := name))
      simp only [List.map_cons, List.find?_cons, same]
      cases key == name <;> simp [ih]

private theorem prefixed_named_token (sigil name : String)
    (nonempty : name ≠ "") (nonanonymous : name ≠ "_") :
    ((sigil ++ name).startsWith sigil &&
      (sigil ++ name != sigil) && (sigil ++ name != sigil ++ "_")) = true := by
  have starts : (sigil ++ name).startsWith sigil = true := by
    simp [String.toList_append]
  have first : sigil ++ name ≠ sigil := by
    intro same
    apply nonempty
    apply (String.append_right_inj sigil).mp
    simpa using same
  have second : sigil ++ name ≠ sigil ++ "_" := by
    intro same
    exact nonanonymous ((String.append_right_inj sigil).mp same)
  simp [starts, first, second]

/-- Actual source variable spelling is transformed by the syntax fold.
The lone question mark is excluded; the expression bridge below also excludes
the anonymous result-binder spelling. -/
theorem source_variable_fold (name : String) (nonempty : name ≠ "") :
    PlainBnfGeneratedPeTTaSyntax.sourceTerm? (.atom ("?" ++ name)) =
      some (.atom ("$" ++ name)) := by
  rw [PlainBnfGeneratedPeTTaSyntax.sourceTerm_atom]
  congr 2
  unfold PlainBnfGeneratedPeTTaSyntax.variableToken
  rw [String.toList_append]
  cases parts : name.toList with
  | nil =>
      have empty : name = "" := by
        apply String.toList_inj.mp
        simpa using parts
      exact False.elim (nonempty empty)
  | cons head tail =>
      apply String.toList_inj.mp
      simp [parts, String.toList_append]

/-- The source/target namespace projections have the same first-binding
lookup, including missing names and duplicate keys. Payloads are not rendered.
This is a variable-leaf bridge, not a whole-template nullary conversion law. -/
theorem source_variable_instantiation (values : List (String × SExpr)) (name : String)
    (nonempty : name ≠ "") (nonanonymous : name ≠ "_") :
    instantiate? (targetEnv values) (.atom ("$" ++ name)) =
      SourceSExprPatternInstantiation.instantiate? (sourceEnv values) (.atom ("?" ++ name)) := by
  have sourceNamed : SourceIntegerProvider.sourceVariableToken ("?" ++ name) = true :=
    prefixed_named_token "?" name nonempty nonanonymous
  have targetNamed : variableToken ("$" ++ name) = true :=
    prefixed_named_token "$" name nonempty nonanonymous
  rw [instantiate_atom, targetNamed, if_pos rfl,
    SourceSExprPatternInstantiation.instantiate?, sourceNamed, if_pos rfl]
  unfold targetEnv sourceEnv
  rw [find_prefixed "$" encode values name,
    find_prefixed "?" (fun value : SExpr => value) values name]
  cases found : values.find? (·.1 == name) with
  | none => rfl
  | some entry =>
      rcases entry with ⟨key, value⟩
      exact decode_encode value

/-- The variable-leaf square uses the actual source-to-PeTTa syntax fold,
not a separately stipulated dollar spelling. -/
theorem actual_source_variable_instantiation (values : List (String × SExpr)) (name : String)
    (nonempty : name ≠ "") (nonanonymous : name ≠ "_") :
    (PlainBnfGeneratedPeTTaSyntax.sourceTerm? (.atom ("?" ++ name))).bind
        (instantiate? (targetEnv values)) =
      SourceSExprPatternInstantiation.instantiate? (sourceEnv values) (.atom ("?" ++ name)) := by
  rw [source_variable_fold name nonempty]
  exact source_variable_instantiation values name nonempty nonanonymous

theorem missing_can_become_bound :
    instantiate? [] (.atom "$x") = none ∧
      instantiate? [("$x", encode (.atom "value"))] (.atom "$x") = some (.atom "value") := by
  constructor
  · apply instantiate_missing <;> simp [variableToken]
  · exact bound_value_is_inert [] "$x" (.atom "value") (by simp [variableToken])

theorem dollar_payload_not_revisited :
    instantiate? [("$x", encode (.atom "$y")), ("$y", encode (.atom "changed"))]
      (.atom "$x") = some (.atom "$y") :=
  bound_value_is_inert _ "$x" _ (by simp [variableToken])

theorem callable_payload_not_revisited :
    instantiate? [("$x", encode (.list [.atom "+", .atom "1", .atom "2"]))]
      (.atom "$x") = some (.list [.atom "+", .atom "1", .atom "2"]) :=
  bound_value_is_inert [] "$x" _ (by simp [variableToken])

theorem nonencoded_binding_refused :
    instantiate? [("$x", .apply "ordinary-ground-term" [])] (.atom "$x") = none := by
  simp [instantiate_atom, variableToken, decode]

theorem ignored_binder_does_not_instantiate_to_its_result :
    [] ∈ bindResult [] (.atom "$_") (.atom "value") ∧
      instantiate? [] (.atom "$_") ≠ some (.atom "value") := by
  simp [bindResult, ignored_token_is_expression_data]

/-- Literal-dollar source data is not covered by the variable-leaf bridge. -/
theorem literal_dollar_source_needs_separate_treatment :
    SourceSExprPatternInstantiation.instantiate? [] (.atom "$x") = some (.atom "$x") ∧
      instantiate? [] (.atom "$x") = none := by
  constructor
  · simp [SourceSExprPatternInstantiation.instantiate?, SourceIntegerProvider.sourceVariableToken]
  · exact missing_can_become_bound.1

/-- The source nullary marker is explicitly converted by the syntax fold,
so direct equality of source and target payload representations is false. -/
theorem nullary_source_is_not_target_data :
    SourceSExprPatternInstantiation.instantiate? []
      (.list [.atom "metta-nullary", .atom "constant"]) =
        some (.list [.atom "metta-nullary", .atom "constant"]) ∧
    (PlainBnfGeneratedPeTTaSyntax.sourceTerm?
      (.list [.atom "metta-nullary", .atom "constant"])).bind (instantiate? []) =
        some (.list [.atom "constant"]) := by
  constructor
  · simp [SourceSExprPatternInstantiation.instantiate?, SourceSExprPatternInstantiation.instantiateList?,
      SourceIntegerProvider.sourceVariableToken]
  · rw [PlainBnfGeneratedPeTTaSyntax.sourceTerm_nullary]
    simp [PlainBnfGeneratedPeTTaSyntax.variableToken, instantiate_atom, variableToken]

#print axioms instantiate_eq_some_iff
#print axioms instantiate_of_extends
#print axioms bindResult_instantiates
#print axioms bound_result_agrees_with_caller
#print axioms actual_source_variable_instantiation

end Mettapedia.GSLT.Parsing.GeneratedPeTTaTemplateInstantiation
