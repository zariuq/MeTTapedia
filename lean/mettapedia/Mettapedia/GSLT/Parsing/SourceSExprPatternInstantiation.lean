import Mettapedia.GSLT.Parsing.SourceSExprPatternCodec
import Mettapedia.GSLT.Parsing.SourceIntegerProvider
import Mettapedia.OSLF.MeTTaIL.Match

/-!
# Source metavariables and existing Pattern substitution

Source schema atoms use the established `sourceVariableToken` convention.
Environment values instead use the ground-data codec: variable-looking payload
text is never interpreted recursively. Instantiation is simultaneous, with the
first-binding lookup of the existing gradual `applyBindings` operation.

This module connects structural source instantiation to that existing operation.
It does not add a rule evaluator, prove matching, or change the strict binding
API's separate policy of rejecting duplicate environment keys.
-/

namespace Mettapedia.GSLT.Parsing.SourceSExprPatternInstantiation

open Algorithms.MeTTa.Simple.Parser
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open SourceSExprPatternCodec
open SourceIntegerProvider (sourceVariableToken)

abbrev Env := List (String × SExpr)

def encodeEnv (env : Env) : Bindings :=
  env.map fun (name, value) => (name, encode value)

mutual
  /-- Translate a source schema; names remain names, not numerical positions. -/
  def pattern : SExpr → Pattern
    | .atom token =>
        if sourceVariableToken token then .fvar token else encode (.atom token)
    | .list values => .apply "source-sexpr-list-v1" (patternList values)

  def patternList : List SExpr → List Pattern
    | [] => []
    | value :: values => pattern value :: patternList values
end

mutual
  /-- Single-pass structural instantiation; a substituted value is inert data. -/
  def instantiate? (env : Env) : SExpr → Option SExpr
    | .atom token =>
        if sourceVariableToken token then
          (env.find? (·.1 == token)).map (·.2)
        else some (.atom token)
    | .list values => SExpr.list <$> instantiateList? env values

  def instantiateList? (env : Env) : List SExpr → Option (List SExpr)
    | [] => some []
    | value :: values => do
        return (← instantiate? env value) :: (← instantiateList? env values)
end

theorem find_encodeEnv (env : Env) (name : String) :
    (encodeEnv env).find? (·.1 == name) =
      (env.find? (·.1 == name)).map (fun (key, value) => (key, encode value)) := by
  induction env with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      simp only [encodeEnv, List.map_cons, List.find?_cons]
      split <;> simp_all [encodeEnv]

theorem encodeEnv_valuesGround (env : Env) : (encodeEnv env).valuesGround = true := by
  induction env with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      simp only [encodeEnv, List.map_cons, Bindings.valuesGround, encode_isGround]
      exact ih

mutual
  /-- All source inputs, including missing bindings, agree after exact decoding. -/
  theorem decode_applyBindings_pattern (env : Env) (source : SExpr) :
      decode (applyBindings (encodeEnv env) (pattern source)) = instantiate? env source := by
    cases source with
    | atom token =>
        cases isVariable : sourceVariableToken token with
        | false =>
            simp [pattern, instantiate?, isVariable, encode, applyBindings, decode]
        | true =>
            simp only [pattern, instantiate?, isVariable, ↓reduceIte,
              applyBindings, find_encodeEnv]
            cases found : env.find? (·.1 == token) with
            | none => rfl
            | some entry =>
                rcases entry with ⟨key, value⟩
                exact decode_encode value
    | list sources =>
        rw [pattern, applyBindings]
        change (SExpr.list <$> decodeList
          ((patternList sources).map (applyBindings (encodeEnv env)))) = _
        rw [decodeList_applyBindings_patternList env sources]
        rfl
  termination_by sizeOf source

  theorem decodeList_applyBindings_patternList (env : Env) (sources : List SExpr) :
      decodeList ((patternList sources).map (applyBindings (encodeEnv env))) =
        instantiateList? env sources := by
    cases sources with
    | nil => rfl
    | cons source sources =>
        change (do return (← decode (applyBindings (encodeEnv env) (pattern source))) ::
          (← decodeList ((patternList sources).map (applyBindings (encodeEnv env))))) = _
        rw [decode_applyBindings_pattern env source,
          decodeList_applyBindings_patternList env sources]
        rfl
  termination_by sizeOf sources
end

/-- Successful source instantiation commutes with the existing substitution. -/
theorem instantiate_commutes {env : Env} {source value : SExpr}
    (instantiated : instantiate? env source = some value) :
    applyBindings (encodeEnv env) (pattern source) = encode value := by
  exact (encode_of_decode ((decode_applyBindings_pattern env source).trans instantiated)).symm

/-- Exact result reflection, with no assumed correctness of a source evaluator. -/
theorem applyBindings_eq_encode_iff (env : Env) (source value : SExpr) :
    applyBindings (encodeEnv env) (pattern source) = encode value ↔
      instantiate? env source = some value := by
  constructor
  · intro equal
    rw [← decode_applyBindings_pattern env source, equal, decode_encode]
  · exact instantiate_commutes

theorem missing_binding_has_no_encoded_result {env : Env} {source : SExpr}
    (missing : instantiate? env source = none) (value : SExpr) :
    applyBindings (encodeEnv env) (pattern source) ≠ encode value := by
  intro equal
  have found := (applyBindings_eq_encode_iff env source value).mp equal
  rw [missing] at found
  cases found

mutual
  /-- Payload data stays inert even under an arbitrary later binding map. -/
  theorem applyBindings_encode (bindings : Bindings) (value : SExpr) :
      applyBindings bindings (encode value) = encode value := by
    cases value with
    | atom value => simp only [encode, applyBindings, List.map_cons, List.map_nil]
    | list values =>
        rw [encode, applyBindings]
        rw [map_applyBindings_encodeList bindings values]
  termination_by sizeOf value

  theorem map_applyBindings_encodeList (bindings : Bindings) (values : List SExpr) :
      (encodeList values).map (applyBindings bindings) = encodeList values := by
    cases values with
    | nil => rfl
    | cons value values =>
        change applyBindings bindings (encode value) ::
          ((encodeList values).map (applyBindings bindings)) = _
        rw [applyBindings_encode bindings value, map_applyBindings_encodeList bindings values]
        rfl
  termination_by sizeOf values
end

theorem first_binding_retained (first later : SExpr) :
    instantiate? [("?x", first), ("?x", later)] (.atom "?x") = some first := by
  simp [instantiate?, sourceVariableToken]

/-- The separately checked API intentionally has a stricter environment policy. -/
theorem strict_application_rejects_duplicate_keys (first later : SExpr) :
    applyBindings? (encodeEnv [("?x", first), ("?x", later)])
      (pattern (.atom "?x")) = none := by
  simp [applyBindings?, Bindings.hasUniqueNames, encodeEnv, List.eraseDups_cons]

theorem repeated_variable_occurrences (value : SExpr) :
    instantiate? [("?x", value)] (.list [.atom "?x", .atom "?x"]) =
      some (.list [value, value]) := by
  simp [instantiate?, instantiateList?, sourceVariableToken]

theorem distinct_names_may_share_payload (value : SExpr) :
    instantiate? [("?x", value), ("?y", value)] (.list [.atom "?x", .atom "?y"]) =
      some (.list [value, value]) := by
  simp [instantiate?, instantiateList?, sourceVariableToken]

theorem variable_payload_not_reinterpreted :
    instantiate? [("?x", .atom "?y"), ("?y", .atom "42")] (.atom "?x") =
      some (.atom "?y") := by
  simp [instantiate?, sourceVariableToken]

theorem recursive_alias_interpretation_changes_result :
    instantiate? [("?x", .atom "?y"), ("?y", .atom "42")] (.atom "?x") ≠
      some (.atom "42") := by
  rw [variable_payload_not_reinterpreted]
  simp

theorem reserved_tokens_and_dollar_names_are_literals (env : Env) :
    instantiate? env (.list [.atom "?", .atom "?_", .atom "$x"]) =
      some (.list [.atom "?", .atom "?_", .atom "$x"]) := by
  simp [instantiate?, instantiateList?, sourceVariableToken]

theorem unbound_variable_refused : instantiate? [] (.atom "?x") = none := by
  simp [instantiate?, sourceVariableToken]

theorem singleton_list_not_atom (env : Env) :
    instantiate? env (.atom "a") ≠ instantiate? env (.list [.atom "a"]) := by
  simp [instantiate?, instantiateList?, sourceVariableToken]

#print axioms decode_applyBindings_pattern
#print axioms instantiate_commutes
#print axioms applyBindings_eq_encode_iff
#print axioms applyBindings_encode

end Mettapedia.GSLT.Parsing.SourceSExprPatternInstantiation
