import Mettapedia.GSLT.Parsing.SourceSExprPatternInstantiation
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.OSLF.Framework.PredFiniteSufficient
import Mettapedia.GSLT.LanguageDef.CertificateGSLTStepAdequacyGeneral

/-!
# Existing matching is exact for source S-expression schemas

Source schemas inhabit the existing match-correct fragment. The established
matcher reconstruction/completeness theorems therefore apply; the additional
source-specific fact is that every returned binding is encoded source data.
Decoding those actual bindings reconstructs a source instantiation.

There is no new matching algorithm or rule execution semantics here. Neither
unused ambient assignments nor a particular returned binding-list order are
required for completeness.
-/

namespace Mettapedia.GSLT.Parsing.SourceSExprPatternMatching

open Algorithms.MeTTa.Simple.Parser
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.Framework.PredFiniteSufficient
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open SourceSExprPatternCodec
open SourceSExprPatternInstantiation
open SourceIntegerProvider (sourceVariableToken)

mutual
  theorem pattern_isMatchCorrect (source : SExpr) :
      isMatchCorrectAux (pattern source) = true := by
    cases source with
    | atom token =>
        simp only [pattern]
        split <;> rfl
    | list sources => exact patternList_isMatchCorrect sources
  termination_by sizeOf source

  theorem patternList_isMatchCorrect (sources : List SExpr) :
      isMatchCorrectListAux (patternList sources) = true := by
    cases sources with
    | nil => rfl
    | cons source sources =>
        change (isMatchCorrectAux (pattern source) &&
          isMatchCorrectListAux (patternList sources)) = true
        rw [pattern_isMatchCorrect source, patternList_isMatchCorrect sources]
        rfl
  termination_by sizeOf sources
end

mutual
  theorem encode_canonical (value : SExpr) :
      (encode value).hasCanonicalBinderMetadata = true := by
    cases value with
    | atom token => rfl
    | list values => exact encodeList_canonical values
  termination_by sizeOf value

  theorem encodeList_canonical (values : List SExpr) :
      Pattern.hasCanonicalBinderMetadataList (encodeList values) = true := by
    cases values with
    | nil => rfl
    | cons value values =>
        change ((encode value).hasCanonicalBinderMetadata &&
          Pattern.hasCanonicalBinderMetadataList (encodeList values)) = true
        rw [encode_canonical value, encodeList_canonical values]
        rfl
  termination_by sizeOf values
end

/-- Existing matcher soundness specialized to all source schemas. -/
theorem match_reconstructs {source value : SExpr} {bindings : Bindings}
    (matched : bindings ∈ matchPattern (pattern source) (encode value)) :
    applyBindings bindings (pattern source) = encode value :=
  matchPattern_correct matched (pattern_isMatchCorrect source)

/-- Every binding value is in the exact source-data image. -/
def EncodedBindings (bindings : Bindings) : Prop :=
  ∀ pair ∈ bindings, ∃ value : SExpr, encode value = pair.2

theorem encodedBindings_nil : EncodedBindings [] := by
  intro pair member
  cases member

theorem encodedBindings_merge {left right merged : Bindings}
    (leftEncoded : EncodedBindings left) (rightEncoded : EncodedBindings right)
    (combined : mergeBindings left right = some merged) : EncodedBindings merged := by
  intro pair member
  rcases mergeBindings_mem_source combined pair member with fromLeft | fromRight
  · exact leftEncoded pair fromLeft
  · exact rightEncoded pair fromRight

mutual
  theorem match_bindings_encoded (source value : SExpr) (bindings : Bindings)
      (matched : bindings ∈ matchPattern (pattern source) (encode value)) :
      EncodedBindings bindings := by
    cases source with
    | atom token =>
        cases isVariable : sourceVariableToken token with
        | true =>
            simp only [pattern, isVariable, ↓reduceIte, matchPattern,
              List.mem_singleton] at matched
            subst bindings
            intro pair member
            simp only [List.mem_singleton] at member
            subst pair
            exact ⟨value, rfl⟩
        | false =>
            have same := matchPattern_closedSkeleton_eq
              (pattern := encode (.atom token))
              (by simp [patternClosedSkeleton, patternsClosedSkeleton, encode]) (by rfl)
              (encode_canonical value) bindings
              (by simpa only [pattern, isVariable, Bool.false_eq_true, ↓reduceIte] using matched)
            rw [same.2]
            exact encodedBindings_nil
    | list sources =>
        cases value with
        | atom token => simp [pattern, encode, matchPattern] at matched
        | list values =>
            simp only [pattern, encode, matchPattern] at matched
            split at matched
            · exact match_args_bindings_encoded sources values bindings matched
            · cases matched
  termination_by sizeOf source

  theorem match_args_bindings_encoded (sources values : List SExpr) (bindings : Bindings)
      (matched : bindings ∈ matchArgs (patternList sources) (encodeList values)) :
      EncodedBindings bindings := by
    cases sources with
    | nil =>
        cases values with
        | nil =>
            simp only [patternList, encodeList, matchArgs, List.mem_singleton] at matched
            subst bindings
            exact encodedBindings_nil
        | cons value values => simp [patternList, encodeList, matchArgs] at matched
    | cons source sources =>
        cases values with
        | nil => simp [patternList, encodeList, matchArgs] at matched
        | cons value values =>
            simp only [patternList, encodeList, matchArgs, List.mem_flatMap,
              List.mem_filterMap] at matched
            obtain ⟨head, headMatch, tail, tailMatch, combined⟩ := matched
            exact encodedBindings_merge
              (match_bindings_encoded source value head headMatch)
              (match_args_bindings_encoded sources values tail tailMatch) combined
  termination_by sizeOf sources
end

/-- Decode the actual returned binding list, preserving its keys and order. -/
def decodeEnv : Bindings → Option Env
  | [] => some []
  | (name, value) :: rest => do
      return (name, ← decode value) :: (← decodeEnv rest)

theorem decodeEnv_of_encoded {bindings : Bindings} (encoded : EncodedBindings bindings) :
    ∃ env, decodeEnv bindings = some env ∧ encodeEnv env = bindings := by
  induction bindings with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons pair rest ih =>
      rcases pair with ⟨name, value⟩
      obtain ⟨source, sourceEq⟩ := encoded (name, value) (by simp)
      change encode source = value at sourceEq
      obtain ⟨env, decoded, encodedEq⟩ := ih
        (fun pair member => encoded pair (List.mem_cons_of_mem _ member))
      refine ⟨(name, source) :: env, ?_, ?_⟩
      · simp only [decodeEnv, ← sourceEq, decode_encode, decoded, bind, Option.bind, pure]
      · simp only [encodeEnv, List.map_cons, sourceEq]
        exact congrArg (List.cons (name, value)) encodedEq

/-- Every actual match reconstructs a source environment and exact source result. -/
theorem match_source_sound {source value : SExpr} {bindings : Bindings}
    (matched : bindings ∈ matchPattern (pattern source) (encode value)) :
    ∃ env, decodeEnv bindings = some env ∧ encodeEnv env = bindings ∧
      instantiate? env source = some value := by
  obtain ⟨env, decoded, encoded⟩ := decodeEnv_of_encoded
    (match_bindings_encoded source value bindings matched)
  refine ⟨env, decoded, encoded, ?_⟩
  apply (applyBindings_eq_encode_iff env source value).mp
  rw [encoded]
  exact match_reconstructs matched

/-- Consistent instances match, with returned assignments agreeing with the
supplied environment. Completeness permits unused ambient bindings to disappear. -/
theorem match_source_complete {env : Env} {source value : SExpr}
    (instantiated : instantiate? env source = some value) :
    ∃ bindings ∈ matchPattern (pattern source) (encode value),
      BindingsValued bindings (lookupOrFvar (encodeEnv env)) := by
  obtain ⟨bindings, matched, agrees⟩ := matchPattern_applyBindings_complete
    (bs := encodeEnv env) (pattern_isMatchCorrect source)
  rw [instantiate_commutes instantiated] at matched
  exact ⟨bindings, matched, agrees⟩

theorem match_exists_iff_source_instance (source value : SExpr) :
    (∃ bindings, bindings ∈ matchPattern (pattern source) (encode value)) ↔
      ∃ env, instantiate? env source = some value := by
  constructor
  · rintro ⟨bindings, matched⟩
    obtain ⟨env, _, _, instantiated⟩ := match_source_sound matched
    exact ⟨env, instantiated⟩
  · rintro ⟨env, instantiated⟩
    obtain ⟨bindings, matched, _⟩ := match_source_complete instantiated
    exact ⟨bindings, matched⟩

theorem matched_bindings_are_ground {source value : SExpr} {bindings : Bindings}
    (matched : bindings ∈ matchPattern (pattern source) (encode value)) :
    bindings.valuesGround = true := by
  obtain ⟨env, _, encoded, _⟩ := match_source_sound matched
  rw [← encoded]
  exact encodeEnv_valuesGround env

theorem repeated_variable_matches (value : SExpr) :
    ∃ bindings, bindings ∈ matchPattern
      (pattern (.list [.atom "?x", .atom "?x"])) (encode (.list [value, value])) := by
  apply (match_exists_iff_source_instance _ _).mpr
  exact ⟨[("?x", value)], repeated_variable_occurrences value⟩

theorem repeated_variable_rejects_distinct (left right : SExpr) (distinct : left ≠ right) :
    ¬ ∃ bindings, bindings ∈ matchPattern
      (pattern (.list [.atom "?x", .atom "?x"])) (encode (.list [left, right])) := by
  rintro ⟨bindings, matched⟩
  have reconstructed := match_reconstructs matched
  simp only [pattern, patternList, encode, encodeList, sourceVariableToken,
    applyBindings, List.map_cons, List.map_nil] at reconstructed
  have children := (Pattern.apply.inj reconstructed).2
  have first := (List.cons.inj children).1
  have second := (List.cons.inj (List.cons.inj children).2).1
  exact distinct (encode_injective (first.symm.trans second))

theorem literal_atom_does_not_match_list (name : String) (values : List SExpr)
    (literal : sourceVariableToken name = false) :
    matchPattern (pattern (.atom name)) (encode (.list values)) = [] := by
  simp [pattern, literal, encode, matchPattern]

theorem variable_payload_matches_as_data :
    ∃ bindings, bindings ∈ matchPattern (pattern (.atom "?x")) (encode (.atom "?y")) := by
  apply (match_exists_iff_source_instance _ _).mpr
  exact ⟨[("?x", .atom "?y"), ("?y", .atom "42")], variable_payload_not_reinterpreted⟩

#print axioms match_reconstructs
#print axioms match_source_sound
#print axioms match_source_complete
#print axioms match_exists_iff_source_instance
#print axioms repeated_variable_rejects_distinct

end Mettapedia.GSLT.Parsing.SourceSExprPatternMatching
