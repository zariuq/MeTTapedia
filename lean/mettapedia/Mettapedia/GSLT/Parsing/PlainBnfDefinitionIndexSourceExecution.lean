import Mettapedia.GSLT.Parsing.PlainBnfEnumerationSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfHeapSourceExecution

/-!
# Authored definition-index construction and lookup

Discovery occurrences 38–39 and 49–51 are executed with the original sparse
trie rules. The independent observation is an ordered list fold retaining
the first complete body/span payload for each name. Existing index payloads
remain opaque. These are source/contextual laws, not generated-runtime or
whole-admission correspondence.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfDefinitionIndexSourceExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT (Rewrite decodeList)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open SourceSExprPatternCodec (encode encodeList)
open SourceSExprPatternInstantiation (pattern patternList
  applyRuleBindings_of_binderFree binderFree_pattern)
open PlainBnfGraphNameTrie (Trie lookup insertFirst)
open PlainBnfSourceRank (Rank)
open PlainBnfCollectorSourceExecution (NameScalarCodec name)
open PlainBnfTrieSourceExecution
  (scalarRelations trie value call result observedRule trie_injective result_injective
    lookupCall lookupHeight insertCall insertHeight)
open PlainBnfIndexedCollectorSourceExecution
  (headedBy premiseClosed closed_extension disjoint_heads_do_not_match trieNames trie_closed)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

def mode? (relation : String) : Option (Nat × Nat) :=
  match relation with
  | "BNFDiscoveryDefinitionIndexV1" => some (2, 1)
  | "BNFDefinitionLookupV1" => some (2, 1)
  | "BNFDiscoveryDefinitionResultV1" => some (1, 1)
  | _ => PlainBnfCollectorSourceExecution.mode? relation

def splitCall? : SExpr → Option (SExpr × SExpr)
  | .list (.atom relation :: arguments) => do
      let (inputs, outputs) ← mode? relation
      if arguments.length = inputs + outputs then
        some (.list (.atom relation :: arguments.take inputs), .list (arguments.drop inputs))
      else none
  | _ => none

def lowerPremise? : SExpr → Option Premise
  | .list [.atom "different", left, right] =>
      some (.relationQuery "different" [pattern left, pattern right])
  | source => do
      let (input, output) ← splitCall? source
      some (.congruence (pattern input) (pattern output))

def lowerRule? (source : Rewrite) : Option RewriteRule := do
  let (input, output) ← splitCall? source.head
  let premises ← decodeList lowerPremise? source.body
  some {
    name := source.name
    typeContext := []
    premises := premises
    left := pattern input
    right := pattern output }

def indexRows : List Rewrite :=
  (PlainBnfCollectorSourceAdmission.discoverySource.rewrites.drop 38).take 2 ++
    (PlainBnfCollectorSourceAdmission.discoverySource.rewrites.drop 49).take 3

def rows : List Rewrite :=
  PlainBnfCollectorSourceAdmission.indexSource.rewrites.take 14 ++ indexRows

def rules? : Option (List RewriteRule) := rows.mapM lowerRule?

theorem rules_present : rules?.isSome = true := rfl

def language : LanguageDef :=
  { name := "PlainBnfAuthoredDefinitionIndex", types := [], terms := [], equations := [],
    rewrites := rules?.get rules_present }

def indexRules : List RewriteRule := (indexRows.mapM lowerRule?).get (by rfl)

theorem source_translation_exact : rows.mapM lowerRule? = some language.rewrites := rfl

theorem index_occurrences_exact :
    ((indexRows.take 2).zipIdx 38 ++ (indexRows.drop 2).zipIdx 49) =
      ((PlainBnfCollectorSourceAdmission.discoverySource.rewrites.zipIdx).drop 38).take 2 ++
      ((PlainBnfCollectorSourceAdmission.discoverySource.rewrites.zipIdx).drop 49).take 3 := rfl

theorem language_partition : language.rewrites =
    PlainBnfTrieSourceExecution.language.rewrites ++ indexRules := rfl

theorem exactly_nineteen_rules : language.rewrites.length = 19 := rfl

/-- Checked observations of translated rows, not replacement executable rules. -/
private def observedRules : List RewriteRule := [
  observedRule "bnf-discovery-definition-index-nil-v1"
    (metta_sexpr% petta "(BNFDiscoveryDefinitionIndexV1 BNFDiscoveryDefinitionsNilV1 ?index)")
    (metta_sexpr% petta "(?index)"),
  observedRule "bnf-discovery-definition-index-cons-v1"
    (metta_sexpr% petta "(BNFDiscoveryDefinitionIndexV1 (BNFDiscoveryDefinitionsConsV1 (BNFDiscoveryDefinitionV1 ?rank ?name ?expression ?span) ?tail) ?index)")
    (metta_sexpr% petta "(?result)")
    [.congruence
        (pattern (metta_sexpr% petta "(BNFGraphTrieInsertFirstV1 ?name (BNFDefinitionFoundV1 ?expression ?span) ?index)"))
        (pattern (metta_sexpr% petta "(?next)")),
     .congruence (pattern (metta_sexpr% petta "(BNFDiscoveryDefinitionIndexV1 ?tail ?next)"))
        (pattern (metta_sexpr% petta "(?result)"))],
  observedRule "bnf-discovery-definition-lookup-v1"
    (metta_sexpr% petta "(BNFDefinitionLookupV1 ?name (BNFIndexedDefinitionsV1 ?index))")
    (metta_sexpr% petta "(?result)")
    [.congruence (pattern (metta_sexpr% petta "(BNFGraphTrieLookupV1 ?name ?index)"))
        (pattern (metta_sexpr% petta "(?lookup)")),
     .congruence (pattern (metta_sexpr% petta "(BNFDiscoveryDefinitionResultV1 ?lookup)"))
        (pattern (metta_sexpr% petta "(?result)"))],
  observedRule "bnf-discovery-definition-missing-v1"
    (metta_sexpr% petta "(BNFDiscoveryDefinitionResultV1 BNFIndexMissingV1)")
    (metta_sexpr% petta "(BNFDefinitionMissingV1)"),
  observedRule "bnf-discovery-definition-found-v1"
    (metta_sexpr% petta "(BNFDiscoveryDefinitionResultV1 (BNFIndexFoundV1 ?definition))")
    (metta_sexpr% petta "(?definition)")]

private theorem index_rules_exact : indexRules = observedRules := rfl

def indexNames :=
  ["BNFDiscoveryDefinitionIndexV1", "BNFDefinitionLookupV1", "BNFDiscoveryDefinitionResultV1"]

theorem trie_heads : PlainBnfTrieSourceExecution.language.rewrites.all
    (fun rule => headedBy trieNames rule.left) = true := by
  simp [PlainBnfTrieSourceExecution.source_rules_exact, PlainBnfTrieSourceExecution.observedRules,
    observedRule, headedBy, trieNames, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode]

theorem index_heads : indexRules.all (fun rule => headedBy indexNames rule.left) = true := by
  simp [index_rules_exact, observedRules, observedRule, headedBy, indexNames,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode]

def relationHeads := trieNames ++ indexNames

theorem family_heads : language.rewrites.all
    (fun rule => headedBy relationHeads rule.left) = true := by
  simp [language_partition, PlainBnfTrieSourceExecution.source_rules_exact,
    PlainBnfTrieSourceExecution.observedRules, index_rules_exact, observedRules,
    observedRule, headedBy, relationHeads, trieNames, indexNames,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode]

theorem family_closed : language.rewrites.all
    (fun rule => rule.premises.all (premiseClosed relationHeads)) = true := by
  simp [language_partition, PlainBnfTrieSourceExecution.source_rules_exact,
    PlainBnfTrieSourceExecution.observedRules, index_rules_exact, observedRules,
    observedRule, premiseClosed, headedBy, relationHeads, trieNames, indexNames,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode]

theorem names_disjoint : List.Disjoint indexNames trieNames := by simp [indexNames, trieNames]

theorem trie_conservative_extension (env : RelationEnv) (fuel : Nat) (source : Pattern)
    (headed : headedBy trieNames source = true) :
    rewriteAt (engineBasePremises env) language fuel source =
      rewriteAt (engineBasePremises env) PlainBnfTrieSourceExecution.language fuel source := by
  apply closed_extension trieNames env PlainBnfTrieSourceExecution.language language [] indexRules
    (by simpa using language_partition) ?_ ?_ fuel source headed
  · intro rule member premise inside
    exact List.all_eq_true.mp (List.all_eq_true.mp trie_closed rule member) premise inside
  · intro rule member term termHead
    exact disjoint_heads_do_not_match indexNames trieNames names_disjoint _ _
      (List.all_eq_true.mp index_heads rule (by simpa using member)) termHead

private theorem index_rewriteAt (env : RelationEnv) (fuel : Nat) (source : Pattern)
    (headed : headedBy indexNames source = true) :
    rewriteAt (engineBasePremises env) language (fuel + 1) source =
      indexRules.flatMap (fun rule => applyRuleUsing (engineBasePremises env) language
        (rewriteAt (engineBasePremises env) language fuel) rule source) := by
  apply PlainBnfHeapSourceExecution.skip_unmatched_prefix _ language
    PlainBnfTrieSourceExecution.language.rewrites indexRules language_partition fuel source
  intro rule member
  exact disjoint_heads_do_not_match trieNames indexNames names_disjoint.symm _ _
    (List.all_eq_true.mp trie_heads rule member) headed

abbrev Definition (Scalar : Type) :=
  PlainBnfDeclarationSemantics.Definition (List Scalar) SExpr SExpr

variable {Scalar : Type} [NameScalarCodec Scalar]

/-- Reuse the enumeration wire; only the existing name codec is applied. -/
def wireDefinition (item : Definition Scalar) : PlainBnfEnumerationSourceExecution.Definition :=
  ⟨name item.name, item.expression, item.span⟩

def rankedDefinitions (input : List (Rank × Definition Scalar)) : SExpr :=
  PlainBnfEnumerationSourceExecution.rankedDefinitions
    (input.map fun item => (item.1, wireDefinition item.2))

def payload (item : Definition Scalar) : SExpr :=
  .list [.atom "BNFDefinitionFoundV1", item.expression, item.span]

def indexCall (input : List (Rank × Definition Scalar)) (index : Trie SExpr Scalar) : Pattern :=
  call "BNFDiscoveryDefinitionIndexV1" [rankedDefinitions input, trie index]

def definitionResult (found : Option SExpr) : SExpr := found.getD (.atom "BNFDefinitionMissingV1")

def resultCall (found : Option SExpr) : Pattern :=
  call "BNFDiscoveryDefinitionResultV1" [value found]

def definitionLookupCall (key : List Scalar) (index : Trie SExpr Scalar) : Pattern :=
  call "BNFDefinitionLookupV1" [name key, .list [.atom "BNFIndexedDefinitionsV1", trie index]]

theorem result_answers (env : RelationEnv) (fuel : Nat) (found : Option SExpr) :
    rewriteAt (engineBasePremises env) language fuel (resultCall found) =
      if 0 < fuel then [result (definitionResult found)] else [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [index_rewriteAt env fuel _ (by rfl)]
    cases found <;>
      simp [index_rules_exact, observedRules, observedRule, applyRuleUsing,
        applyRuleBindings_of_binderFree, binderFree, binderFreeList,
        resultCall, definitionResult, call, result, value,
        pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
        matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private theorem index_nil (env : RelationEnv) (fuel : Nat) (index : Trie SExpr Scalar) :
    rewriteAt (engineBasePremises env) language (fuel + 1) (indexCall [] index) =
      [result (trie index)] := by
  rw [index_rewriteAt env fuel _ (by rfl)]
  simp [index_rules_exact, observedRules, observedRule, applyRuleUsing,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    indexCall, rankedDefinitions, PlainBnfEnumerationSourceExecution.rankedDefinitions,
    call, result, pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private theorem index_first_none (env : RelationEnv) (fuel : Nat)
    (item : Rank × Definition Scalar) (tail : List (Rank × Definition Scalar))
    (index : Trie SExpr Scalar)
    (first : rewriteAt (engineBasePremises env) language fuel
      (insertCall item.2.name (payload item.2) index) = []) :
    rewriteAt (engineBasePremises env) language (fuel + 1) (indexCall (item :: tail) index) = [] := by
  rw [index_rewriteAt env fuel _ (by rfl)]
  simp [index_rules_exact, observedRules, observedRule, applyRuleUsing,
    indexCall, rankedDefinitions, PlainBnfEnumerationSourceExecution.rankedDefinitions,
    PlainBnfEnumerationSourceExecution.rankedDefinition, wireDefinition,
    call, pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing, applyBindings]
  simp only [insertCall, payload, call, encode, encodeList] at first
  rw [first]
  simp

private theorem index_following (env : RelationEnv) (fuel : Nat)
    (item : Rank × Definition Scalar) (tail : List (Rank × Definition Scalar))
    (index next : Trie SExpr Scalar) (answers : List SExpr)
    (first : rewriteAt (engineBasePremises env) language fuel
      (insertCall item.2.name (payload item.2) index) = [result (trie next)])
    (following : rewriteAt (engineBasePremises env) language fuel
      (indexCall tail next) = answers.map result) :
    rewriteAt (engineBasePremises env) language (fuel + 1)
      (indexCall (item :: tail) index) = answers.map result := by
  rw [index_rewriteAt env fuel _ (by rfl)]
  simp [index_rules_exact, observedRules, observedRule, applyRuleUsing,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    indexCall, rankedDefinitions, PlainBnfEnumerationSourceExecution.rankedDefinitions,
    PlainBnfEnumerationSourceExecution.rankedDefinition, wireDefinition,
    call, pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing, applyBindings]
  simp only [insertCall, payload, call, result, encode, encodeList] at first
  rw [first]
  simp [matchPattern, matchArgs, mergeBindings, List.foldlM]
  simp only [indexCall, rankedDefinitions, wireDefinition, call, encode, encodeList] at following
  rw [following]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap, result, encode, encodeList]

private theorem lookup_first_none (env : RelationEnv) (fuel : Nat)
    (key : List Scalar) (index : Trie SExpr Scalar)
    (first : rewriteAt (engineBasePremises env) language fuel (lookupCall key index) = []) :
    rewriteAt (engineBasePremises env) language (fuel + 1) (definitionLookupCall key index) = [] := by
  rw [index_rewriteAt env fuel _ (by rfl)]
  simp [index_rules_exact, observedRules, observedRule, applyRuleUsing,
    definitionLookupCall, call, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings]
  simp only [lookupCall, call, encode, encodeList] at first
  rw [first]
  simp

private theorem lookup_following (env : RelationEnv) (fuel : Nat)
    (key : List Scalar) (index : Trie SExpr Scalar) (found : Option SExpr) (answers : List SExpr)
    (first : rewriteAt (engineBasePremises env) language fuel (lookupCall key index) =
      [result (value found)])
    (following : rewriteAt (engineBasePremises env) language fuel (resultCall found) = answers.map result) :
    rewriteAt (engineBasePremises env) language (fuel + 1)
      (definitionLookupCall key index) = answers.map result := by
  rw [index_rewriteAt env fuel _ (by rfl)]
  simp [index_rules_exact, observedRules, observedRule, applyRuleUsing,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    definitionLookupCall, call, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings]
  simp only [lookupCall, call, result, encode, encodeList] at first
  rw [first]
  simp [matchPattern, matchArgs, mergeBindings, List.foldlM]
  simp only [resultCall, call, encode, encodeList] at following
  rw [following]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap, result, encode, encodeList]

variable [DecidableEq Scalar]

/-- Independent ordered construction using the ordinary list fold. -/
def buildIndex (input : List (Rank × Definition Scalar)) (index : Trie SExpr Scalar) : Trie SExpr Scalar :=
  input.foldl (fun current item => insertFirst item.2.name (payload item.2) current) index

omit [NameScalarCodec Scalar] in
theorem buildIndex_cons (item : Rank × Definition Scalar) (tail : List (Rank × Definition Scalar))
    (index : Trie SExpr Scalar) :
    buildIndex (item :: tail) index = buildIndex tail (insertFirst item.2.name (payload item.2) index) := rfl

/-- Required contextual-premise depth, not a provider of definition-index answers. -/
def indexHeight : List (Rank × Definition Scalar) → Trie SExpr Scalar → Nat
  | [], _ => 0
  | item :: tail, index =>
      max (insertHeight item.2.name index)
        (indexHeight tail (insertFirst item.2.name (payload item.2) index)) + 1

theorem insert_answers (fuel : Nat) (key : List Scalar) (stored : SExpr) (index : Trie SExpr Scalar) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (insertCall key stored index) =
      if insertHeight key index < fuel then [result (trie (insertFirst key stored index))] else [] := by
  rw [trie_conservative_extension _ fuel _ (by rfl)]
  exact (PlainBnfTrieSourceExecution.insert_answers fuel).1 key stored index

theorem lookup_answers (fuel : Nat) (key : List Scalar) (index : Trie SExpr Scalar) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (lookupCall key index) =
      if lookupHeight key index < fuel then [result (value (lookup key index))] else [] := by
  rw [trie_conservative_extension _ fuel _ (by rfl)]
  exact (PlainBnfTrieSourceExecution.lookup_answers fuel).1 key index

/-- Exact answer occurrences, including failure to return at insufficient depth. -/
theorem index_answers (fuel : Nat) (input : List (Rank × Definition Scalar)) (index : Trie SExpr Scalar) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (indexCall input index) =
      if indexHeight input index < fuel then [result (trie (buildIndex input index))] else [] := by
  induction fuel generalizing input index with
  | zero => simp [rewriteAt]
  | succ fuel ih =>
    cases input with
    | nil => simpa [indexHeight, buildIndex] using index_nil scalarRelations fuel index
    | cons item tail =>
      have first := insert_answers fuel item.2.name (payload item.2) index
      have following := ih tail (insertFirst item.2.name (payload item.2) index)
      by_cases hfirst : insertHeight item.2.name index < fuel
      · simp only [hfirst, ↓reduceIte] at first
        by_cases hfollowing : indexHeight tail (insertFirst item.2.name (payload item.2) index) < fuel
        · simp only [hfollowing, ↓reduceIte] at following
          have step := index_following scalarRelations fuel item tail index
            (insertFirst item.2.name (payload item.2) index)
            [trie (buildIndex tail (insertFirst item.2.name (payload item.2) index))]
            first (by simpa using following)
          simpa [indexHeight, Nat.add_lt_add_iff_right, max_lt_iff, hfirst, hfollowing,
            buildIndex_cons] using step
        · simp only [hfollowing, ↓reduceIte] at following
          have step := index_following scalarRelations fuel item tail index
            (insertFirst item.2.name (payload item.2) index) [] first (by simpa using following)
          simpa [indexHeight, Nat.add_lt_add_iff_right, max_lt_iff, hfirst, hfollowing] using step
      · simp only [hfirst, ↓reduceIte] at first
        have absent := index_first_none scalarRelations fuel item tail index first
        simpa [indexHeight, Nat.add_lt_add_iff_right, max_lt_iff, hfirst] using absent

theorem definition_lookup_answers (fuel : Nat) (key : List Scalar) (index : Trie SExpr Scalar) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (definitionLookupCall key index) =
      if lookupHeight key index + 1 < fuel then [result (definitionResult (lookup key index))] else [] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
    have first := lookup_answers fuel key index
    by_cases enough : lookupHeight key index < fuel
    · simp only [enough, ↓reduceIte] at first
      have positive : 0 < fuel := by omega
      have following := result_answers scalarRelations fuel (lookup key index)
      simp only [positive, ↓reduceIte] at following
      have step := lookup_following scalarRelations fuel key index (lookup key index)
        [definitionResult (lookup key index)] first (by simpa using following)
      simpa [Nat.add_lt_add_iff_right, enough] using step
    · simp only [enough, ↓reduceIte] at first
      simpa [Nat.add_lt_add_iff_right, enough] using
        lookup_first_none scalarRelations fuel key index first

theorem index_step_iff (input : List (Rank × Definition Scalar)) (index : Trie SExpr Scalar)
    (target : Pattern) :
    Step (engineBasePremises scalarRelations) language (indexCall input index) target ↔
      target = result (trie (buildIndex input index)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [index_answers] at member
    split at member
    · simpa using member
    · cases member
  · intro same
    subst target
    exact ⟨indexHeight input index + 1, by simp [index_answers]⟩

theorem index_decoded_step_iff (input : List (Rank × Definition Scalar)) (before after : Trie SExpr Scalar) :
    Step (engineBasePremises scalarRelations) language (indexCall input before) (result (trie after)) ↔
      after = buildIndex input before := by
  rw [index_step_iff]
  exact ⟨fun same => trie_injective (result_injective same), fun same => by rw [same]⟩

theorem definition_lookup_step_iff (key : List Scalar) (index : Trie SExpr Scalar) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language (definitionLookupCall key index) target ↔
      target = result (definitionResult (lookup key index)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [definition_lookup_answers] at member
    split at member
    · simpa using member
    · cases member
  · intro same
    subst target
    exact ⟨lookupHeight key index + 2, by simp [definition_lookup_answers]⟩

omit [NameScalarCodec Scalar] in
/-- Existing bindings win; otherwise the first authored occurrence supplies the
whole expression/span payload. Equality of names never chooses a later row. -/
theorem lookup_buildIndex (input : List (Rank × Definition Scalar)) (query : List Scalar)
    (index : Trie SExpr Scalar) :
    lookup query (buildIndex input index) =
      (lookup query index).or ((input.find? (fun item => query == item.2.name)).map
        (fun item => payload item.2)) := by
  induction input generalizing index with
  | nil => simp [buildIndex]
  | cons item tail ih =>
    rw [buildIndex_cons, ih, PlainBnfGraphNameTrie.lookup_insertFirst]
    by_cases same : query = item.2.name
    · subst query
      cases lookup item.2.name index <;> simp
    · simp [same]

/-- Wire observation of the existing ordered declaration semantics. -/
def declarationResult : PlainBnfDeclarationSemantics.LookupResult SExpr SExpr → SExpr
  | .missing => .atom "BNFDefinitionMissingV1"
  | .found expression span => .list [.atom "BNFDefinitionFoundV1", expression, span]

omit [NameScalarCodec Scalar] in
theorem first_occurrence_matches_declaration_lookup (input : List (Rank × Definition Scalar))
    (query : List Scalar) :
    definitionResult ((input.find? (fun item => query == item.2.name)).map (fun item => payload item.2)) =
      declarationResult (PlainBnfDeclarationSemantics.lookup query (input.map Prod.snd)) := by
  induction input with
  | nil => rfl
  | cons item tail ih =>
    by_cases same : query = item.2.name
    · simp [same, definitionResult, payload, PlainBnfDeclarationSemantics.lookup,
        declarationResult]
    · simpa [List.find?_cons, same, PlainBnfDeclarationSemantics.lookup] using ih

/-- For a constructed empty-origin index, actual indexed lookup has exactly the
meaning of the independent ordered declaration lookup, for every target. -/
theorem constructed_lookup_step_iff (input : List (Rank × Definition Scalar)) (query : List Scalar)
    (target : Pattern) :
    Step (engineBasePremises scalarRelations) language
      (definitionLookupCall query (buildIndex input .empty)) target ↔
      target = result (declarationResult
        (PlainBnfDeclarationSemantics.lookup query (input.map Prod.snd))) := by
  rw [definition_lookup_step_iff, lookup_buildIndex]
  simp only [PlainBnfGraphNameTrie.lookup_empty, Option.none_or]
  rw [first_occurrence_matches_declaration_lookup]

/-- Composition consumes actual construction evidence rather than assuming a
finished index has the right lookup behavior. -/
theorem constructed_then_lookup_iff (input : List (Rank × Definition Scalar)) (query : List Scalar)
    (after : Trie SExpr Scalar) (target : Pattern)
    (constructed : Step (engineBasePremises scalarRelations) language
      (indexCall input .empty) (result (trie after))) :
    Step (engineBasePremises scalarRelations) language (definitionLookupCall query after) target ↔
      target = result (declarationResult
        (PlainBnfDeclarationSemantics.lookup query (input.map Prod.snd))) := by
  rw [index_decoded_step_iff] at constructed
  rw [constructed, constructed_lookup_step_iff]

omit [NameScalarCodec Scalar] in
theorem existing_payload_survives (input : List (Rank × Definition Scalar)) (query : List Scalar)
    (old : SExpr) (index : Trie SExpr Scalar) (found : lookup query index = some old) :
    lookup query (buildIndex input index) = some old := by
  simp [lookup_buildIndex, found]

omit [NameScalarCodec Scalar] in
theorem absent_name_stays_missing (input : List (Rank × Definition Scalar)) (query : List Scalar)
    (index : Trie SExpr Scalar) (missing : lookup query index = none)
    (absent : ∀ item ∈ input, query ≠ item.2.name) :
    lookup query (buildIndex input index) = none := by
  rw [lookup_buildIndex, missing]
  have notFound : input.find? (fun item => query == item.2.name) = none := by
    apply List.find?_eq_none.mpr
    intro item member
    simpa using absent item member
  simp [notFound]

omit [NameScalarCodec Scalar] in
theorem first_definition_retains_body_and_span (priority : Rank) (item : Definition Scalar)
    (tail : List (Rank × Definition Scalar)) (index : Trie SExpr Scalar)
    (missing : lookup item.name index = none) :
    lookup item.name (buildIndex ((priority, item) :: tail) index) = some (payload item) := by
  simp [lookup_buildIndex, missing]

theorem duplicate_definitions_return_first (firstRank secondRank : Rank) (key : List Scalar)
    (firstBody secondBody firstSpan secondSpan : SExpr) :
    Step (engineBasePremises scalarRelations) language
      (definitionLookupCall key (buildIndex
        [(firstRank, ⟨key, firstBody, firstSpan⟩), (secondRank, ⟨key, secondBody, secondSpan⟩)] .empty))
      (result (.list [.atom "BNFDefinitionFoundV1", firstBody, firstSpan])) := by
  rw [constructed_lookup_step_iff]
  simp [declarationResult]

theorem duplicate_cannot_replace_body_or_span (firstRank secondRank : Rank) (key : List Scalar)
    (firstBody secondBody firstSpan secondSpan : SExpr)
    (different : firstBody ≠ secondBody ∨ firstSpan ≠ secondSpan) :
    ¬ Step (engineBasePremises scalarRelations) language
      (definitionLookupCall key (buildIndex
        [(firstRank, ⟨key, firstBody, firstSpan⟩), (secondRank, ⟨key, secondBody, secondSpan⟩)] .empty))
      (result (.list [.atom "BNFDefinitionFoundV1", secondBody, secondSpan])) := by
  rw [constructed_lookup_step_iff]
  simp only [List.map_cons, List.map_nil, PlainBnfDeclarationSemantics.lookup,
    ↓reduceIte, declarationResult]
  intro same
  have components := result_injective same
  simp only [SExpr.list.injEq, List.cons.injEq, and_true, true_and] at components
  rcases different with bodies | spans
  · exact bodies components.1.symm
  · exact spans components.2.symm

theorem arbitrary_stored_payload_is_not_repaired (key : List Scalar) (old : SExpr)
    (index : Trie SExpr Scalar) (found : lookup key index = some old) :
    Step (engineBasePremises scalarRelations) language (definitionLookupCall key index) (result old) := by
  rw [definition_lookup_step_iff]
  simp [found, definitionResult]

/-- A result tag alone cannot prove absence in an arbitrary caller-supplied
index: the source deliberately returns an existing opaque payload unchanged. -/
theorem missing_answer_does_not_imply_absence (key : List Scalar) :
    let index := insertFirst key (.atom "BNFDefinitionMissingV1") (.empty : Trie SExpr Scalar)
    lookup key index ≠ none ∧
      Step (engineBasePremises scalarRelations) language (definitionLookupCall key index)
        (result (.atom "BNFDefinitionMissingV1")) := by
  dsimp
  have found : lookup key (insertFirst key (.atom "BNFDefinitionMissingV1") (.empty : Trie SExpr Scalar)) =
      some (.atom "BNFDefinitionMissingV1") := by simp [PlainBnfGraphNameTrie.lookup_inserted]
  constructor
  · simp [found]
  · exact arbitrary_stored_payload_is_not_repaired key _ _ found

theorem insufficient_depth_has_no_answer (input : List (Rank × Definition Scalar))
    (index : Trie SExpr Scalar) (fuel : Nat) (insufficient : fuel ≤ indexHeight input index) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (indexCall input index) = [] := by
  simp [index_answers, Nat.not_lt.mpr insufficient]

theorem signed_names_are_distinct (body span : SExpr) :
    lookup [-7] (buildIndex [(.zero, ⟨[-7], body, span⟩)] (.empty : Trie SExpr Int)) =
      some (.list [.atom "BNFDefinitionFoundV1", body, span]) ∧
    lookup [7] (buildIndex [(.zero, ⟨[-7], body, span⟩)] (.empty : Trie SExpr Int)) = none := by
  simp [lookup_buildIndex, payload]

#print axioms index_answers
#print axioms index_decoded_step_iff
#print axioms definition_lookup_step_iff
#print axioms lookup_buildIndex
#print axioms constructed_then_lookup_iff
#print axioms duplicate_cannot_replace_body_or_span

end Mettapedia.GSLT.Parsing.PlainBnfDefinitionIndexSourceExecution
