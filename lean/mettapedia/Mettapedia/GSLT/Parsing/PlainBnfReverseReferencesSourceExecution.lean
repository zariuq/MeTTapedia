import Mettapedia.GSLT.Parsing.PlainBnfTrieOverwriteSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfIndexedCollectorSourceExecution

/-!
# Authored reverse-reference bucket updates

Discovery occurrences 54–57 execute lookup, bucket selection, overwrite, and
ordered reference traversal in the existing contextual semantics. The
independent observation is an ordinary list fold over the existing sparse
trie. Complete node payloads and pre-existing bucket tails remain opaque data.
This is not whole-worklist or generated-runtime correspondence.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfReverseReferencesSourceExecution

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
open PlainBnfGraphNameTrie (Trie)
open PlainBnfCollectorSourceExecution (NameScalarCodec name)
open PlainBnfTrieSourceExecution
  (scalarRelations trie value call result observedRule trie_injective result_injective
    lookupCall lookupHeight)
open PlainBnfTrieOverwriteSourceExecution (putCall putHeight)
open PlainBnfIndexedCollectorSourceExecution
  (headedBy premiseClosed closed_extension disjoint_heads_do_not_match trieNames trie_closed)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

def mode? (relation : String) : Option (Nat × Nat) :=
  match relation with
  | "BNFDiscoveryDependentsV1" => some (1, 1)
  | "BNFDiscoveryAddReferencesV1" => some (3, 1)
  | _ => (PlainBnfTrieOverwriteSourceExecution.mode? relation).or
      (PlainBnfCollectorSourceExecution.mode? relation)

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

def referenceRows : List Rewrite :=
  (PlainBnfCollectorSourceAdmission.discoverySource.rewrites.drop 54).take 4

def rows : List Rewrite :=
  PlainBnfCollectorSourceAdmission.indexSource.rewrites.take 14 ++
    PlainBnfTrieOverwriteSourceExecution.rows ++ referenceRows

def rules? : Option (List RewriteRule) := rows.mapM lowerRule?

theorem rules_present : rules?.isSome = true := rfl

def language : LanguageDef :=
  { name := "PlainBnfAuthoredReverseReferences", types := [], terms := [], equations := [],
    rewrites := rules?.get rules_present }

def referenceRules : List RewriteRule := (referenceRows.mapM lowerRule?).get (by rfl)

theorem source_translation_exact : rows.mapM lowerRule? = some language.rewrites := rfl

theorem reference_occurrences_exact : referenceRows.zipIdx 54 =
    ((PlainBnfCollectorSourceAdmission.discoverySource.rewrites.zipIdx).drop 54).take 4 := rfl

theorem language_partition : language.rewrites =
    PlainBnfTrieSourceExecution.language.rewrites ++
      PlainBnfTrieOverwriteSourceExecution.language.rewrites ++ referenceRules := rfl

theorem exactly_twenty_four_rules : language.rewrites.length = 24 := rfl

/-- Proof observations, checked against the actual translated rows above. -/
private def observedRules : List RewriteRule := [
  observedRule "bnf-discovery-dependents-missing-v1"
    (metta_sexpr% petta "(BNFDiscoveryDependentsV1 BNFIndexMissingV1)")
    (metta_sexpr% petta "(BNFDiscoveryDefinitionsNilV1)"),
  observedRule "bnf-discovery-dependents-found-v1"
    (metta_sexpr% petta "(BNFDiscoveryDependentsV1 (BNFIndexFoundV1 ?definitions))")
    (metta_sexpr% petta "(?definitions)"),
  observedRule "bnf-discovery-add-references-nil-v1"
    (metta_sexpr% petta "(BNFDiscoveryAddReferencesV1 BNFNamesNilV1 ?node ?index)")
    (metta_sexpr% petta "(?index)"),
  observedRule "bnf-discovery-add-references-cons-v1"
    (metta_sexpr% petta "(BNFDiscoveryAddReferencesV1 (BNFNamesConsV1 ?name ?tail) ?node ?index)")
    (metta_sexpr% petta "(?result)")
    [.congruence (pattern (metta_sexpr% petta "(BNFGraphTrieLookupV1 ?name ?index)"))
        (pattern (metta_sexpr% petta "(?lookup)")),
     .congruence (pattern (metta_sexpr% petta "(BNFDiscoveryDependentsV1 ?lookup)"))
        (pattern (metta_sexpr% petta "(?previous)")),
     .congruence (pattern (metta_sexpr% petta "(BNFGraphTriePutV1 ?name (BNFDiscoveryDefinitionsConsV1 ?node ?previous) ?index)"))
        (pattern (metta_sexpr% petta "(?next)")),
     .congruence (pattern (metta_sexpr% petta "(BNFDiscoveryAddReferencesV1 ?tail ?node ?next)"))
        (pattern (metta_sexpr% petta "(?result)"))]]

private theorem reference_rules_exact : referenceRules = observedRules := rfl

def putNames : List String := ["BNFGraphTriePutV1", "BNFGraphTrieEdgePutV1"]
def referenceNames : List String := ["BNFDiscoveryDependentsV1", "BNFDiscoveryAddReferencesV1"]

theorem trie_heads : PlainBnfTrieSourceExecution.language.rewrites.all
    (fun rule => headedBy trieNames rule.left) = true := by
  simp [PlainBnfTrieSourceExecution.source_rules_exact, PlainBnfTrieSourceExecution.observedRules,
    observedRule, headedBy, trieNames, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode]

theorem put_heads : PlainBnfTrieOverwriteSourceExecution.language.rewrites.all
    (fun rule => headedBy putNames rule.left) = true := by
  simp [PlainBnfTrieOverwriteSourceExecution.source_rules_exact,
    PlainBnfTrieOverwriteSourceExecution.observedRules, observedRule, headedBy, putNames,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode]

theorem put_closed : PlainBnfTrieOverwriteSourceExecution.language.rewrites.all
    (fun rule => rule.premises.all (premiseClosed putNames)) = true := by
  simp [PlainBnfTrieOverwriteSourceExecution.source_rules_exact,
    PlainBnfTrieOverwriteSourceExecution.observedRules, observedRule, premiseClosed, headedBy,
    putNames, pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode]

theorem reference_heads : referenceRules.all
    (fun rule => headedBy referenceNames rule.left) = true := by
  simp [reference_rules_exact, observedRules, observedRule, headedBy, referenceNames,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode]

/-- Observed call-family boundary; this does not construct executable rules. -/
def relationHeads := trieNames ++ putNames ++ referenceNames

theorem family_heads : language.rewrites.all
    (fun rule => headedBy relationHeads rule.left) = true := by
  simp [language_partition, PlainBnfTrieSourceExecution.source_rules_exact,
    PlainBnfTrieSourceExecution.observedRules, PlainBnfTrieOverwriteSourceExecution.source_rules_exact,
    PlainBnfTrieOverwriteSourceExecution.observedRules, reference_rules_exact, observedRules,
    observedRule, headedBy, relationHeads, trieNames, putNames, referenceNames,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode]

theorem family_closed : language.rewrites.all
    (fun rule => rule.premises.all (premiseClosed relationHeads)) = true := by
  simp [language_partition, PlainBnfTrieSourceExecution.source_rules_exact,
    PlainBnfTrieSourceExecution.observedRules, PlainBnfTrieOverwriteSourceExecution.source_rules_exact,
    PlainBnfTrieOverwriteSourceExecution.observedRules, reference_rules_exact, observedRules,
    observedRule, premiseClosed, headedBy, relationHeads, trieNames, putNames, referenceNames,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode]

theorem trie_put_disjoint : List.Disjoint trieNames putNames := by simp [trieNames, putNames]
theorem trie_reference_disjoint : List.Disjoint trieNames referenceNames := by
  simp [trieNames, referenceNames]
theorem put_reference_disjoint : List.Disjoint putNames referenceNames := by
  simp [putNames, referenceNames]

theorem trie_conservative_extension (env : RelationEnv) (fuel : Nat) (source : Pattern)
    (headed : headedBy trieNames source = true) :
    rewriteAt (engineBasePremises env) language fuel source =
      rewriteAt (engineBasePremises env) PlainBnfTrieSourceExecution.language fuel source := by
  apply closed_extension trieNames env PlainBnfTrieSourceExecution.language language []
    (PlainBnfTrieOverwriteSourceExecution.language.rewrites ++ referenceRules)
    (by simpa [List.append_assoc] using language_partition) ?_ ?_ fuel source headed
  · intro rule member premise inside
    exact List.all_eq_true.mp (List.all_eq_true.mp trie_closed rule member) premise inside
  · intro rule member term termHead
    simp only [List.nil_append, List.mem_append] at member
    rcases member with member | member
    · exact disjoint_heads_do_not_match putNames trieNames trie_put_disjoint.symm _ _
        (List.all_eq_true.mp put_heads rule member) termHead
    · exact disjoint_heads_do_not_match referenceNames trieNames trie_reference_disjoint.symm _ _
        (List.all_eq_true.mp reference_heads rule member) termHead

theorem put_conservative_extension (env : RelationEnv) (fuel : Nat) (source : Pattern)
    (headed : headedBy putNames source = true) :
    rewriteAt (engineBasePremises env) language fuel source =
      rewriteAt (engineBasePremises env) PlainBnfTrieOverwriteSourceExecution.language fuel source := by
  apply closed_extension putNames env PlainBnfTrieOverwriteSourceExecution.language language
    PlainBnfTrieSourceExecution.language.rewrites referenceRules language_partition ?_ ?_ fuel source headed
  · intro rule member premise inside
    exact List.all_eq_true.mp (List.all_eq_true.mp put_closed rule member) premise inside
  · intro rule member term termHead
    rcases List.mem_append.mp member with member | member
    · exact disjoint_heads_do_not_match trieNames putNames trie_put_disjoint _ _
        (List.all_eq_true.mp trie_heads rule member) termHead
    · exact disjoint_heads_do_not_match referenceNames putNames put_reference_disjoint.symm _ _
        (List.all_eq_true.mp reference_heads rule member) termHead

private theorem reference_rewriteAt (env : RelationEnv) (fuel : Nat) (source : Pattern)
    (headed : headedBy referenceNames source = true) :
    rewriteAt (engineBasePremises env) language (fuel + 1) source =
      referenceRules.flatMap (fun rule => applyRuleUsing (engineBasePremises env) language
        (rewriteAt (engineBasePremises env) language fuel) rule source) := by
  rw [rewriteAt, language_partition]
  simp only [List.flatMap_append]
  have noTrie : PlainBnfTrieSourceExecution.language.rewrites.flatMap
      (fun rule => applyRuleUsing (engineBasePremises env) language
        (rewriteAt (engineBasePremises env) language fuel) rule source) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro rule member
    simp [applyRuleUsing, disjoint_heads_do_not_match trieNames referenceNames
      trie_reference_disjoint _ _ (List.all_eq_true.mp trie_heads rule member) headed]
  have noPut : PlainBnfTrieOverwriteSourceExecution.language.rewrites.flatMap
      (fun rule => applyRuleUsing (engineBasePremises env) language
        (rewriteAt (engineBasePremises env) language fuel) rule source) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro rule member
    simp [applyRuleUsing, disjoint_heads_do_not_match putNames referenceNames
      put_reference_disjoint _ _ (List.all_eq_true.mp put_heads rule member) headed]
  rw [noTrie, noPut]
  simp

def emptyBucket : SExpr := .atom "BNFDiscoveryDefinitionsNilV1"
def bucketCons (node tail : SExpr) : SExpr :=
  .list [.atom "BNFDiscoveryDefinitionsConsV1", node, tail]

def dependents (found : Option SExpr) : SExpr := found.getD emptyBucket
def dependentsCall (found : Option SExpr) : Pattern :=
  call "BNFDiscoveryDependentsV1" [value found]

variable {Scalar : Type} [NameScalarCodec Scalar]

def names : List (List Scalar) → SExpr
  | [] => .atom "BNFNamesNilV1"
  | head :: tail => .list [.atom "BNFNamesConsV1", name head, names tail]

def addCall (references : List (List Scalar)) (node : SExpr) (index : Trie SExpr Scalar) : Pattern :=
  call "BNFDiscoveryAddReferencesV1" [names references, node, trie index]

theorem dependents_answers (env : RelationEnv) (fuel : Nat) (found : Option SExpr) :
    rewriteAt (engineBasePremises env) language fuel (dependentsCall found) =
      if 0 < fuel then [result (dependents found)] else [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [reference_rewriteAt env fuel _ (by rfl)]
    cases found <;>
      simp [reference_rules_exact, observedRules, observedRule, applyRuleUsing,
        applyRuleBindings_of_binderFree, binderFree, binderFreeList,
        dependentsCall, dependents, emptyBucket, call, result, value,
        pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
        matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private theorem add_nil (env : RelationEnv) (fuel : Nat) (node : SExpr)
    (index : Trie SExpr Scalar) :
    rewriteAt (engineBasePremises env) language (fuel + 1) (addCall [] node index) =
      [result (trie index)] := by
  rw [reference_rewriteAt env fuel _ (by rfl)]
  simp [reference_rules_exact, observedRules, observedRule, applyRuleUsing,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    addCall, names, call, result, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private theorem add_first_none (env : RelationEnv) (fuel : Nat)
    (key : List Scalar) (tail : List (List Scalar)) (node : SExpr) (index : Trie SExpr Scalar)
    (first : rewriteAt (engineBasePremises env) language fuel (lookupCall key index) = []) :
    rewriteAt (engineBasePremises env) language (fuel + 1)
      (addCall (key :: tail) node index) = [] := by
  rw [reference_rewriteAt env fuel _ (by rfl)]
  simp [reference_rules_exact, observedRules, observedRule, applyRuleUsing,
    addCall, names, call, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing, applyBindings]
  simp only [lookupCall, call, encode, encodeList] at first
  rw [first]
  simp

private theorem add_put_none (env : RelationEnv) (fuel : Nat)
    (key : List Scalar) (tail : List (List Scalar)) (node : SExpr) (index : Trie SExpr Scalar)
    (found : Option SExpr)
    (first : rewriteAt (engineBasePremises env) language fuel (lookupCall key index) =
      [result (value found)])
    (second : rewriteAt (engineBasePremises env) language fuel (dependentsCall found) =
      [result (dependents found)])
    (third : rewriteAt (engineBasePremises env) language fuel
      (putCall key (bucketCons node (dependents found)) index) = []) :
    rewriteAt (engineBasePremises env) language (fuel + 1)
      (addCall (key :: tail) node index) = [] := by
  rw [reference_rewriteAt env fuel _ (by rfl)]
  simp [reference_rules_exact, observedRules, observedRule, applyRuleUsing,
    addCall, names, call, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing, applyBindings]
  simp only [lookupCall, call, result, encode, encodeList] at first
  rw [first]
  simp [matchPattern, matchArgs, mergeBindings, List.foldlM]
  simp only [dependentsCall, call, result, encode, encodeList] at second
  rw [second]
  simp [matchPattern, matchArgs, mergeBindings, List.foldlM]
  simp only [putCall, bucketCons, call, encode, encodeList] at third
  rw [third]
  simp

private theorem add_following (env : RelationEnv) (fuel : Nat)
    (key : List Scalar) (tail : List (List Scalar)) (node : SExpr) (index next : Trie SExpr Scalar)
    (found : Option SExpr) (answers : List SExpr)
    (first : rewriteAt (engineBasePremises env) language fuel (lookupCall key index) =
      [result (value found)])
    (second : rewriteAt (engineBasePremises env) language fuel (dependentsCall found) =
      [result (dependents found)])
    (third : rewriteAt (engineBasePremises env) language fuel
      (putCall key (bucketCons node (dependents found)) index) = [result (trie next)])
    (following : rewriteAt (engineBasePremises env) language fuel
      (addCall tail node next) = answers.map result) :
    rewriteAt (engineBasePremises env) language (fuel + 1)
      (addCall (key :: tail) node index) = answers.map result := by
  rw [reference_rewriteAt env fuel _ (by rfl)]
  simp [reference_rules_exact, observedRules, observedRule, applyRuleUsing,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    addCall, names, call, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing, applyBindings]
  simp only [lookupCall, call, result, encode, encodeList] at first
  rw [first]
  simp [matchPattern, matchArgs, mergeBindings, List.foldlM]
  simp only [dependentsCall, call, result, encode, encodeList] at second
  rw [second]
  simp [matchPattern, matchArgs, mergeBindings, List.foldlM]
  simp only [putCall, bucketCons, call, result, encode, encodeList] at third
  rw [third]
  simp [matchPattern, matchArgs, mergeBindings, List.foldlM]
  simp only [addCall, call, encode, encodeList] at following
  rw [following]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap, result, encode, encodeList]

variable [DecidableEq Scalar]

/-- One independent bucket update over the existing trie. The complete node
and pre-existing bucket tail are data, not interpreted as source calls. -/
def addOne (key : List Scalar) (node : SExpr) (index : Trie SExpr Scalar) : Trie SExpr Scalar :=
  PlainBnfGraphNameTrie.put key
    (bucketCons node (dependents (PlainBnfGraphNameTrie.lookup key index))) index

/-- Independent ordered reference traversal, using the ordinary list fold. -/
def addReferences (references : List (List Scalar)) (node : SExpr)
    (index : Trie SExpr Scalar) : Trie SExpr Scalar :=
  references.foldl (fun current key => addOne key node current) index

omit [NameScalarCodec Scalar] in
theorem addReferences_nil (node : SExpr) (index : Trie SExpr Scalar) :
    addReferences [] node index = index := rfl

omit [NameScalarCodec Scalar] in
theorem addReferences_cons (key : List Scalar) (tail : List (List Scalar)) (node : SExpr)
    (index : Trie SExpr Scalar) :
    addReferences (key :: tail) node index = addReferences tail node (addOne key node index) := rfl

/-- Contextual-premise depth; not an executable bucket-answer service. -/
def addHeight : List (List Scalar) → SExpr → Trie SExpr Scalar → Nat
  | [], _, _ => 0
  | key :: tail, node, index =>
      max (lookupHeight key index)
        (max (putHeight key index) (addHeight tail node (addOne key node index))) + 1

theorem lookup_answers (fuel : Nat) (key : List Scalar) (index : Trie SExpr Scalar) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (lookupCall key index) =
      if lookupHeight key index < fuel then
        [result (value (PlainBnfGraphNameTrie.lookup key index))] else [] := by
  rw [trie_conservative_extension _ fuel _ (by rfl)]
  exact (PlainBnfTrieSourceExecution.lookup_answers fuel).1 key index

theorem put_answers (fuel : Nat) (key : List Scalar) (payload : SExpr) (index : Trie SExpr Scalar) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (putCall key payload index) =
      if putHeight key index < fuel then
        [result (trie (PlainBnfGraphNameTrie.put key payload index))] else [] := by
  rw [put_conservative_extension _ fuel _ (by rfl)]
  exact (PlainBnfTrieOverwriteSourceExecution.put_answers fuel).1 key payload index

/-- Exact ordered answer lists, including absence at insufficient depth.
Each of the four source premises executes in the combined source language. -/
theorem add_answers (fuel : Nat) (references : List (List Scalar)) (node : SExpr)
    (index : Trie SExpr Scalar) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (addCall references node index) =
      if addHeight references node index < fuel then
        [result (trie (addReferences references node index))] else [] := by
  induction fuel generalizing references index with
  | zero => simp [rewriteAt]
  | succ fuel ih =>
    cases references with
    | nil => simpa [addHeight, addReferences_nil] using add_nil scalarRelations fuel node index
    | cons key tail =>
      have first := lookup_answers fuel key index
      have second := dependents_answers scalarRelations fuel (PlainBnfGraphNameTrie.lookup key index)
      have third := put_answers fuel key
        (bucketCons node (dependents (PlainBnfGraphNameTrie.lookup key index))) index
      have following := ih tail (addOne key node index)
      by_cases hfirst : lookupHeight key index < fuel
      · simp only [hfirst, ↓reduceIte] at first
        have positive : 0 < fuel := by omega
        simp only [positive, ↓reduceIte] at second
        by_cases hthird : putHeight key index < fuel
        · simp only [hthird, ↓reduceIte] at third
          by_cases hfollowing : addHeight tail node (addOne key node index) < fuel
          · simp only [hfollowing, ↓reduceIte] at following
            have step := add_following scalarRelations fuel key tail node index (addOne key node index)
              (PlainBnfGraphNameTrie.lookup key index) [trie (addReferences tail node (addOne key node index))]
              first second third (by simpa using following)
            simpa [addHeight, Nat.add_lt_add_iff_right, max_lt_iff, hfirst, hthird, hfollowing,
              addReferences_cons] using step
          · simp only [hfollowing, ↓reduceIte] at following
            have step := add_following scalarRelations fuel key tail node index (addOne key node index)
              (PlainBnfGraphNameTrie.lookup key index) [] first second third (by simpa using following)
            simpa [addHeight, Nat.add_lt_add_iff_right, max_lt_iff, hfirst, hthird, hfollowing] using step
        · simp only [hthird, ↓reduceIte] at third
          have absent := add_put_none scalarRelations fuel key tail node index
            (PlainBnfGraphNameTrie.lookup key index) first second third
          simpa [addHeight, Nat.add_lt_add_iff_right, max_lt_iff, hfirst, hthird] using absent
      · simp only [hfirst, ↓reduceIte] at first
        have absent := add_first_none scalarRelations fuel key tail node index first
        simpa [addHeight, Nat.add_lt_add_iff_right, max_lt_iff, hfirst] using absent

theorem dependents_step_iff (env : RelationEnv) (found : Option SExpr) (target : Pattern) :
    Step (engineBasePremises env) language (dependentsCall found) target ↔
      target = result (dependents found) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [dependents_answers] at member
    split at member
    · simpa using member
    · cases member
  · intro same
    subst target
    exact ⟨1, by simp [dependents_answers]⟩

theorem add_step_iff (references : List (List Scalar)) (node : SExpr)
    (index : Trie SExpr Scalar) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language (addCall references node index) target ↔
      target = result (trie (addReferences references node index)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [add_answers] at member
    split at member
    · simpa using member
    · cases member
  · intro same
    subst target
    exact ⟨addHeight references node index + 1, by simp [add_answers]⟩

theorem add_decoded_step_iff (references : List (List Scalar)) (node : SExpr)
    (before after : Trie SExpr Scalar) :
    Step (engineBasePremises scalarRelations) language (addCall references node before)
      (result (trie after)) ↔ after = addReferences references node before := by
  rw [add_step_iff]
  exact ⟨fun same => trie_injective (result_injective same), fun same => by rw [same]⟩

/-- Repeated node occurrences preceding an unchanged opaque bucket tail. -/
def repeatNode : Nat → SExpr → SExpr → SExpr
  | 0, _, tail => tail
  | count + 1, node, tail => bucketCons node (repeatNode count node tail)

theorem repeatNode_cons (count : Nat) (node tail : SExpr) :
    repeatNode count node (bucketCons node tail) = repeatNode (count + 1) node tail := by
  induction count with
  | zero => rfl
  | succ count ih => simpa [repeatNode] using congrArg (bucketCons node) ih

omit [NameScalarCodec Scalar] in
theorem lookup_addOne (key query : List Scalar) (node : SExpr) (index : Trie SExpr Scalar) :
    PlainBnfGraphNameTrie.lookup query (addOne key node index) =
      if query = key then some (bucketCons node (dependents (PlainBnfGraphNameTrie.lookup key index)))
      else PlainBnfGraphNameTrie.lookup query index := by
  rw [addOne, PlainBnfGraphNameTrie.lookup_put]

omit [NameScalarCodec Scalar] in
/-- Each matching reference contributes one whole node occurrence. No other
key is modified; any prior bucket tail remains behind those occurrences. -/
theorem lookup_addReferences (references : List (List Scalar)) (query : List Scalar)
    (node : SExpr) (index : Trie SExpr Scalar) :
    PlainBnfGraphNameTrie.lookup query (addReferences references node index) =
      if query ∈ references then
        some (repeatNode (references.count query) node
          (dependents (PlainBnfGraphNameTrie.lookup query index)))
      else PlainBnfGraphNameTrie.lookup query index := by
  induction references generalizing index with
  | nil => simp [addReferences_nil]
  | cons key tail ih =>
    rw [addReferences_cons, ih, lookup_addOne]
    by_cases same : query = key
    · subst key
      by_cases inside : query ∈ tail
      · simp [inside, dependents, repeatNode_cons]
      · have zero : tail.count query = 0 := List.count_eq_zero.mpr inside
        simp [inside, zero, dependents, repeatNode]
    · simp [same, Ne.symm same]

theorem execution_lookup (references : List (List Scalar)) (query : List Scalar)
    (node : SExpr) (before after : Trie SExpr Scalar)
    (execution : Step (engineBasePremises scalarRelations) language
      (addCall references node before) (result (trie after))) :
    PlainBnfGraphNameTrie.lookup query after =
      if query ∈ references then
        some (repeatNode (references.count query) node
          (dependents (PlainBnfGraphNameTrie.lookup query before)))
      else PlainBnfGraphNameTrie.lookup query before := by
  rw [add_decoded_step_iff] at execution
  rw [execution, lookup_addReferences]

theorem missing_bucket_is_empty (env : RelationEnv) :
    Step (engineBasePremises env) language (dependentsCall none) (result emptyBucket) := by
  rw [dependents_step_iff]
  rfl

theorem present_bucket_is_opaque (env : RelationEnv) (previous : SExpr) :
    Step (engineBasePremises env) language (dependentsCall (some previous)) (result previous) := by
  rw [dependents_step_iff]
  rfl

omit [NameScalarCodec Scalar] in
theorem repeated_reference_retains_both_nodes (key : List Scalar) (node previous : SExpr)
    (index : Trie SExpr Scalar) (found : PlainBnfGraphNameTrie.lookup key index = some previous) :
    PlainBnfGraphNameTrie.lookup key (addReferences [key, key] node index) =
      some (bucketCons node (bucketCons node previous)) := by
  simp [lookup_addReferences, found, dependents, repeatNode]

omit [NameScalarCodec Scalar] in
theorem absent_reference_cannot_create_bucket (references : List (List Scalar))
    (query : List Scalar) (node : SExpr) (index : Trie SExpr Scalar)
    (absent : query ∉ references) (missing : PlainBnfGraphNameTrie.lookup query index = none) :
    PlainBnfGraphNameTrie.lookup query (addReferences references node index) = none := by
  simp [lookup_addReferences, absent, missing]

omit [NameScalarCodec Scalar] in
theorem later_node_precedes_earlier (key : List Scalar) (earlier later previous : SExpr)
    (index : Trie SExpr Scalar) (found : PlainBnfGraphNameTrie.lookup key index = some previous) :
    PlainBnfGraphNameTrie.lookup key
      (addReferences [key] later (addReferences [key] earlier index)) =
      some (bucketCons later (bucketCons earlier previous)) := by
  simp [lookup_addReferences, found, dependents, repeatNode]

theorem empty_references_preserve_entire_index (node : SExpr) (index : Trie SExpr Scalar) :
    Step (engineBasePremises scalarRelations) language (addCall [] node index) (result (trie index)) := by
  rw [add_step_iff, addReferences_nil]

theorem signed_key_retains_complete_node (rank name expression span : SExpr) :
    let node := SExpr.list [SExpr.atom "BNFDiscoveryDefinitionV1", rank, name, expression, span]
    PlainBnfGraphNameTrie.lookup [-7]
      (addReferences ([[-7], [-7]] : List (List Int)) node .empty) =
      some (bucketCons node (bucketCons node emptyBucket)) ∧
    PlainBnfGraphNameTrie.lookup [7]
      (addReferences ([[-7], [-7]] : List (List Int)) node .empty) = none := by
  simp [lookup_addReferences, repeatNode, dependents]

theorem bucketCons_injective {left right old next : SExpr}
    (same : bucketCons left old = bucketCons right next) : left = right ∧ old = next := by
  simpa [bucketCons] using same

theorem bucketCons_ne_tail (node tail : SExpr) : bucketCons node tail ≠ tail := by
  intro same
  have sizes := congrArg sizeOf same
  simp [bucketCons] at sizes
  omega

/-- Replacing two equal reference occurrences by one changes source execution,
even when the entire node payload is identical. -/
theorem repeated_reference_cannot_be_collapsed (key : List Scalar) (node : SExpr)
    (index : Trie SExpr Scalar) :
    ¬ Step (engineBasePremises scalarRelations) language (addCall [key, key] node index)
      (result (trie (addReferences [key] node index))) := by
  intro execution
  have exactBucket := execution_lookup [key, key] key node index _ execution
  simp only [lookup_addReferences, List.mem_cons, true_or, ↓reduceIte] at exactBucket
  simp only [List.count_cons_self, List.count_nil, repeatNode] at exactBucket
  have tails := (bucketCons_injective (Option.some.inj exactBucket)).2
  exact bucketCons_ne_tail node _ tails.symm

theorem absent_reference_refuses_spurious_bucket (references : List (List Scalar))
    (query : List Scalar) (node payload : SExpr) (before after : Trie SExpr Scalar)
    (absent : query ∉ references) (missing : PlainBnfGraphNameTrie.lookup query before = none)
    (spurious : PlainBnfGraphNameTrie.lookup query after = some payload) :
    ¬ Step (engineBasePremises scalarRelations) language
      (addCall references node before) (result (trie after)) := by
  intro execution
  have exactBucket := execution_lookup references query node before after execution
  simp [absent, missing, spurious] at exactBucket

theorem later_node_cannot_be_reordered (key : List Scalar) (earlier later previous : SExpr)
    (different : earlier ≠ later) (index after : Trie SExpr Scalar)
    (found : PlainBnfGraphNameTrie.lookup key index = some previous)
    (reordered : PlainBnfGraphNameTrie.lookup key after =
      some (bucketCons earlier (bucketCons later previous))) :
    ¬ Step (engineBasePremises scalarRelations) language
      (addCall [key] later (addReferences [key] earlier index)) (result (trie after)) := by
  intro execution
  have exactBucket := execution_lookup [key] key later _ after execution
  simp [lookup_addReferences, found, reordered, dependents, repeatNode] at exactBucket
  exact different (bucketCons_injective exactBucket).1

theorem insufficient_depth_has_no_partial_index (references : List (List Scalar))
    (node : SExpr) (index : Trie SExpr Scalar) (fuel : Nat)
    (insufficient : fuel ≤ addHeight references node index) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (addCall references node index) = [] := by
  rw [add_answers]
  simp [show ¬ addHeight references node index < fuel by omega]

#print axioms source_translation_exact
#print axioms trie_conservative_extension
#print axioms put_conservative_extension
#print axioms add_answers
#print axioms add_step_iff
#print axioms execution_lookup

end Mettapedia.GSLT.Parsing.PlainBnfReverseReferencesSourceExecution
