import Mettapedia.GSLT.Parsing.PlainBnfCollectorSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfCollectorSourceAdmission

/-!
# Authored sparse-trie source execution

The source rules are translated into the existing contextual relation. The
only additional primitive is ground structural disequality; it does not compute
lookup or insertion answers. Payloads remain existing source S-expressions.
The scalar-parametric codec has proved canonical Nat and Integer instances;
the Integer instance covers signed structured text without changing the trie.
These are source/contextual laws, not a physical integer-runtime refinement.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfTrieSourceExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open SourceSExprPatternCodec (encode encodeList encode_injective)
open SourceSExprPatternInstantiation (pattern patternList applyBindings_encode
  applyRuleBindings_of_binderFree binderFree_pattern)
open PlainBnfGraphNameTrie (Trie)
open PlainBnfCollectorSourceExecution (name splitCall? lowerPremise? lowerRule?)
open PlainBnfCollectorSourceExecution (NameScalarCodec)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

variable {Scalar : Type} [NameScalarCodec Scalar]

def scalar (value : Scalar) : SExpr := .atom (NameScalarCodec.decimal value)

theorem scalar_injective : Function.Injective (scalar (Scalar := Scalar)) := by
  intro left right same
  exact NameScalarCodec.injective (SExpr.atom.inj same)

theorem encoded_scalar_eq_iff (left right : Scalar) :
    encode (scalar left) = encode (scalar right) ↔ left = right :=
  ⟨fun same => scalar_injective (encode_injective same),
    fun same => congrArg (fun input => encode (scalar input)) same⟩

/-- A selected ground source primitive, not an interpretation of open PeTTa
disequality. Its only returned row is its unchanged pair of arguments. -/
def scalarRelations : RelationEnv where
  tuples relation arguments := match relation, arguments with
    | "different", [left, right] => if left = right then [] else [[left, right]]
    | _, _ => []

theorem scalar_different_exact [DecidableEq Scalar] (left right : Scalar) :
    scalarRelations.tuples "different" [encode (scalar left), encode (scalar right)] =
      if left = right then [] else [[encode (scalar left), encode (scalar right)]] := by
  simp [scalarRelations, encoded_scalar_eq_iff]

theorem equal_scalar_refused (value : Scalar) :
    scalarRelations.tuples "different" [encode (scalar value), encode (scalar value)] = [] := by
  simp [scalarRelations]

theorem unequal_scalar_retains_exact_pair (left right : Scalar) (different : left ≠ right) :
    scalarRelations.tuples "different" [encode (scalar left), encode (scalar right)] =
      [[encode (scalar left), encode (scalar right)]] := by
  simp [scalarRelations, encoded_scalar_eq_iff, different]

def triePremise? : SExpr → Option Premise
  | .list [.atom "different", left, right] =>
      some (.relationQuery "different" [pattern left, pattern right])
  | source => lowerPremise? source

/-- The collector's checked mode split is reused. The source's ordered body
is preserved, with exactly the selected structural primitive added. -/
def trieRule? (source : Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT.Rewrite) : Option RewriteRule := do
  let (input, output) ← splitCall? source.head
  let premises ← Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT.decodeList triePremise? source.body
  some {
    name := source.name
    typeContext := []
    premises := premises
    left := pattern input
    right := pattern output }

private def ruleAt? (index : Nat) : Option RewriteRule :=
  PlainBnfCollectorSourceAdmission.indexSource.rewrites[index]? >>= trieRule?

def language : LanguageDef :=
  { name := "PlainBnfAuthoredSparseTrie", types := [], terms := [], equations := [],
    rewrites := (List.range 14).flatMap fun index => (ruleAt? index).toList }

def value : Option SExpr → SExpr
  | none => .atom "BNFIndexMissingV1"
  | some payload => .list [.atom "BNFIndexFoundV1", payload]

mutual
  def trie : Trie SExpr Scalar → SExpr
    | .empty => .atom "BNFGraphTrieEmptyV1"
    | .node payload children => .list [.atom "BNFGraphTrieV1", value payload, edges children]

  def edges : List (Scalar × Trie SExpr Scalar) → SExpr
    | [] => .atom "BNFGraphTrieEdgesNilV1"
    | (head, child) :: rest =>
        .list [.atom "BNFGraphTrieEdgesConsV1", scalar head, trie child, edges rest]
end

theorem value_injective : Function.Injective value := by
  intro left right same
  cases left <;> cases right <;> simp_all [value]

mutual
  theorem trie_injective {left right : Trie SExpr Scalar} (same : trie left = trie right) : left = right := by
    cases left with
    | empty => cases right <;> simp_all [trie]
    | node payload children =>
      cases right with
      | empty => simp [trie] at same
      | node other rest =>
        simp only [trie, SExpr.list.injEq, List.cons.injEq, and_true, true_and] at same
        have values := value_injective same.1
        have lists := edges_injective same.2
        cases values
        cases lists
        rfl
  termination_by sizeOf left

  theorem edges_injective {left right : List (Scalar × Trie SExpr Scalar)} (same : edges left = edges right) :
      left = right := by
    cases left with
    | nil => cases right <;> simp_all [edges]
    | cons edge rest =>
      cases edgeEq : edge with
      | mk head child =>
        simp only [edgeEq] at same
        cases right with
        | nil => simp [edges] at same
        | cons other following =>
          rcases other with ⟨stored, next⟩
          simp only [edges, SExpr.list.injEq, List.cons.injEq, and_true, true_and] at same
          have heads := scalar_injective same.1
          have children := trie_injective same.2.1
          have tails := edges_injective same.2.2
          cases heads
          cases children
          cases tails
          rfl
  termination_by sizeOf left
  decreasing_by all_goals simp_all only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]; omega
end

def call (relation : String) (arguments : List SExpr) : Pattern :=
  encode (.list (.atom relation :: arguments))

def result (output : SExpr) : Pattern := encode (.list [output])

def lookupCall (key : (List Scalar)) (index : Trie SExpr Scalar) : Pattern :=
  call "BNFGraphTrieLookupV1" [name key, trie index]

def edgeLookupCall (head : Scalar) (tail : (List Scalar)) (children : List (Scalar × Trie SExpr Scalar)) : Pattern :=
  call "BNFGraphTrieEdgeLookupV1" [scalar head, name tail, edges children]

def insertCall (key : (List Scalar)) (payload : SExpr) (index : Trie SExpr Scalar) : Pattern :=
  call "BNFGraphTrieInsertFirstV1" [name key, payload, trie index]

def edgeInsertCall (head : Scalar) (tail : (List Scalar)) (payload : SExpr)
    (children : List (Scalar × Trie SExpr Scalar)) : Pattern :=
  call "BNFGraphTrieEdgeInsertV1" [scalar head, name tail, payload, edges children]

/-- A target-shape observation used only in proofs. The executable language
above is computed from admitted source rows, independently of this helper. -/
def observedRule (ruleName : String) (input output : SExpr)
    (premises : List Premise := []) : RewriteRule :=
  { name := ruleName, typeContext := [], premises, left := pattern input, right := pattern output }

/-- Public proof observations, checked against the executed source translation
by `source_rules_exact`; these do not define `language`. -/
def observedRules : List RewriteRule :=
  [observedRule "bnf-graph-trie-lookup-empty-v1"
      (metta_sexpr% petta "(BNFGraphTrieLookupV1 ?key BNFGraphTrieEmptyV1)")
      (metta_sexpr% petta "(BNFIndexMissingV1)"),
    observedRule "bnf-graph-trie-lookup-value-v1"
      (metta_sexpr% petta "(BNFGraphTrieLookupV1 (metta-nullary bnf-v1:text-nil) (BNFGraphTrieV1 ?value ?edges))")
      (metta_sexpr% petta "(?value)"),
    observedRule "bnf-graph-trie-lookup-cons-v1"
      (metta_sexpr% petta "(BNFGraphTrieLookupV1 (bnf-v1:text-cons ?head ?tail) (BNFGraphTrieV1 ?value ?edges))")
      (metta_sexpr% petta "(?result)")
      [.congruence (pattern (metta_sexpr% petta "(BNFGraphTrieEdgeLookupV1 ?head ?tail ?edges)"))
        (pattern (metta_sexpr% petta "(?result)"))],
    observedRule "bnf-graph-trie-edge-lookup-nil-v1"
      (metta_sexpr% petta "(BNFGraphTrieEdgeLookupV1 ?head ?tail BNFGraphTrieEdgesNilV1)")
      (metta_sexpr% petta "(BNFIndexMissingV1)"),
    observedRule "bnf-graph-trie-edge-lookup-found-v1"
      (metta_sexpr% petta "(BNFGraphTrieEdgeLookupV1 ?head ?tail (BNFGraphTrieEdgesConsV1 ?head ?child ?rest))")
      (metta_sexpr% petta "(?result)")
      [.congruence (pattern (metta_sexpr% petta "(BNFGraphTrieLookupV1 ?tail ?child)"))
        (pattern (metta_sexpr% petta "(?result)"))],
    observedRule "bnf-graph-trie-edge-lookup-next-v1"
      (metta_sexpr% petta "(BNFGraphTrieEdgeLookupV1 ?head ?tail (BNFGraphTrieEdgesConsV1 ?other ?child ?rest))")
      (metta_sexpr% petta "(?result)")
      [.relationQuery "different" [pattern (.atom "?head"), pattern (.atom "?other")],
        .congruence (pattern (metta_sexpr% petta "(BNFGraphTrieEdgeLookupV1 ?head ?tail ?rest)"))
          (pattern (metta_sexpr% petta "(?result)"))],
    observedRule "bnf-graph-trie-insert-empty-v1"
      (metta_sexpr% petta "(BNFGraphTrieInsertFirstV1 ?key ?value BNFGraphTrieEmptyV1)")
      (metta_sexpr% petta "(?result)")
      [.congruence (pattern (metta_sexpr% petta "(BNFGraphTrieInsertFirstV1 ?key ?value (BNFGraphTrieV1 BNFIndexMissingV1 BNFGraphTrieEdgesNilV1))"))
        (pattern (metta_sexpr% petta "(?result)"))],
    observedRule "bnf-graph-trie-insert-value-v1"
      (metta_sexpr% petta "(BNFGraphTrieInsertFirstV1 (metta-nullary bnf-v1:text-nil) ?value (BNFGraphTrieV1 ?old ?edges))")
      (metta_sexpr% petta "((BNFGraphTrieV1 ?next ?edges))")
      [.congruence (pattern (metta_sexpr% petta "(BNFGraphTrieFirstValueV1 ?old ?value)"))
        (pattern (metta_sexpr% petta "(?next)"))],
    observedRule "bnf-graph-trie-insert-cons-v1"
      (metta_sexpr% petta "(BNFGraphTrieInsertFirstV1 (bnf-v1:text-cons ?head ?tail) ?value (BNFGraphTrieV1 ?old ?edges))")
      (metta_sexpr% petta "((BNFGraphTrieV1 ?old ?nextEdges))")
      [.congruence (pattern (metta_sexpr% petta "(BNFGraphTrieEdgeInsertV1 ?head ?tail ?value ?edges)"))
        (pattern (metta_sexpr% petta "(?nextEdges)"))],
    observedRule "bnf-graph-trie-first-value-empty-v1"
      (metta_sexpr% petta "(BNFGraphTrieFirstValueV1 BNFIndexMissingV1 ?value)")
      (metta_sexpr% petta "((BNFIndexFoundV1 ?value))"),
    observedRule "bnf-graph-trie-first-value-present-v1"
      (metta_sexpr% petta "(BNFGraphTrieFirstValueV1 (BNFIndexFoundV1 ?old) ?value)")
      (metta_sexpr% petta "((BNFIndexFoundV1 ?old))"),
    observedRule "bnf-graph-trie-edge-insert-nil-v1"
      (metta_sexpr% petta "(BNFGraphTrieEdgeInsertV1 ?head ?tail ?value BNFGraphTrieEdgesNilV1)")
      (metta_sexpr% petta "((BNFGraphTrieEdgesConsV1 ?head ?child BNFGraphTrieEdgesNilV1))")
      [.congruence (pattern (metta_sexpr% petta "(BNFGraphTrieInsertFirstV1 ?tail ?value BNFGraphTrieEmptyV1)"))
        (pattern (metta_sexpr% petta "(?child)"))],
    observedRule "bnf-graph-trie-edge-insert-found-v1"
      (metta_sexpr% petta "(BNFGraphTrieEdgeInsertV1 ?head ?tail ?value (BNFGraphTrieEdgesConsV1 ?head ?child ?rest))")
      (metta_sexpr% petta "((BNFGraphTrieEdgesConsV1 ?head ?nextChild ?rest))")
      [.congruence (pattern (metta_sexpr% petta "(BNFGraphTrieInsertFirstV1 ?tail ?value ?child)"))
        (pattern (metta_sexpr% petta "(?nextChild)"))],
    observedRule "bnf-graph-trie-edge-insert-next-v1"
      (metta_sexpr% petta "(BNFGraphTrieEdgeInsertV1 ?head ?tail ?value (BNFGraphTrieEdgesConsV1 ?other ?child ?rest))")
      (metta_sexpr% petta "((BNFGraphTrieEdgesConsV1 ?other ?child ?nextRest))")
      [.relationQuery "different" [pattern (.atom "?head"), pattern (.atom "?other")],
        .congruence (pattern (metta_sexpr% petta "(BNFGraphTrieEdgeInsertV1 ?head ?tail ?value ?rest)"))
          (pattern (metta_sexpr% petta "(?nextRest)"))]]

/-- These shapes are checked observations of the source-derived rules, not the
definition of the executable language above. -/
theorem source_rules_exact : language.rewrites = observedRules := by rfl


theorem source_rules_count : language.rewrites.length = 14 := by
  rw [source_rules_exact]
  rfl

/-- The ordered admitted source family is the input to the executed
translation. No wrapper or graph-analysis rule is added to this language. -/
theorem source_family_translation_exact :
    language.rewrites =
      (PlainBnfCollectorSourceAdmission.family PlainBnfCollectorSourceAdmission.indexSource).flatMap
        (fun row => (trieRule? row.1).toList) := by rfl

/-- Every selected occurrence translates once, in its authored order; the
Option decoder does not silently discard a malformed selected row. -/
theorem translated_occurrences_exact :
    (PlainBnfCollectorSourceAdmission.family PlainBnfCollectorSourceAdmission.indexSource).flatMap
      (fun row => (trieRule? row.1).toList.map (fun _ => row.2)) = List.range 14 := by rfl

theorem source_rule_iff (rule : RewriteRule) :
    rule ∈ language.rewrites ↔
      ∃ row occurrence,
        Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT.rawRewriteAt?
          PlainBnfCollectorSourceAdmission.indexSyntax occurrence = some row ∧
        occurrence < 14 ∧ trieRule? row = some rule := by
  rw [source_family_translation_exact]
  simp only [List.mem_flatMap, Option.mem_toList]
  constructor
  · rintro ⟨⟨row, occurrence⟩, member, translated⟩
    have admitted := (PlainBnfCollectorSourceAdmission.index_family_iff row occurrence).mp member
    exact ⟨row, occurrence, admitted.1, admitted.2, translated⟩
  · rintro ⟨row, occurrence, found, bound, translated⟩
    exact ⟨(row, occurrence),
      (PlainBnfCollectorSourceAdmission.index_family_iff row occurrence).mpr ⟨found, bound⟩,
      translated⟩

theorem first_value_rewriteAt (base : BasePremiseEvaluator) (fuel : Nat)
    (old : Option SExpr) (newValue : SExpr) :
    rewriteAt base language (fuel + 1) (call "BNFGraphTrieFirstValueV1" [value old, newValue]) =
      [result (value (old.or (some newValue)))] := by
  cases old <;>
    simp [rewriteAt, source_rules_exact, observedRules, observedRule,
      applyRuleUsing, call, result, value, pattern, patternList,
      applyRuleBindings_of_binderFree, binderFree, binderFreeList,
      SourceIntegerProvider.sourceVariableToken, encode, encodeList,
      matchPattern, matchArgs, mergeBindings, List.foldlM,
      premisesUsing, applyBindings]

mutual
  /-- Contextual depth needed by the authored lookup call, minus its root.
  This records only recursion depth, not an answer-producing interpreter. -/
  def lookupHeight [DecidableEq Scalar] : (List Scalar) → Trie SExpr Scalar → Nat
    | _, .empty => 0
    | [], .node _ _ => 0
    | head :: tail, .node _ children => 1 + edgeLookupHeight head tail children
  termination_by key index => sizeOf key + sizeOf index

  def edgeLookupHeight [DecidableEq Scalar] (head : Scalar) (tail : (List Scalar)) : List (Scalar × Trie SExpr Scalar) → Nat
    | [] => 0
    | (stored, child) :: rest =>
      if head = stored then 1 + lookupHeight tail child
      else 1 + edgeLookupHeight head tail rest
  termination_by children => sizeOf tail + sizeOf children
end

private theorem lookup_empty_rewriteAt (fuel : Nat) (key : (List Scalar)) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1) (lookupCall key .empty) =
      [result (value none)] := by
  cases key <;>
    simp [rewriteAt, source_rules_exact, observedRules, observedRule,
      applyRuleUsing, lookupCall, call, result, trie, value, name, pattern, patternList,
      applyRuleBindings_of_binderFree, binderFree, binderFreeList,
      SourceIntegerProvider.sourceVariableToken, encode, encodeList,
      matchPattern, matchArgs, mergeBindings, List.foldlM,
      premisesUsing, applyBindings]

private theorem lookup_value_rewriteAt (fuel : Nat) (old : Option SExpr)
    (children : List (Scalar × Trie SExpr Scalar)) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1) (lookupCall [] (.node old children)) =
      [result (value old)] := by
  simp [rewriteAt, source_rules_exact, observedRules, observedRule,
    applyRuleUsing, lookupCall, call, result, trie, value, name, pattern, patternList,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, applyBindings]

private theorem edge_nil_rewriteAt (fuel : Nat) (head : Scalar) (tail : (List Scalar)) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1) (edgeLookupCall head tail []) =
      [result (value none)] := by
  simp [rewriteAt, source_rules_exact, observedRules, observedRule,
    applyRuleUsing, edgeLookupCall, call, result, edges, value, pattern, patternList,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, applyBindings]

private theorem lookup_cons_rewriteAt (fuel : Nat) (head : Scalar) (tail : (List Scalar)) (old : Option SExpr)
    (children : List (Scalar × Trie SExpr Scalar)) (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises scalarRelations) language fuel
      (edgeLookupCall head tail children) = answers.map result) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (lookupCall (head :: tail) (.node old children)) = answers.map result := by
  rw [rewriteAt]
  simp [source_rules_exact, observedRules, observedRule,
    List.flatMap_cons, List.flatMap_nil, applyRuleUsing,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    matchPatternForRule_eq_syntactic, lookupCall, call, trie, name,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings,
    List.foldlM, applyBindingsForRule_eq_syntactic, premisesUsing, premiseStepUsing,
    applyBindings]
  simp only [edgeLookupCall, call, scalar, encode, encodeList] at recursive
  rw [recursive]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap, result, encode, encodeList]

private theorem edge_same_rewriteAt (fuel : Nat) (head : Scalar) (tail : (List Scalar)) (child : Trie SExpr Scalar)
    (rest : List (Scalar × Trie SExpr Scalar)) (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises scalarRelations) language fuel
      (lookupCall tail child) = answers.map result) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (edgeLookupCall head tail ((head, child) :: rest)) = answers.map result := by
  rw [rewriteAt]
  simp [source_rules_exact, observedRules, observedRule,
    applyRuleUsing, edgeLookupCall, call, edges, scalar,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings, engineBasePremises,
    premiseStepWithEnv, relationQueryStep, builtinRelationTuples, scalarRelations]
  simp [lookupCall, call, encode, encodeList, scalarRelations] at recursive
  rw [recursive]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap, result, encode, encodeList]

private theorem edge_other_rewriteAt (fuel : Nat) (head stored : Scalar) (different : head ≠ stored)
    (tail : (List Scalar)) (child : Trie SExpr Scalar) (rest : List (Scalar × Trie SExpr Scalar)) (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises scalarRelations) language fuel
      (edgeLookupCall head tail rest) = answers.map result) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (edgeLookupCall head tail ((stored, child) :: rest)) = answers.map result := by
  rw [rewriteAt]
  simp [source_rules_exact, observedRules, observedRule,
    applyRuleUsing, edgeLookupCall, call, edges, scalar,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings, engineBasePremises,
    premiseStepWithEnv, relationQueryStep, builtinRelationTuples, scalarRelations,
    matchRelationArgs, matchRelationArgument, Bindings.lookup, different]
  simp [edgeLookupCall, call, encode, encodeList, scalar, scalarRelations] at recursive
  rw [recursive]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap, result, encode, encodeList]

variable [DecidableEq Scalar]

/-- Complete answer lists of both mutually recursive source lookup operations.
The independent trie lookup supplies the stated meaning, not a provider. -/
theorem lookup_answers (fuel : Nat) :
    (∀ (key : List Scalar) (index : Trie SExpr Scalar), rewriteAt (engineBasePremises scalarRelations) language fuel (lookupCall key index) =
      if lookupHeight key index < fuel then
        [result (value (PlainBnfGraphNameTrie.lookup key index))] else []) ∧
    (∀ (head : Scalar) (tail : List Scalar) children,
      rewriteAt (engineBasePremises scalarRelations) language fuel (edgeLookupCall head tail children) =
      if edgeLookupHeight head tail children < fuel then
        [result (value (PlainBnfGraphNameTrie.lookup tail (PlainBnfGraphNameTrie.childFor head children)))]
      else []) := by
  induction fuel with
  | zero => constructor <;> intros <;> simp [rewriteAt]
  | succ fuel ih =>
    constructor
    · intro key index
      cases index with
      | empty => simpa [lookupHeight] using lookup_empty_rewriteAt fuel key
      | node old children =>
        cases key with
        | nil => simpa [lookupHeight, PlainBnfGraphNameTrie.lookup, PlainBnfGraphNameTrie.valueAt]
            using lookup_value_rewriteAt fuel old children
        | cons head tail =>
          by_cases enough : edgeLookupHeight head tail children < fuel
          · have recursiveResult := ih.2 head tail children
            simp only [enough, ↓reduceIte] at recursiveResult
            have step := lookup_cons_rewriteAt fuel head tail old children
              [value (PlainBnfGraphNameTrie.lookup tail (PlainBnfGraphNameTrie.childFor head children))]
              (by simpa using recursiveResult)
            have larger : lookupHeight (head :: tail) (.node old children) < fuel + 1 := by
              rw [lookupHeight]; omega
            simpa [larger, PlainBnfGraphNameTrie.lookup, PlainBnfGraphNameTrie.edgesOf] using step
          · have recursiveResult := ih.2 head tail children
            simp only [enough, ↓reduceIte] at recursiveResult
            have step := lookup_cons_rewriteAt fuel head tail old children [] (by simpa using recursiveResult)
            have smaller : ¬ lookupHeight (head :: tail) (.node old children) < fuel + 1 := by
              rw [lookupHeight]; omega
            simpa [smaller] using step
    · intro head tail children
      cases children with
      | nil => simpa [edgeLookupHeight, PlainBnfGraphNameTrie.childFor] using edge_nil_rewriteAt fuel head tail
      | cons edge rest =>
        rcases edge with ⟨stored, child⟩
        by_cases equal : head = stored
        · subst stored
          by_cases enough : lookupHeight tail child < fuel
          · have recursiveResult := ih.1 tail child
            simp only [enough, ↓reduceIte] at recursiveResult
            have step := edge_same_rewriteAt fuel head tail child rest
              [value (PlainBnfGraphNameTrie.lookup tail child)] (by simpa using recursiveResult)
            have larger : edgeLookupHeight head tail ((head, child) :: rest) < fuel + 1 := by
              simp only [edgeLookupHeight, ↓reduceIte]; omega
            simpa [larger, PlainBnfGraphNameTrie.childFor] using step
          · have recursiveResult := ih.1 tail child
            simp only [enough, ↓reduceIte] at recursiveResult
            have step := edge_same_rewriteAt fuel head tail child rest [] (by simpa using recursiveResult)
            have smaller : ¬ edgeLookupHeight head tail ((head, child) :: rest) < fuel + 1 := by
              simp only [edgeLookupHeight, ↓reduceIte]; omega
            simpa [smaller] using step
        · by_cases enough : edgeLookupHeight head tail rest < fuel
          · have recursiveResult := ih.2 head tail rest
            simp only [enough, ↓reduceIte] at recursiveResult
            have step := edge_other_rewriteAt fuel head stored equal tail child rest
              [value (PlainBnfGraphNameTrie.lookup tail (PlainBnfGraphNameTrie.childFor head rest))]
              (by simpa using recursiveResult)
            have larger : edgeLookupHeight head tail ((stored, child) :: rest) < fuel + 1 := by
              simp only [edgeLookupHeight, equal, ↓reduceIte]; omega
            simpa [larger, PlainBnfGraphNameTrie.childFor, equal] using step
          · have recursiveResult := ih.2 head tail rest
            simp only [enough, ↓reduceIte] at recursiveResult
            have step := edge_other_rewriteAt fuel head stored equal tail child rest [] (by simpa using recursiveResult)
            have smaller : ¬ edgeLookupHeight head tail ((stored, child) :: rest) < fuel + 1 := by
              simp only [edgeLookupHeight, equal, ↓reduceIte]; omega
            simpa [smaller] using step

omit [DecidableEq Scalar] in
private theorem insert_empty_rewriteAt (fuel : Nat) (key : (List Scalar)) (payload : SExpr)
    (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises scalarRelations) language fuel
      (insertCall key payload (.node none [])) = answers.map result) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (insertCall key payload .empty) = answers.map result := by
  have emptyMap (items : List Bindings) : items.flatMap (fun _ => ([] : List Bindings)) = [] :=
    List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
  rw [rewriteAt]
  simp [source_rules_exact, observedRules, observedRule,
    applyRuleUsing, insertCall, call, trie,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings, emptyMap]
  simp [insertCall, call, trie, edges, value, encode, encodeList] at recursive
  rw [recursive]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap, result, encode, encodeList]

omit [DecidableEq Scalar] in
private theorem insert_value_rewriteAt (fuel : Nat) (old : Option SExpr) (payload : SExpr)
    (children : List (Scalar × Trie SExpr Scalar)) (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises scalarRelations) language fuel
      (call "BNFGraphTrieFirstValueV1" [value old, payload]) = answers.map result) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (insertCall [] payload (.node old children)) =
        answers.map (fun next => result (.list [.atom "BNFGraphTrieV1", next, edges children])) := by
  rw [rewriteAt]
  simp [source_rules_exact, observedRules, observedRule,
    applyRuleUsing, insertCall, call, trie, name,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings]
  simp [call, encode, encodeList] at recursive
  rw [recursive]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap]

omit [DecidableEq Scalar] in
private theorem insert_cons_rewriteAt (fuel : Nat) (head : Scalar) (tail : (List Scalar)) (old : Option SExpr)
    (payload : SExpr) (children : List (Scalar × Trie SExpr Scalar)) (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises scalarRelations) language fuel
      (edgeInsertCall head tail payload children) = answers.map result) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (insertCall (head :: tail) payload (.node old children)) =
        answers.map (fun next => result (.list [.atom "BNFGraphTrieV1", value old, next])) := by
  rw [rewriteAt]
  simp [source_rules_exact, observedRules, observedRule,
    applyRuleUsing, insertCall, call, trie, name,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings]
  simp [edgeInsertCall, call, scalar, encode, encodeList] at recursive
  rw [recursive]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap]

omit [DecidableEq Scalar] in
private theorem edge_insert_nil_rewriteAt (fuel : Nat) (head : Scalar) (tail : (List Scalar)) (payload : SExpr)
    (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises scalarRelations) language fuel
      (insertCall tail payload .empty) = answers.map result) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (edgeInsertCall head tail payload []) =
        answers.map (fun next => result (.list [.atom "BNFGraphTrieEdgesConsV1",
          scalar head, next, .atom "BNFGraphTrieEdgesNilV1"])) := by
  rw [rewriteAt]
  simp [source_rules_exact, observedRules, observedRule,
    applyRuleUsing, edgeInsertCall, call, edges, scalar,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings]
  simp [insertCall, call, trie, encode, encodeList] at recursive
  rw [recursive]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap]

omit [DecidableEq Scalar] in
private theorem edge_insert_same_rewriteAt (fuel : Nat) (head : Scalar) (tail : (List Scalar)) (payload : SExpr)
    (child : Trie SExpr Scalar) (rest : List (Scalar × Trie SExpr Scalar)) (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises scalarRelations) language fuel
      (insertCall tail payload child) = answers.map result) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (edgeInsertCall head tail payload ((head, child) :: rest)) =
        answers.map (fun next => result (.list [.atom "BNFGraphTrieEdgesConsV1",
          scalar head, next, edges rest])) := by
  rw [rewriteAt]
  simp [source_rules_exact, observedRules, observedRule,
    applyRuleUsing, edgeInsertCall, call, edges, scalar,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings, engineBasePremises,
    premiseStepWithEnv, relationQueryStep, builtinRelationTuples, scalarRelations]
  simp [insertCall, call, encode, encodeList, scalarRelations] at recursive
  rw [recursive]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap]

omit [DecidableEq Scalar] in
private theorem edge_insert_other_rewriteAt (fuel : Nat) (head stored : Scalar) (different : head ≠ stored)
    (tail : (List Scalar)) (payload : SExpr) (child : Trie SExpr Scalar) (rest : List (Scalar × Trie SExpr Scalar))
    (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises scalarRelations) language fuel
      (edgeInsertCall head tail payload rest) = answers.map result) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (edgeInsertCall head tail payload ((stored, child) :: rest)) =
        answers.map (fun next => result (.list [.atom "BNFGraphTrieEdgesConsV1",
          scalar stored, trie child, next])) := by
  rw [rewriteAt]
  simp [source_rules_exact, observedRules, observedRule,
    applyRuleUsing, edgeInsertCall, call, edges, scalar,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings, engineBasePremises,
    premiseStepWithEnv, relationQueryStep, builtinRelationTuples, scalarRelations,
    matchRelationArgs, matchRelationArgument, Bindings.lookup, different]
  simp [edgeInsertCall, call, encode, encodeList, scalar, scalarRelations] at recursive
  rw [recursive]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap]

mutual
  def insertHeight : (List Scalar) → Trie SExpr Scalar → Nat
    | key, .empty => 1 + insertHeight key (.node none [])
    | [], .node _ _ => 1
    | head :: tail, .node _ children => 1 + edgeInsertHeight head tail children
  termination_by key index => (key.length, (match index with | .empty => 1 | .node _ _ => 0), 0)

  def edgeInsertHeight (head : Scalar) (tail : (List Scalar)) : List (Scalar × Trie SExpr Scalar) → Nat
    | [] => 1 + insertHeight tail .empty
    | (stored, child) :: rest =>
      if head = stored then 1 + insertHeight tail child
      else 1 + edgeInsertHeight head tail rest
  termination_by children => (tail.length, 2, children.length)
  decreasing_by
    all_goals simp_wf
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by decide))
    · apply Prod.Lex.right
      apply Prod.Lex.left
      cases child <;> simp
    · exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
end

/-- Complete answers of authored insertion and edge insertion, including
first-binding retention and the exact ordered edge list returned by updateChild. -/
theorem insert_answers (fuel : Nat) :
    (∀ (key : List Scalar) payload (index : Trie SExpr Scalar),
      rewriteAt (engineBasePremises scalarRelations) language fuel (insertCall key payload index) =
      if insertHeight key index < fuel then
        [result (trie (PlainBnfGraphNameTrie.insertFirst key payload index))] else []) ∧
    (∀ (head : Scalar) (tail : List Scalar) payload children,
      rewriteAt (engineBasePremises scalarRelations) language fuel
        (edgeInsertCall head tail payload children) =
      if edgeInsertHeight head tail children < fuel then
        [result (edges (PlainBnfGraphNameTrie.updateChild head
          (PlainBnfGraphNameTrie.insertFirst tail payload) children))] else []) := by
  induction fuel with
  | zero => constructor <;> intros <;> simp [rewriteAt]
  | succ fuel ih =>
    constructor
    · intro key payload index
      cases index with
      | empty =>
        by_cases enough : insertHeight key (.node none []) < fuel
        · have recursiveResult := ih.1 key payload (.node none [])
          simp only [enough, ↓reduceIte] at recursiveResult
          have step := insert_empty_rewriteAt fuel key payload
            [trie (PlainBnfGraphNameTrie.insertFirst key payload (.node none []))]
            (by simpa using recursiveResult)
          have larger : insertHeight key .empty < fuel + 1 := by rw [insertHeight]; omega
          cases key <;>
            simpa [larger, PlainBnfGraphNameTrie.insertFirst, PlainBnfGraphNameTrie.valueAt,
              PlainBnfGraphNameTrie.edgesOf] using step
        · have recursiveResult := ih.1 key payload (.node none [])
          simp only [enough, ↓reduceIte] at recursiveResult
          have step := insert_empty_rewriteAt fuel key payload [] (by simpa using recursiveResult)
          have smaller : ¬ insertHeight key .empty < fuel + 1 := by rw [insertHeight]; omega
          simpa [smaller] using step
      | node old children =>
        cases key with
        | nil =>
          cases fuel with
          | zero =>
            have step := insert_value_rewriteAt 0 old payload children [] (by simp [rewriteAt])
            simpa [insertHeight] using step
          | succ fuel =>
            have recursiveResult := first_value_rewriteAt (engineBasePremises scalarRelations) fuel old payload
            have step := insert_value_rewriteAt (fuel + 1) old payload children
              [value (old.or (some payload))] (by simpa using recursiveResult)
            simpa [insertHeight, PlainBnfGraphNameTrie.insertFirst,
              PlainBnfGraphNameTrie.valueAt, PlainBnfGraphNameTrie.edgesOf, trie] using step
        | cons head tail =>
          by_cases enough : edgeInsertHeight head tail children < fuel
          · have recursiveResult := ih.2 head tail payload children
            simp only [enough, ↓reduceIte] at recursiveResult
            have step := insert_cons_rewriteAt fuel head tail old payload children
              [edges (PlainBnfGraphNameTrie.updateChild head
                (PlainBnfGraphNameTrie.insertFirst tail payload) children)]
              (by simpa using recursiveResult)
            have larger : insertHeight (head :: tail) (.node old children) < fuel + 1 := by
              rw [insertHeight]; omega
            simpa [larger, PlainBnfGraphNameTrie.insertFirst, PlainBnfGraphNameTrie.valueAt,
              PlainBnfGraphNameTrie.edgesOf, trie] using step
          · have recursiveResult := ih.2 head tail payload children
            simp only [enough, ↓reduceIte] at recursiveResult
            have step := insert_cons_rewriteAt fuel head tail old payload children [] (by simpa using recursiveResult)
            have smaller : ¬ insertHeight (head :: tail) (.node old children) < fuel + 1 := by
              rw [insertHeight]; omega
            simpa [smaller] using step
    · intro head tail payload children
      cases children with
      | nil =>
        by_cases enough : insertHeight tail .empty < fuel
        · have recursiveResult := ih.1 tail payload .empty
          simp only [enough, ↓reduceIte] at recursiveResult
          have step := edge_insert_nil_rewriteAt fuel head tail payload
            [trie (PlainBnfGraphNameTrie.insertFirst tail payload .empty)] (by simpa using recursiveResult)
          have larger : edgeInsertHeight head tail [] < fuel + 1 := by rw [edgeInsertHeight]; omega
          simpa [larger, PlainBnfGraphNameTrie.updateChild, edges] using step
        · have recursiveResult := ih.1 tail payload .empty
          simp only [enough, ↓reduceIte] at recursiveResult
          have step := edge_insert_nil_rewriteAt fuel head tail payload [] (by simpa using recursiveResult)
          have smaller : ¬ edgeInsertHeight head tail [] < fuel + 1 := by rw [edgeInsertHeight]; omega
          simpa [smaller] using step
      | cons edge rest =>
        rcases edge with ⟨stored, child⟩
        by_cases equal : head = stored
        · subst stored
          by_cases enough : insertHeight tail child < fuel
          · have recursiveResult := ih.1 tail payload child
            simp only [enough, ↓reduceIte] at recursiveResult
            have step := edge_insert_same_rewriteAt fuel head tail payload child rest
              [trie (PlainBnfGraphNameTrie.insertFirst tail payload child)] (by simpa using recursiveResult)
            have larger : edgeInsertHeight head tail ((head, child) :: rest) < fuel + 1 := by
              simp only [edgeInsertHeight, ↓reduceIte]; omega
            simpa [larger, PlainBnfGraphNameTrie.updateChild, edges] using step
          · have recursiveResult := ih.1 tail payload child
            simp only [enough, ↓reduceIte] at recursiveResult
            have step := edge_insert_same_rewriteAt fuel head tail payload child rest [] (by simpa using recursiveResult)
            have smaller : ¬ edgeInsertHeight head tail ((head, child) :: rest) < fuel + 1 := by
              simp only [edgeInsertHeight, ↓reduceIte]; omega
            simpa [smaller] using step
        · by_cases enough : edgeInsertHeight head tail rest < fuel
          · have recursiveResult := ih.2 head tail payload rest
            simp only [enough, ↓reduceIte] at recursiveResult
            have step := edge_insert_other_rewriteAt fuel head stored equal tail payload child rest
              [edges (PlainBnfGraphNameTrie.updateChild head
                (PlainBnfGraphNameTrie.insertFirst tail payload) rest)] (by simpa using recursiveResult)
            have larger : edgeInsertHeight head tail ((stored, child) :: rest) < fuel + 1 := by
              simp only [edgeInsertHeight, equal, ↓reduceIte]; omega
            simpa [larger, PlainBnfGraphNameTrie.updateChild, equal, edges] using step
          · have recursiveResult := ih.2 head tail payload rest
            simp only [enough, ↓reduceIte] at recursiveResult
            have step := edge_insert_other_rewriteAt fuel head stored equal tail payload child rest []
              (by simpa using recursiveResult)
            have smaller : ¬ edgeInsertHeight head tail ((stored, child) :: rest) < fuel + 1 := by
              simp only [edgeInsertHeight, equal, ↓reduceIte]; omega
            simpa [smaller] using step

/-- Exact unbounded contextual execution, including arbitrary targets outside
the encoded source-data image. The premise environment is fixed explicitly. -/
theorem lookup_step_iff (key : (List Scalar)) (index : Trie SExpr Scalar) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language (lookupCall key index) target ↔
      target = result (value (PlainBnfGraphNameTrie.lookup key index)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [(lookup_answers fuel).1] at member
    split at member
    · simpa using member
    · cases member
  · intro same
    subst target
    refine ⟨lookupHeight key index + 1, ?_⟩
    simp [(lookup_answers _).1]

theorem edge_lookup_step_iff (head : Scalar) (tail : (List Scalar))
    (children : List (Scalar × Trie SExpr Scalar)) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language (edgeLookupCall head tail children) target ↔
      target = result (value (PlainBnfGraphNameTrie.lookup tail
        (PlainBnfGraphNameTrie.childFor head children))) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [(lookup_answers fuel).2] at member
    split at member
    · simpa using member
    · cases member
  · intro same
    subst target
    refine ⟨edgeLookupHeight head tail children + 1, ?_⟩
    simp [(lookup_answers _).2]

theorem insert_step_iff (key : (List Scalar)) (payload : SExpr) (index : Trie SExpr Scalar) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language (insertCall key payload index) target ↔
      target = result (trie (PlainBnfGraphNameTrie.insertFirst key payload index)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [(insert_answers fuel).1] at member
    split at member
    · simpa using member
    · cases member
  · intro same
    subst target
    refine ⟨insertHeight key index + 1, ?_⟩
    simp [(insert_answers _).1]

theorem edge_insert_step_iff (head : Scalar) (tail : (List Scalar)) (payload : SExpr)
    (children : List (Scalar × Trie SExpr Scalar)) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language
        (edgeInsertCall head tail payload children) target ↔
      target = result (edges (PlainBnfGraphNameTrie.updateChild head
        (PlainBnfGraphNameTrie.insertFirst tail payload) children)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [(insert_answers fuel).2] at member
    split at member
    · simpa using member
    · cases member
  · intro same
    subst target
    refine ⟨edgeInsertHeight head tail children + 1, ?_⟩
    simp [(insert_answers _).2]

theorem result_injective : Function.Injective result := by
  intro left right same
  exact (List.cons.inj (SExpr.list.inj (encode_injective same))).1

/-- Composition with the independent first-binding law. This is still the
selected authored language, not a native-runtime or whole-collector theorem. -/
theorem lookup_after_insert_step_iff (key query : (List Scalar)) (payload : SExpr)
    (index : Trie SExpr Scalar) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language
        (lookupCall query (PlainBnfGraphNameTrie.insertFirst key payload index)) target ↔
      target = result (value (if query = key then
        (PlainBnfGraphNameTrie.lookup key index).or (some payload)
        else PlainBnfGraphNameTrie.lookup query index)) := by
  rw [lookup_step_iff, PlainBnfGraphNameTrie.lookup_insertFirst]

theorem missing_lookup_does_not_invent_payload (key : (List Scalar)) (index : Trie SExpr Scalar)
    (missing : PlainBnfGraphNameTrie.lookup key index = none) (payload : SExpr) :
    ¬ Step (engineBasePremises scalarRelations) language (lookupCall key index)
      (result (value (some payload))) := by
  rw [lookup_step_iff, missing]
  intro same
  have contradiction := value_injective (result_injective same)
  cases contradiction

theorem duplicate_binding_is_not_overwritten (key : (List Scalar)) (index : Trie SExpr Scalar)
    (first later : SExpr) (different : first ≠ later)
    (found : PlainBnfGraphNameTrie.lookup key index = some first) :
    ¬ Step (engineBasePremises scalarRelations) language
      (lookupCall key (PlainBnfGraphNameTrie.insertFirst key later index))
      (result (value (some later))) := by
  rw [lookup_after_insert_step_iff]
  simp only [↓reduceIte, found, Option.or_some]
  intro same
  exact different (Option.some.inj (value_injective (result_injective same))).symm

theorem prefix_is_not_a_full_key (payload : SExpr) :
    Step (engineBasePremises scalarRelations) language
      (lookupCall ([1] : List Nat) (PlainBnfGraphNameTrie.insertFirst [1, 2] payload .empty))
      (result (value none)) := by
  rw [lookup_after_insert_step_iff]
  simp [PlainBnfGraphNameTrie.lookup, PlainBnfGraphNameTrie.edgesOf,
    PlainBnfGraphNameTrie.childFor, PlainBnfGraphNameTrie.valueAt]

theorem variable_looking_payload_remains_data :
    Step (engineBasePremises scalarRelations) language
      (lookupCall ([] : List Nat) (.node (some (.atom "?value")) []))
      (result (value (some (.atom "?value")))) := by
  rw [lookup_step_iff]
  rfl

theorem atom_payload_is_not_nullary_list :
    ¬ Step (engineBasePremises scalarRelations) language
      (lookupCall ([] : List Nat) (.node (some (.atom "value")) []))
      (result (value (some (.list [.atom "value"])))) := by
  rw [lookup_step_iff]
  intro same
  have impossible := value_injective (result_injective same)
  simp [PlainBnfGraphNameTrie.lookup, PlainBnfGraphNameTrie.valueAt] at impossible

theorem insertion_does_not_drop_repeated_edge (head : Scalar) (payload : SExpr)
    (child : Trie SExpr Scalar) :
    ¬ Step (engineBasePremises scalarRelations) language
      (insertCall [head] payload (.node none [(head, child), (head, child)]))
      (result (trie (.node none
        [(head, PlainBnfGraphNameTrie.insertFirst [] payload child)]))) := by
  rw [insert_step_iff]
  intro same
  have impossible := trie_injective (result_injective same)
  simp [PlainBnfGraphNameTrie.insertFirst, PlainBnfGraphNameTrie.valueAt,
    PlainBnfGraphNameTrie.edgesOf, PlainBnfGraphNameTrie.updateChild] at impossible

theorem lookup_exhaustion_is_not_a_missing_answer (key : (List Scalar)) (index : Trie SExpr Scalar)
    (fuel : Nat) (insufficient : fuel ≤ lookupHeight key index) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (lookupCall key index) = [] := by
  rw [(lookup_answers fuel).1]
  simp [show ¬ lookupHeight key index < fuel by omega]

/-- The canonical negative Integer spelling is retained in the source atom. -/
theorem negative_scalar_wire (magnitude : Nat) :
    scalar (Int.negSucc magnitude) = .atom ("-" ++ Nat.repr (magnitude + 1)) := rfl

theorem signed_scalar_disequality :
    scalarRelations.tuples "different" [encode (scalar (-7 : Int)), encode (scalar (7 : Int))] =
      [[encode (scalar (-7 : Int)), encode (scalar (7 : Int))]] := by
  rw [scalar_different_exact]
  decide

theorem signed_scalar_equality_refused :
    scalarRelations.tuples "different" [encode (scalar (-7 : Int)), encode (scalar (-7 : Int))] = [] :=
  equal_scalar_refused _

theorem signed_key_lookup (payload : SExpr) :
    Step (engineBasePremises scalarRelations) language
      (lookupCall ([-7, 0] : List Int)
        (PlainBnfGraphNameTrie.insertFirst [-7, 0] payload .empty))
      (result (value (some payload))) := by
  rw [lookup_after_insert_step_iff]
  simp [PlainBnfGraphNameTrie.lookup_empty]

theorem signed_key_does_not_alias_absolute_value (payload : SExpr) :
    Step (engineBasePremises scalarRelations) language
      (lookupCall ([7, 0] : List Int)
        (PlainBnfGraphNameTrie.insertFirst [-7, 0] payload .empty))
      (result (value none)) := by
  rw [lookup_after_insert_step_iff]
  simp [PlainBnfGraphNameTrie.lookup_empty]

end Mettapedia.GSLT.Parsing.PlainBnfTrieSourceExecution
