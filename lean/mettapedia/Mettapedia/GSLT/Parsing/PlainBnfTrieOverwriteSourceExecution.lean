import Mettapedia.GSLT.Parsing.PlainBnfTrieSourceExecution

/-!
# Authored sparse-trie overwrite execution

Discovery source occurrences 32–37 overwrite a reverse-reference bucket in
the existing sparse trie. The language below is computed from those admitted
source rows, not from the proof observations or the independent trie algorithm.
The only primitive is the existing ground structural scalar disequality.

The result concerns this selected source/contextual language. It is not a
generated PeTTa or C execution theorem, nor a whole-worklist theorem.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfTrieOverwriteSourceExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT (Rewrite decodeList)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open SourceSExprPatternCodec (encode encodeList)
open SourceSExprPatternInstantiation (pattern patternList)
open PlainBnfGraphNameTrie (Trie)
open PlainBnfCollectorSourceExecution (NameScalarCodec name)
open PlainBnfTrieSourceExecution
  (scalar scalarRelations trie edges value call result observedRule
    trie_injective edges_injective result_injective)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

def mode? : String → Option (Nat × Nat)
  | "BNFGraphTriePutV1" => some (3, 1)
  | "BNFGraphTrieEdgePutV1" => some (4, 1)
  | _ => none

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

def rows : List Rewrite :=
  (PlainBnfCollectorSourceAdmission.discoverySource.rewrites.drop 32).take 6

def rules? : Option (List RewriteRule) := rows.mapM lowerRule?

theorem rules_present : rules?.isSome = true := rfl

def language : LanguageDef :=
  { name := "PlainBnfAuthoredTrieOverwrite", types := [], terms := [], equations := [],
    rewrites := rules?.get rules_present }

theorem source_translation_exact : rows.mapM lowerRule? = some language.rewrites := rfl

theorem source_occurrences_exact : rows.zipIdx 32 =
    ((PlainBnfCollectorSourceAdmission.discoverySource.rewrites.zipIdx).drop 32).take 6 := rfl

theorem exactly_six_source_rules : language.rewrites.length = 6 := rfl

/-- Checked target-shape observations only. `language` above is independently
computed from the admitted source head and each ordered body. -/
def observedRules : List RewriteRule := [
  observedRule "bnf-discovery-trie-put-empty-v1"
    (metta_sexpr% petta "(BNFGraphTriePutV1 ?key ?value BNFGraphTrieEmptyV1)")
    (metta_sexpr% petta "(?result)")
    [.congruence
      (pattern (metta_sexpr% petta "(BNFGraphTriePutV1 ?key ?value (BNFGraphTrieV1 BNFIndexMissingV1 BNFGraphTrieEdgesNilV1))"))
      (pattern (metta_sexpr% petta "(?result)"))],
  observedRule "bnf-discovery-trie-put-value-v1"
    (metta_sexpr% petta "(BNFGraphTriePutV1 (metta-nullary bnf-v1:text-nil) ?value (BNFGraphTrieV1 ?old ?edges))")
    (metta_sexpr% petta "((BNFGraphTrieV1 (BNFIndexFoundV1 ?value) ?edges))"),
  observedRule "bnf-discovery-trie-put-cons-v1"
    (metta_sexpr% petta "(BNFGraphTriePutV1 (bnf-v1:text-cons ?head ?tail) ?value (BNFGraphTrieV1 ?old ?edges))")
    (metta_sexpr% petta "((BNFGraphTrieV1 ?old ?next))")
    [.congruence
      (pattern (metta_sexpr% petta "(BNFGraphTrieEdgePutV1 ?head ?tail ?value ?edges)"))
      (pattern (metta_sexpr% petta "(?next)"))],
  observedRule "bnf-discovery-trie-edge-put-nil-v1"
    (metta_sexpr% petta "(BNFGraphTrieEdgePutV1 ?head ?tail ?value BNFGraphTrieEdgesNilV1)")
    (metta_sexpr% petta "((BNFGraphTrieEdgesConsV1 ?head ?child BNFGraphTrieEdgesNilV1))")
    [.congruence
      (pattern (metta_sexpr% petta "(BNFGraphTriePutV1 ?tail ?value BNFGraphTrieEmptyV1)"))
      (pattern (metta_sexpr% petta "(?child)"))],
  observedRule "bnf-discovery-trie-edge-put-found-v1"
    (metta_sexpr% petta "(BNFGraphTrieEdgePutV1 ?head ?tail ?value (BNFGraphTrieEdgesConsV1 ?head ?child ?rest))")
    (metta_sexpr% petta "((BNFGraphTrieEdgesConsV1 ?head ?next ?rest))")
    [.congruence
      (pattern (metta_sexpr% petta "(BNFGraphTriePutV1 ?tail ?value ?child)"))
      (pattern (metta_sexpr% petta "(?next)"))],
  observedRule "bnf-discovery-trie-edge-put-next-v1"
    (metta_sexpr% petta "(BNFGraphTrieEdgePutV1 ?head ?tail ?value (BNFGraphTrieEdgesConsV1 ?other ?child ?rest))")
    (metta_sexpr% petta "((BNFGraphTrieEdgesConsV1 ?other ?child ?next))")
    [.relationQuery "different" [pattern (.atom "?head"), pattern (.atom "?other")],
     .congruence
      (pattern (metta_sexpr% petta "(BNFGraphTrieEdgePutV1 ?head ?tail ?value ?rest)"))
      (pattern (metta_sexpr% petta "(?next)"))]]

theorem source_rules_exact : language.rewrites = observedRules := rfl

variable {Scalar : Type} [NameScalarCodec Scalar]

def putCall (key : List Scalar) (payload : SExpr) (index : Trie SExpr Scalar) : Pattern :=
  call "BNFGraphTriePutV1" [name key, payload, trie index]

def edgePutCall (head : Scalar) (tail : List Scalar) (payload : SExpr)
    (children : List (Scalar × Trie SExpr Scalar)) : Pattern :=
  call "BNFGraphTrieEdgePutV1" [scalar head, name tail, payload, edges children]

private theorem put_empty_rewriteAt (fuel : Nat) (key : List Scalar) (payload : SExpr)
    (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises scalarRelations) language fuel
      (putCall key payload (.node none [])) = answers.map result) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (putCall key payload .empty) = answers.map result := by
  have emptyMap (items : List Bindings) : items.flatMap (fun _ => ([] : List Bindings)) = [] :=
    List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
  rw [rewriteAt]
  simp [source_rules_exact, observedRules, observedRule,
    applyRuleUsing, putCall, call, trie,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings, emptyMap]
  simp [putCall, call, trie, edges, value, encode, encodeList] at recursive
  rw [recursive]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap, result, encode, encodeList]

private theorem put_value_rewriteAt (fuel : Nat) (old : Option SExpr) (payload : SExpr)
    (children : List (Scalar × Trie SExpr Scalar)) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (putCall [] payload (.node old children)) =
        [result (trie (.node (some payload) children))] := by
  rw [rewriteAt]
  simp [source_rules_exact, observedRules, observedRule,
    applyRuleUsing, putCall, call, trie, name, value, result,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings]

private theorem put_cons_rewriteAt (fuel : Nat) (head : Scalar) (tail : List Scalar)
    (old : Option SExpr) (payload : SExpr) (children : List (Scalar × Trie SExpr Scalar))
    (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises scalarRelations) language fuel
      (edgePutCall head tail payload children) = answers.map result) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (putCall (head :: tail) payload (.node old children)) =
        answers.map (fun next => result (.list [.atom "BNFGraphTrieV1", value old, next])) := by
  rw [rewriteAt]
  simp [source_rules_exact, observedRules, observedRule,
    applyRuleUsing, putCall, call, trie, name,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings]
  simp [edgePutCall, call, scalar, encode, encodeList] at recursive
  rw [recursive]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap]

private theorem edge_put_nil_rewriteAt (fuel : Nat) (head : Scalar) (tail : List Scalar)
    (payload : SExpr) (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises scalarRelations) language fuel
      (putCall tail payload .empty) = answers.map result) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (edgePutCall head tail payload []) =
        answers.map (fun next => result (.list [.atom "BNFGraphTrieEdgesConsV1",
          scalar head, next, .atom "BNFGraphTrieEdgesNilV1"])) := by
  rw [rewriteAt]
  simp [source_rules_exact, observedRules, observedRule,
    applyRuleUsing, edgePutCall, call, edges, scalar,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings]
  simp [putCall, call, trie, encode, encodeList] at recursive
  rw [recursive]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap]

private theorem edge_put_same_rewriteAt (fuel : Nat) (head : Scalar) (tail : List Scalar)
    (payload : SExpr) (child : Trie SExpr Scalar) (rest : List (Scalar × Trie SExpr Scalar))
    (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises scalarRelations) language fuel
      (putCall tail payload child) = answers.map result) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (edgePutCall head tail payload ((head, child) :: rest)) =
        answers.map (fun next => result (.list [.atom "BNFGraphTrieEdgesConsV1",
          scalar head, next, edges rest])) := by
  rw [rewriteAt]
  simp [source_rules_exact, observedRules, observedRule,
    applyRuleUsing, edgePutCall, call, edges, scalar,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings, engineBasePremises,
    premiseStepWithEnv, relationQueryStep, builtinRelationTuples, scalarRelations]
  simp [putCall, call, encode, encodeList, scalarRelations] at recursive
  rw [recursive]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap]

private theorem edge_put_other_rewriteAt (fuel : Nat) (head stored : Scalar)
    (different : head ≠ stored) (tail : List Scalar) (payload : SExpr)
    (child : Trie SExpr Scalar) (rest : List (Scalar × Trie SExpr Scalar))
    (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises scalarRelations) language fuel
      (edgePutCall head tail payload rest) = answers.map result) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (edgePutCall head tail payload ((stored, child) :: rest)) =
        answers.map (fun next => result (.list [.atom "BNFGraphTrieEdgesConsV1",
          scalar stored, trie child, next])) := by
  rw [rewriteAt]
  simp [source_rules_exact, observedRules, observedRule,
    applyRuleUsing, edgePutCall, call, edges, scalar,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings, engineBasePremises,
    premiseStepWithEnv, relationQueryStep, builtinRelationTuples, scalarRelations,
    matchRelationArgs, matchRelationArgument, Bindings.lookup, different]
  simp [edgePutCall, call, encode, encodeList, scalar, scalarRelations] at recursive
  rw [recursive]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap]

variable [DecidableEq Scalar]

/- Source-premise depth, not a new executor or an expected-answer provider. -/
mutual
  def putHeight : List Scalar → Trie SExpr Scalar → Nat
    | key, .empty => 1 + putHeight key (.node none [])
    | [], .node _ _ => 0
    | head :: tail, .node _ children => 1 + edgePutHeight head tail children
  termination_by key index => (key.length, (match index with | .empty => 1 | .node _ _ => 0), 0)

  def edgePutHeight (head : Scalar) (tail : List Scalar) : List (Scalar × Trie SExpr Scalar) → Nat
    | [] => 1 + putHeight tail .empty
    | (stored, child) :: rest =>
      if head = stored then 1 + putHeight tail child
      else 1 + edgePutHeight head tail rest
  termination_by children => (tail.length, 2, children.length)
  decreasing_by
    all_goals simp_wf
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ (by decide))
    · apply Prod.Lex.right
      apply Prod.Lex.left
      cases child <;> simp
    · exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))
end

/-- All answers, in their original order and multiplicity. A sufficient
source-premise depth yields one complete trie or edge list; a smaller depth
yields no answer, never a partially updated value. -/
theorem put_answers (fuel : Nat) :
    (∀ (key : List Scalar) payload (index : Trie SExpr Scalar),
      rewriteAt (engineBasePremises scalarRelations) language fuel (putCall key payload index) =
      if putHeight key index < fuel then
        [result (trie (PlainBnfGraphNameTrie.put key payload index))] else []) ∧
    (∀ (head : Scalar) (tail : List Scalar) payload children,
      rewriteAt (engineBasePremises scalarRelations) language fuel
        (edgePutCall head tail payload children) =
      if edgePutHeight head tail children < fuel then
        [result (edges (PlainBnfGraphNameTrie.updateChild head
          (PlainBnfGraphNameTrie.put tail payload) children))] else []) := by
  induction fuel with
  | zero => constructor <;> intros <;> simp [rewriteAt]
  | succ fuel ih =>
    constructor
    · intro key payload index
      cases index with
      | empty =>
        by_cases enough : putHeight key (.node none []) < fuel
        · have recursiveResult := ih.1 key payload (.node none [])
          simp only [enough, ↓reduceIte] at recursiveResult
          have step := put_empty_rewriteAt fuel key payload
            [trie (PlainBnfGraphNameTrie.put key payload (.node none []))]
            (by simpa using recursiveResult)
          have larger : putHeight key .empty < fuel + 1 := by rw [putHeight]; omega
          cases key <;>
            simpa [larger, PlainBnfGraphNameTrie.put, PlainBnfGraphNameTrie.valueAt,
              PlainBnfGraphNameTrie.edgesOf] using step
        · have recursiveResult := ih.1 key payload (.node none [])
          simp only [enough, ↓reduceIte] at recursiveResult
          have step := put_empty_rewriteAt fuel key payload [] (by simpa using recursiveResult)
          have smaller : ¬ putHeight key .empty < fuel + 1 := by rw [putHeight]; omega
          simpa [smaller] using step
      | node old children =>
        cases key with
        | nil =>
          simpa [putHeight, PlainBnfGraphNameTrie.put, PlainBnfGraphNameTrie.edgesOf] using
            put_value_rewriteAt fuel old payload children
        | cons head tail =>
          by_cases enough : edgePutHeight head tail children < fuel
          · have recursiveResult := ih.2 head tail payload children
            simp only [enough, ↓reduceIte] at recursiveResult
            have step := put_cons_rewriteAt fuel head tail old payload children
              [edges (PlainBnfGraphNameTrie.updateChild head
                (PlainBnfGraphNameTrie.put tail payload) children)]
              (by simpa using recursiveResult)
            have larger : putHeight (head :: tail) (.node old children) < fuel + 1 := by
              rw [putHeight]; omega
            simpa [larger, PlainBnfGraphNameTrie.put, PlainBnfGraphNameTrie.valueAt,
              PlainBnfGraphNameTrie.edgesOf, trie] using step
          · have recursiveResult := ih.2 head tail payload children
            simp only [enough, ↓reduceIte] at recursiveResult
            have step := put_cons_rewriteAt fuel head tail old payload children [] (by simpa using recursiveResult)
            have smaller : ¬ putHeight (head :: tail) (.node old children) < fuel + 1 := by
              rw [putHeight]; omega
            simpa [smaller] using step
    · intro head tail payload children
      cases children with
      | nil =>
        by_cases enough : putHeight tail .empty < fuel
        · have recursiveResult := ih.1 tail payload .empty
          simp only [enough, ↓reduceIte] at recursiveResult
          have step := edge_put_nil_rewriteAt fuel head tail payload
            [trie (PlainBnfGraphNameTrie.put tail payload .empty)] (by simpa using recursiveResult)
          have larger : edgePutHeight head tail [] < fuel + 1 := by rw [edgePutHeight]; omega
          simpa [larger, PlainBnfGraphNameTrie.updateChild, edges] using step
        · have recursiveResult := ih.1 tail payload .empty
          simp only [enough, ↓reduceIte] at recursiveResult
          have step := edge_put_nil_rewriteAt fuel head tail payload [] (by simpa using recursiveResult)
          have smaller : ¬ edgePutHeight head tail [] < fuel + 1 := by rw [edgePutHeight]; omega
          simpa [smaller] using step
      | cons edge rest =>
        rcases edge with ⟨stored, child⟩
        by_cases equal : head = stored
        · subst stored
          by_cases enough : putHeight tail child < fuel
          · have recursiveResult := ih.1 tail payload child
            simp only [enough, ↓reduceIte] at recursiveResult
            have step := edge_put_same_rewriteAt fuel head tail payload child rest
              [trie (PlainBnfGraphNameTrie.put tail payload child)] (by simpa using recursiveResult)
            have larger : edgePutHeight head tail ((head, child) :: rest) < fuel + 1 := by
              simp only [edgePutHeight, ↓reduceIte]; omega
            simpa [larger, PlainBnfGraphNameTrie.updateChild, edges] using step
          · have recursiveResult := ih.1 tail payload child
            simp only [enough, ↓reduceIte] at recursiveResult
            have step := edge_put_same_rewriteAt fuel head tail payload child rest [] (by simpa using recursiveResult)
            have smaller : ¬ edgePutHeight head tail ((head, child) :: rest) < fuel + 1 := by
              simp only [edgePutHeight, ↓reduceIte]; omega
            simpa [smaller] using step
        · by_cases enough : edgePutHeight head tail rest < fuel
          · have recursiveResult := ih.2 head tail payload rest
            simp only [enough, ↓reduceIte] at recursiveResult
            have step := edge_put_other_rewriteAt fuel head stored equal tail payload child rest
              [edges (PlainBnfGraphNameTrie.updateChild head
                (PlainBnfGraphNameTrie.put tail payload) rest)] (by simpa using recursiveResult)
            have larger : edgePutHeight head tail ((stored, child) :: rest) < fuel + 1 := by
              simp only [edgePutHeight, equal, ↓reduceIte]; omega
            simpa [larger, PlainBnfGraphNameTrie.updateChild, equal, edges] using step
          · have recursiveResult := ih.2 head tail payload rest
            simp only [enough, ↓reduceIte] at recursiveResult
            have step := edge_put_other_rewriteAt fuel head stored equal tail payload child rest []
              (by simpa using recursiveResult)
            have smaller : ¬ edgePutHeight head tail ((stored, child) :: rest) < fuel + 1 := by
              simp only [edgePutHeight, equal, ↓reduceIte]; omega
            simpa [smaller] using step

/-- Arbitrary target patterns are covered, including targets outside the data
codec's image. No extra provider can manufacture an overwrite answer. -/
theorem put_step_iff (key : List Scalar) (payload : SExpr) (index : Trie SExpr Scalar)
    (target : Pattern) :
    Step (engineBasePremises scalarRelations) language (putCall key payload index) target ↔
      target = result (trie (PlainBnfGraphNameTrie.put key payload index)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [(put_answers fuel).1] at member
    split at member
    · simpa using member
    · cases member
  · intro same
    subst target
    refine ⟨putHeight key index + 1, ?_⟩
    simp [(put_answers _).1]

theorem edge_put_step_iff (head : Scalar) (tail : List Scalar) (payload : SExpr)
    (children : List (Scalar × Trie SExpr Scalar)) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language
        (edgePutCall head tail payload children) target ↔
      target = result (edges (PlainBnfGraphNameTrie.updateChild head
        (PlainBnfGraphNameTrie.put tail payload) children)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [(put_answers fuel).2] at member
    split at member
    · simpa using member
    · cases member
  · intro same
    subst target
    refine ⟨edgePutHeight head tail children + 1, ?_⟩
    simp [(put_answers _).2]

theorem put_decoded_step_iff (key : List Scalar) (payload : SExpr)
    (before after : Trie SExpr Scalar) :
    Step (engineBasePremises scalarRelations) language
      (putCall key payload before) (result (trie after)) ↔
      after = PlainBnfGraphNameTrie.put key payload before := by
  rw [put_step_iff]
  exact ⟨fun same => trie_injective (result_injective same), fun same => by rw [same]⟩

theorem execution_lookup (key query : List Scalar) (payload : SExpr)
    (before after : Trie SExpr Scalar)
    (execution : Step (engineBasePremises scalarRelations) language
      (putCall key payload before) (result (trie after))) :
    PlainBnfGraphNameTrie.lookup query after =
      if query = key then some payload else PlainBnfGraphNameTrie.lookup query before := by
  rw [put_decoded_step_iff] at execution
  rw [execution, PlainBnfGraphNameTrie.lookup_put]

theorem execution_replaces_selected_key (key : List Scalar) (payload : SExpr)
    (before after : Trie SExpr Scalar)
    (execution : Step (engineBasePremises scalarRelations) language
      (putCall key payload before) (result (trie after))) :
    PlainBnfGraphNameTrie.lookup key after = some payload := by
  simpa using execution_lookup key key payload before after execution

theorem execution_preserves_other_key (key query : List Scalar) (payload : SExpr)
    (before after : Trie SExpr Scalar) (different : query ≠ key)
    (execution : Step (engineBasePremises scalarRelations) language
      (putCall key payload before) (result (trie after))) :
    PlainBnfGraphNameTrie.lookup query after = PlainBnfGraphNameTrie.lookup query before := by
  simpa [different] using execution_lookup key query payload before after execution

/-- Two equal edge occurrences are not a set: only the first child's value
changes, and the second child remains in its original position. -/
theorem execution_preserves_shadowed_duplicate (head : Scalar) (payload : SExpr)
    (first shadowed : Trie SExpr Scalar) :
    Step (engineBasePremises scalarRelations) language
      (putCall [head] payload (.node none [(head, first), (head, shadowed)]))
      (result (trie (.node none
        [(head, .node (some payload) (PlainBnfGraphNameTrie.edgesOf first)),
         (head, shadowed)]))) := by
  rw [put_step_iff]
  simp [PlainBnfGraphNameTrie.put, PlainBnfGraphNameTrie.valueAt,
    PlainBnfGraphNameTrie.edgesOf, PlainBnfGraphNameTrie.updateChild]

theorem execution_cannot_drop_repeated_edge (head : Scalar) (payload : SExpr)
    (child : Trie SExpr Scalar) :
    ¬ Step (engineBasePremises scalarRelations) language
      (putCall [head] payload (.node none [(head, child), (head, child)]))
      (result (trie (.node none [(head, PlainBnfGraphNameTrie.put [] payload child)]))) := by
  rw [put_decoded_step_iff]
  simp [PlainBnfGraphNameTrie.put, PlainBnfGraphNameTrie.valueAt,
    PlainBnfGraphNameTrie.edgesOf, PlainBnfGraphNameTrie.updateChild]

/-- The former payload cannot survive as the selected-key answer when the
new payload is different. This distinguishes overwrite from insert-first. -/
theorem overwrite_is_not_first_insertion (key : List Scalar) (before : Trie SExpr Scalar)
    (oldPayload newPayload : SExpr) (different : oldPayload ≠ newPayload)
    (found : PlainBnfGraphNameTrie.lookup key before = some oldPayload) :
    ¬ Step (engineBasePremises scalarRelations) language (putCall key newPayload before)
      (result (trie (PlainBnfGraphNameTrie.insertFirst key newPayload before))) := by
  intro execution
  have selected := execution_replaces_selected_key key newPayload before _ execution
  rw [PlainBnfGraphNameTrie.lookup_inserted, found, Option.or_some] at selected
  exact different (Option.some.inj selected)

theorem prefix_replacement_retains_extension (prefixPayload extensionPayload newPayload : SExpr) :
    let before : Trie SExpr Int := PlainBnfGraphNameTrie.insertFirst [-7, 0] extensionPayload
      (PlainBnfGraphNameTrie.insertFirst [-7] prefixPayload .empty)
    let after := PlainBnfGraphNameTrie.put [-7] newPayload before
    Step (engineBasePremises scalarRelations) language
      (putCall [-7] newPayload before) (result (trie after)) ∧
    PlainBnfGraphNameTrie.lookup [-7] after = some newPayload ∧
    PlainBnfGraphNameTrie.lookup [-7, 0] after = some extensionPayload ∧
    PlainBnfGraphNameTrie.lookup [7] after = none := by
  dsimp
  constructor
  · rw [put_step_iff]
  constructor
  · exact PlainBnfGraphNameTrie.lookup_put_same _ _ _
  simp [PlainBnfGraphNameTrie.lookup_put, PlainBnfGraphNameTrie.lookup_insertFirst]

theorem empty_key_replacement_retains_children (oldPayload newPayload : SExpr)
    (children : List (Scalar × Trie SExpr Scalar)) :
    Step (engineBasePremises scalarRelations) language
      (putCall [] newPayload (.node (some oldPayload) children))
      (result (trie (.node (some newPayload) children))) := by
  rw [put_step_iff]
  rfl

theorem variable_looking_payload_remains_data :
    Step (engineBasePremises scalarRelations) language
      (putCall ([] : List Int) (.atom "?value") .empty)
      (result (trie (.node (some (.atom "?value")) [] : Trie SExpr Int))) := by
  rw [put_step_iff]
  rfl

theorem atom_payload_is_not_nullary_list :
    ¬ Step (engineBasePremises scalarRelations) language
      (putCall ([] : List Int) (.atom "value") .empty)
      (result (trie (.node (some (.list [.atom "value"])) [] : Trie SExpr Int))) := by
  rw [put_decoded_step_iff]
  simp [PlainBnfGraphNameTrie.put, PlainBnfGraphNameTrie.edgesOf]

theorem insufficient_depth_has_no_partial_value (key : List Scalar) (payload : SExpr)
    (index : Trie SExpr Scalar) (fuel : Nat) (insufficient : fuel ≤ putHeight key index) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (putCall key payload index) = [] := by
  rw [(put_answers fuel).1]
  simp [show ¬ putHeight key index < fuel by omega]

/-- A duplicated actual matching source occurrence produces two answers. The
singleton theorem depends on the admitted six-row family, not deduplication. -/
private def duplicateValueLanguage : LanguageDef :=
  { language with rewrites := language.rewrites ++ (language.rewrites.drop 1).take 1 }

theorem duplicate_matching_occurrence_is_observable (payload : SExpr) :
    rewriteAt (engineBasePremises scalarRelations) duplicateValueLanguage 1
      (putCall ([] : List Int) payload (.node none [])) =
      [result (trie (.node (some payload) [] : Trie SExpr Int)),
       result (trie (.node (some payload) [] : Trie SExpr Int))] := by
  rw [rewriteAt]
  simp [duplicateValueLanguage, source_rules_exact, observedRules, observedRule,
    applyRuleUsing, putCall, call, trie, name, value, result,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings]

#print axioms source_translation_exact
#print axioms put_answers
#print axioms put_step_iff
#print axioms edge_put_step_iff
#print axioms execution_lookup
#print axioms duplicate_matching_occurrence_is_observable

end Mettapedia.GSLT.Parsing.PlainBnfTrieOverwriteSourceExecution
