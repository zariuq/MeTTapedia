import Mettapedia.GSLT.Parsing.PlainBnfReferenceCollectionSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfReverseReferencesSourceExecution

/-!
# Authored outer reverse-index traversal

Discovery occurrences 52–53 execute the existing expression reference
collector, bucket-update family, and recursive definition traversal. Inputs
use the existing String-based structured expression and source-span carriers.
String names are connected explicitly to the existing Nat-scalar wire.
Arbitrary edited Integer expressions and physical execution are not covered.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfReverseIndexSourceExecution

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
open PlainBnfSourceRank (Rank)
open PlainBnfTrieSourceExecution (scalarRelations trie call result observedRule trie_injective result_injective)
open PlainBnfIndexedCollectorSourceExecution (headedBy premiseClosed closed_extension disjoint_heads_do_not_match)
open PlainBnfStructuredDenotation (Expression SourceSpan LexicalDeclaration)
open PlainBnfReferenceCollectionSourceExecution
  (text expression span declarations grammarReferences expressionCall expressionHeight)
open PlainBnfReverseReferencesSourceExecution (addCall addReferences addHeight bucketCons repeatNode dependents)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

def mode? (relation : String) : Option (Nat × Nat) :=
  match relation with
  | "BNFDiscoveryReverseIndexV1" => some (3, 1)
  | _ => (PlainBnfReferenceCollectionSourceExecution.mode? relation).or
      (PlainBnfReverseReferencesSourceExecution.mode? relation)

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

def outerRows : List Rewrite :=
  (PlainBnfCollectorSourceAdmission.discoverySource.rewrites.drop 52).take 2

def collectionRows : List Rewrite :=
  PlainBnfReferenceCollectionSourceExecution.appendRows ++
    PlainBnfReferenceCollectionSourceExecution.lookupRows ++
    PlainBnfReferenceCollectionSourceExecution.collectionRows

def rows : List Rewrite :=
  collectionRows ++ PlainBnfReverseReferencesSourceExecution.rows ++ outerRows

def rules? : Option (List RewriteRule) := rows.mapM lowerRule?
theorem rules_present : rules?.isSome = true := rfl

def language : LanguageDef :=
  { name := "PlainBnfAuthoredReverseIndex", types := [], terms := [], equations := [],
    rewrites := rules?.get rules_present }

def outerRules : List RewriteRule := (outerRows.mapM lowerRule?).get (by rfl)

theorem source_translation_exact : rows.mapM lowerRule? = some language.rewrites := rfl
theorem outer_occurrences_exact : outerRows.zipIdx 52 =
    ((PlainBnfCollectorSourceAdmission.discoverySource.rewrites.zipIdx).drop 52).take 2 := rfl
theorem exactly_forty_rules : language.rewrites.length = 40 := rfl

theorem language_partition : language.rewrites =
    PlainBnfReferenceCollectionSourceExecution.language.rewrites ++
      PlainBnfReverseReferencesSourceExecution.language.rewrites ++ outerRules := rfl

/-- These observations do not construct `language`; translation above reads
the actual source head and each of its three ordered recursive premises. -/
private def observedRules : List RewriteRule := [
  observedRule "bnf-discovery-reverse-index-nil-v1"
    (metta_sexpr% petta "(BNFDiscoveryReverseIndexV1 BNFDiscoveryDefinitionsNilV1 ?lexicals ?index)")
    (metta_sexpr% petta "(?index)"),
  observedRule "bnf-discovery-reverse-index-cons-v1"
    (metta_sexpr% petta "(BNFDiscoveryReverseIndexV1 (BNFDiscoveryDefinitionsConsV1 (BNFDiscoveryDefinitionV1 ?rank ?name ?expression ?span) ?tail) ?lexicals ?index)")
    (metta_sexpr% petta "(?result)")
    [.congruence (pattern (metta_sexpr% petta "(BNFCollectExpressionReferencesV1 ?expression ?lexicals)"))
       (pattern (metta_sexpr% petta "(?references)")),
     .congruence (pattern (metta_sexpr% petta "(BNFDiscoveryAddReferencesV1 ?references (BNFDiscoveryDefinitionV1 ?rank ?name ?expression ?span) ?index)"))
       (pattern (metta_sexpr% petta "(?next)")),
     .congruence (pattern (metta_sexpr% petta "(BNFDiscoveryReverseIndexV1 ?tail ?lexicals ?next)"))
       (pattern (metta_sexpr% petta "(?result)"))]]

private theorem outer_rules_exact : outerRules = observedRules := rfl
def outerHeads := ["BNFDiscoveryReverseIndexV1"]

private theorem outer_heads : outerRules.all (fun rule => headedBy outerHeads rule.left) = true := by
  simp [outer_rules_exact, observedRules, observedRule, headedBy, outerHeads,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode]

private theorem families_disjoint :
    List.Disjoint PlainBnfReferenceCollectionSourceExecution.relationHeads
      PlainBnfReverseReferencesSourceExecution.relationHeads := by
  simp [PlainBnfReferenceCollectionSourceExecution.relationHeads,
    PlainBnfReverseReferencesSourceExecution.relationHeads,
    PlainBnfIndexedCollectorSourceExecution.trieNames,
    PlainBnfReverseReferencesSourceExecution.putNames,
    PlainBnfReverseReferencesSourceExecution.referenceNames]

private theorem collection_outer_disjoint :
    List.Disjoint PlainBnfReferenceCollectionSourceExecution.relationHeads outerHeads := by
  simp [PlainBnfReferenceCollectionSourceExecution.relationHeads, outerHeads]

private theorem buckets_outer_disjoint :
    List.Disjoint PlainBnfReverseReferencesSourceExecution.relationHeads outerHeads := by
  simp [PlainBnfReverseReferencesSourceExecution.relationHeads,
    PlainBnfIndexedCollectorSourceExecution.trieNames,
    PlainBnfReverseReferencesSourceExecution.putNames,
    PlainBnfReverseReferencesSourceExecution.referenceNames, outerHeads]

theorem collection_conservative_extension (env : RelationEnv) (fuel : Nat) (source : Pattern)
    (headed : headedBy PlainBnfReferenceCollectionSourceExecution.relationHeads source = true) :
    rewriteAt (engineBasePremises env) language fuel source =
      rewriteAt (engineBasePremises env) PlainBnfReferenceCollectionSourceExecution.language fuel source := by
  apply closed_extension PlainBnfReferenceCollectionSourceExecution.relationHeads env
    PlainBnfReferenceCollectionSourceExecution.language language []
    (PlainBnfReverseReferencesSourceExecution.language.rewrites ++ outerRules)
    (by simpa [List.append_assoc] using language_partition) ?_ ?_ fuel source headed
  · intro rule member premise inside
    exact List.all_eq_true.mp
      (List.all_eq_true.mp PlainBnfReferenceCollectionSourceExecution.family_closed rule member) premise inside
  · intro rule member term termHead
    simp only [List.nil_append, List.mem_append] at member
    rcases member with member | member
    · exact disjoint_heads_do_not_match _ _ families_disjoint.symm _ _
        (List.all_eq_true.mp PlainBnfReverseReferencesSourceExecution.family_heads rule member) termHead
    · exact disjoint_heads_do_not_match _ _ collection_outer_disjoint.symm _ _
        (List.all_eq_true.mp outer_heads rule member) termHead

theorem buckets_conservative_extension (env : RelationEnv) (fuel : Nat) (source : Pattern)
    (headed : headedBy PlainBnfReverseReferencesSourceExecution.relationHeads source = true) :
    rewriteAt (engineBasePremises env) language fuel source =
      rewriteAt (engineBasePremises env) PlainBnfReverseReferencesSourceExecution.language fuel source := by
  apply closed_extension PlainBnfReverseReferencesSourceExecution.relationHeads env
    PlainBnfReverseReferencesSourceExecution.language language
    PlainBnfReferenceCollectionSourceExecution.language.rewrites outerRules language_partition ?_ ?_
    fuel source headed
  · intro rule member premise inside
    exact List.all_eq_true.mp
      (List.all_eq_true.mp PlainBnfReverseReferencesSourceExecution.family_closed rule member) premise inside
  · intro rule member term termHead
    rcases List.mem_append.mp member with member | member
    · exact disjoint_heads_do_not_match _ _ families_disjoint _ _
        (List.all_eq_true.mp PlainBnfReferenceCollectionSourceExecution.family_heads rule member) termHead
    · exact disjoint_heads_do_not_match _ _ buckets_outer_disjoint.symm _ _
        (List.all_eq_true.mp outer_heads rule member) termHead

private theorem outer_rewriteAt (env : RelationEnv) (fuel : Nat) (source : Pattern)
    (headed : headedBy outerHeads source = true) :
    rewriteAt (engineBasePremises env) language (fuel + 1) source =
      outerRules.flatMap (fun rule => applyRuleUsing (engineBasePremises env) language
        (rewriteAt (engineBasePremises env) language fuel) rule source) := by
  rw [rewriteAt, language_partition]
  simp only [List.flatMap_append]
  have noCollection : PlainBnfReferenceCollectionSourceExecution.language.rewrites.flatMap
      (fun rule => applyRuleUsing (engineBasePremises env) language
        (rewriteAt (engineBasePremises env) language fuel) rule source) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro rule member
    simp [applyRuleUsing, disjoint_heads_do_not_match _ _ collection_outer_disjoint _ _
      (List.all_eq_true.mp PlainBnfReferenceCollectionSourceExecution.family_heads rule member) headed]
  have noBuckets : PlainBnfReverseReferencesSourceExecution.language.rewrites.flatMap
      (fun rule => applyRuleUsing (engineBasePremises env) language
        (rewriteAt (engineBasePremises env) language fuel) rule source) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro rule member
    simp [applyRuleUsing, disjoint_heads_do_not_match _ _ buckets_outer_disjoint _ _
      (List.all_eq_true.mp PlainBnfReverseReferencesSourceExecution.family_heads rule member) headed]
  rw [noCollection, noBuckets]
  simp

abbrev Definition := PlainBnfDeclarationSemantics.Definition String Expression SourceSpan
abbrev Item := Rank × Definition

def key (value : String) : List Nat := value.toList.map Char.toNat

theorem key_injective : Function.Injective key := by
  intro left right same
  exact String.toList_injective ((List.map_inj_right (fun _ _ equal => Char.toNat_inj.mp equal)).mp same)

theorem text_wire (value : String) :
    text value = PlainBnfCollectorSourceExecution.name (key value) := rfl

theorem names_wire (values : List String) :
    PlainBnfReferenceCollectionSourceExecution.names values =
      PlainBnfReverseReferencesSourceExecution.names (values.map key) := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      simp [PlainBnfReferenceCollectionSourceExecution.names,
        PlainBnfReverseReferencesSourceExecution.names, text_wire, ih]

def node (item : Item) : SExpr :=
  PlainBnfHeapSourceExecution.rankedDefinition
    (item.1, ⟨text item.2.name, expression item.2.expression, span item.2.span⟩)

def nodes : List Item → SExpr
  | [] => .atom "BNFDiscoveryDefinitionsNilV1"
  | item :: rest => bucketCons (node item) (nodes rest)

def reverseCall (input : List Item) (lexicals : List LexicalDeclaration) (index : Trie SExpr) : Pattern :=
  call "BNFDiscoveryReverseIndexV1" [nodes input, declarations lexicals, trie index]

def referenceKeys (item : Item) (lexicals : List LexicalDeclaration) : List (List Nat) :=
  (grammarReferences item.2.expression lexicals).map key

def addDefinition (item : Item) (lexicals : List LexicalDeclaration) (index : Trie SExpr) : Trie SExpr :=
  addReferences (referenceKeys item lexicals) (node item) index

/-- Ordinary ordered definition fold; it does not define any source answer. -/
def reverseIndex (input : List Item) (lexicals : List LexicalDeclaration) (index : Trie SExpr) : Trie SExpr :=
  input.foldl (fun current item => addDefinition item lexicals current) index

theorem reverseIndex_nil (lexicals : List LexicalDeclaration) (index : Trie SExpr) :
    reverseIndex [] lexicals index = index := rfl

theorem reverseIndex_cons (item : Item) (rest : List Item) (lexicals : List LexicalDeclaration)
    (index : Trie SExpr) :
    reverseIndex (item :: rest) lexicals index = reverseIndex rest lexicals (addDefinition item lexicals index) := rfl

theorem collection_answers (fuel : Nat) (item : Item) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (expressionCall item.2.expression lexicals) =
      if expressionHeight item.2.expression lexicals < fuel then
        [result (PlainBnfReverseReferencesSourceExecution.names (referenceKeys item lexicals))] else [] := by
  rw [collection_conservative_extension _ fuel _ (by rfl),
    PlainBnfReferenceCollectionSourceExecution.expression_answers, names_wire]
  rfl

theorem buckets_answers (fuel : Nat) (item : Item) (lexicals : List LexicalDeclaration)
    (index : Trie SExpr) :
    rewriteAt (engineBasePremises scalarRelations) language fuel
      (addCall (referenceKeys item lexicals) (node item) index) =
      if addHeight (referenceKeys item lexicals) (node item) index < fuel then
        [result (trie (addDefinition item lexicals index))] else [] := by
  rw [buckets_conservative_extension _ fuel _ (by rfl), PlainBnfReverseReferencesSourceExecution.add_answers]
  rfl

private theorem reverse_nil (env : RelationEnv) (fuel : Nat)
    (lexicals : List LexicalDeclaration) (index : Trie SExpr) :
    rewriteAt (engineBasePremises env) language (fuel + 1) (reverseCall [] lexicals index) =
      [result (trie index)] := by
  rw [outer_rewriteAt env fuel _ (by rfl)]
  simp [outer_rules_exact, observedRules, observedRule, applyRuleUsing,
    reverseCall, nodes, call, result, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private theorem reverse_first_none (env : RelationEnv) (fuel : Nat) (item : Item) (rest : List Item)
    (lexicals : List LexicalDeclaration) (index : Trie SExpr)
    (first : rewriteAt (engineBasePremises env) language fuel
      (expressionCall item.2.expression lexicals) = []) :
    rewriteAt (engineBasePremises env) language (fuel + 1)
      (reverseCall (item :: rest) lexicals index) = [] := by
  rw [outer_rewriteAt env fuel _ (by rfl)]
  simp [outer_rules_exact, observedRules, observedRule, applyRuleUsing,
    reverseCall, nodes, node, PlainBnfHeapSourceExecution.rankedDefinition, bucketCons,
    call, pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing, applyBindings]
  simp only [expressionCall, call, encode, encodeList] at first
  rw [first]
  simp

private theorem reverse_second_none (env : RelationEnv) (fuel : Nat) (item : Item) (rest : List Item)
    (lexicals : List LexicalDeclaration) (index : Trie SExpr) (references : List (List Nat))
    (first : rewriteAt (engineBasePremises env) language fuel
      (expressionCall item.2.expression lexicals) =
      [result (PlainBnfReverseReferencesSourceExecution.names references)])
    (second : rewriteAt (engineBasePremises env) language fuel
      (addCall references (node item) index) = []) :
    rewriteAt (engineBasePremises env) language (fuel + 1)
      (reverseCall (item :: rest) lexicals index) = [] := by
  rw [outer_rewriteAt env fuel _ (by rfl)]
  simp [outer_rules_exact, observedRules, observedRule, applyRuleUsing,
    reverseCall, nodes, node, PlainBnfHeapSourceExecution.rankedDefinition, bucketCons,
    call, pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing, applyBindings]
  simp only [expressionCall, call, result, encode, encodeList] at first
  rw [first]
  simp [matchPattern, matchArgs, mergeBindings, List.foldlM]
  simp only [addCall, node, PlainBnfHeapSourceExecution.rankedDefinition, call, encode, encodeList] at second
  rw [second]
  simp

private theorem reverse_following (env : RelationEnv) (fuel : Nat) (item : Item) (rest : List Item)
    (lexicals : List LexicalDeclaration) (index next : Trie SExpr)
    (references : List (List Nat)) (answers : List SExpr)
    (first : rewriteAt (engineBasePremises env) language fuel
      (expressionCall item.2.expression lexicals) =
      [result (PlainBnfReverseReferencesSourceExecution.names references)])
    (second : rewriteAt (engineBasePremises env) language fuel
      (addCall references (node item) index) = [result (trie next)])
    (following : rewriteAt (engineBasePremises env) language fuel
      (reverseCall rest lexicals next) = answers.map result) :
    rewriteAt (engineBasePremises env) language (fuel + 1)
      (reverseCall (item :: rest) lexicals index) = answers.map result := by
  rw [outer_rewriteAt env fuel _ (by rfl)]
  simp [outer_rules_exact, observedRules, observedRule, applyRuleUsing,
    reverseCall, nodes, node, PlainBnfHeapSourceExecution.rankedDefinition, bucketCons,
    call, pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing, applyBindings]
  simp only [expressionCall, call, result, encode, encodeList] at first
  rw [first]
  simp [matchPattern, matchArgs, mergeBindings, List.foldlM]
  simp only [addCall, node, PlainBnfHeapSourceExecution.rankedDefinition, call, result, encode, encodeList] at second
  rw [second]
  simp [matchPattern, matchArgs, mergeBindings, List.foldlM]
  simp only [reverseCall, call, encode, encodeList] at following
  rw [following]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap, result, encode, encodeList]

/-- Maximum recursive-premise depth, not a bucket result provider. -/
def reverseHeight : List Item → List LexicalDeclaration → Trie SExpr → Nat
  | [], _, _ => 0
  | item :: rest, lexicals, index =>
      max (expressionHeight item.2.expression lexicals)
        (max (addHeight (referenceKeys item lexicals) (node item) index)
          (reverseHeight rest lexicals (addDefinition item lexicals index))) + 1

/-- The actual outer clauses and their dependencies return exactly the
ordinary fold's whole trie, once, at sufficient contextual depth. -/
theorem reverse_answers (fuel : Nat) (input : List Item) (lexicals : List LexicalDeclaration)
    (index : Trie SExpr) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (reverseCall input lexicals index) =
      if reverseHeight input lexicals index < fuel then
        [result (trie (reverseIndex input lexicals index))] else [] := by
  induction fuel generalizing input index with
  | zero => simp [rewriteAt]
  | succ fuel ih =>
    cases input with
    | nil => simpa [reverseHeight, reverseIndex_nil] using reverse_nil scalarRelations fuel lexicals index
    | cons item rest =>
      have first := collection_answers fuel item lexicals
      have second := buckets_answers fuel item lexicals index
      have following := ih rest (addDefinition item lexicals index)
      by_cases hfirst : expressionHeight item.2.expression lexicals < fuel
      · simp only [hfirst, ↓reduceIte] at first
        by_cases hsecond : addHeight (referenceKeys item lexicals) (node item) index < fuel
        · simp only [hsecond, ↓reduceIte] at second
          by_cases hfollowing : reverseHeight rest lexicals (addDefinition item lexicals index) < fuel
          · simp only [hfollowing, ↓reduceIte] at following
            have step := reverse_following scalarRelations fuel item rest lexicals index
              (addDefinition item lexicals index) (referenceKeys item lexicals)
              [trie (reverseIndex rest lexicals (addDefinition item lexicals index))]
              first second (by simpa using following)
            simpa [reverseHeight, Nat.add_lt_add_iff_right, max_lt_iff, hfirst, hsecond, hfollowing,
              reverseIndex_cons] using step
          · simp only [hfollowing, ↓reduceIte] at following
            have step := reverse_following scalarRelations fuel item rest lexicals index
              (addDefinition item lexicals index) (referenceKeys item lexicals) []
              first second (by simpa using following)
            simpa [reverseHeight, Nat.add_lt_add_iff_right, max_lt_iff, hfirst, hsecond, hfollowing] using step
        · simp only [hsecond, ↓reduceIte] at second
          have absent := reverse_second_none scalarRelations fuel item rest lexicals index
            (referenceKeys item lexicals) first second
          simpa [reverseHeight, Nat.add_lt_add_iff_right, max_lt_iff, hfirst, hsecond] using absent
      · simp only [hfirst, ↓reduceIte] at first
        have absent := reverse_first_none scalarRelations fuel item rest lexicals index first
        simpa [reverseHeight, Nat.add_lt_add_iff_right, max_lt_iff, hfirst] using absent

theorem reverse_step_iff (input : List Item) (lexicals : List LexicalDeclaration)
    (index : Trie SExpr) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language (reverseCall input lexicals index) target ↔
      target = result (trie (reverseIndex input lexicals index)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [reverse_answers] at member
    split at member
    · simpa using member
    · cases member
  · intro same
    subst target
    exact ⟨reverseHeight input lexicals index + 1, by simp [reverse_answers]⟩

theorem reverse_decoded_step_iff (input : List Item) (lexicals : List LexicalDeclaration)
    (before after : Trie SExpr) :
    Step (engineBasePremises scalarRelations) language (reverseCall input lexicals before)
      (result (trie after)) ↔ after = reverseIndex input lexicals before := by
  rw [reverse_step_iff]
  exact ⟨fun same => trie_injective (result_injective same), fun same => by rw [same]⟩

/-- The source-order node occurrence ledger for one referenced name. An
individual definition contributes one complete node per matching reference. -/
def occurrencesFor (input : List Item) (query : String) (lexicals : List LexicalDeclaration) : List SExpr :=
  input.flatMap fun item =>
    List.replicate ((grammarReferences item.2.expression lexicals).count query) (node item)

/-- Earlier occurrences are behind later ones because source bucket updates
prepend. A key with no new occurrences retains its original optional value. -/
def applyOccurrences (occurrences : List SExpr) (before : Option SExpr) : Option SExpr :=
  match occurrences with
  | [] => before
  | _ :: _ => some (occurrences.reverse.foldr bucketCons (dependents before))

theorem applyOccurrences_append (left right : List SExpr) (before : Option SExpr) :
    applyOccurrences (left ++ right) before = applyOccurrences right (applyOccurrences left before) := by
  cases left <;> cases right <;>
    simp [applyOccurrences, List.reverse_append, List.foldr_append, dependents]

theorem replicate_foldr (count : Nat) (node tail : SExpr) :
    (List.replicate count node).foldr bucketCons tail = repeatNode count node tail := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, repeatNode, ih]

theorem applyOccurrences_replicate (count : Nat) (node : SExpr) (before : Option SExpr) :
    applyOccurrences (List.replicate count node) before =
      if count = 0 then before else some (repeatNode count node (dependents before)) := by
  cases count with
  | zero => rfl
  | succ count =>
      simp [List.replicate_succ, applyOccurrences, List.foldr_append, replicate_foldr,
        repeatNode, PlainBnfReverseReferencesSourceExecution.repeatNode_cons]

theorem reference_count_wire (item : Item) (query : String) (lexicals : List LexicalDeclaration) :
    (referenceKeys item lexicals).count (key query) =
      (grammarReferences item.2.expression lexicals).count query := by
  exact List.count_map_of_injective _ key key_injective query

theorem lookup_addDefinition (item : Item) (query : String) (lexicals : List LexicalDeclaration)
    (index : Trie SExpr) :
    PlainBnfGraphNameTrie.lookup (key query) (addDefinition item lexicals index) =
      applyOccurrences
        (List.replicate ((grammarReferences item.2.expression lexicals).count query) (node item))
        (PlainBnfGraphNameTrie.lookup (key query) index) := by
  rw [addDefinition, PlainBnfReverseReferencesSourceExecution.lookup_addReferences,
    applyOccurrences_replicate, ← reference_count_wire]
  by_cases zero : (referenceKeys item lexicals).count (key query) = 0
  · have absent := List.count_eq_zero.mp zero
    simp [zero, absent]
  · have present : key query ∈ referenceKeys item lexicals := by
      by_contra absent
      exact zero (List.count_eq_zero.mpr absent)
    simp [zero, present]

/-- Exact bucket provenance, including duplicate occurrences and the original
tail. This observes the independent ordinary fold, not a second executor. -/
theorem lookup_reverseIndex (input : List Item) (query : String)
    (lexicals : List LexicalDeclaration) (index : Trie SExpr) :
    PlainBnfGraphNameTrie.lookup (key query) (reverseIndex input lexicals index) =
      applyOccurrences (occurrencesFor input query lexicals)
        (PlainBnfGraphNameTrie.lookup (key query) index) := by
  induction input generalizing index with
  | nil => rfl
  | cons item rest ih =>
      rw [reverseIndex_cons, ih, lookup_addDefinition]
      simp only [occurrencesFor, List.flatMap_cons, applyOccurrences_append]

theorem execution_bucket_provenance (input : List Item) (query : String)
    (lexicals : List LexicalDeclaration) (before after : Trie SExpr)
    (executed : Step (engineBasePremises scalarRelations) language
      (reverseCall input lexicals before) (result (trie after))) :
    PlainBnfGraphNameTrie.lookup (key query) after =
      applyOccurrences (occurrencesFor input query lexicals)
        (PlainBnfGraphNameTrie.lookup (key query) before) := by
  rw [reverse_decoded_step_iff] at executed
  rw [executed, lookup_reverseIndex]

theorem occurrence_count (input : List Item) (query : String) (lexicals : List LexicalDeclaration) :
    (occurrencesFor input query lexicals).length =
      (input.map fun item => (grammarReferences item.2.expression lexicals).count query).sum := by
  simp [occurrencesFor]

theorem absent_references_preserve_bucket (input : List Item) (query : String)
    (lexicals : List LexicalDeclaration) (index : Trie SExpr)
    (absent : ∀ item ∈ input, query ∉ grammarReferences item.2.expression lexicals) :
    PlainBnfGraphNameTrie.lookup (key query) (reverseIndex input lexicals index) =
      PlainBnfGraphNameTrie.lookup (key query) index := by
  rw [lookup_reverseIndex]
  have noOccurrences : occurrencesFor input query lexicals = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro item member
    simp [List.count_eq_zero.mpr (absent item member)]
  rw [noOccurrences]
  rfl

theorem lexical_name_has_no_bucket_occurrences (input : List Item) (query : String)
    (lexicals : List LexicalDeclaration)
    (lexical : lexicals.any (·.referenceName == query) = true) :
    occurrencesFor input query lexicals = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro item _
  have absent : query ∉ grammarReferences item.2.expression lexicals := by
    simp [grammarReferences, lexical]
  simp [List.count_eq_zero.mpr absent]

private def location : SourceSpan := ⟨0, 1⟩
private def repeatedExpression : Expression :=
  ⟨[⟨[.reference "β" location, .reference "β" location], location⟩], location⟩
private def followingExpression : Expression :=
  ⟨[⟨[.reference "β" location], location⟩], location⟩
private def firstItem : Item := (.zero, ⟨"first", repeatedExpression, location⟩)
private def secondItem : Item := (.one .zero, ⟨"second", followingExpression, location⟩)
private def specimen : List Item := [firstItem, secondItem]

theorem specimen_occurrences : occurrencesFor specimen "β" [] =
    [node firstItem, node firstItem, node secondItem] := rfl

theorem specimen_execution :
    Step (engineBasePremises scalarRelations) language (reverseCall specimen [] .empty)
      (result (trie (reverseIndex specimen [] .empty))) := by
  rw [reverse_step_iff]

theorem specimen_bucket :
    PlainBnfGraphNameTrie.lookup (key "β") (reverseIndex specimen [] .empty) =
      some (bucketCons (node secondItem)
        (bucketCons (node firstItem)
          (bucketCons (node firstItem) PlainBnfReverseReferencesSourceExecution.emptyBucket))) := by
  rw [lookup_reverseIndex, specimen_occurrences]
  rfl

theorem missing_duplicate_occurrence_refused (after : Trie SExpr)
    (missing : PlainBnfGraphNameTrie.lookup (key "β") after =
      some (bucketCons (node secondItem)
        (bucketCons (node firstItem) PlainBnfReverseReferencesSourceExecution.emptyBucket))) :
    ¬ Step (engineBasePremises scalarRelations) language (reverseCall specimen [] .empty)
      (result (trie after)) := by
  intro executed
  have exactBucket := execution_bucket_provenance specimen "β" [] .empty after executed
  rw [specimen_occurrences] at exactBucket
  change PlainBnfGraphNameTrie.lookup (key "β") after =
    some (bucketCons (node secondItem) (bucketCons (node firstItem)
      (bucketCons (node firstItem) PlainBnfReverseReferencesSourceExecution.emptyBucket))) at exactBucket
  have same := Option.some.inj (missing.symm.trans exactBucket)
  have next := (PlainBnfReverseReferencesSourceExecution.bucketCons_injective same).2
  have tail := (PlainBnfReverseReferencesSourceExecution.bucketCons_injective next).2
  exact PlainBnfReverseReferencesSourceExecution.bucketCons_ne_tail _ _ tail.symm

theorem reordered_definition_occurrences_refused (after : Trie SExpr)
    (reordered : PlainBnfGraphNameTrie.lookup (key "β") after =
      some (bucketCons (node firstItem) (bucketCons (node firstItem)
        (bucketCons (node secondItem) PlainBnfReverseReferencesSourceExecution.emptyBucket)))) :
    ¬ Step (engineBasePremises scalarRelations) language (reverseCall specimen [] .empty)
      (result (trie after)) := by
  intro executed
  have exactBucket := execution_bucket_provenance specimen "β" [] .empty after executed
  rw [specimen_occurrences] at exactBucket
  change PlainBnfGraphNameTrie.lookup (key "β") after =
    some (bucketCons (node secondItem) (bucketCons (node firstItem)
      (bucketCons (node firstItem) PlainBnfReverseReferencesSourceExecution.emptyBucket))) at exactBucket
  have same := Option.some.inj (reordered.symm.trans exactBucket)
  have different : node firstItem ≠ node secondItem := by
    intro equal
    have ranks := congrArg Prod.fst
      (PlainBnfHeapSourceExecution.ranked_definition_injective equal)
    cases ranks
  exact different (PlainBnfReverseReferencesSourceExecution.bucketCons_injective same).1

theorem spurious_bucket_refused (input : List Item) (query : String)
    (lexicals : List LexicalDeclaration) (before after : Trie SExpr) (payload : SExpr)
    (absent : ∀ item ∈ input, query ∉ grammarReferences item.2.expression lexicals)
    (missing : PlainBnfGraphNameTrie.lookup (key query) before = none)
    (spurious : PlainBnfGraphNameTrie.lookup (key query) after = some payload) :
    ¬ Step (engineBasePremises scalarRelations) language (reverseCall input lexicals before)
      (result (trie after)) := by
  intro executed
  have exactIndex := (reverse_decoded_step_iff input lexicals before after).mp executed
  have exactBucket := absent_references_preserve_bucket input query lexicals before absent
  rw [← exactIndex, missing, spurious] at exactBucket
  cases exactBucket

theorem empty_input_preserves_complete_index (lexicals : List LexicalDeclaration) (index : Trie SExpr) :
    Step (engineBasePremises scalarRelations) language (reverseCall [] lexicals index)
      (result (trie index)) := by
  rw [reverse_step_iff, reverseIndex_nil]

theorem insufficient_depth_has_no_partial_index (input : List Item) (lexicals : List LexicalDeclaration)
    (index : Trie SExpr) (fuel : Nat) (insufficient : fuel ≤ reverseHeight input lexicals index) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (reverseCall input lexicals index) = [] := by
  rw [reverse_answers]
  simp [show ¬ reverseHeight input lexicals index < fuel by omega]

theorem outer_mode_refuses_extra_field (input : List Item) (lexicals : List LexicalDeclaration)
    (index : Trie SExpr) (output extra : SExpr) :
    splitCall? (.list [.atom "BNFDiscoveryReverseIndexV1", nodes input, declarations lexicals,
      trie index, output, extra]) = none := rfl

#print axioms source_translation_exact
#print axioms collection_conservative_extension
#print axioms buckets_conservative_extension
#print axioms reverse_answers
#print axioms reverse_step_iff
#print axioms execution_bucket_provenance

end Mettapedia.GSLT.Parsing.PlainBnfReverseIndexSourceExecution
