import Mettapedia.GSLT.Parsing.PlainBnfTrieSourceExecution

/-!
# Authored indexed declaration collection

The collector and its recursive trie/reversal dependencies are translated
from the admitted source occurrences into the existing contextual semantics.
The same proofs cover Nat and signed Integer name components via the existing
source codecs; no duplicate collector or name representation is introduced.
Generated PeTTa execution and physical integer representation remain separate.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfIndexedCollectorSourceExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open SourceSExprPatternCodec (encode encodeList encode_injective)
open SourceSExprPatternInstantiation (pattern patternList applyBindings_encode)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

def collectorRules : List RewriteRule :=
  (PlainBnfCollectorSourceAdmission.family PlainBnfCollectorSourceAdmission.discoverySource).flatMap
    (fun row => (PlainBnfTrieSourceExecution.trieRule? row.1).toList)

def language : LanguageDef :=
  { name := "PlainBnfAuthoredIndexedCollector", types := [], terms := [], equations := [],
    rewrites := collectorRules ++ PlainBnfTrieSourceExecution.language.rewrites }

theorem collector_occurrences_exact :
    (PlainBnfCollectorSourceAdmission.family PlainBnfCollectorSourceAdmission.discoverySource).flatMap
      (fun row => (PlainBnfTrieSourceExecution.trieRule? row.1).toList.map (fun _ => row.2)) =
        List.range' 40 9 := by rfl

theorem source_rule_count : language.rewrites.length = 23 := by rfl

theorem source_family_translation_exact : language.rewrites =
    ((PlainBnfCollectorSourceAdmission.family PlainBnfCollectorSourceAdmission.discoverySource) ++
      (PlainBnfCollectorSourceAdmission.family PlainBnfCollectorSourceAdmission.indexSource)).flatMap
      (fun row => (PlainBnfTrieSourceExecution.trieRule? row.1).toList) := by
  simp only [language, collectorRules, List.flatMap_append,
    PlainBnfTrieSourceExecution.source_family_translation_exact]

theorem collector_rule_source_iff (rule : RewriteRule) : rule ∈ collectorRules ↔
    ∃ row occurrence,
      Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT.rawRewriteAt?
        PlainBnfCollectorSourceAdmission.discoverySyntax occurrence = some row ∧
      40 ≤ occurrence ∧ occurrence < 49 ∧ PlainBnfTrieSourceExecution.trieRule? row = some rule := by
  simp only [collectorRules, List.mem_flatMap, Option.mem_toList]
  constructor
  · rintro ⟨⟨row, occurrence⟩, member, translated⟩
    have admitted := (PlainBnfCollectorSourceAdmission.discovery_family_iff row occurrence).mp member
    exact ⟨row, occurrence, admitted.1, admitted.2.1, admitted.2.2, translated⟩
  · rintro ⟨row, occurrence, found, lower, upper, translated⟩
    exact ⟨(row, occurrence), (PlainBnfCollectorSourceAdmission.discovery_family_iff row occurrence).mpr
      ⟨found, lower, upper⟩, translated⟩

theorem source_rule_iff (rule : RewriteRule) : rule ∈ language.rewrites ↔
    (∃ row occurrence,
      Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT.rawRewriteAt?
        PlainBnfCollectorSourceAdmission.discoverySyntax occurrence = some row ∧
      40 ≤ occurrence ∧ occurrence < 49 ∧ PlainBnfTrieSourceExecution.trieRule? row = some rule) ∨
    (∃ row occurrence,
      Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT.rawRewriteAt?
        PlainBnfCollectorSourceAdmission.indexSyntax occurrence = some row ∧
      occurrence < 14 ∧ PlainBnfTrieSourceExecution.trieRule? row = some rule) := by
  simp only [language, List.mem_append, collector_rule_source_iff,
    PlainBnfTrieSourceExecution.source_rule_iff]

private def observation (ruleName : String) (input output : SExpr) (premises : List Premise := []) :=
  PlainBnfTrieSourceExecution.observedRule ruleName input output premises

private def observedCollector : List RewriteRule := [
  observation "bnf-discovery-collect-definitions-v1"
    (metta_sexpr% petta "(BNFDiscoveryCollectDefinitionsV1 ?entries)")
    (metta_sexpr% petta "(?definitions ?diagnostics ?index)")
    [.congruence (pattern (metta_sexpr% petta "(BNFDiscoveryCollectLoopV1 ?entries BNFGraphTrieEmptyV1 BNFDefinitionsNilV1)"))
      (pattern (metta_sexpr% petta "(?definitions ?diagnostics ?index)"))],
  observation "bnf-discovery-collect-nil-v1"
    (metta_sexpr% petta "(BNFDiscoveryCollectLoopV1 (metta-nullary bnf-v1:entries-nil) ?index ?reversed)")
    (metta_sexpr% petta "(?definitions BNFDiagnosticsNilV1 ?index)")
    [.congruence (pattern (metta_sexpr% petta "(BNFDiscoveryReverseDefinitionsV1 ?reversed BNFDefinitionsNilV1)"))
      (pattern (metta_sexpr% petta "(?definitions)"))],
  observation "bnf-discovery-collect-comment-v1"
    (metta_sexpr% petta "(BNFDiscoveryCollectLoopV1 (bnf-v1:entries-cons (bnf-v1:comment ?text ?span) ?tail) ?index ?reversed)")
    (metta_sexpr% petta "(?definitions ?diagnostics ?finalIndex)")
    [.congruence (pattern (metta_sexpr% petta "(BNFDiscoveryCollectLoopV1 ?tail ?index ?reversed)"))
      (pattern (metta_sexpr% petta "(?definitions ?diagnostics ?finalIndex)"))],
  observation "bnf-discovery-collect-blank-v1"
    (metta_sexpr% petta "(BNFDiscoveryCollectLoopV1 (bnf-v1:entries-cons (bnf-v1:blank ?span) ?tail) ?index ?reversed)")
    (metta_sexpr% petta "(?definitions ?diagnostics ?finalIndex)")
    [.congruence (pattern (metta_sexpr% petta "(BNFDiscoveryCollectLoopV1 ?tail ?index ?reversed)"))
      (pattern (metta_sexpr% petta "(?definitions ?diagnostics ?finalIndex)"))],
  observation "bnf-discovery-collect-rule-v1"
    (metta_sexpr% petta "(BNFDiscoveryCollectLoopV1 (bnf-v1:entries-cons (bnf-v1:rule ?name ?expression ?span) ?tail) ?index ?reversed)")
    (metta_sexpr% petta "(?definitions ?diagnostics ?finalIndex)")
    [.congruence (pattern (metta_sexpr% petta "(BNFGraphTrieLookupV1 ?name ?index)"))
      (pattern (metta_sexpr% petta "(?lookup)")),
     .congruence (pattern (metta_sexpr% petta "(BNFDiscoveryCollectAfterLookupV1 ?lookup (BNFDefinitionV1 ?name ?expression ?span) ?tail ?index ?reversed)"))
      (pattern (metta_sexpr% petta "(?definitions ?diagnostics ?finalIndex)"))],
  observation "bnf-discovery-collect-fresh-v1"
    (metta_sexpr% petta "(BNFDiscoveryCollectAfterLookupV1 BNFIndexMissingV1 (BNFDefinitionV1 ?name ?expression ?span) ?tail ?index ?reversed)")
    (metta_sexpr% petta "(?definitions ?diagnostics ?finalIndex)")
    [.congruence (pattern (metta_sexpr% petta "(BNFGraphTrieInsertFirstV1 ?name (BNFDefinitionFoundV1 ?expression ?span) ?index)"))
      (pattern (metta_sexpr% petta "(?next)")),
     .congruence (pattern (metta_sexpr% petta "(BNFDiscoveryCollectLoopV1 ?tail ?next (BNFDefinitionsConsV1 (BNFDefinitionV1 ?name ?expression ?span) ?reversed))"))
      (pattern (metta_sexpr% petta "(?definitions ?diagnostics ?finalIndex)"))],
  observation "bnf-discovery-collect-duplicate-v1"
    (metta_sexpr% petta "(BNFDiscoveryCollectAfterLookupV1 (BNFIndexFoundV1 (BNFDefinitionFoundV1 ?firstExpression ?firstSpan)) (BNFDefinitionV1 ?name ?expression ?span) ?tail ?index ?reversed)")
    (metta_sexpr% petta "(?definitions (BNFDiagnosticsConsV1 (BNFDuplicateDefinitionV1 ?name ?firstSpan ?span) ?following) ?finalIndex)")
    [.congruence (pattern (metta_sexpr% petta "(BNFDiscoveryCollectLoopV1 ?tail ?index ?reversed)"))
      (pattern (metta_sexpr% petta "(?definitions ?following ?finalIndex)"))],
  observation "bnf-discovery-reverse-definitions-nil-v1"
    (metta_sexpr% petta "(BNFDiscoveryReverseDefinitionsV1 BNFDefinitionsNilV1 ?result)")
    (metta_sexpr% petta "(?result)"),
  observation "bnf-discovery-reverse-definitions-cons-v1"
    (metta_sexpr% petta "(BNFDiscoveryReverseDefinitionsV1 (BNFDefinitionsConsV1 ?head ?tail) ?before)")
    (metta_sexpr% petta "(?after)")
    [.congruence (pattern (metta_sexpr% petta "(BNFDiscoveryReverseDefinitionsV1 ?tail (BNFDefinitionsConsV1 ?head ?before))"))
      (pattern (metta_sexpr% petta "(?after)"))]]

theorem collector_rules_exact : collectorRules = observedCollector := by rfl

/-- Only the outer encoded relation name is inspected. Arguments are not
evaluated or quotiented when establishing family noninterference. -/
def headedBy (names : List String) : Pattern → Bool
  | .apply "source-sexpr-list-v1"
      (.apply "source-sexpr-atom-v1" [.apply name []] :: _) => names.contains name
  | _ => false

theorem headedBy_applyBindings (names : List String) (bindings : Bindings) (source : Pattern)
    (headed : headedBy names source = true) :
    headedBy names (applyBindings bindings source) = true := by
  unfold headedBy at headed
  split at headed
  · simpa [applyBindings, headedBy] using headed
  · contradiction

private theorem base_language_independent (env : RelationEnv) (left right : LanguageDef)
    (bindings : Bindings) (premise : Premise) :
    engineBasePremises env left bindings premise = engineBasePremises env right bindings premise := by
  cases premise <;> rfl

/-- A syntactic closure test on existing premises, not an execution model. -/
def premiseClosed (names : List String) : Premise → Bool
  | .congruence source _ => headedBy names source
  | _ => true

private theorem premises_congr (names : List String) (env : RelationEnv)
    (left right : LanguageDef) (executeLeft executeRight : Pattern → List Pattern)
    (recursive : ∀ source, headedBy names source = true → executeLeft source = executeRight source)
    (premises : List Premise) (closed : ∀ premise ∈ premises, premiseClosed names premise = true)
    (bindings : Bindings) :
    premisesUsing (engineBasePremises env) left executeLeft premises bindings =
      premisesUsing (engineBasePremises env) right executeRight premises bindings := by
  induction premises generalizing bindings with
  | nil => rfl
  | cons premise rest ih =>
    have first : premiseStepUsing (engineBasePremises env) left executeLeft bindings premise =
        premiseStepUsing (engineBasePremises env) right executeRight bindings premise := by
      cases premise with
      | congruence source target =>
        simp only [premiseStepUsing]
        rw [recursive _ (headedBy_applyBindings names bindings source
          (closed (.congruence source target) (by simp))) ]
      | freshness condition => exact base_language_independent env left right bindings (.freshness condition)
      | relationQuery relation arguments =>
        exact base_language_independent env left right bindings (.relationQuery relation arguments)
      | forAll collection parameter body =>
        exact base_language_independent env left right bindings (.forAll collection parameter body)
    simp only [premisesUsing, first]
    apply List.flatMap_congr
    intro next _
    exact ih (fun p member => closed p (List.mem_cons_of_mem _ member)) next

theorem applyRule_congr (names : List String) (env : RelationEnv)
    (left right : LanguageDef) (executeLeft executeRight : Pattern → List Pattern)
    (recursive : ∀ source, headedBy names source = true → executeLeft source = executeRight source)
    (rule : RewriteRule) (closed : ∀ premise ∈ rule.premises, premiseClosed names premise = true)
    (source : Pattern) :
    applyRuleUsing (engineBasePremises env) left executeLeft rule source =
      applyRuleUsing (engineBasePremises env) right executeRight rule source := by
  simp only [applyRuleUsing, matchPatternForRule_eq_syntactic, applyBindingsForRule_eq_syntactic]
  apply List.flatMap_congr
  intro bindings _
  rw [premises_congr names env left right executeLeft executeRight recursive rule.premises closed]

/-- Ordered-list conservative extension for this existing contextual
evaluator. Closure and exclusion are discharged from the actual rows below. -/
theorem closed_extension (names : List String) (env : RelationEnv)
    (small large : LanguageDef) (before after : List RewriteRule)
    (partition : large.rewrites = before ++ small.rewrites ++ after)
    (closed : ∀ rule ∈ small.rewrites, ∀ premise ∈ rule.premises,
      premiseClosed names premise = true)
    (excluded : ∀ rule ∈ before ++ after, ∀ source, headedBy names source = true →
      matchPattern rule.left source = [])
    (fuel : Nat) (source : Pattern) (headed : headedBy names source = true) :
    rewriteAt (engineBasePremises env) large fuel source =
      rewriteAt (engineBasePremises env) small fuel source := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
    rw [rewriteAt, rewriteAt, partition]
    simp only [List.flatMap_append]
    have empty (rules : List RewriteRule) (included : ∀ rule ∈ rules, rule ∈ before ++ after) :
        rules.flatMap (fun rule => applyRuleUsing (engineBasePremises env) large
          (rewriteAt (engineBasePremises env) large fuel) rule source) = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro rule member
      simp [applyRuleUsing, excluded rule (included rule member) source headed]
    rw [empty before (fun rule member => List.mem_append_left _ member),
      empty after (fun rule member => List.mem_append_right _ member)]
    simp only [List.nil_append, List.append_nil]
    apply List.flatMap_congr
    intro rule member
    exact applyRule_congr names env large small _ _ ih rule (closed rule member) source

theorem disjoint_heads_do_not_match (leftNames rightNames : List String)
    (disjoint : List.Disjoint leftNames rightNames) (left right : Pattern)
    (leftHead : headedBy leftNames left = true) (rightHead : headedBy rightNames right = true) :
    matchPattern left right = [] := by
  unfold headedBy at leftHead rightHead
  split at leftHead
  · rename_i _ leftName leftArgs
    split at rightHead
    · rename_i _ rightName rightArgs
      have different : leftName ≠ rightName := by
        intro same
        subst rightName
        exact disjoint (by simpa using leftHead) (by simpa using rightHead)
      simp [matchPattern, matchArgs, different]
    · contradiction
  · contradiction

def trieNames : List String := ["BNFGraphTrieLookupV1", "BNFGraphTrieEdgeLookupV1",
  "BNFGraphTrieInsertFirstV1", "BNFGraphTrieEdgeInsertV1", "BNFGraphTrieFirstValueV1"]

def collectorNames : List String := ["BNFDiscoveryCollectDefinitionsV1", "BNFDiscoveryCollectLoopV1",
  "BNFDiscoveryCollectAfterLookupV1", "BNFDiscoveryReverseDefinitionsV1"]

theorem trie_closed : PlainBnfTrieSourceExecution.language.rewrites.all
    (fun rule => rule.premises.all (premiseClosed trieNames)) = true := by
  simp [PlainBnfTrieSourceExecution.source_rules_exact, premiseClosed, headedBy,
    PlainBnfTrieSourceExecution.observedRules, PlainBnfTrieSourceExecution.observedRule,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, trieNames, encode]

theorem collector_heads : collectorRules.all (fun rule => headedBy collectorNames rule.left) = true := by
  simp [collector_rules_exact, observedCollector, observation, PlainBnfTrieSourceExecution.observedRule,
    headedBy, pattern, patternList, SourceIntegerProvider.sourceVariableToken, collectorNames, encode]

theorem trie_collector_names_disjoint : List.Disjoint collectorNames trieNames := by
  simp [collectorNames, trieNames, List.disjoint_left]

theorem trie_conservative_extension (fuel : Nat) (source : Pattern)
    (headed : headedBy trieNames source = true) :
    rewriteAt (engineBasePremises PlainBnfTrieSourceExecution.scalarRelations) language fuel source =
      rewriteAt (engineBasePremises PlainBnfTrieSourceExecution.scalarRelations)
        PlainBnfTrieSourceExecution.language fuel source := by
  apply closed_extension trieNames _ _ _ collectorRules []
  · simp [language]
  · intro rule member premise present
    exact List.all_eq_true.mp (List.all_eq_true.mp trie_closed rule member) premise present
  · intro rule member source headed
    simp only [List.append_nil] at member
    exact disjoint_heads_do_not_match collectorNames trieNames trie_collector_names_disjoint _ _
      (List.all_eq_true.mp collector_heads rule member) headed
  · exact headed

def reversalNames : List String := ["BNFDiscoveryReverseDefinitionsV1"]

def nonReversalNames : List String := collectorNames.take 3 ++ trieNames

theorem reversal_partition : language.rewrites = collectorRules.take 7 ++
    PlainBnfCollectorSourceExecution.reversalLanguage.rewrites ++
    PlainBnfTrieSourceExecution.language.rewrites := by rfl

theorem reversal_closed : PlainBnfCollectorSourceExecution.reversalLanguage.rewrites.all
    (fun rule => rule.premises.all (premiseClosed reversalNames)) = true := by
  change (observedCollector.drop 7).all (fun rule => rule.premises.all (premiseClosed reversalNames)) = true
  simp [observedCollector, observation, PlainBnfTrieSourceExecution.observedRule,
    premiseClosed, headedBy, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    reversalNames, encode]

theorem nonReversal_heads :
    (collectorRules.take 7 ++ PlainBnfTrieSourceExecution.language.rewrites).all
      (fun rule => headedBy nonReversalNames rule.left) = true := by
  simp [collector_rules_exact, observedCollector, observation,
    PlainBnfTrieSourceExecution.source_rules_exact, PlainBnfTrieSourceExecution.observedRules,
    PlainBnfTrieSourceExecution.observedRule, headedBy, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, nonReversalNames, collectorNames, trieNames, encode]

theorem reversal_names_disjoint : List.Disjoint nonReversalNames reversalNames := by
  simp [nonReversalNames, reversalNames, collectorNames, trieNames]

theorem reversal_conservative_extension (fuel : Nat) (source : Pattern)
    (headed : headedBy reversalNames source = true) :
    rewriteAt (engineBasePremises PlainBnfTrieSourceExecution.scalarRelations) language fuel source =
      rewriteAt (engineBasePremises PlainBnfTrieSourceExecution.scalarRelations)
        PlainBnfCollectorSourceExecution.reversalLanguage fuel source := by
  apply closed_extension reversalNames _ _ _ (collectorRules.take 7)
    PlainBnfTrieSourceExecution.language.rewrites reversal_partition
  · intro rule member premise present
    exact List.all_eq_true.mp (List.all_eq_true.mp reversal_closed rule member) premise present
  · intro rule member source headed
    exact disjoint_heads_do_not_match nonReversalNames reversalNames reversal_names_disjoint _ _
      (List.all_eq_true.mp nonReversal_heads rule member) headed
  · exact headed

abbrev Name (Scalar : Type := Nat) := List Scalar
abbrev Index (Scalar : Type := Nat) := PlainBnfTrieDeclarationCollector.Index SExpr SExpr Scalar
abbrev Definition (Scalar : Type := Nat) := PlainBnfDeclarationSemantics.Definition (Name Scalar) SExpr SExpr
abbrev Entry (Scalar : Type := Nat) := PlainBnfDeclarationSemantics.Entry (Name Scalar) SExpr SExpr SExpr
abbrev Diagnostic (Scalar : Type := Nat) := PlainBnfDeclarationSemantics.Diagnostic (Name Scalar) SExpr

variable {Scalar : Type} [DecidableEq Scalar]

def payload (pair : SExpr × SExpr) : SExpr :=
  .list [.atom "BNFDefinitionFoundV1", pair.1, pair.2]

theorem payload_injective : Function.Injective payload := by
  rintro ⟨expression, span⟩ ⟨other, location⟩ same
  simp only [payload, SExpr.list.injEq, List.cons.injEq, and_true, true_and] at same
  exact Prod.ext same.1 same.2

mutual
  def indexTrie : (Index Scalar) → PlainBnfGraphNameTrie.Trie SExpr Scalar
    | .empty => .empty
    | .node value children => .node (value.map payload) (indexEdges children)

  def indexEdges : List (Scalar × (Index Scalar)) → List (Scalar × PlainBnfGraphNameTrie.Trie SExpr Scalar)
    | [] => []
    | (head, child) :: rest => (head, indexTrie child) :: indexEdges rest
end

omit [DecidableEq Scalar] in
private theorem index_value (index : (Index Scalar)) :
    PlainBnfGraphNameTrie.valueAt (indexTrie index) =
      (PlainBnfGraphNameTrie.valueAt index).map payload := by cases index <;> rfl

omit [DecidableEq Scalar] in
private theorem index_edges (index : (Index Scalar)) :
    PlainBnfGraphNameTrie.edgesOf (indexTrie index) =
      indexEdges (PlainBnfGraphNameTrie.edgesOf index) := by cases index <;> rfl

private theorem index_child (head : Scalar) (children : List (Scalar × (Index Scalar))) :
    PlainBnfGraphNameTrie.childFor head (indexEdges children) =
      indexTrie (PlainBnfGraphNameTrie.childFor head children) := by
  induction children with
  | nil => rfl
  | cons edge rest ih =>
    rcases edge with ⟨stored, child⟩
    by_cases same : head = stored <;> simp [indexEdges, PlainBnfGraphNameTrie.childFor, same, ih]

theorem index_lookup (key : (Name Scalar)) (index : (Index Scalar)) :
    PlainBnfGraphNameTrie.lookup key (indexTrie index) =
      (PlainBnfGraphNameTrie.lookup key index).map payload := by
  induction key generalizing index with
  | nil => exact index_value index
  | cons head tail ih =>
    simp only [PlainBnfGraphNameTrie.lookup, index_edges, index_child, ih]

private theorem index_update (head : Scalar) (update : (Index Scalar) → (Index Scalar))
    (other : PlainBnfGraphNameTrie.Trie SExpr Scalar → PlainBnfGraphNameTrie.Trie SExpr Scalar)
    (commutes : ∀ child, indexTrie (update child) = other (indexTrie child))
    (children : List (Scalar × (Index Scalar))) :
    indexEdges (PlainBnfGraphNameTrie.updateChild head update children) =
      PlainBnfGraphNameTrie.updateChild head other (indexEdges children) := by
  induction children with
  | nil => simp [PlainBnfGraphNameTrie.updateChild, indexEdges, commutes, indexTrie]
  | cons edge rest ih =>
    rcases edge with ⟨stored, child⟩
    by_cases same : head = stored <;>
      simp [PlainBnfGraphNameTrie.updateChild, indexEdges, same, commutes, ih]

theorem index_insert (key : (Name Scalar)) (pair : SExpr × SExpr) (index : (Index Scalar)) :
    indexTrie (PlainBnfGraphNameTrie.insertFirst key pair index) =
      PlainBnfGraphNameTrie.insertFirst key (payload pair) (indexTrie index) := by
  induction key generalizing index with
  | nil =>
    cases index with
    | empty => rfl
    | node value children =>
      cases value <;> rfl
  | cons head tail ih =>
    cases index with
    | empty =>
      simpa [PlainBnfGraphNameTrie.insertFirst, PlainBnfGraphNameTrie.valueAt,
        PlainBnfGraphNameTrie.edgesOf, indexTrie, indexEdges, PlainBnfGraphNameTrie.updateChild]
        using congrArg (fun next => PlainBnfGraphNameTrie.Trie.node none [(head, next)])
          (ih (.empty : (Index Scalar)))
    | node value children =>
      simp only [PlainBnfGraphNameTrie.insertFirst, PlainBnfGraphNameTrie.valueAt,
        PlainBnfGraphNameTrie.edgesOf, indexTrie]
      rw [index_update head _ _ ih]

open PlainBnfCollectorSourceExecution (entries definitions definition diagnostics name)
open PlainBnfTrieSourceExecution (call result value scalarRelations)

variable [PlainBnfCollectorSourceExecution.NameScalarCodec Scalar]

def encodeIndex (index : (Index Scalar)) : SExpr := PlainBnfTrieSourceExecution.trie (indexTrie index)

def loopCall (input : List (Entry Scalar)) (index : (Index Scalar)) (reversed : List (Definition Scalar)) : Pattern :=
  call "BNFDiscoveryCollectLoopV1" [entries input, encodeIndex index, definitions (reversed.map definition)]

def collectCall (input : List (Entry Scalar)) : Pattern := call "BNFDiscoveryCollectDefinitionsV1" [entries input]

def afterCall (found : Option (SExpr × SExpr)) (item : (Definition Scalar)) (tail : List (Entry Scalar))
    (index : (Index Scalar)) (reversed : List (Definition Scalar)) : Pattern :=
  call "BNFDiscoveryCollectAfterLookupV1" [value (found.map payload), definition item,
    entries tail, encodeIndex index, definitions (reversed.map definition)]

def packet (outputs : (SExpr × SExpr) × SExpr) : Pattern :=
  encode (.list [outputs.1.1, outputs.1.2, outputs.2])

def resultData (output : (List (Definition Scalar) × List (Diagnostic Scalar)) × (Index Scalar)) : (SExpr × SExpr) × SExpr :=
  ((definitions (output.1.1.map definition), diagnostics output.1.2), encodeIndex output.2)

def encodeResult (output : (List (Definition Scalar) × List (Diagnostic Scalar)) × (Index Scalar)) : Pattern := packet (resultData output)

private theorem trie_heads : PlainBnfTrieSourceExecution.language.rewrites.all
    (fun rule => headedBy trieNames rule.left) = true := by
  simp [PlainBnfTrieSourceExecution.source_rules_exact, PlainBnfTrieSourceExecution.observedRules,
    PlainBnfTrieSourceExecution.observedRule, headedBy, trieNames, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, encode]

private theorem collector_rewriteAt (fuel : Nat) (source : Pattern)
    (headed : headedBy collectorNames source = true) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1) source =
      collectorRules.flatMap (fun rule => applyRuleUsing (engineBasePremises scalarRelations) language
        (rewriteAt (engineBasePremises scalarRelations) language fuel) rule source) := by
  rw [rewriteAt]
  change (collectorRules ++ PlainBnfTrieSourceExecution.language.rewrites).flatMap _ = _
  rw [List.flatMap_append]
  have noTrie : PlainBnfTrieSourceExecution.language.rewrites.flatMap
      (fun rule => applyRuleUsing (engineBasePremises scalarRelations) language
        (rewriteAt (engineBasePremises scalarRelations) language fuel) rule source) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro rule member
    have absent := disjoint_heads_do_not_match trieNames collectorNames
      trie_collector_names_disjoint.symm _ _ (List.all_eq_true.mp trie_heads rule member) headed
    simp [applyRuleUsing, absent]
  rw [noTrie, List.append_nil]

theorem lookup_answers (fuel : Nat) (key : (Name Scalar)) (index : (Index Scalar)) :
    rewriteAt (engineBasePremises scalarRelations) language fuel
        (PlainBnfTrieSourceExecution.lookupCall key (indexTrie index)) =
      if PlainBnfTrieSourceExecution.lookupHeight key (indexTrie index) < fuel then
        [result (value ((PlainBnfGraphNameTrie.lookup key index).map payload))] else [] := by
  rw [trie_conservative_extension fuel _ (by
    simp [PlainBnfTrieSourceExecution.lookupCall, call, encode, encodeList, headedBy, trieNames])]
  rw [(PlainBnfTrieSourceExecution.lookup_answers fuel).1, index_lookup]

theorem insert_answers (fuel : Nat) (key : (Name Scalar)) (pair : SExpr × SExpr) (index : (Index Scalar)) :
    rewriteAt (engineBasePremises scalarRelations) language fuel
        (PlainBnfTrieSourceExecution.insertCall key (payload pair) (indexTrie index)) =
      if PlainBnfTrieSourceExecution.insertHeight key (indexTrie index) < fuel then
        [result (encodeIndex (PlainBnfGraphNameTrie.insertFirst key pair index))] else [] := by
  rw [trie_conservative_extension fuel _ (by
    simp [PlainBnfTrieSourceExecution.insertCall, call, encode, encodeList, headedBy, trieNames])]
  rw [(PlainBnfTrieSourceExecution.insert_answers fuel).1, ← index_insert]
  rfl

theorem reversal_answers (fuel : Nat) (reversed before : List SExpr) :
    rewriteAt (engineBasePremises scalarRelations) language fuel
        (encode (PlainBnfCollectorSourceExecution.reverseCall reversed before)) =
      if reversed.length < fuel then
        [encode (PlainBnfCollectorSourceExecution.resultTuple (List.reverseAux reversed before))] else [] := by
  rw [reversal_conservative_extension fuel _ (by
    simp [PlainBnfCollectorSourceExecution.reverseCall, encode, encodeList, headedBy, reversalNames])]
  exact PlainBnfCollectorSourceExecution.reversal_rewriteAt _ _ _ _

omit [DecidableEq Scalar] in
private theorem entry_rewriteAt (fuel : Nat) (input : List (Entry Scalar))
    (answers : List ((SExpr × SExpr) × SExpr))
    (recursive : rewriteAt (engineBasePremises scalarRelations) language fuel
      (loopCall input .empty []) = answers.map packet) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1) (collectCall input) =
      answers.map packet := by
  rw [collector_rewriteAt fuel _ (by simp [collectCall, call, encode, encodeList, headedBy, collectorNames])]
  simp [collector_rules_exact, observedCollector, observation, PlainBnfTrieSourceExecution.observedRule,
    applyRuleUsing, collectCall, call, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings]
  simp [loopCall, call, encode, encodeList, encodeIndex, indexTrie, PlainBnfTrieSourceExecution.trie,
    definitions] at recursive
  rw [recursive]
  simp [List.flatMap_map, packet, encode, encodeList, matchPattern, matchArgs, List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap, packet, encode, encodeList]

omit [DecidableEq Scalar] in
private theorem comment_rewriteAt (fuel : Nat) (text span : SExpr) (tail : List (Entry Scalar))
    (index : (Index Scalar)) (reversed : List (Definition Scalar)) (answers : List ((SExpr × SExpr) × SExpr))
    (recursive : rewriteAt (engineBasePremises scalarRelations) language fuel
      (loopCall tail index reversed) = answers.map packet) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (loopCall (.comment text span :: tail) index reversed) = answers.map packet := by
  rw [collector_rewriteAt fuel _ (by simp [loopCall, call, encode, encodeList, headedBy, collectorNames])]
  simp [collector_rules_exact, observedCollector, observation, PlainBnfTrieSourceExecution.observedRule,
    applyRuleUsing, loopCall, entries, PlainBnfCollectorSourceExecution.entry, call,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings]
  simp [loopCall, call, encode, encodeList] at recursive
  rw [recursive]
  simp [List.flatMap_map, packet, encode, encodeList, matchPattern, matchArgs, List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap, packet, encode, encodeList]

omit [DecidableEq Scalar] in
private theorem blank_rewriteAt (fuel : Nat) (span : SExpr) (tail : List (Entry Scalar))
    (index : (Index Scalar)) (reversed : List (Definition Scalar)) (answers : List ((SExpr × SExpr) × SExpr))
    (recursive : rewriteAt (engineBasePremises scalarRelations) language fuel
      (loopCall tail index reversed) = answers.map packet) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (loopCall (.blank span :: tail) index reversed) = answers.map packet := by
  rw [collector_rewriteAt fuel _ (by simp [loopCall, call, encode, encodeList, headedBy, collectorNames])]
  simp [collector_rules_exact, observedCollector, observation, PlainBnfTrieSourceExecution.observedRule,
    applyRuleUsing, loopCall, entries, PlainBnfCollectorSourceExecution.entry, call,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings]
  simp [loopCall, call, encode, encodeList] at recursive
  rw [recursive]
  simp [List.flatMap_map, packet, encode, encodeList, matchPattern, matchArgs, List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap, packet, encode, encodeList]

omit [DecidableEq Scalar] in
private theorem nil_rewriteAt (fuel : Nat) (index : (Index Scalar)) (reversed : List (Definition Scalar))
    (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises scalarRelations) language fuel
      (encode (PlainBnfCollectorSourceExecution.reverseCall (reversed.map definition) [])) =
        answers.map result) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1) (loopCall [] index reversed) =
      answers.map (fun ordered => packet ((ordered, .atom "BNFDiagnosticsNilV1"), encodeIndex index)) := by
  rw [collector_rewriteAt fuel _ (by simp [loopCall, call, encode, encodeList, headedBy, collectorNames])]
  simp [collector_rules_exact, observedCollector, observation, PlainBnfTrieSourceExecution.observedRule,
    applyRuleUsing, loopCall, entries, call, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings]
  simp [PlainBnfCollectorSourceExecution.reverseCall, definitions, encode, encodeList] at recursive
  rw [recursive]
  simp [List.flatMap_map, result, packet, encode, encodeList, matchPattern, matchArgs, List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap]

omit [DecidableEq Scalar] in
private theorem rule_rewriteAt (fuel : Nat) (item : (Definition Scalar)) (tail : List (Entry Scalar))
    (index : (Index Scalar)) (reversed : List (Definition Scalar)) (found : Option (SExpr × SExpr))
    (answers : List ((SExpr × SExpr) × SExpr))
    (queried : rewriteAt (engineBasePremises scalarRelations) language fuel
      (PlainBnfTrieSourceExecution.lookupCall item.name (indexTrie index)) = [result (value (found.map payload))])
    (recursive : rewriteAt (engineBasePremises scalarRelations) language fuel
      (afterCall found item tail index reversed) = answers.map packet) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (loopCall (.rule item.name item.expression item.span :: tail) index reversed) = answers.map packet := by
  rw [collector_rewriteAt fuel _ (by simp [loopCall, call, encode, encodeList, headedBy, collectorNames])]
  simp [collector_rules_exact, observedCollector, observation, PlainBnfTrieSourceExecution.observedRule,
    applyRuleUsing, loopCall, entries, PlainBnfCollectorSourceExecution.entry, call,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings]
  simp [PlainBnfTrieSourceExecution.lookupCall, call, encode, encodeList] at queried
  rw [show encodeIndex index = PlainBnfTrieSourceExecution.trie (indexTrie index) by rfl, queried]
  simp [result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]
  simp [afterCall, definition, call, encode, encodeList, encodeIndex] at recursive
  rw [recursive]
  simp [List.flatMap_map, packet, encode, encodeList, matchPattern, matchArgs, List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap, packet, encode, encodeList]

omit [DecidableEq Scalar] in
private theorem rule_query_exhausted (fuel : Nat) (item : (Definition Scalar)) (tail : List (Entry Scalar))
    (index : (Index Scalar)) (reversed : List (Definition Scalar))
    (queried : rewriteAt (engineBasePremises scalarRelations) language fuel
      (PlainBnfTrieSourceExecution.lookupCall item.name (indexTrie index)) = []) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (loopCall (.rule item.name item.expression item.span :: tail) index reversed) = [] := by
  rw [collector_rewriteAt fuel _ (by simp [loopCall, call, encode, encodeList, headedBy, collectorNames])]
  simp [collector_rules_exact, observedCollector, observation, PlainBnfTrieSourceExecution.observedRule,
    applyRuleUsing, loopCall, entries, PlainBnfCollectorSourceExecution.entry, call,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings]
  simp [PlainBnfTrieSourceExecution.lookupCall, call, encode, encodeList] at queried
  rw [show encodeIndex index = PlainBnfTrieSourceExecution.trie (indexTrie index) by rfl, queried]
  simp

omit [DecidableEq Scalar] in
private theorem fresh_rewriteAt (fuel : Nat) (item : (Definition Scalar)) (tail : List (Entry Scalar))
    (index next : (Index Scalar)) (reversed : List (Definition Scalar)) (answers : List ((SExpr × SExpr) × SExpr))
    (inserted : rewriteAt (engineBasePremises scalarRelations) language fuel
      (PlainBnfTrieSourceExecution.insertCall item.name (payload (item.expression, item.span))
        (indexTrie index)) = [result (encodeIndex next)])
    (recursive : rewriteAt (engineBasePremises scalarRelations) language fuel
      (loopCall tail next (item :: reversed)) = answers.map packet) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (afterCall none item tail index reversed) = answers.map packet := by
  rw [collector_rewriteAt fuel _ (by simp [afterCall, call, encode, encodeList, headedBy, collectorNames])]
  simp [collector_rules_exact, observedCollector, observation, PlainBnfTrieSourceExecution.observedRule,
    applyRuleUsing, afterCall, definition, value, call,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings]
  simp [PlainBnfTrieSourceExecution.insertCall, payload, call, encode, encodeList] at inserted
  rw [show encodeIndex index = PlainBnfTrieSourceExecution.trie (indexTrie index) by rfl, inserted]
  simp [result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]
  simp [loopCall, definitions, definition, call, encode, encodeList] at recursive
  rw [recursive]
  simp [List.flatMap_map, packet, encode, encodeList, matchPattern, matchArgs, List.foldlM, mergeBindings]
  simp [← List.map_eq_flatMap, packet, encode, encodeList]

omit [DecidableEq Scalar] in
private theorem fresh_insert_exhausted (fuel : Nat) (item : (Definition Scalar)) (tail : List (Entry Scalar))
    (index : (Index Scalar)) (reversed : List (Definition Scalar))
    (inserted : rewriteAt (engineBasePremises scalarRelations) language fuel
      (PlainBnfTrieSourceExecution.insertCall item.name (payload (item.expression, item.span))
        (indexTrie index)) = []) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (afterCall none item tail index reversed) = [] := by
  rw [collector_rewriteAt fuel _ (by simp [afterCall, call, encode, encodeList, headedBy, collectorNames])]
  simp [collector_rules_exact, observedCollector, observation, PlainBnfTrieSourceExecution.observedRule,
    applyRuleUsing, afterCall, definition, value, call,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings]
  simp [PlainBnfTrieSourceExecution.insertCall, payload, call, encode, encodeList] at inserted
  rw [show encodeIndex index = PlainBnfTrieSourceExecution.trie (indexTrie index) by rfl, inserted]
  simp

omit [DecidableEq Scalar] in
private theorem duplicate_rewriteAt (fuel : Nat) (item : (Definition Scalar)) (tail : List (Entry Scalar))
    (index : (Index Scalar)) (reversed : List (Definition Scalar)) (firstExpression firstSpan : SExpr)
    (answers : List ((SExpr × SExpr) × SExpr))
    (recursive : rewriteAt (engineBasePremises scalarRelations) language fuel
      (loopCall tail index reversed) = answers.map packet) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (afterCall (some (firstExpression, firstSpan)) item tail index reversed) =
      answers.map (fun output => packet ((output.1.1,
        .list [.atom "BNFDiagnosticsConsV1", PlainBnfCollectorSourceExecution.diagnostic
          (.duplicate item.name firstSpan item.span), output.1.2]), output.2)) := by
  rw [collector_rewriteAt fuel _ (by simp [afterCall, call, encode, encodeList, headedBy, collectorNames])]
  simp [collector_rules_exact, observedCollector, observation, PlainBnfTrieSourceExecution.observedRule,
    applyRuleUsing, afterCall, definition, value, payload, call,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings]
  simp [loopCall, call, encode, encodeList] at recursive
  rw [recursive]
  simp [List.flatMap_map, packet, encode, encodeList, matchPattern, matchArgs, List.foldlM, mergeBindings,
    PlainBnfCollectorSourceExecution.diagnostic]
  simp [← List.map_eq_flatMap]

/-- The after-lookup branch of the existing finite collector, stated also for
an explicitly supplied typed lookup result. -/
def afterMeaning (found : Option (SExpr × SExpr)) (item : (Definition Scalar)) (tail : List (Entry Scalar))
    (index : (Index Scalar)) (reversed : List (Definition Scalar)) : (List (Definition Scalar) × List (Diagnostic Scalar)) × (Index Scalar) :=
  match found with
  | none => PlainBnfTrieDeclarationCollector.collectLoop tail
      (PlainBnfGraphNameTrie.insertFirst item.name (item.expression, item.span) index) (item :: reversed)
  | some (_, firstSpan) =>
      let rest := PlainBnfTrieDeclarationCollector.collectLoop tail index reversed
      ((rest.1.1, .duplicate item.name firstSpan item.span :: rest.1.2), rest.2)

mutual
  def loopHeight : List (Entry Scalar) → (Index Scalar) → List (Definition Scalar) → Nat
    | [], _, reversed => 1 + reversed.length
    | .comment _ _ :: tail, index, reversed => 1 + loopHeight tail index reversed
    | .blank _ :: tail, index, reversed => 1 + loopHeight tail index reversed
    | .rule key expression span :: tail, index, reversed =>
        1 + max (PlainBnfTrieSourceExecution.lookupHeight key (indexTrie index))
          (afterHeight (PlainBnfGraphNameTrie.lookup key index) ⟨key, expression, span⟩ tail index reversed)
  termination_by input _ _ => 2 * input.length

  def afterHeight (found : Option (SExpr × SExpr)) (item : (Definition Scalar)) (tail : List (Entry Scalar))
      (index : (Index Scalar)) (reversed : List (Definition Scalar)) : Nat :=
    match found with
    | none => 1 + max (PlainBnfTrieSourceExecution.insertHeight item.name (indexTrie index))
        (loopHeight tail (PlainBnfGraphNameTrie.insertFirst item.name (item.expression, item.span) index)
          (item :: reversed))
    | some _ => 1 + loopHeight tail index reversed
  termination_by 2 * tail.length + 1
end

/-- Every answer occurrence for the loop and its after-lookup continuation.
Insufficient contextual depth returns no result, not a partial declaration
list or a negative grammar verdict. -/
theorem collector_answers (fuel : Nat) :
    (∀ (input : List (Entry Scalar)) (index : Index Scalar) reversed,
      rewriteAt (engineBasePremises scalarRelations) language fuel (loopCall input index reversed) =
        if loopHeight input index reversed < fuel then
          [encodeResult (PlainBnfTrieDeclarationCollector.collectLoop input index reversed)] else []) ∧
    (∀ found (item : Definition Scalar) tail (index : Index Scalar) reversed,
      rewriteAt (engineBasePremises scalarRelations) language fuel (afterCall found item tail index reversed) =
        if afterHeight found item tail index reversed < fuel then
          [encodeResult (afterMeaning found item tail index reversed)] else []) := by
  induction fuel with
  | zero => constructor <;> intros <;> simp [rewriteAt]
  | succ fuel ih =>
    constructor
    · intro input index reversed
      cases input with
      | nil =>
        by_cases enough : reversed.length < fuel
        · have recursive := reversal_answers fuel (reversed.map definition) []
          simp only [List.length_map, enough, ↓reduceIte] at recursive
          have step := nil_rewriteAt fuel index reversed
            [definitions (List.reverseAux (reversed.map definition) [])] (by simpa
              [PlainBnfCollectorSourceExecution.resultTuple, result] using recursive)
          have bound : loopHeight [] index reversed < fuel + 1 := by rw [loopHeight]; omega
          simpa [bound, encodeResult, resultData, PlainBnfTrieDeclarationCollector.collectLoop,
            List.reverseAux_eq, diagnostics] using step
        · have recursive := reversal_answers fuel (reversed.map definition) []
          simp only [List.length_map, enough, ↓reduceIte] at recursive
          have step := nil_rewriteAt fuel index reversed [] (by simpa using recursive)
          have bound : ¬ loopHeight [] index reversed < fuel + 1 := by rw [loopHeight]; omega
          simpa [bound] using step

      | cons item tail =>
        cases item with
        | comment text span =>
          by_cases enough : loopHeight tail index reversed < fuel
          · have recursive := ih.1 tail index reversed
            simp only [enough, ↓reduceIte] at recursive
            have step := comment_rewriteAt fuel text span tail index reversed
              [resultData (PlainBnfTrieDeclarationCollector.collectLoop tail index reversed)]
              (by simpa [encodeResult] using recursive)
            have bound : loopHeight (.comment text span :: tail) index reversed < fuel + 1 := by
              rw [loopHeight]; omega
            simpa [bound, encodeResult, PlainBnfTrieDeclarationCollector.collectLoop] using step
          · have recursive := ih.1 tail index reversed
            simp only [enough, ↓reduceIte] at recursive
            have step := comment_rewriteAt fuel text span tail index reversed [] (by simpa using recursive)
            have bound : ¬ loopHeight (.comment text span :: tail) index reversed < fuel + 1 := by
              rw [loopHeight]; omega
            simpa [bound] using step
        | blank span =>
          by_cases enough : loopHeight tail index reversed < fuel
          · have recursive := ih.1 tail index reversed
            simp only [enough, ↓reduceIte] at recursive
            have step := blank_rewriteAt fuel span tail index reversed
              [resultData (PlainBnfTrieDeclarationCollector.collectLoop tail index reversed)]
              (by simpa [encodeResult] using recursive)
            have bound : loopHeight (.blank span :: tail) index reversed < fuel + 1 := by
              rw [loopHeight]; omega
            simpa [bound, encodeResult, PlainBnfTrieDeclarationCollector.collectLoop] using step
          · have recursive := ih.1 tail index reversed
            simp only [enough, ↓reduceIte] at recursive
            have step := blank_rewriteAt fuel span tail index reversed [] (by simpa using recursive)
            have bound : ¬ loopHeight (.blank span :: tail) index reversed < fuel + 1 := by
              rw [loopHeight]; omega
            simpa [bound] using step
        | rule key expression span =>
          by_cases queryEnough : PlainBnfTrieSourceExecution.lookupHeight key (indexTrie index) < fuel
          · have queried := lookup_answers fuel key index
            simp only [queryEnough, ↓reduceIte] at queried
            by_cases afterEnough : afterHeight (PlainBnfGraphNameTrie.lookup key index)
                ⟨key, expression, span⟩ tail index reversed < fuel
            · have recursive := ih.2 (PlainBnfGraphNameTrie.lookup key index) ⟨key, expression, span⟩ tail index reversed
              simp only [afterEnough, ↓reduceIte] at recursive
              have step := rule_rewriteAt fuel ⟨key, expression, span⟩ tail index reversed _
                [resultData (afterMeaning (PlainBnfGraphNameTrie.lookup key index) ⟨key, expression, span⟩ tail index reversed)]
                queried (by simpa [encodeResult] using recursive)
              have bound : loopHeight (.rule key expression span :: tail) index reversed < fuel + 1 := by
                rw [loopHeight]; omega
              cases found : PlainBnfGraphNameTrie.lookup key index with
              | none =>
                simpa [bound, encodeResult, PlainBnfTrieDeclarationCollector.collectLoop, afterMeaning, found] using step
              | some pair =>
                rcases pair with ⟨firstExpression, firstSpan⟩
                simpa [bound, encodeResult, PlainBnfTrieDeclarationCollector.collectLoop, afterMeaning, found] using step
            · have recursive := ih.2 (PlainBnfGraphNameTrie.lookup key index) ⟨key, expression, span⟩ tail index reversed
              simp only [afterEnough, ↓reduceIte] at recursive
              have step := rule_rewriteAt fuel ⟨key, expression, span⟩ tail index reversed _ []
                queried (by simpa using recursive)
              have bound : ¬ loopHeight (.rule key expression span :: tail) index reversed < fuel + 1 := by
                rw [loopHeight]; omega
              simpa [bound] using step
          · have queried := lookup_answers fuel key index
            simp only [queryEnough, ↓reduceIte] at queried
            have step := rule_query_exhausted fuel ⟨key, expression, span⟩ tail index reversed queried
            have bound : ¬ loopHeight (.rule key expression span :: tail) index reversed < fuel + 1 := by
              rw [loopHeight]; omega
            simpa [bound] using step
    · intro found item tail index reversed
      cases found with
      | none =>
        by_cases insertEnough : PlainBnfTrieSourceExecution.insertHeight item.name (indexTrie index) < fuel
        · have inserted := insert_answers fuel item.name (item.expression, item.span) index
          simp only [insertEnough, ↓reduceIte] at inserted
          by_cases loopEnough : loopHeight tail
              (PlainBnfGraphNameTrie.insertFirst item.name (item.expression, item.span) index) (item :: reversed) < fuel
          · have recursive := ih.1 tail
              (PlainBnfGraphNameTrie.insertFirst item.name (item.expression, item.span) index) (item :: reversed)
            simp only [loopEnough, ↓reduceIte] at recursive
            have step := fresh_rewriteAt fuel item tail index _ reversed
              [resultData (afterMeaning none item tail index reversed)] inserted (by
                simpa [encodeResult, afterMeaning] using recursive)
            have bound : afterHeight none item tail index reversed < fuel + 1 := by rw [afterHeight]; omega
            simpa [bound, encodeResult] using step
          · have recursive := ih.1 tail
              (PlainBnfGraphNameTrie.insertFirst item.name (item.expression, item.span) index) (item :: reversed)
            simp only [loopEnough, ↓reduceIte] at recursive
            have step := fresh_rewriteAt fuel item tail index _ reversed [] inserted (by simpa using recursive)
            have bound : ¬ afterHeight none item tail index reversed < fuel + 1 := by rw [afterHeight]; omega
            simpa [bound] using step
        · have inserted := insert_answers fuel item.name (item.expression, item.span) index
          simp only [insertEnough, ↓reduceIte] at inserted
          have step := fresh_insert_exhausted fuel item tail index reversed inserted
          have bound : ¬ afterHeight none item tail index reversed < fuel + 1 := by rw [afterHeight]; omega
          simpa [bound] using step
      | some pair =>
        rcases pair with ⟨firstExpression, firstSpan⟩
        by_cases enough : loopHeight tail index reversed < fuel
        · have recursive := ih.1 tail index reversed
          simp only [enough, ↓reduceIte] at recursive
          have step := duplicate_rewriteAt fuel item tail index reversed firstExpression firstSpan
            [resultData (PlainBnfTrieDeclarationCollector.collectLoop tail index reversed)] (by
              simpa [encodeResult] using recursive)
          have bound : afterHeight (some (firstExpression, firstSpan)) item tail index reversed < fuel + 1 := by
            rw [afterHeight]; omega
          simpa [bound, encodeResult, resultData, afterMeaning, diagnostics] using step
        · have recursive := ih.1 tail index reversed
          simp only [enough, ↓reduceIte] at recursive
          have step := duplicate_rewriteAt fuel item tail index reversed firstExpression firstSpan [] (by simpa using recursive)
          have bound : ¬ afterHeight (some (firstExpression, firstSpan)) item tail index reversed < fuel + 1 := by
            rw [afterHeight]; omega
          simpa [bound] using step

theorem collect_answers (fuel : Nat) (input : List (Entry Scalar)) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (collectCall input) =
      if 1 + loopHeight input .empty [] < fuel then
        [encodeResult (PlainBnfTrieDeclarationCollector.collectIndexed input)] else [] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
    by_cases enough : loopHeight input .empty [] < fuel
    · have recursive := (collector_answers fuel).1 input .empty []
      simp only [enough, ↓reduceIte] at recursive
      have step := entry_rewriteAt fuel input
        [resultData (PlainBnfTrieDeclarationCollector.collectIndexed input)] (by
          simpa [encodeResult, PlainBnfTrieDeclarationCollector.collectIndexed] using recursive)
      have bound : 1 + loopHeight input .empty [] < fuel + 1 := by omega
      simpa [bound, encodeResult] using step
    · have recursive := (collector_answers fuel).1 input .empty []
      simp only [enough, ↓reduceIte] at recursive
      have step := entry_rewriteAt fuel input [] (by simpa using recursive)
      have bound : ¬ 1 + loopHeight input .empty [] < fuel + 1 := by omega
      simpa [bound] using step

theorem loop_step_iff (input : List (Entry Scalar)) (index : (Index Scalar)) (reversed : List (Definition Scalar)) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language (loopCall input index reversed) target ↔
      target = encodeResult (PlainBnfTrieDeclarationCollector.collectLoop input index reversed) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [(collector_answers fuel).1] at member
    split at member
    · simpa using member
    · cases member
  · intro same
    subst target
    refine ⟨loopHeight input index reversed + 1, ?_⟩
    simp [(collector_answers _).1]

theorem after_step_iff (found : Option (SExpr × SExpr)) (item : (Definition Scalar)) (tail : List (Entry Scalar))
    (index : (Index Scalar)) (reversed : List (Definition Scalar)) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language (afterCall found item tail index reversed) target ↔
      target = encodeResult (afterMeaning found item tail index reversed) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [(collector_answers fuel).2] at member
    split at member
    · simpa using member
    · cases member
  · intro same
    subst target
    refine ⟨afterHeight found item tail index reversed + 1, ?_⟩
    simp [(collector_answers _).2]

theorem collect_step_iff (input : List (Entry Scalar)) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language (collectCall input) target ↔
      target = encodeResult (PlainBnfTrieDeclarationCollector.collectIndexed input) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [collect_answers] at member
    split at member
    · simpa using member
    · cases member
  · intro same
    subst target
    refine ⟨1 + loopHeight input .empty [] + 1, ?_⟩
    simp [collect_answers]

/-- The declarations and diagnostics are the independently defined ordered
collector's result; the same answer also carries the actual constructed index. -/
theorem collect_independent_step_iff (input : List (Entry Scalar)) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language (collectCall input) target ↔
      target = packet ((definitions ((PlainBnfDeclarationSemantics.collect input []).1.map definition),
        diagnostics (PlainBnfDeclarationSemantics.collect input []).2),
        encodeIndex (PlainBnfTrieDeclarationCollector.collectIndexed input).2) := by
  rw [collect_step_iff]
  simp [encodeResult, resultData, PlainBnfTrieDeclarationCollector.collectIndexed_eq]

omit [DecidableEq Scalar] [PlainBnfCollectorSourceExecution.NameScalarCodec Scalar] in
mutual
  theorem indexTrie_injective {left right : (Index Scalar)} (same : indexTrie left = indexTrie right) :
      left = right := by
    cases left with
    | empty => cases right <;> simp_all [indexTrie]
    | node value children =>
      cases right with
      | empty => simp [indexTrie] at same
      | node other rest =>
        simp only [indexTrie, PlainBnfGraphNameTrie.Trie.node.injEq] at same
        have values := Option.map_injective payload_injective same.1
        have lists := indexEdges_injective same.2
        cases values
        cases lists
        rfl
  termination_by sizeOf left

  theorem indexEdges_injective {left right : List (Scalar × (Index Scalar))} (same : indexEdges left = indexEdges right) :
      left = right := by
    cases left with
    | nil => cases right <;> simp_all [indexEdges]
    | cons edge rest =>
      cases edgeEq : edge with
      | mk head child =>
        simp only [edgeEq] at same
        cases right with
        | nil => simp [indexEdges] at same
        | cons other following =>
          rcases other with ⟨stored, next⟩
          simp only [indexEdges, List.cons.injEq, Prod.mk.injEq] at same
          have children := indexTrie_injective same.1.2
          have tails := indexEdges_injective same.2
          cases same.1.1
          cases children
          cases tails
          rfl
  termination_by sizeOf left
  decreasing_by all_goals simp_all only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]; omega
end

omit [DecidableEq Scalar] in
theorem encodeIndex_injective : Function.Injective (encodeIndex (Scalar := Scalar)) := by
  intro left right same
  exact indexTrie_injective (PlainBnfTrieSourceExecution.trie_injective same)

theorem packet_injective : Function.Injective packet := by
  rintro ⟨⟨a, b⟩, c⟩ ⟨⟨x, y⟩, z⟩ same
  have decoded := encode_injective same
  simp only [SExpr.list.injEq, List.cons.injEq, and_true] at decoded
  exact Prod.ext (Prod.ext decoded.1 decoded.2.1) decoded.2.2

omit [DecidableEq Scalar] in
theorem encodeResult_injective : Function.Injective (encodeResult (Scalar := Scalar)) := by
  intro left right same
  have decoded := packet_injective same
  have ordered := PlainBnfCollectorSourceExecution.definitions_injective
    (congrArg (fun pair : (SExpr × SExpr) × SExpr => pair.1.1) decoded)
  have definitionsEqual := (List.map_inj_right
    (fun _ _ same => PlainBnfCollectorSourceExecution.definition_injective same)).mp ordered
  have diagnosticsEqual := PlainBnfCollectorSourceExecution.diagnostics_injective
    (congrArg (fun pair : (SExpr × SExpr) × SExpr => pair.1.2) decoded)
  have indexEqual := encodeIndex_injective (congrArg Prod.snd decoded)
  exact Prod.ext (Prod.ext definitionsEqual diagnosticsEqual) indexEqual

theorem collect_decoded_step_iff (input : List (Entry Scalar)) (output : (List (Definition Scalar) × List (Diagnostic Scalar)) × (Index Scalar)) :
    Step (engineBasePremises scalarRelations) language (collectCall input) (encodeResult output) ↔
      output = PlainBnfTrieDeclarationCollector.collectIndexed input := by
  rw [collect_step_iff]
  exact ⟨fun same => encodeResult_injective same, congrArg encodeResult⟩

theorem loop_decoded_step_iff (input : List (Entry Scalar)) (index : (Index Scalar)) (reversed : List (Definition Scalar))
    (output : (List (Definition Scalar) × List (Diagnostic Scalar)) × (Index Scalar)) :
    Step (engineBasePremises scalarRelations) language (loopCall input index reversed) (encodeResult output) ↔
      output = PlainBnfTrieDeclarationCollector.collectLoop input index reversed := by
  rw [loop_step_iff]
  exact ⟨fun same => encodeResult_injective same, congrArg encodeResult⟩

theorem loop_observations (input : List (Entry Scalar)) (index : (Index Scalar)) (reversed : List (Definition Scalar))
    (represents : PlainBnfTrieDeclarationCollector.Represents index reversed.reverse)
    (output : (List (Definition Scalar) × List (Diagnostic Scalar)) × (Index Scalar))
    (executed : Step (engineBasePremises scalarRelations) language (loopCall input index reversed) (encodeResult output)) :
    output.1 = PlainBnfDeclarationSemantics.collect input reversed.reverse ∧
      PlainBnfTrieDeclarationCollector.Represents output.2 output.1.1 := by
  have exactOutput := (loop_decoded_step_iff input index reversed output).mp executed
  subst output
  exact PlainBnfTrieDeclarationCollector.collectLoop_exact input index reversed represents

/-- Actual source execution supplies both independent ordered observations and
the first-complete-definition invariant of the returned constructed index. -/
theorem collect_observations (input : List (Entry Scalar)) (output : (List (Definition Scalar) × List (Diagnostic Scalar)) × (Index Scalar))
    (executed : Step (engineBasePremises scalarRelations) language (collectCall input) (encodeResult output)) :
    output.1 = PlainBnfDeclarationSemantics.collect input [] ∧
      PlainBnfTrieDeclarationCollector.Represents output.2 output.1.1 := by
  have exactOutput := (collect_decoded_step_iff input output).mp executed
  subst output
  exact ⟨PlainBnfTrieDeclarationCollector.collectIndexed_eq input,
    PlainBnfTrieDeclarationCollector.collectIndexed_index input⟩

theorem comments_blanks_preserve_source_answers (text commentSpan blankSpan : SExpr)
    (input : List (Entry Scalar)) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language
        (collectCall (.comment text commentSpan :: .blank blankSpan :: input)) target ↔
      Step (engineBasePremises scalarRelations) language (collectCall input) target := by
  rw [collect_step_iff, collect_step_iff,
    PlainBnfTrieDeclarationCollector.comments_and_blanks_preserve_outputs]

theorem empty_loop_restores_accumulator (index : (Index Scalar)) (reversed : List (Definition Scalar)) :
    Step (engineBasePremises scalarRelations) language (loopCall [] index reversed)
      (encodeResult ((reversed.reverse, []), index)) := by
  rw [loop_step_iff]
  simp [PlainBnfTrieDeclarationCollector.collectLoop, List.reverseAux_eq]

theorem duplicate_diagnostics_cannot_collapse (key : (Name Scalar)) (firstExpression laterExpression : SExpr)
    (firstSpan duplicateSpan : SExpr) (outputIndex : (Index Scalar)) :
    ¬ Step (engineBasePremises scalarRelations) language
      (collectCall [.rule key firstExpression firstSpan, .rule key laterExpression duplicateSpan,
        .rule key laterExpression duplicateSpan])
      (encodeResult (([⟨key, firstExpression, firstSpan⟩], [.duplicate key firstSpan duplicateSpan]), outputIndex)) := by
  rw [collect_decoded_step_iff]
  intro same
  have observed := congrArg (fun output : (List (Definition Scalar) × List (Diagnostic Scalar)) × (Index Scalar) => output.1.2) same
  have repeated := PlainBnfTrieDeclarationCollector.identical_diagnostic_occurrences
    (Text := SExpr) key firstExpression laterExpression firstSpan duplicateSpan
  have diagnosticCount := congrArg (fun result : List (Definition Scalar) × List (Diagnostic Scalar) => result.2.length) repeated
  have outputCount := congrArg List.length observed
  simp at outputCount diagnosticCount
  omega

theorem first_payload_remains_in_returned_index (key : (Name Scalar)) (firstExpression laterExpression : SExpr)
    (firstSpan laterSpan : SExpr) (output : (List (Definition Scalar) × List (Diagnostic Scalar)) × (Index Scalar))
    (executed : Step (engineBasePremises scalarRelations) language
      (collectCall [.rule key firstExpression firstSpan, .rule key laterExpression laterSpan])
      (encodeResult output)) :
    PlainBnfGraphNameTrie.lookup key output.2 = some (firstExpression, firstSpan) := by
  have exactOutput := (collect_decoded_step_iff _ output).mp executed
  subst output
  exact PlainBnfTrieDeclarationCollector.first_complete_payload_in_index
    (Text := SExpr) key firstExpression laterExpression firstSpan laterSpan

theorem accumulator_order_is_not_output_order (firstName secondName : (Name Scalar))
    (firstExpression secondExpression firstSpan secondSpan : SExpr)
    (different : firstName ≠ secondName) (outputIndex : (Index Scalar)) :
    ¬ Step (engineBasePremises scalarRelations) language
      (collectCall [.rule firstName firstExpression firstSpan, .rule secondName secondExpression secondSpan])
      (encodeResult (([⟨secondName, secondExpression, secondSpan⟩,
        ⟨firstName, firstExpression, firstSpan⟩], []), outputIndex)) := by
  rw [collect_decoded_step_iff]
  intro same
  have observed := congrArg (fun output : (List (Definition Scalar) × List (Diagnostic Scalar)) × (Index Scalar) => output.1) same
  rw [PlainBnfTrieDeclarationCollector.source_order_not_private_accumulator_order
    firstName secondName firstExpression secondExpression firstSpan secondSpan different] at observed
  have names := congrArg (fun output : List (Definition Scalar) × List (Diagnostic Scalar) => output.1.map (·.name)) observed
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at names
  exact different names.1.symm

theorem insufficient_depth_has_no_partial_answer (input : List (Entry Scalar)) (fuel : Nat)
    (insufficient : fuel ≤ 1 + loopHeight input .empty []) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (collectCall input) = [] := by
  rw [collect_answers]
  simp [show ¬ 1 + loopHeight input .empty [] < fuel by omega]

/-- Actual source execution over signed names retains both opposite-signed
definitions, the first complete payload, and both identical diagnostic
occurrences. The comment and blank are source entries, not preprocessing. -/
theorem signed_names_first_payload_and_duplicate_occurrences
    (first later positive firstSpan laterSpan positiveSpan text : SExpr) :
    Step (engineBasePremises scalarRelations) language
      (collectCall ([.rule [-7] first firstSpan, .comment text laterSpan,
        .rule [7] positive positiveSpan, .blank laterSpan,
        .rule [-7] later laterSpan, .rule [-7] later laterSpan] : List (Entry Int)))
      (encodeResult
        (([⟨[-7], first, firstSpan⟩, ⟨[7], positive, positiveSpan⟩],
          [.duplicate [-7] firstSpan laterSpan, .duplicate [-7] firstSpan laterSpan]),
        PlainBnfGraphNameTrie.insertFirst ([7] : List Int) (positive, positiveSpan)
          (PlainBnfGraphNameTrie.insertFirst [-7] (first, firstSpan) .empty))) := by
  rw [collect_step_iff]
  simp [PlainBnfTrieDeclarationCollector.collectIndexed,
    PlainBnfTrieDeclarationCollector.collectLoop,
    PlainBnfGraphNameTrie.lookup_insertFirst, PlainBnfGraphNameTrie.lookup_empty]

theorem signed_duplicate_cannot_lose_an_occurrence
    (first later firstSpan laterSpan : SExpr) (outputIndex : Index Int) :
    ¬ Step (engineBasePremises scalarRelations) language
      (collectCall [.rule ([-7] : List Int) first firstSpan,
        .rule [-7] later laterSpan, .rule [-7] later laterSpan])
      (encodeResult (([⟨[-7], first, firstSpan⟩], [.duplicate [-7] firstSpan laterSpan]), outputIndex)) :=
  duplicate_diagnostics_cannot_collapse [-7] first later firstSpan laterSpan outputIndex

end Mettapedia.GSLT.Parsing.PlainBnfIndexedCollectorSourceExecution
