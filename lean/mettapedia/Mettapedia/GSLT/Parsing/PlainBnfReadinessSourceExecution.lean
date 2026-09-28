import Mettapedia.GSLT.Parsing.PlainBnfProductiveSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfNullableSourceExecution

/-!
# Authored discovery readiness

The two discovery dispatch rules execute the actual productive and nullable
families. Their shared name-index and lexical-lookup rules occur once. The
combined language is an ordered composition of translated source occurrences,
not a provider returning a precomputed readiness answer. Exact bounded answer
lists are the observation; physical generated/native agreement is separate.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfReadinessSourceExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT (Rewrite decodeList)
open SourceSExprPatternCodec (encode encodeList)
open SourceSExprPatternInstantiation (pattern patternList
  applyRuleBindings_of_binderFree binderFree_pattern)
open PlainBnfStructuredDenotation (Expression LexicalDeclaration)
open PlainBnfTrieSourceExecution (call result)
open PlainBnfKnownNamesSourceExecution (known Valid)
open PlainBnfReferenceCollectionSourceExecution (expression declarations)
open PlainBnfLexicalMatcherSourceExecution (relations answer)
open PlainBnfIndexedCollectorSourceExecution (headedBy premiseClosed)
open PlainBnfReadinessEnvironment
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

abbrev NameIndex := PlainBnfGraphNameTrie.Trie SExpr Nat

def mode? : String → Option (Nat × Nat)
  | "BNFDiscoveryReadyV1" => some (4, 1)
  | "BNFExpressionProductiveV1" | "BNFExpressionNullableV1" => some (3, 1)
  | _ => none

def splitCall? : SExpr → Option (SExpr × SExpr)
  | .list (.atom relation :: arguments) => do
      let (inputs, outputs) ← mode? relation
      if arguments.length = inputs + outputs then
        some (.list (.atom relation :: arguments.take inputs), .list (arguments.drop inputs))
      else none
  | _ => none

def lowerPremise? (source : SExpr) : Option Premise := do
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
  (PlainBnfCollectorSourceAdmission.discoverySource.rewrites.drop 58).take 2
def rules : List RewriteRule := (rows.mapM lowerRule?).get (by rfl)
def language : LanguageDef :=
  { name := "PlainBnfAuthoredReadiness", types := [], terms := [], equations := [],
    rewrites := PlainBnfProductiveSourceExecution.language.rewrites ++
      PlainBnfNullableSourceExecution.nullableRules ++ rules }

theorem translation_exact : rows.mapM lowerRule? = some rules := rfl
theorem source_occurrences_exact : rows.zipIdx 58 =
    ((PlainBnfCollectorSourceAdmission.discoverySource.rewrites.zipIdx).drop 58).take 2 := rfl
theorem source_family_exhaustive :
    PlainBnfCollectorSourceAdmission.discoverySource.rewrites.filter (fun row => match row.head with
      | .list (.atom head :: _) => head == "BNFDiscoveryReadyV1"
      | _ => false) = rows := rfl
theorem source_rule_count : language.rewrites.length = 70 := rfl

def readyHeads := ["BNFDiscoveryReadyV1"]
def relationHeads := PlainBnfProductiveSourceExecution.wholeHeads ++
  PlainBnfNullableSourceExecution.nullableHeads ++ readyHeads

private def observedRules : List RewriteRule := [
  { name := "bnf-discovery-ready-productive-v1", typeContext := [],
    left := pattern (metta_sexpr% petta "(BNFDiscoveryReadyV1 BNFDiscoveryProductiveV1 ?expression ?known ?lexicals)"),
    right := pattern (metta_sexpr% petta "(?result)"),
    premises := [.congruence
      (pattern (metta_sexpr% petta "(BNFExpressionProductiveV1 ?expression ?known ?lexicals)"))
      (pattern (metta_sexpr% petta "(?result)"))] },
  { name := "bnf-discovery-ready-nullable-v1", typeContext := [],
    left := pattern (metta_sexpr% petta "(BNFDiscoveryReadyV1 BNFDiscoveryNullableV1 ?expression ?known ?lexicals)"),
    right := pattern (metta_sexpr% petta "(?result)"),
    premises := [.congruence
      (pattern (metta_sexpr% petta "(BNFExpressionNullableV1 ?expression ?known ?lexicals)"))
      (pattern (metta_sexpr% petta "(?result)"))] }]

private theorem rules_exact : rules = observedRules := rfl
theorem ready_heads : rules.all (fun rule => headedBy readyHeads rule.left) = true := by
  simp [rules_exact, observedRules, headedBy, readyHeads, pattern, patternList,
    encode, SourceIntegerProvider.sourceVariableToken]

theorem family_heads : language.rewrites.all (fun rule => headedBy relationHeads rule.left) = true := by
  simp only [language, List.all_append, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact List.all_eq_true.mpr (fun rule member => headedBy_mono _ _ (by
      intro name present; exact List.mem_append_left _ (List.mem_append_left _ present)) _
      (List.all_eq_true.mp PlainBnfProductiveSourceExecution.whole_heads rule member))
  · exact List.all_eq_true.mpr (fun rule member => headedBy_mono _ _ (by
      intro name present; exact List.mem_append_left _ (List.mem_append_right _ present)) _
      (List.all_eq_true.mp PlainBnfNullableSourceExecution.nullable_heads rule member))
  · exact List.all_eq_true.mpr (fun rule member => headedBy_mono _ _ (by
      intro name present; exact List.mem_append_right _ present) _
      (List.all_eq_true.mp ready_heads rule member))

theorem finite_disjoint (left right : List String)
    (checked : left.all (fun name => !right.contains name) = true) : List.Disjoint left right := by
  intro name member present
  have absent := List.all_eq_true.mp checked name member
  simp [present] at absent

private theorem premise_mono (small large : List String) (included : small ⊆ large)
    (premise : Premise) (closed : premiseClosed small premise = true) :
    premiseClosed large premise = true := by
  cases premise with
  | congruence source target => exact headedBy_mono small large included source closed
  | scopedStep step =>
    simp only [premiseClosed, Bool.or_eq_true] at closed ⊢
    exact closed.imp id (headedBy_mono small large included step.source)
  | _ => rfl

theorem family_closed : language.rewrites.all
    (fun rule => rule.premises.all (premiseClosed relationHeads)) = true := by
  have readyClosed : rules.all (fun rule => rule.premises.all (premiseClosed relationHeads)) = true := by
    simp [rules_exact, observedRules, premiseClosed, headedBy, relationHeads, readyHeads,
      PlainBnfProductiveSourceExecution.wholeHeads, PlainBnfProductiveSourceExecution.relationHeads,
      PlainBnfNullableSourceExecution.nullableHeads, knownHeads, lexicalLookupHeads, lexicalMatcherHeads,
      PlainBnfKnownNamesSourceExecution.knownNames, PlainBnfIndexedCollectorSourceExecution.trieNames,
      pattern, patternList, encode, SourceIntegerProvider.sourceVariableToken]
  apply List.all_eq_true.mpr
  intro rule member
  apply List.all_eq_true.mpr
  intro premise present
  simp only [language, List.mem_append] at member
  rcases member with (member | member) | member
  · exact premise_mono PlainBnfProductiveSourceExecution.wholeHeads relationHeads
      (by intro name found; simp [relationHeads, found]) premise
      (List.all_eq_true.mp (List.all_eq_true.mp
        PlainBnfProductiveSourceExecution.whole_closed rule member) premise present)
  · have member' : rule ∈ PlainBnfNullableSourceExecution.language.rewrites := by
      rw [PlainBnfNullableSourceExecution.language_partition]
      exact List.mem_append_right _ member
    exact premise_mono PlainBnfNullableSourceExecution.relationHeads relationHeads
      (by decide) premise
      (List.all_eq_true.mp (List.all_eq_true.mp
        PlainBnfNullableSourceExecution.family_closed rule member') premise present)
  · exact List.all_eq_true.mp (List.all_eq_true.mp readyClosed rule member) premise present

theorem productive_selection : language.rewrites.filter
    (fun rule => headedBy PlainBnfProductiveSourceExecution.wholeHeads rule.left) =
      PlainBnfProductiveSourceExecution.language.rewrites := by
  simp only [language, List.filter_append]
  rw [filter_included _ _ (List.Subset.refl _) _ PlainBnfProductiveSourceExecution.whole_heads,
    filter_disjoint _ _ (by apply finite_disjoint; decide) _ PlainBnfNullableSourceExecution.nullable_heads,
    filter_disjoint _ _ (by apply finite_disjoint; decide) _ ready_heads]
  simp

theorem nullable_selection : language.rewrites.filter
    (fun rule => headedBy PlainBnfNullableSourceExecution.relationHeads rule.left) =
      PlainBnfNullableSourceExecution.language.rewrites := by
  simp only [language, PlainBnfProductiveSourceExecution.language,
    PlainBnfProductiveSourceExecution.dependencies, List.filter_append]
  rw [filter_included _ _ (by decide) _ known_heads,
    filter_included _ _ (by decide) _ lexical_lookup_heads,
    filter_disjoint _ _ (by apply finite_disjoint; decide) _ lexical_matcher_heads,
    filter_disjoint _ _ (by apply finite_disjoint; decide) _ PlainBnfProductiveSourceExecution.family_heads,
    filter_included _ _ (by decide) _ PlainBnfNullableSourceExecution.nullable_heads,
    filter_disjoint _ _ (by apply finite_disjoint; decide) _ ready_heads]
  simpa using PlainBnfNullableSourceExecution.language_partition.symm

theorem productive_extension (fuel : Nat) (source : Pattern)
    (headed : headedBy PlainBnfProductiveSourceExecution.wholeHeads source = true) :
    rewriteAt (engineBasePremises relations) language fuel source =
      rewriteAt (engineBasePremises relations) PlainBnfProductiveSourceExecution.language fuel source := by
  apply filtered_extension _ relations _ _ productive_selection
  · intro rule member premise present
    exact List.all_eq_true.mp (List.all_eq_true.mp
      PlainBnfProductiveSourceExecution.whole_closed rule member) premise present
  · intro rule member foreign input itsHead
    exact foreign_head_does_not_match _ relationHeads _ _
      (List.all_eq_true.mp family_heads rule member) foreign itsHead
  · exact headed

theorem nullable_extension (fuel : Nat) (source : Pattern)
    (headed : headedBy PlainBnfNullableSourceExecution.relationHeads source = true) :
    rewriteAt (engineBasePremises relations) language fuel source =
      rewriteAt (engineBasePremises PlainBnfTrieSourceExecution.scalarRelations)
        PlainBnfNullableSourceExecution.language fuel source := by
  rw [filtered_extension _ relations _ _ nullable_selection (by
    intro rule member premise present
    exact List.all_eq_true.mp (List.all_eq_true.mp
      PlainBnfNullableSourceExecution.family_closed rule member) premise present) (by
    intro rule member foreign input itsHead
    exact foreign_head_does_not_match _ relationHeads _ _
      (List.all_eq_true.mp family_heads rule member) foreign itsHead) fuel source headed]
  exact different_only_environment _ PlainBnfNullableSourceExecution.family_queries fuel source

def readyCall (tag : SExpr) (input : Expression) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) : Pattern :=
  call "BNFDiscoveryReadyV1" [tag, expression input, known index history, declarations lexicals]

def productiveCall := readyCall (.atom "BNFDiscoveryProductiveV1")
def nullableCall := readyCall (.atom "BNFDiscoveryNullableV1")

private theorem ready_rewriteAt (fuel : Nat) (source : Pattern)
    (headed : headedBy readyHeads source = true) :
    rewriteAt (engineBasePremises relations) language (fuel + 1) source =
      rules.flatMap (fun rule => applyRuleUsing (engineBasePremises relations) language
        (rewriteAt (engineBasePremises relations) language fuel) rule source) := by
  apply PlainBnfHeapSourceExecution.skip_unmatched_prefix _ language
    (PlainBnfProductiveSourceExecution.language.rewrites ++
      PlainBnfNullableSourceExecution.nullableRules) rules rfl
  intro rule member
  rcases List.mem_append.mp member with member | member
  · exact PlainBnfIndexedCollectorSourceExecution.disjoint_heads_do_not_match _ readyHeads
      (by apply finite_disjoint; decide) _ _ (List.all_eq_true.mp PlainBnfProductiveSourceExecution.whole_heads rule member) headed
  · exact PlainBnfIndexedCollectorSourceExecution.disjoint_heads_do_not_match _ readyHeads
      (by apply finite_disjoint; decide) _ _ (List.all_eq_true.mp PlainBnfNullableSourceExecution.nullable_heads rule member) headed

theorem productive_answers (fuel : Nat) (input : Expression) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (valid : Valid index history) :
    rewriteAt (engineBasePremises relations) language fuel (productiveCall input index history lexicals) =
      if PlainBnfProductiveSourceExecution.expressionHeight index history lexicals input + 1 < fuel
      then [result (answer (PlainBnfProductiveSourceExecution.expressionMeaning history lexicals input))]
      else [] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
    rw [ready_rewriteAt fuel _ (by simp [productiveCall, readyCall, call, encode, encodeList, headedBy, readyHeads])]
    have recursive := PlainBnfProductiveSourceExecution.expression_answers fuel input index history lexicals valid
    have extension := productive_extension fuel (PlainBnfProductiveSourceExecution.expressionCall input index history lexicals) (by rfl)
    rw [← extension] at recursive
    simp [rules_exact, observedRules, applyRuleUsing, productiveCall, readyCall, call,
      applyRuleBindings_of_binderFree, binderFree, binderFreeList,
      pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
      matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing, applyBindings]
    simp only [PlainBnfProductiveSourceExecution.expressionCall, call, encode, encodeList] at recursive
    rw [recursive]
    split <;> simp_all [result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]

theorem nullable_answers (fuel : Nat) (input : Expression) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (valid : Valid index history) :
    rewriteAt (engineBasePremises relations) language fuel (nullableCall input index history lexicals) =
      if PlainBnfNullableSourceExecution.expressionHeight input index history lexicals + 1 < fuel
      then [result (answer (PlainBnfNullableSourceExecution.expressionMeaning history input))]
      else [] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
    rw [ready_rewriteAt fuel _ (by simp [nullableCall, readyCall, call, encode, encodeList, headedBy, readyHeads])]
    have recursive := PlainBnfNullableSourceExecution.expression_answers fuel input index history lexicals valid
    have extension := nullable_extension fuel (PlainBnfNullableSourceExecution.expressionCall input index history lexicals) (by rfl)
    rw [← extension] at recursive
    simp [rules_exact, observedRules, applyRuleUsing, nullableCall, readyCall, call,
      applyRuleBindings_of_binderFree, binderFree, binderFreeList,
      pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
      matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing, applyBindings]
    simp only [PlainBnfNullableSourceExecution.expressionCall, call, encode, encodeList] at recursive
    rw [recursive]
    split <;> simp_all [result, PlainBnfNullableSourceExecution.answer, answer,
      encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]

theorem productive_step_iff (input : Expression) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (valid : Valid index history) (target : Pattern) :
    Step (engineBasePremises relations) language (productiveCall input index history lexicals) target ↔
      target = result (answer (PlainBnfProductiveSourceExecution.expressionMeaning history lexicals input)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [productive_answers _ _ _ _ _ valid] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨PlainBnfProductiveSourceExecution.expressionHeight index history lexicals input + 2,
      by simp [productive_answers, valid]⟩

theorem nullable_step_iff (input : Expression) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (valid : Valid index history) (target : Pattern) :
    Step (engineBasePremises relations) language (nullableCall input index history lexicals) target ↔
      target = result (answer (PlainBnfNullableSourceExecution.expressionMeaning history input)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [nullable_answers _ _ _ _ _ valid] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨PlainBnfNullableSourceExecution.expressionHeight input index history lexicals + 2,
      by simp [nullable_answers, valid]⟩

theorem productive_decoded_step_iff (input : Expression) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (valid : Valid index history) (output : Bool) :
    Step (engineBasePremises relations) language (productiveCall input index history lexicals)
      (result (answer output)) ↔
      output = PlainBnfProductiveSourceExecution.expressionMeaning history lexicals input := by
  rw [productive_step_iff _ _ _ _ valid]
  exact PlainBnfLexicalMatcherSourceExecution.result_answer_injective.eq_iff

theorem nullable_decoded_step_iff (input : Expression) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (valid : Valid index history) (output : Bool) :
    Step (engineBasePremises relations) language (nullableCall input index history lexicals)
      (result (answer output)) ↔
      output = PlainBnfNullableSourceExecution.expressionMeaning history input := by
  rw [nullable_step_iff _ _ _ _ valid]
  exact PlainBnfLexicalMatcherSourceExecution.result_answer_injective.eq_iff

theorem insufficient_depth_is_not_false (input : Expression) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (valid : Valid index history) :
    rewriteAt (engineBasePremises relations) language
      (PlainBnfProductiveSourceExecution.expressionHeight index history lexicals input + 1)
      (productiveCall input index history lexicals) = [] ∧
    rewriteAt (engineBasePremises relations) language
      (PlainBnfNullableSourceExecution.expressionHeight input index history lexicals + 1)
      (nullableCall input index history lexicals) = [] := by
  simp [productive_answers, nullable_answers, valid]

/-- Readiness is relative to the current known-name set. It is not yet a
theorem about the discovery loop's final least fixed point. -/
theorem productive_yes_iff_graph (input : Expression) (index : NameIndex) (history : List SExpr)
    (knownValid : Valid index history) (authority : PlainBnfStructuredDenotation.GrammarAuthority)
    (unique : (authority.lexicalDeclarations.map (·.referenceName)).Nodup)
    (valid : ∀ declaration ∈ authority.lexicalDeclarations,
      PlainBnfSemanticAdmission.MatcherWellFormed declaration.matcher) :
    Step (engineBasePremises relations) language
      (productiveCall input index history authority.lexicalDeclarations) (result (answer true)) ↔
      PlainBnfGraphSemantics.ExpressionProductive
        {key | PlainBnfReferenceCollectionSourceExecution.text key ∈ history} authority input := by
  rw [productive_decoded_step_iff _ _ _ _ knownValid, eq_comm]
  exact PlainBnfProductiveSourceExecution.expressionMeaning_iff history authority unique valid input

theorem nullable_yes_iff_graph (input : Expression) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (valid : Valid index history) :
    Step (engineBasePremises relations) language
      (nullableCall input index history lexicals) (result (answer true)) ↔
      PlainBnfGraphSemantics.ExpressionNullable
        {key | PlainBnfReferenceCollectionSourceExecution.text key ∈ history} input := by
  rw [nullable_decoded_step_iff _ _ _ _ valid, eq_comm]
  exact PlainBnfNullableSourceExecution.expression_meaning_iff history input

theorem unsupported_mode_has_no_answer (fuel : Nat) (input : Expression) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises relations) language fuel
      (readyCall (.atom "BNFDiscoveryUnknownV1") input index history lexicals) = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [ready_rewriteAt fuel _ (by simp [readyCall, call, encode, encodeList, headedBy, readyHeads])]
    simp [rules_exact, observedRules, applyRuleUsing, readyCall, call, pattern, patternList,
      SourceIntegerProvider.sourceVariableToken, encode, encodeList, matchPattern, matchArgs,
      mergeBindings, List.foldlM]

theorem ready_answer_hook_absent (arguments : List Pattern) :
    relations.tuples "BNFDiscoveryReadyV1" arguments = [] := rfl

#print axioms productive_answers
#print axioms nullable_answers
#print axioms productive_step_iff
#print axioms nullable_step_iff
#print axioms productive_yes_iff_graph
#print axioms nullable_yes_iff_graph
#print axioms unsupported_mode_has_no_answer

end Mettapedia.GSLT.Parsing.PlainBnfReadinessSourceExecution
