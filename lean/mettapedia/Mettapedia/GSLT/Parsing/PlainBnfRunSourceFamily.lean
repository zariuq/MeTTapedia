import Mettapedia.GSLT.Parsing.PlainBnfWakeSourceFamily

/-!
# The authored discovery controller source family

The four original Run/Closure rules are translated from their admitted
source occurrences. Their recursive dependencies share the original trie
rules once. The observations below check that translation; they do not
provide answers or construct a replacement controller.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfRunSourceFamily

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT (Rewrite decodeList)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open PlainBnfIndexedCollectorSourceExecution (headedBy premiseClosed)
open PlainBnfReadinessEnvironment
open PlainBnfReadinessSourceExecution (finite_disjoint)
open PlainBnfLexicalMatcherSourceExecution (relations)
open SourceSExprPatternInstantiation (pattern patternList
  applyRuleBindings_of_binderFree binderFree_pattern)
open SourceSExprPatternCodec (encode encodeList)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

def mode? (relation : String) : Option (Nat × Nat) :=
  match relation with
  | "BNFDiscoveryRunV1" => some (5, 1)
  | "BNFDiscoveryClosureV1" => some (4, 1)
  | "BNFDiscoveryDependentsV1" => some (1, 1)
  | _ => (PlainBnfWakeSourceExecution.mode? relation).or
      ((PlainBnfHeapCombineSourceExecution.mode? relation).or
        (PlainBnfKnownNamesSourceExecution.mode? relation))

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
  (PlainBnfCollectorSourceAdmission.discoverySource.rewrites.drop 73).take 4

def rules : List RewriteRule := (rows.mapM lowerRule?).get (by rfl)

def dependentsRows : List Rewrite :=
  (PlainBnfCollectorSourceAdmission.discoverySource.rewrites.drop 54).take 2

def dependentsRules : List RewriteRule := (dependentsRows.mapM lowerRule?).get (by rfl)

def language : LanguageDef :=
  { name := "PlainBnfAuthoredRun", types := [], terms := [], equations := [],
    rewrites := PlainBnfWakeSourceFamily.language.rewrites ++
      PlainBnfHeapCombineSourceExecution.combineRules ++ dependentsRules ++ rules }

theorem source_translation_exact : rows.mapM lowerRule? = some rules := rfl

theorem source_occurrences_exact : rows.zipIdx 73 =
    ((PlainBnfCollectorSourceAdmission.discoverySource.rewrites.zipIdx).drop 73).take 4 := rfl

theorem source_family_exhaustive :
    PlainBnfCollectorSourceAdmission.discoverySource.rewrites.filter (fun row => match row.head with
      | .list (.atom head :: _) => head == "BNFDiscoveryRunV1" || head == "BNFDiscoveryClosureV1"
      | _ => false) = rows := rfl

theorem dependents_translation_exact : dependentsRows.mapM lowerRule? = some dependentsRules := rfl

theorem dependents_occurrences_exact : dependentsRows.zipIdx 54 =
    ((PlainBnfCollectorSourceAdmission.discoverySource.rewrites.zipIdx).drop 54).take 2 := rfl

theorem dependents_family_exhaustive :
    PlainBnfCollectorSourceAdmission.discoverySource.rewrites.filter (fun row => match row.head with
      | .list (.atom head :: _) => head == "BNFDiscoveryDependentsV1"
      | _ => false) = dependentsRows := rfl

theorem source_rule_count : language.rewrites.length = 114 := by
  simp only [language, List.length_append, PlainBnfWakeSourceFamily.source_rule_count]
  rfl

def runHeads := ["BNFDiscoveryRunV1", "BNFDiscoveryClosureV1"]
def dependentsHeads := ["BNFDiscoveryDependentsV1"]
def relationHeads := PlainBnfWakeSourceFamily.relationHeads ++
  PlainBnfHeapCombineSourceExecution.combineNames ++ dependentsHeads ++ runHeads

/-- Finite proof observations of the actual translated source. -/
def observedRules : List RewriteRule := [
  PlainBnfTrieSourceExecution.observedRule "bnf-discovery-run-done-v1"
    (metta_sexpr% petta "(BNFDiscoveryRunV1 ?mode ?reverse ?lexicals ?known (BNFDiscoveryQueuesV1 BNFDiscoveryHeapNilV1 BNFDiscoveryHeapNilV1 ?scheduled))")
    (metta_sexpr% petta "(?known)"),
  PlainBnfTrieSourceExecution.observedRule "bnf-discovery-run-next-round-v1"
    (metta_sexpr% petta "(BNFDiscoveryRunV1 ?mode ?reverse ?lexicals ?known (BNFDiscoveryQueuesV1 BNFDiscoveryHeapNilV1 (BNFDiscoveryHeapV1 ?node ?children ?siblings) ?scheduled))")
    (metta_sexpr% petta "(?result)")
    [.congruence (pattern (metta_sexpr% petta "(BNFDiscoveryRunV1 ?mode ?reverse ?lexicals ?known (BNFDiscoveryQueuesV1 (BNFDiscoveryHeapV1 ?node ?children ?siblings) BNFDiscoveryHeapNilV1 ?scheduled))"))
      (pattern (metta_sexpr% petta "(?result)"))],
  PlainBnfTrieSourceExecution.observedRule "bnf-discovery-run-publish-v1"
    (metta_sexpr% petta "(BNFDiscoveryRunV1 ?mode ?reverse ?lexicals ?known (BNFDiscoveryQueuesV1 (BNFDiscoveryHeapV1 (BNFDiscoveryDefinitionV1 ?rank ?name ?expression ?span) ?children BNFDiscoveryHeapNilV1) ?following ?scheduled))")
    (metta_sexpr% petta "(?result)")
    [.congruence (pattern (metta_sexpr% petta "(BNFDiscoveryHeapCombineV1 ?children)"))
      (pattern (metta_sexpr% petta "(?remaining)")),
     .congruence (pattern (metta_sexpr% petta "(BNFAppendNameV1 ?known ?name)"))
      (pattern (metta_sexpr% petta "(?nextKnown)")),
     .congruence (pattern (metta_sexpr% petta "(BNFGraphTrieLookupV1 ?name ?reverse)"))
      (pattern (metta_sexpr% petta "(?lookup)")),
     .congruence (pattern (metta_sexpr% petta "(BNFDiscoveryDependentsV1 ?lookup)"))
      (pattern (metta_sexpr% petta "(?dependents)")),
     .congruence (pattern (metta_sexpr% petta "(BNFDiscoveryWakeV1 ?mode ?dependents (BNFDiscoveryAfterPositionV1 ?rank) ?nextKnown ?lexicals (BNFDiscoveryQueuesV1 ?remaining ?following ?scheduled))"))
      (pattern (metta_sexpr% petta "(?nextQueues)")),
     .congruence (pattern (metta_sexpr% petta "(BNFDiscoveryRunV1 ?mode ?reverse ?lexicals ?nextKnown ?nextQueues)"))
      (pattern (metta_sexpr% petta "(?result)"))],
  PlainBnfTrieSourceExecution.observedRule "bnf-discovery-closure-v1"
    (metta_sexpr% petta "(BNFDiscoveryClosureV1 ?mode ?ranked ?reverse ?lexicals)")
    (metta_sexpr% petta "(?result)")
    [.congruence (pattern (metta_sexpr% petta "(BNFDiscoveryWakeV1 ?mode ?ranked BNFDiscoveryInitialV1 (BNFDiscoveryKnownV1 BNFGraphTrieEmptyV1 BNFNamesNilV1) ?lexicals (BNFDiscoveryQueuesV1 BNFDiscoveryHeapNilV1 BNFDiscoveryHeapNilV1 BNFGraphTrieEmptyV1))"))
      (pattern (metta_sexpr% petta "(?initial)")),
     .congruence (pattern (metta_sexpr% petta "(BNFDiscoveryRunV1 ?mode ?reverse ?lexicals (BNFDiscoveryKnownV1 BNFGraphTrieEmptyV1 BNFNamesNilV1) ?initial)"))
      (pattern (metta_sexpr% petta "(?result)"))]]

theorem rules_exact : rules = observedRules := rfl

def observedDependents : List RewriteRule := [
  PlainBnfTrieSourceExecution.observedRule "bnf-discovery-dependents-missing-v1"
    (metta_sexpr% petta "(BNFDiscoveryDependentsV1 BNFIndexMissingV1)")
    (metta_sexpr% petta "(BNFDiscoveryDefinitionsNilV1)"),
  PlainBnfTrieSourceExecution.observedRule "bnf-discovery-dependents-found-v1"
    (metta_sexpr% petta "(BNFDiscoveryDependentsV1 (BNFIndexFoundV1 ?definitions))")
    (metta_sexpr% petta "(?definitions)")]

theorem dependents_exact : dependentsRules = observedDependents := rfl

theorem run_heads : rules.all (fun rule => headedBy runHeads rule.left) = true := by
  simp [rules_exact, observedRules, PlainBnfTrieSourceExecution.observedRule,
    headedBy, runHeads, pattern, patternList, encode, SourceIntegerProvider.sourceVariableToken]

theorem dependents_heads : dependentsRules.all
    (fun rule => headedBy dependentsHeads rule.left) = true := by
  simp [dependents_exact, observedDependents, PlainBnfTrieSourceExecution.observedRule,
    headedBy, dependentsHeads, pattern, patternList, encode, SourceIntegerProvider.sourceVariableToken]

theorem family_heads : language.rewrites.all
    (fun rule => headedBy relationHeads rule.left) = true := by
  apply List.all_eq_true.mpr
  intro rule member
  simp only [language, List.mem_append] at member
  rcases member with ((member | member) | member) | member
  · exact headedBy_mono _ _ (by decide) _
      (List.all_eq_true.mp PlainBnfWakeSourceFamily.family_heads rule member)
  · exact headedBy_mono _ _ (by decide) _
      (List.all_eq_true.mp PlainBnfHeapCombineSourceExecution.combine_heads rule member)
  · exact headedBy_mono _ _ (by decide) _ (List.all_eq_true.mp dependents_heads rule member)
  · exact headedBy_mono _ _ (by decide) _ (List.all_eq_true.mp run_heads rule member)

theorem wake_extension (fuel : Nat) (source : Pattern)
    (headed : headedBy PlainBnfWakeSourceFamily.relationHeads source = true) :
    rewriteAt (engineBasePremises relations) language fuel source =
      rewriteAt (engineBasePremises relations) PlainBnfWakeSourceFamily.language fuel source := by
  apply PlainBnfIndexedCollectorSourceExecution.closed_extension
    PlainBnfWakeSourceFamily.relationHeads relations _ _ []
    (PlainBnfHeapCombineSourceExecution.combineRules ++ dependentsRules ++ rules)
  · simp [language, List.append_assoc]
  · intro rule member premise present
    exact List.all_eq_true.mp (List.all_eq_true.mp
      PlainBnfWakeSourceFamily.family_closed rule member) premise present
  · intro rule member input itsHead
    simp only [List.nil_append, List.mem_append] at member
    rcases member with (member | member) | member
    · exact PlainBnfIndexedCollectorSourceExecution.disjoint_heads_do_not_match _ _
        (by apply finite_disjoint; decide) _ _
        (List.all_eq_true.mp PlainBnfHeapCombineSourceExecution.combine_heads rule member) itsHead
    · exact PlainBnfIndexedCollectorSourceExecution.disjoint_heads_do_not_match _ _
        (by apply finite_disjoint; decide) _ _
        (List.all_eq_true.mp dependents_heads rule member) itsHead
    · exact PlainBnfIndexedCollectorSourceExecution.disjoint_heads_do_not_match _ _
        (by apply finite_disjoint; decide) _ _
        (List.all_eq_true.mp run_heads rule member) itsHead
  · exact headed

theorem run_rewriteAt (fuel : Nat) (source : Pattern)
    (headed : headedBy runHeads source = true) :
    rewriteAt (engineBasePremises relations) language (fuel + 1) source =
      rules.flatMap (fun rule => applyRuleUsing (engineBasePremises relations) language
        (rewriteAt (engineBasePremises relations) language fuel) rule source) := by
  apply PlainBnfHeapSourceExecution.skip_unmatched_prefix _ language
    (PlainBnfWakeSourceFamily.language.rewrites ++
      PlainBnfHeapCombineSourceExecution.combineRules ++ dependentsRules) rules rfl
  intro rule member
  simp only [List.mem_append] at member
  rcases member with (member | member) | member
  · exact PlainBnfIndexedCollectorSourceExecution.disjoint_heads_do_not_match _ runHeads
      (by apply finite_disjoint; decide) _ _
      (List.all_eq_true.mp PlainBnfWakeSourceFamily.family_heads rule member) headed
  · exact PlainBnfIndexedCollectorSourceExecution.disjoint_heads_do_not_match _ runHeads
      (by apply finite_disjoint; decide) _ _
      (List.all_eq_true.mp PlainBnfHeapCombineSourceExecution.combine_heads rule member) headed
  · exact PlainBnfIndexedCollectorSourceExecution.disjoint_heads_do_not_match _ runHeads
      (by apply finite_disjoint; decide) _ _
      (List.all_eq_true.mp dependents_heads rule member) headed

def combineHeads := PlainBnfHeapCombineSourceExecution.dependencyNames ++
  PlainBnfHeapCombineSourceExecution.combineNames

theorem combine_selection : language.rewrites.filter
    (fun rule => headedBy combineHeads rule.left) =
      PlainBnfHeapCombineSourceExecution.language.rewrites := by
  simp only [language, PlainBnfWakeSourceFamily.language, List.filter_append]
  rw [filter_included _ _ (by decide) _ PlainBnfHeapCombineSourceExecution.dependencies_heads,
    filter_disjoint _ _ (by apply finite_disjoint; decide) _
      PlainBnfReadinessSourceExecution.family_heads,
    filter_disjoint _ _ (by apply finite_disjoint; decide) _
      PlainBnfScheduleSourceExecution.schedule_heads,
    filter_disjoint _ _ (by apply finite_disjoint; decide) _ PlainBnfWakeSourceFamily.wake_heads,
    filter_included _ _ (by decide) _ PlainBnfHeapCombineSourceExecution.combine_heads,
    filter_disjoint _ _ (by apply finite_disjoint; decide) _ dependents_heads,
    filter_disjoint _ _ (by apply finite_disjoint; decide) _ run_heads]
  simp [PlainBnfHeapCombineSourceExecution.language_partition]

theorem combine_closed : PlainBnfHeapCombineSourceExecution.language.rewrites.all
    (fun rule => rule.premises.all (premiseClosed combineHeads)) = true := by
  apply List.all_eq_true.mpr
  intro rule member
  simp only [PlainBnfHeapCombineSourceExecution.language_partition, List.mem_append] at member
  rcases member with member | member
  · apply List.all_eq_true.mpr
    intro premise present
    have closed := List.all_eq_true.mp (List.all_eq_true.mp
      PlainBnfHeapCombineSourceExecution.dependencies_closed rule member) premise present
    cases premise with
    | congruence source target => exact headedBy_mono _ _ (by decide) _ closed
    | scopedStep step =>
      simp only [premiseClosed, Bool.or_eq_true] at closed ⊢
      exact closed.imp id (headedBy_mono _ _ (by decide) step.source)
    | _ => rfl
  · have closed : PlainBnfHeapCombineSourceExecution.combineRules.all
        (fun rule => rule.premises.all (premiseClosed combineHeads)) = true := by
      simp [PlainBnfHeapCombineSourceExecution.rules_exact,
        PlainBnfHeapCombineSourceExecution.observedRules, PlainBnfHeapCombineSourceExecution.observed,
        PlainBnfHeapSourceExecution.observed, PlainBnfTrieSourceExecution.observedRule,
        premiseClosed, headedBy, combineHeads, PlainBnfHeapCombineSourceExecution.dependencyNames,
        PlainBnfHeapCombineSourceExecution.combineNames, PlainBnfHeapSourceExecution.rankNames,
        PlainBnfHeapSourceExecution.heapNames, pattern, patternList, encode,
        SourceIntegerProvider.sourceVariableToken]
    exact List.all_eq_true.mp closed rule member

theorem combine_extension (fuel : Nat) (source : Pattern)
    (headed : headedBy combineHeads source = true) :
    rewriteAt (engineBasePremises relations) language fuel source =
      rewriteAt (engineBasePremises relations)
        PlainBnfHeapCombineSourceExecution.language fuel source := by
  apply filtered_extension _ relations _ _ combine_selection
  · intro rule member premise present
    exact List.all_eq_true.mp (List.all_eq_true.mp combine_closed rule member) premise present
  · intro rule member foreign input itsHead
    exact foreign_head_does_not_match _ relationHeads _ _
      (List.all_eq_true.mp family_heads rule member) foreign itsHead
  · exact headed

theorem known_extension (fuel : Nat) (source : Pattern)
    (headed : headedBy knownHeads source = true) :
    rewriteAt (engineBasePremises relations) language fuel source =
      rewriteAt (engineBasePremises PlainBnfTrieSourceExecution.scalarRelations)
        PlainBnfKnownNamesSourceExecution.language fuel source := by
  rw [wake_extension fuel source (headedBy_mono _ _ (by decide) _ headed),
    PlainBnfWakeSourceFamily.ready_extension fuel source (headedBy_mono _ _ (by decide) _ headed),
    PlainBnfReadinessSourceExecution.productive_extension fuel source
      (headedBy_mono _ _ (by decide) _ headed),
    PlainBnfProductiveSourceExecution.known_extension fuel source headed]
  exact known_environment fuel source

theorem trie_extension (fuel : Nat) (source : Pattern)
    (headed : headedBy PlainBnfIndexedCollectorSourceExecution.trieNames source = true) :
    rewriteAt (engineBasePremises relations) language fuel source =
      rewriteAt (engineBasePremises PlainBnfTrieSourceExecution.scalarRelations)
        PlainBnfTrieSourceExecution.language fuel source := by
  rw [wake_extension fuel source (headedBy_mono _ _ (by decide) _ headed)]
  exact PlainBnfWakeSourceFamily.trie_extension fuel source headed

theorem dependents_selection : language.rewrites.filter
    (fun rule => headedBy dependentsHeads rule.left) = dependentsRules := by
  simp only [language, List.filter_append]
  rw [filter_disjoint _ _ (by apply finite_disjoint; decide) _ PlainBnfWakeSourceFamily.family_heads,
    filter_disjoint _ _ (by apply finite_disjoint; decide) _
      PlainBnfHeapCombineSourceExecution.combine_heads,
    filter_included _ _ (List.Subset.refl _) _ dependents_heads,
    filter_disjoint _ _ (by apply finite_disjoint; decide) _ run_heads]
  simp

theorem dependents_rewriteAt (fuel : Nat) (source : Pattern)
    (headed : headedBy dependentsHeads source = true) :
    rewriteAt (engineBasePremises relations) language (fuel + 1) source =
      dependentsRules.flatMap (fun rule => applyRuleUsing (engineBasePremises relations) language
        (rewriteAt (engineBasePremises relations) language fuel) rule source) := by
  let selected := fun rule : RewriteRule => headedBy dependentsHeads rule.left
  let answers := fun rule => applyRuleUsing (engineBasePremises relations) language
    (rewriteAt (engineBasePremises relations) language fuel) rule source
  have filterAnswers (entries : List RewriteRule)
      (empty : ∀ rule ∈ entries, selected rule = false → answers rule = []) :
      entries.flatMap answers = (entries.filter selected).flatMap answers := by
    induction entries with
    | nil => rfl
    | cons rule rest ih =>
      have tail := ih (fun entry member => empty entry (by simp [member]))
      cases test : selected rule with
      | false => simp [test, empty rule (by simp) test, tail]
      | true => simp [test, tail]
  rw [rewriteAt, filterAnswers language.rewrites (by
    intro rule member foreign
    have unmatched := foreign_head_does_not_match dependentsHeads relationHeads _ _
      (List.all_eq_true.mp family_heads rule member) foreign headed
    simp [answers, applyRuleUsing, unmatched]), dependents_selection]

theorem dependents_answers (fuel : Nat) (found : Option SExpr) :
    rewriteAt (engineBasePremises relations) language fuel
      (PlainBnfReverseReferencesSourceExecution.dependentsCall found) =
      if 0 < fuel then [PlainBnfTrieSourceExecution.result
        (PlainBnfReverseReferencesSourceExecution.dependents found)] else [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [dependents_rewriteAt fuel _ (by rfl)]
    cases found <;>
      simp [dependents_exact, observedDependents, PlainBnfTrieSourceExecution.observedRule,
        applyRuleUsing, PlainBnfReverseReferencesSourceExecution.dependentsCall,
        applyRuleBindings_of_binderFree, binderFree, binderFreeList,
        PlainBnfReverseReferencesSourceExecution.dependents, PlainBnfReverseReferencesSourceExecution.emptyBucket,
        PlainBnfTrieSourceExecution.call, PlainBnfTrieSourceExecution.result, PlainBnfTrieSourceExecution.value,
        pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
        matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

theorem wake_step_iff (source target : Pattern)
    (headed : headedBy PlainBnfWakeSourceFamily.relationHeads source = true) :
    Step (engineBasePremises relations) language source target ↔
      Step (engineBasePremises relations) PlainBnfWakeSourceFamily.language source target := by
  rw [← exists_mem_rewriteAt_iff_step, ← exists_mem_rewriteAt_iff_step]
  simp only [wake_extension _ source headed]

theorem dependents_step_iff (found : Option SExpr) (target : Pattern) :
    Step (engineBasePremises relations) language
      (PlainBnfReverseReferencesSourceExecution.dependentsCall found) target ↔
      target = PlainBnfTrieSourceExecution.result
        (PlainBnfReverseReferencesSourceExecution.dependents found) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [dependents_answers] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨1, by simp [dependents_answers]⟩

theorem run_closed : rules.all
    (fun rule => rule.premises.all (premiseClosed relationHeads)) = true := by
  simp [rules_exact, observedRules, PlainBnfTrieSourceExecution.observedRule,
    premiseClosed, headedBy, relationHeads, runHeads, dependentsHeads,
    PlainBnfWakeSourceFamily.relationHeads, PlainBnfWakeSourceFamily.wakeHeads,
    PlainBnfHeapCombineSourceExecution.dependencyNames, PlainBnfHeapCombineSourceExecution.combineNames,
    PlainBnfHeapSourceExecution.rankNames, PlainBnfHeapSourceExecution.heapNames,
    PlainBnfReadinessSourceExecution.relationHeads, PlainBnfReadinessSourceExecution.readyHeads,
    PlainBnfProductiveSourceExecution.wholeHeads, PlainBnfProductiveSourceExecution.relationHeads,
    PlainBnfNullableSourceExecution.nullableHeads, knownHeads, lexicalLookupHeads, lexicalMatcherHeads,
    PlainBnfKnownNamesSourceExecution.knownNames, PlainBnfIndexedCollectorSourceExecution.trieNames,
    PlainBnfScheduleSourceExecution.scheduleNames,
    pattern, patternList, encode, SourceIntegerProvider.sourceVariableToken]

theorem dependents_closed : dependentsRules.all
    (fun rule => rule.premises.all (premiseClosed relationHeads)) = true := by
  rw [dependents_exact]
  rfl

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
  apply List.all_eq_true.mpr
  intro rule member
  apply List.all_eq_true.mpr
  intro premise present
  simp only [language, List.mem_append] at member
  rcases member with ((member | member) | member) | member
  · exact premise_mono _ _ (by decide) _
      (List.all_eq_true.mp (List.all_eq_true.mp
        PlainBnfWakeSourceFamily.family_closed rule member) premise present)
  · have included : rule ∈ PlainBnfHeapCombineSourceExecution.language.rewrites := by
      simp only [PlainBnfHeapCombineSourceExecution.language_partition, List.mem_append]
      exact Or.inr member
    exact premise_mono _ _ (by decide) _
      (List.all_eq_true.mp (List.all_eq_true.mp combine_closed rule included) premise present)
  · exact List.all_eq_true.mp (List.all_eq_true.mp dependents_closed rule member) premise present
  · exact List.all_eq_true.mp (List.all_eq_true.mp run_closed rule member) premise present

#print axioms source_translation_exact
#print axioms wake_extension
#print axioms combine_extension
#print axioms known_extension
#print axioms trie_extension
#print axioms dependents_answers
#print axioms run_rewriteAt
#print axioms family_closed

end Mettapedia.GSLT.Parsing.PlainBnfRunSourceFamily
