import Mettapedia.GSLT.Parsing.PlainBnfReadinessSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfWakeSourceExecution

/-!
# The authored Wake source family

This ordered composition shares the actual trie clauses once. Readiness and
scheduling remain recursive source calls. Filtering by disjoint relation heads
recovers each complete component, with exact bounded answer-list preservation.
No readiness or scheduling answer is supplied by the primitive environment.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfWakeSourceFamily

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open PlainBnfIndexedCollectorSourceExecution (headedBy premiseClosed)
open PlainBnfReadinessEnvironment
open PlainBnfReadinessSourceExecution (finite_disjoint)
open PlainBnfLexicalMatcherSourceExecution (relations)
open SourceSExprPatternInstantiation (pattern patternList)
open SourceSExprPatternCodec (encode)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

def language : LanguageDef :=
  { name := "PlainBnfAuthoredWake", types := [], terms := [], equations := [],
    rewrites := PlainBnfHeapSourceExecution.language.rewrites ++
      PlainBnfReadinessSourceExecution.language.rewrites ++
      PlainBnfScheduleSourceExecution.scheduleRules ++ PlainBnfWakeSourceExecution.rules }

def wakeHeads :=
  ["BNFDiscoveryWakeV1", "BNFDiscoveryAfterScheduledV1", "BNFDiscoveryAfterReadyV1"]

def relationHeads := PlainBnfHeapCombineSourceExecution.dependencyNames ++
  PlainBnfReadinessSourceExecution.relationHeads ++
  PlainBnfScheduleSourceExecution.scheduleNames ++ wakeHeads

/-- Proof observations, checked against the translated source occurrences.
They do not define the executable family. -/
def observedRules : List RewriteRule := [
  PlainBnfTrieSourceExecution.observedRule "bnf-discovery-wake-nil-v1"
    (metta_sexpr% petta "(BNFDiscoveryWakeV1 ?mode BNFDiscoveryDefinitionsNilV1 ?origin ?known ?lexicals ?queues)")
    (metta_sexpr% petta "(?queues)"),
  PlainBnfTrieSourceExecution.observedRule "bnf-discovery-wake-cons-v1"
    (metta_sexpr% petta "(BNFDiscoveryWakeV1 ?mode (BNFDiscoveryDefinitionsConsV1 (BNFDiscoveryDefinitionV1 ?rank ?name ?expression ?span) ?rest) ?origin ?known ?lexicals (BNFDiscoveryQueuesV1 ?current ?following ?scheduled))")
    (metta_sexpr% petta "(?after)")
    [.congruence (pattern (metta_sexpr% petta "(BNFGraphTrieLookupV1 ?name ?scheduled)"))
        (pattern (metta_sexpr% petta "(?lookup)")),
      .congruence (pattern (metta_sexpr% petta "(BNFDiscoveryAfterScheduledV1 ?lookup ?mode (BNFDiscoveryDefinitionV1 ?rank ?name ?expression ?span) ?rest ?origin ?known ?lexicals (BNFDiscoveryQueuesV1 ?current ?following ?scheduled))"))
        (pattern (metta_sexpr% petta "(?after)"))],
  PlainBnfTrieSourceExecution.observedRule "bnf-discovery-already-scheduled-v1"
    (metta_sexpr% petta "(BNFDiscoveryAfterScheduledV1 (BNFIndexFoundV1 ?name) ?mode ?node ?rest ?origin ?known ?lexicals ?before)")
    (metta_sexpr% petta "(?after)")
    [.congruence (pattern (metta_sexpr% petta "(BNFDiscoveryWakeV1 ?mode ?rest ?origin ?known ?lexicals ?before)"))
        (pattern (metta_sexpr% petta "(?after)"))],
  PlainBnfTrieSourceExecution.observedRule "bnf-discovery-not-scheduled-v1"
    (metta_sexpr% petta "(BNFDiscoveryAfterScheduledV1 BNFIndexMissingV1 ?mode (BNFDiscoveryDefinitionV1 ?rank ?name ?expression ?span) ?rest ?origin ?known ?lexicals ?before)")
    (metta_sexpr% petta "(?after)")
    [.congruence (pattern (metta_sexpr% petta "(BNFDiscoveryReadyV1 ?mode ?expression ?known ?lexicals)"))
        (pattern (metta_sexpr% petta "(?ready)")),
      .congruence (pattern (metta_sexpr% petta "(BNFDiscoveryAfterReadyV1 ?ready ?mode (BNFDiscoveryDefinitionV1 ?rank ?name ?expression ?span) ?rest ?origin ?known ?lexicals ?before)"))
        (pattern (metta_sexpr% petta "(?after)"))],
  PlainBnfTrieSourceExecution.observedRule "bnf-discovery-not-ready-v1"
    (metta_sexpr% petta "(BNFDiscoveryAfterReadyV1 BNFNoV1 ?mode ?node ?rest ?origin ?known ?lexicals ?before)")
    (metta_sexpr% petta "(?after)")
    [.congruence (pattern (metta_sexpr% petta "(BNFDiscoveryWakeV1 ?mode ?rest ?origin ?known ?lexicals ?before)"))
        (pattern (metta_sexpr% petta "(?after)"))],
  PlainBnfTrieSourceExecution.observedRule "bnf-discovery-ready-v1"
    (metta_sexpr% petta "(BNFDiscoveryAfterReadyV1 BNFYesV1 ?mode ?node ?rest ?origin ?known ?lexicals ?before)")
    (metta_sexpr% petta "(?after)")
    [.congruence (pattern (metta_sexpr% petta "(BNFDiscoveryScheduleV1 ?node ?origin ?before)"))
        (pattern (metta_sexpr% petta "(?next)")),
      .congruence (pattern (metta_sexpr% petta "(BNFDiscoveryWakeV1 ?mode ?rest ?origin ?known ?lexicals ?next)"))
        (pattern (metta_sexpr% petta "(?after)"))]]

theorem rules_exact : PlainBnfWakeSourceExecution.rules = observedRules := rfl

theorem source_rule_count : language.rewrites.length = 105 := by
  simp only [language, List.length_append,
    PlainBnfHeapSourceExecution.source_rule_count, PlainBnfReadinessSourceExecution.source_rule_count]
  rfl

theorem wake_heads : PlainBnfWakeSourceExecution.rules.all
    (fun rule => headedBy wakeHeads rule.left) = true := by
  simp [rules_exact, observedRules, PlainBnfTrieSourceExecution.observedRule,
    headedBy, wakeHeads, pattern, patternList, encode, SourceIntegerProvider.sourceVariableToken]

theorem wake_closed : PlainBnfWakeSourceExecution.rules.all
    (fun rule => rule.premises.all (premiseClosed relationHeads)) = true := by
  simp [rules_exact, observedRules, PlainBnfTrieSourceExecution.observedRule,
    premiseClosed, headedBy, relationHeads, wakeHeads,
    PlainBnfHeapCombineSourceExecution.dependencyNames,
    PlainBnfHeapSourceExecution.rankNames, PlainBnfHeapSourceExecution.heapNames,
    PlainBnfReadinessSourceExecution.relationHeads, PlainBnfReadinessSourceExecution.readyHeads,
    PlainBnfProductiveSourceExecution.wholeHeads, PlainBnfProductiveSourceExecution.relationHeads,
    PlainBnfNullableSourceExecution.nullableHeads, knownHeads, lexicalLookupHeads, lexicalMatcherHeads,
    PlainBnfKnownNamesSourceExecution.knownNames, PlainBnfIndexedCollectorSourceExecution.trieNames,
    PlainBnfScheduleSourceExecution.scheduleNames,
    pattern, patternList, encode, SourceIntegerProvider.sourceVariableToken]

private theorem trie_heads : PlainBnfTrieSourceExecution.language.rewrites.all
    (fun rule => headedBy PlainBnfIndexedCollectorSourceExecution.trieNames rule.left) = true := by
  simp [PlainBnfTrieSourceExecution.source_rules_exact, PlainBnfTrieSourceExecution.observedRules,
    PlainBnfTrieSourceExecution.observedRule, headedBy, pattern, patternList,
    SourceIntegerProvider.sourceVariableToken, PlainBnfIndexedCollectorSourceExecution.trieNames, encode]

theorem family_heads : language.rewrites.all
    (fun rule => headedBy relationHeads rule.left) = true := by
  apply List.all_eq_true.mpr
  intro rule member
  simp only [language, List.mem_append] at member
  rcases member with ((member | member) | member) | member
  · exact headedBy_mono _ _ (by decide) _
      (List.all_eq_true.mp PlainBnfHeapCombineSourceExecution.dependencies_heads rule member)
  · exact headedBy_mono _ _ (by decide) _
      (List.all_eq_true.mp PlainBnfReadinessSourceExecution.family_heads rule member)
  · exact headedBy_mono _ _ (by decide) _
      (List.all_eq_true.mp PlainBnfScheduleSourceExecution.schedule_heads rule member)
  · exact headedBy_mono _ _ (by decide) _ (List.all_eq_true.mp wake_heads rule member)

private theorem premise_mono (small large : List String) (included : small ⊆ large)
    (premise : Premise) (closed : premiseClosed small premise = true) :
    premiseClosed large premise = true := by
  cases premise with
  | congruence source target => exact headedBy_mono small large included source closed
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
        PlainBnfHeapCombineSourceExecution.dependencies_closed rule member) premise present)
  · exact premise_mono _ _ (by decide) _
      (List.all_eq_true.mp (List.all_eq_true.mp
        PlainBnfReadinessSourceExecution.family_closed rule member) premise present)
  · have included : rule ∈ PlainBnfScheduleSourceExecution.language.rewrites := by
      simp only [PlainBnfScheduleSourceExecution.language, List.mem_append]
      exact Or.inr member
    exact premise_mono _ _ (by decide) _
      (List.all_eq_true.mp (List.all_eq_true.mp
        PlainBnfScheduleSourceExecution.family_closed rule included) premise present)
  · exact List.all_eq_true.mp (List.all_eq_true.mp wake_closed rule member) premise present

theorem ready_selection : language.rewrites.filter
    (fun rule => headedBy PlainBnfReadinessSourceExecution.relationHeads rule.left) =
      PlainBnfReadinessSourceExecution.language.rewrites := by
  simp only [language, List.filter_append]
  rw [filter_disjoint _ _ (by apply finite_disjoint; decide) _
      PlainBnfHeapCombineSourceExecution.dependencies_heads,
    filter_included _ _ (List.Subset.refl _) _ PlainBnfReadinessSourceExecution.family_heads,
    filter_disjoint _ _ (by apply finite_disjoint; decide) _
      PlainBnfScheduleSourceExecution.schedule_heads,
    filter_disjoint _ _ (by apply finite_disjoint; decide) _ wake_heads]
  simp

theorem schedule_selection : language.rewrites.filter
    (fun rule => headedBy PlainBnfScheduleSourceExecution.relationHeads rule.left) =
      PlainBnfScheduleSourceExecution.language.rewrites := by
  simp only [language, PlainBnfReadinessSourceExecution.language,
    PlainBnfProductiveSourceExecution.language, PlainBnfProductiveSourceExecution.dependencies,
    PlainBnfKnownNamesSourceExecution.language_partition, List.filter_append]
  rw [filter_included _ _ (by decide) _ PlainBnfHeapCombineSourceExecution.dependencies_heads,
    filter_included _ _ (by decide) _ trie_heads,
    filter_disjoint _ _ (by apply finite_disjoint; decide) _
      PlainBnfKnownNamesSourceExecution.known_heads,
    filter_disjoint _ _ (by apply finite_disjoint; decide) _ lexical_lookup_heads,
    filter_disjoint _ _ (by apply finite_disjoint; decide) _ lexical_matcher_heads,
    filter_disjoint _ _ (by apply finite_disjoint; decide) _
      PlainBnfProductiveSourceExecution.family_heads,
    filter_disjoint _ _ (by apply finite_disjoint; decide) _
      PlainBnfNullableSourceExecution.nullable_heads,
    filter_disjoint _ _ (by apply finite_disjoint; decide) _ PlainBnfReadinessSourceExecution.ready_heads,
    filter_included _ _ (by decide) _ PlainBnfScheduleSourceExecution.schedule_heads,
    filter_disjoint _ _ (by apply finite_disjoint; decide) _ wake_heads]
  simp [PlainBnfScheduleSourceExecution.language]

theorem ready_extension (fuel : Nat) (source : Pattern)
    (headed : headedBy PlainBnfReadinessSourceExecution.relationHeads source = true) :
    rewriteAt (engineBasePremises relations) language fuel source =
      rewriteAt (engineBasePremises relations) PlainBnfReadinessSourceExecution.language fuel source := by
  apply filtered_extension _ relations _ _ ready_selection
  · intro rule member premise present
    exact List.all_eq_true.mp (List.all_eq_true.mp
      PlainBnfReadinessSourceExecution.family_closed rule member) premise present
  · intro rule member foreign input itsHead
    exact foreign_head_does_not_match _ relationHeads _ _
      (List.all_eq_true.mp family_heads rule member) foreign itsHead
  · exact headed

theorem schedule_extension (fuel : Nat) (source : Pattern)
    (headed : headedBy PlainBnfScheduleSourceExecution.relationHeads source = true) :
    rewriteAt (engineBasePremises relations) language fuel source =
      rewriteAt (engineBasePremises PlainBnfTrieSourceExecution.scalarRelations)
        PlainBnfScheduleSourceExecution.language fuel source := by
  rw [filtered_extension _ relations _ _ schedule_selection (by
    intro rule member premise present
    exact List.all_eq_true.mp (List.all_eq_true.mp
      PlainBnfScheduleSourceExecution.family_closed rule member) premise present) (by
    intro rule member foreign input itsHead
    exact foreign_head_does_not_match _ relationHeads _ _
      (List.all_eq_true.mp family_heads rule member) foreign itsHead) fuel source headed]
  exact schedule_environment fuel source

theorem trie_extension (fuel : Nat) (source : Pattern)
    (headed : headedBy PlainBnfIndexedCollectorSourceExecution.trieNames source = true) :
    rewriteAt (engineBasePremises relations) language fuel source =
      rewriteAt (engineBasePremises PlainBnfTrieSourceExecution.scalarRelations)
        PlainBnfTrieSourceExecution.language fuel source := by
  rw [schedule_extension fuel source (headedBy_mono _ _ (by decide) _ headed)]
  exact PlainBnfScheduleSourceExecution.trie_conservative_extension _ fuel source headed

theorem wake_rewriteAt (fuel : Nat) (source : Pattern)
    (headed : headedBy wakeHeads source = true) :
    rewriteAt (engineBasePremises relations) language (fuel + 1) source =
      PlainBnfWakeSourceExecution.rules.flatMap (fun rule =>
        applyRuleUsing (engineBasePremises relations) language
          (rewriteAt (engineBasePremises relations) language fuel) rule source) := by
  apply PlainBnfHeapSourceExecution.skip_unmatched_prefix _ language
    (PlainBnfHeapSourceExecution.language.rewrites ++
      PlainBnfReadinessSourceExecution.language.rewrites ++
      PlainBnfScheduleSourceExecution.scheduleRules) PlainBnfWakeSourceExecution.rules rfl
  intro rule member
  simp only [List.mem_append] at member
  rcases member with (member | member) | member
  · exact PlainBnfIndexedCollectorSourceExecution.disjoint_heads_do_not_match _ wakeHeads
      (by apply finite_disjoint; decide) _ _
      (List.all_eq_true.mp PlainBnfHeapCombineSourceExecution.dependencies_heads rule member) headed
  · exact PlainBnfIndexedCollectorSourceExecution.disjoint_heads_do_not_match _ wakeHeads
      (by apply finite_disjoint; decide) _ _
      (List.all_eq_true.mp PlainBnfReadinessSourceExecution.family_heads rule member) headed
  · exact PlainBnfIndexedCollectorSourceExecution.disjoint_heads_do_not_match _ wakeHeads
      (by apply finite_disjoint; decide) _ _
      (List.all_eq_true.mp PlainBnfScheduleSourceExecution.schedule_heads rule member) headed

#print axioms ready_extension
#print axioms schedule_extension
#print axioms trie_extension
#print axioms wake_rewriteAt

end Mettapedia.GSLT.Parsing.PlainBnfWakeSourceFamily
