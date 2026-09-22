import Mettapedia.OSLF.Framework.EngineOccurrenceExtensionGSLT
import Mettapedia.OSLF.Framework.EngineOccurrenceStructuralTransport
import Mettapedia.OSLF.Framework.WMCalculusLanguageDef
import Mettapedia.OSLF.Framework.RedexPosition
import Mettapedia.GSLT.LanguageDef.StructuralCategory

/-!
# Duplicate WM rules distinguish operational occurrences

This canary duplicates one existing unconditional authored rule. Both copies
produce the same reduct, but their numbered engine occurrences and hence
their proof-relevant GSLT events are distinct. The duplicated language is a
test fixture, not a replacement WM presentation.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Mettapedia.OSLF.Framework.WMEngineOccurrenceCanary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.RedexPosition
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework.WeightedOccurrence
open Mettapedia.OSLF.Framework.PremiseAwareOccurrence
open Mettapedia.OSLF.Framework.PremiseAwareOccurrenceExtension
open Mettapedia.OSLF.Framework.EngineOccurrenceExtensionGSLT
open Mettapedia.OSLF.Framework.EngineOccurrenceStructuralTransport
open Mettapedia.OSLF.Framework.EngineOccurrenceGSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Core.InteractionEvent.InteractionPresentation

private def base : BasePremiseEvaluator :=
  engineBasePremises RelationEnv.empty

private def duplicateRuleLanguage : LanguageDef :=
  { wmCoreLanguageDef with rewrites := [ruleCombineZero, ruleCombineZero] }

private def source : Pattern := pCombine pEvidenceZero pEvidenceZero
private def target : Pattern := pEvidenceZero

private def first : RewriteOccurrence :=
  ⟨0, ruleCombineZero.name, 0, target⟩

private def second : RewriteOccurrence :=
  ⟨1, ruleCombineZero.name, 0, target⟩

private theorem first_admitted :
    first ∈ rewriteAtOccurrences base duplicateRuleLanguage 1 source := by
  decide +kernel

private theorem second_admitted :
    second ∈ rewriteAtOccurrences base duplicateRuleLanguage 1 source := by
  decide +kernel

/-- The executable result list itself retains the duplicate multiplicity. -/
theorem two_returned_answers :
    rewriteAt base duplicateRuleLanguage 1 source = [target, target] := by
  decide +kernel

/-- Two actual accepted rule occurrences reach the same answer but remain
different operational events after the generic GSLT construction. -/
theorem two_events_one_answer :
    acceptedEvent base duplicateRuleLanguage 1 source target first first_admitted rfl ≠
      acceptedEvent base duplicateRuleLanguage 1 source target second second_admitted rfl := by
  apply acceptedEvent_ne_of_occurrence_ne
  decide +kernel

/-- Endpoint-only GSLT steps cannot reconstruct which duplicate authored
rule was selected; the proof-relevant-to-extensional map is not injective. -/
theorem event_erasure_not_injective :
    ¬ Function.Injective
      (fun event : (system base duplicateRuleLanguage 1).Event => event.erase) := by
  intro injective
  apply two_events_one_answer
  apply injective
  rfl

private def first_site_event :
    (interactionPresentation base duplicateRuleLanguage 1).Event
      (first.ruleIndex, first.ruleName, first.alternativeIndex)
      (.query source) (.answer source target) :=
  ⟨.accepted ⟨first, first_admitted, rfl⟩, rfl⟩

private def second_site_event :
    (interactionPresentation base duplicateRuleLanguage 1).Event
      (second.ruleIndex, second.ruleName, second.alternativeIndex)
      (.query source) (.answer source target) :=
  ⟨.accepted ⟨second, second_admitted, rfl⟩, rfl⟩

/-- A canary valuation reads the occurrence's local rule position. It is
not a resource-cost model; it tests whether site information survives. -/
private def rulePositionValuation :
    (interactionPresentation base duplicateRuleLanguage 1).EventCost Nat where
  cost := fun {site} _ => site.1

/-- This occurrence-sensitive valuation cannot be reconstructed from the
common extensional source and target of the two events. -/
theorem rule_position_not_endpoint_factorable :
    ¬ rulePositionValuation.FactorsThroughEndpoints := by
  apply EventCost.not_factorsThroughEndpoints_of_parallel_costs
    rulePositionValuation first_site_event second_site_event
  decide +kernel

/-- Erasing either operational event reports the same executable answer. -/
theorem target_is_executable :
    (system base duplicateRuleLanguage 1).theory.Step
      (.query source) (.answer source target) := by
  exact (step_iff_rewriteAt base duplicateRuleLanguage 1 source target).2
    (by decide +kernel)

/-! ## Theory extension does not preserve local occurrence indices -/

private def singleRuleLanguage : LanguageDef :=
  { wmCoreLanguageDef with rewrites := [ruleCombineZero] }

private def prefixedLanguage : LanguageDef :=
  { wmCoreLanguageDef with rewrites := [ruleEvidenceAdd, ruleCombineZero] }

/-- Both sides of the theory-change control are accepted authored
presentations, not malformed rule-list stand-ins. -/
theorem prefix_presentations_validate :
    singleRuleLanguage.validate = [] ∧ prefixedLanguage.validate = [] := by
  simp only [LanguageDef.validate, singleRuleLanguage, prefixedLanguage,
    wmCoreLanguageDef, List.flatMap_cons, List.flatMap_nil]
  simp only [LanguageDef.validateRewrite, LanguageDef.validateRulePatterns,
    ruleEvidenceAdd, ruleCombineZero, LanguageDef.patternFvarNames,
    ← fvarNames_eq, ← binderNames_eq, ← binderNamesList_eq]
  decide +kernel

private def singleValidated : ValidatedLanguageDef :=
  ⟨singleRuleLanguage, prefix_presentations_validate.1⟩

private def prefixedValidated : ValidatedLanguageDef :=
  ⟨prefixedLanguage, prefix_presentations_validate.2⟩

/-- This is a genuine structural morphism of validated presentations. Its
declaration map retains the old rule but, by design, says nothing about the
old rule's numerical position in the new rule list. -/
def prefixStructuralMorphism :
    StructuralMorphism singleValidated prefixedValidated where
  symbols := LanguageDefSymbolMap.id
  mapsTypes := by
    intro declaration member
    rw [mapTypeDecl_id]
    simpa [singleValidated, prefixedValidated, singleRuleLanguage,
      prefixedLanguage, wmCoreLanguageDef] using member
  mapsTerms := by
    intro rule member
    rw [mapGrammarRule_id]
    simpa [singleValidated, prefixedValidated, singleRuleLanguage,
      prefixedLanguage, wmCoreLanguageDef] using member
  mapsEquations := by
    intro equation member
    change equation ∈ ([] : List Equation) at member
    cases member
  mapsRewrites := by
    intro rule member
    rw [mapRewriteRule_id]
    change rule ∈ [ruleCombineZero] at member
    rcases List.mem_singleton.mp member with rfl
    change ruleCombineZero ∈ [ruleEvidenceAdd, ruleCombineZero]
    simp

/-- The original authored rule remains present after a distinct rule is
inserted before it; the new rule does not match this concrete source. -/
theorem prefixed_retains_rule :
    ruleCombineZero ∈ prefixedLanguage.rewrites := by
  simp [prefixedLanguage]

/-- The same request returns precisely the same executable answer before
and after the inert rule is prefixed. -/
theorem prefixed_answer_unchanged :
    rewriteAt base singleRuleLanguage 1 source =
      rewriteAt base prefixedLanguage 1 source := by
  decide +kernel

/-- The exact occurrence lists expose what answer equality forgets: the
old selected rule occupied position zero and now occupies position one. -/
theorem prefixed_occurrence_shift :
    rewriteAtOccurrences base singleRuleLanguage 1 source = [first] ∧
      rewriteAtOccurrences base prefixedLanguage 1 source = [second] := by
  decide +kernel

/-- The concrete shift is an instance of the general premise-aware
occurrence-transport law. Both operational premises are checked on the
actual two presentations, rather than assumed as a global equivalence. -/
theorem prefixed_shift_from_engine_law :
    rewriteAtOccurrences base prefixedLanguage 1 source =
      (rewriteAtOccurrences base singleRuleLanguage 1 source).map
        shiftRuleIndex := by
  apply rewriteAtOccurrences_prefix_shift base base
    singleRuleLanguage prefixedLanguage 0 ruleEvidenceAdd source rfl
  · decide +kernel
  · intro rule member
    have chosen : rule = ruleCombineZero := by
      simpa [singleRuleLanguage] using member
    subst rule
    decide +kernel

/-- The generic forward-transport law applies to the genuine validated
presentation extension: the old rule moves from slot zero to slot one, and
its complete ordered executable alternative list is unchanged here. -/
theorem prefixed_structural_map_admits :
    mapOccurrence LanguageDefSymbolMap.id (fun index => index + 1) first ∈
      rewriteAtOccurrences base prefixedLanguage 1
        (mapPattern LanguageDefSymbolMap.id source) := by
  apply mapOccurrence_admitted base base singleRuleLanguage prefixedLanguage
    LanguageDefSymbolMap.id (fun index => index + 1) 0 source
  · intro index rule ruleAt
    cases index with
    | zero =>
        have chosen : ruleCombineZero = rule := by
          simpa [singleRuleLanguage] using ruleAt
        subst rule
        simp [prefixedLanguage, mapRewriteRule_id]
    | succ index => simp [singleRuleLanguage] at ruleAt
  · intro index rule ruleAt
    cases index with
    | zero =>
        have chosen : ruleCombineZero = rule := by
          simpa [singleRuleLanguage] using ruleAt
        subst rule
        have mapIdentity : mapPattern LanguageDefSymbolMap.id = id :=
          funext mapPattern_id
        simpa only [mapRewriteRule_id, mapPattern_id, mapIdentity, List.map_id] using
          (show applyRuleUsing base prefixedLanguage
              (rewriteAt base prefixedLanguage 0) ruleCombineZero source =
            applyRuleUsing base singleRuleLanguage
              (rewriteAt base singleRuleLanguage 0) ruleCombineZero source from by
            decide +kernel)
    | succ index => simp [singleRuleLanguage] at ruleAt
  · rw [prefixed_occurrence_shift.1]
    simp [first]

/-- The mapped old occurrence is precisely the selected occurrence at its
new slot, not just an unrelated witness of target support. -/
theorem prefixed_structural_map_is_selected :
    mapOccurrence LanguageDefSymbolMap.id (fun index => index + 1) first =
      second := by
  simp [mapOccurrence, first, second, mapPattern_id]
  rfl

/-- At this concrete request the rule-prefix extension is exact on the
proof-relevant query/answer fibre, even though raw occurrence numbers are
not identical. The result is not a whole-language exactness claim. -/
noncomputable def prefixedEvidenceEquiv :
    (judgment base singleRuleLanguage 1).Evidence source target ≃
      (judgment base prefixedLanguage 1).Evidence source target :=
  evidenceEquivOfShift base base singleRuleLanguage prefixedLanguage 1
    source target prefixed_shift_from_engine_law

private def singleSelected :
    (judgment base singleRuleLanguage 1).Evidence source target :=
  ⟨first, by rw [prefixed_occurrence_shift.1]; simp, rfl⟩

/-- The inhabited source fibre maps its actual selected occurrence to the
renumbered target occurrence, retaining the authored name, alternative, and
answer rather than inventing a convenient target witness. -/
theorem prefixedEvidenceEquiv_selected_occurrence :
    (prefixedEvidenceEquiv singleSelected).val = second := by
  calc
    (prefixedEvidenceEquiv singleSelected).val =
        shiftRuleIndex singleSelected.val :=
      evidenceEquivOfShift_occurrence base base singleRuleLanguage
        prefixedLanguage 1 source target prefixed_shift_from_engine_law
        singleSelected
    _ = second := rfl

/-- Even a source-faithful extension that leaves this answer unchanged does
not carry its numbered occurrence by the identity function. -/
theorem prefixed_identity_occurrence_fails :
    first ∈ rewriteAtOccurrences base singleRuleLanguage 1 source ∧
      first ∉ rewriteAtOccurrences base prefixedLanguage 1 source ∧
      second ∈ rewriteAtOccurrences base prefixedLanguage 1 source ∧
      first.target = second.target := by
  rw [prefixed_occurrence_shift.1, prefixed_occurrence_shift.2]
  decide +kernel

#print axioms two_events_one_answer
#print axioms event_erasure_not_injective
#print axioms rule_position_not_endpoint_factorable
#print axioms two_returned_answers
#print axioms target_is_executable
#print axioms prefixed_answer_unchanged
#print axioms prefix_presentations_validate
#print axioms prefixStructuralMorphism
#print axioms prefixed_occurrence_shift
#print axioms prefixed_shift_from_engine_law
#print axioms prefixed_structural_map_admits
#print axioms prefixed_structural_map_is_selected
#print axioms prefixedEvidenceEquiv_selected_occurrence
#print axioms prefixed_identity_occurrence_fails

end Mettapedia.OSLF.Framework.WMEngineOccurrenceCanary
