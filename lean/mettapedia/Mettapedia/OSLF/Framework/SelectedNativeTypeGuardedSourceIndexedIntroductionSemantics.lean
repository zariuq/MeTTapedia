import Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedFormationSemantics

/-!
# Generated-row selection for guarded selected-native introduction

This module identifies the actual guarded introduction row emitted for one
selected authored occurrence.  The proof follows the generator family and
does not enumerate a completed calculus.  Semantic soundness of an instance
remains a separate, source-indexed obligation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedIntroductionSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ContextualInference
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeAuthoredOccurrenceSyntax
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedIntroduction
open Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedIntroduction

private theorem mem_encodeContext_prepend
    (depth : Nat) (formulas : List Pattern) (tail : ContextSchema)
    {formula : Pattern} {formal : String × Nat}
    (formulaMem : formula ∈ formulas)
    (formalMem : formal ∈ patternMetavariableOccurrencesAt depth formula) :
    formal ∈ patternMetavariableOccurrencesAt depth
      (encodeContext (ContextSchema.prepend formulas tail)) := by
  induction formulas with
  | nil => simp at formulaMem
  | cons head rest inductionHypothesis =>
      rcases List.mem_cons.mp formulaMem with rfl | restMem
      · simp only [ContextSchema.prepend, encodeContext,
          patternMetavariableOccurrencesAt,
          patternsMetavariableOccurrencesAt]
        exact List.mem_append_left _ formalMem
      · simp only [ContextSchema.prepend, encodeContext,
          patternMetavariableOccurrencesAt,
          patternsMetavariableOccurrencesAt]
        apply List.mem_append_right
        simpa using inductionHypothesis restMem

/-- Every guarded introduction schema is an actual row of the final flat
guarded definition. -/
theorem introductionRule_mem_definition
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source)
    (separated : SupportSeparatedDemand demand)
    (profile : SelectedNativeTypeGuardedSourceIndexedIntroduction.PremiseProfile
      demand)
    (slot : Occurrence demand) :
    ContextualInference.lowerRule
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
          profile slot) ∈
      (SelectedNativeTypeGuardedSourceIndexedCalculus.definition
        demand separated profile).rules := by
  rw [SelectedNativeTypeGuardedSourceIndexedCalculus.definition_rules]
  apply List.mem_append.mpr
  apply Or.inr
  rw [SelectedNativeTypeGuardedSourceIndexedIntroduction.profiledRules]
  apply List.mem_flatten.mpr
  refine
    ⟨SelectedNativeTypeGuardedSourceIndexedIntroduction.rulesAt
      demand profile slot, ?_, ?_⟩
  · exact List.mem_ofFn.mpr ⟨slot, rfl⟩
  · simp [SelectedNativeTypeGuardedSourceIndexedIntroduction.rulesAt]

/-- Closing a guarded introduction over its inferred formal row changes no
premise or conclusion syntax. -/
theorem introductionConclusion_exact
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (profile : SelectedNativeTypeGuardedSourceIndexedIntroduction.PremiseProfile
      demand)
    (slot : Occurrence demand) :
    (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule
        profile slot).conclusion =
      SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionConclusion
        profile slot := by
  rfl

/-- Every typed authored endpoint binding is a declared formal of the exact
guarded introduction row.  The proof follows its retained variable context,
not a separately maintained formal inventory. -/
theorem introductionRule_declares_authoredBinding
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (profile : PremiseProfile demand) (slot : Occurrence demand)
    {name : String} {type : TypeExpr}
    (membership : (name, type) ∈ authoredBindings demand slot) :
    (renameVariable demand slot name, 0) ∈
      (introductionRule profile slot).metavariables := by
  obtain ⟨binding, bindingExact⟩ := List.get_of_mem membership
  have bindingName :
      (SelectedNativeTypeAuthoredVariableClaim.sourceBinding
        demand slot binding).1 = name := by
    simpa [SelectedNativeTypeAuthoredVariableClaim.sourceBinding] using
      congrArg Prod.fst bindingExact
  let claim := SelectedNativeTypeAuthoredVariableClaim.authoredClaim
    demand slot binding
  have claimMem : claim ∈ guardedAuthoredVariableClaims demand slot := by
    rw [guardedAuthoredVariableClaims,
      SelectedNativeTypeAuthoredVariableClaim.authoredClaims, List.mem_ofFn]
    exact ⟨binding, rfl⟩
  have formalInClaim : (renameVariable demand slot name, 0) ∈
      patternMetavariableOccurrencesAt 0 claim := by
    simp [claim, SelectedNativeTypeAuthoredVariableClaim.authoredClaim,
      SelectedNativeTypeAuthoredVariableClaim.claim, bindingName,
      patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt]
  have formalInVariableContext : (renameVariable demand slot name, 0) ∈
      patternMetavariableOccurrencesAt 0
        (encodeContext (guardedVariableContext demand slot)) := by
    exact mem_encodeContext_prepend 0 _ gamma claimMem formalInClaim
  have formalInConclusion : (renameVariable demand slot name, 0) ∈
      patternMetavariableOccurrencesAt 0
        (lowerSequent
          (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionConclusion
            profile slot)) := by
    unfold lowerSequent
      SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionConclusion
    simp only [patternMetavariableOccurrencesAt,
      patternsMetavariableOccurrencesAt]
    exact List.mem_append_left _ formalInVariableContext
  rw [SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRule]
  change (renameVariable demand slot name, 0) ∈
    (RuleSchema.occurrences
      (lowerRule
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionRuleCore
          profile slot))).eraseDups
  rw [List.mem_eraseDups]
  unfold RuleSchema.occurrences RuleSchema.patterns
  simp only [lowerRule]
  rw [patternsMetavariableOccurrencesAt_append]
  apply List.mem_append_right
  change (renameVariable demand slot name, 0) ∈
    patternsMetavariableOccurrencesAt 0
      [lowerSequent
        (SelectedNativeTypeGuardedSourceIndexedIntroduction.introductionConclusion
          profile slot)]
  simpa [patternsMetavariableOccurrencesAt] using formalInConclusion

/-- If the selected endpoint support is source-bound, every private endpoint
name is declared by the exact guarded introduction row. -/
theorem introductionRule_declares_endpoint
    {source : ValidatedLanguageDef}
    {demand : SelectedNativeTypeDemand source}
    (profile : PremiseProfile demand) (slot : Occurrence demand)
    (sourceBound : ∀ name ∈ endpointVariableNames demand slot,
      name ∈ (typingAt demand slot).site.rewrite.left.freeFvarNames) :
    ∀ name ∈ endpointVariableNames demand slot,
      (renameVariable demand slot name, 0) ∈
        (introductionRule profile slot).metavariables := by
  intro name member
  have nameMember : name ∈ (authoredBindings demand slot).map Prod.fst := by
    rw [authoredBindingNames_of_endpointSourceBound demand slot sourceBound]
    exact member
  obtain ⟨binding, bindingMember, bindingName⟩ := List.mem_map.mp nameMember
  rcases binding with ⟨bindingName', bindingType⟩
  simp only at bindingName
  subst bindingName'
  exact introductionRule_declares_authoredBinding profile slot bindingMember

#print axioms introductionRule_mem_definition
#print axioms introductionConclusion_exact
#print axioms introductionRule_declares_authoredBinding
#print axioms introductionRule_declares_endpoint

end Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedIntroductionSemantics
