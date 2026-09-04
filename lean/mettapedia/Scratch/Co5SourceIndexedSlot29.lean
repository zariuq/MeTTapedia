import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileNTT
import Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedCalculus

set_option autoImplicit false

namespace Scratch.Co5SourceIndexedSlot29

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedIntroduction
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational

theorem separated : SupportSeparatedDemand demand := by
  intro slot
  have membership := List.get_mem demand.occurrences slot
  change DisplayedRewriteVariableProfile.sharedNames
    (demand.occurrences.get slot).typing.site = []
  unfold demand at membership ⊢
  unfold selectedOccurrences at membership ⊢
  simp only [List.mem_flatMap] at membership
  rcases membership with ⟨index, _indexMembership, occurrenceMembership⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at occurrenceMembership
  rcases occurrenceMembership with equality | equality
  · rw [equality]
    simp [profiledRoot, ProfiledRewriteOccurrence.constant, rootTyping]
  · rw [equality]
    simp [profiledRoot, ProfiledRewriteOccurrence.constant, rootTyping]

private def slot29 : Occurrence demand := ⟨29, by decide⟩
private def root14 : Fin coldSource.language.rewrites.length := ⟨14, by decide⟩

private theorem slot29_occurrence_exact :
    occurrenceAt demand slot29 = profiledRoot root14 .box := by rfl

private theorem slot29_typing_exact :
    typingAt demand slot29 = rootTyping root14 := by rfl

private theorem slot29_bindings_exact : bindingsAt demand slot29 = [] := by rfl

private theorem slot29_endpoint_names_exact :
    SelectedNativeTypeAuthoredOccurrenceSyntax.endpointVariableNames
        demand slot29 =
      ["owner", "revision", "head", "arity", "occurrence",
        "declarationHead", "inputs", "output", "remaining", "modes",
        "accepted"] := by
  unfold SelectedNativeTypeAuthoredOccurrenceSyntax.endpointVariableNames
  rw [slot29_typing_exact]
  simp [rootTyping, root14, DisplayedRewriteSite.root,
    DisplayedRewriteSite.rewrite, coldSource,
    language, transitions, openResultTransition, compileResult,
    declarationPattern, compileHalted, outsideFragmentPattern,
    Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.freeFvarNames,
    List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]

private theorem slot29_authored_metavariables_exact :
    SelectedNativeTypeAuthoredOccurrenceSyntax.authoredMetavariables
        demand slot29 =
      [(SelectedNativeTypeAuthoredOccurrenceSyntax.authoredVariableName 29 0, 0),
       (SelectedNativeTypeAuthoredOccurrenceSyntax.authoredVariableName 29 1, 0),
       (SelectedNativeTypeAuthoredOccurrenceSyntax.authoredVariableName 29 2, 0),
       (SelectedNativeTypeAuthoredOccurrenceSyntax.authoredVariableName 29 3, 0),
       (SelectedNativeTypeAuthoredOccurrenceSyntax.authoredVariableName 29 4, 0),
       (SelectedNativeTypeAuthoredOccurrenceSyntax.authoredVariableName 29 5, 0),
       (SelectedNativeTypeAuthoredOccurrenceSyntax.authoredVariableName 29 6, 0),
       (SelectedNativeTypeAuthoredOccurrenceSyntax.authoredVariableName 29 7, 0),
       (SelectedNativeTypeAuthoredOccurrenceSyntax.authoredVariableName 29 8, 0),
       (SelectedNativeTypeAuthoredOccurrenceSyntax.authoredVariableName 29 9, 0),
       (SelectedNativeTypeAuthoredOccurrenceSyntax.authoredVariableName 29 10, 0)] := by
  rw [SelectedNativeTypeAuthoredOccurrenceSyntax.authoredMetavariables,
    slot29_endpoint_names_exact]
  rfl

private theorem slot29_authored_bindings_exact :
    authoredBindings demand slot29 =
      [("owner", .base "CGOwner"), ("revision", .base "CGNat"),
       ("head", .base "CGName"), ("arity", .base "CGNat"),
       ("occurrence", .base "CGNat"),
       ("declarationHead", .base "CGName"),
       ("inputs", .base "CGTerms"), ("output", .base "CGTerm"),
       ("remaining", .base "CGDeclarations"),
       ("modes", .base "CGArgModes"), ("accepted", .base "CGPlans")] := by
  unfold authoredBindings DisplayedRewriteVariableProfile.typedBindings
  rw [slot29_typing_exact, slot29_endpoint_names_exact]
  simp [DisplayedRewriteVariableProfile.variableType?, rootTyping,
    DisplayedRewriteSite.root, DisplayedRewriteSite.rewrite, coldSource,
    language, transitions, openResultTransition, compileResult,
    declarationPattern, WellSorted.FreeTypeContext.ofList]

private theorem slot29_authored_source_exact :
    SelectedNativeTypeAuthoredOccurrenceSyntax.authoredSource demand slot29 =
      .apply "petta-call-guard:compile-result"
        [.fvar (SelectedNativeTypeAuthoredOccurrenceSyntax.authoredVariableName 29 0),
         .fvar (SelectedNativeTypeAuthoredOccurrenceSyntax.authoredVariableName 29 1),
         .fvar (SelectedNativeTypeAuthoredOccurrenceSyntax.authoredVariableName 29 2),
         .fvar (SelectedNativeTypeAuthoredOccurrenceSyntax.authoredVariableName 29 3),
         .apply "petta-call-guard:declaration"
           [.fvar (SelectedNativeTypeAuthoredOccurrenceSyntax.authoredVariableName 29 4),
            .fvar (SelectedNativeTypeAuthoredOccurrenceSyntax.authoredVariableName 29 5),
            .fvar (SelectedNativeTypeAuthoredOccurrenceSyntax.authoredVariableName 29 6),
            .fvar (SelectedNativeTypeAuthoredOccurrenceSyntax.authoredVariableName 29 7)],
         .fvar (SelectedNativeTypeAuthoredOccurrenceSyntax.authoredVariableName 29 8),
         .fvar (SelectedNativeTypeAuthoredOccurrenceSyntax.authoredVariableName 29 9),
         .fvar (SelectedNativeTypeAuthoredOccurrenceSyntax.authoredVariableName 29 10)] := by
  unfold SelectedNativeTypeAuthoredOccurrenceSyntax.authoredSource
    SelectedNativeTypeAuthoredOccurrenceSyntax.authoredPattern
  rw [slot29_typing_exact]
  simp [rootTyping, DisplayedRewriteSite.root, DisplayedRewriteSite.rewrite,
    coldSource, language, transitions, openResultTransition, compileResult,
    declarationPattern,
    SelectedNativeTypeAuthoredOccurrenceSyntax.renameVariable,
    slot29_endpoint_names_exact]

private theorem slot29_authored_focus_exact :
    SelectedNativeTypeAuthoredOccurrenceSyntax.authoredFocus demand slot29 =
      SelectedNativeTypeAuthoredOccurrenceSyntax.authoredSource demand slot29 := by
  unfold SelectedNativeTypeAuthoredOccurrenceSyntax.authoredFocus
    SelectedNativeTypeAuthoredOccurrenceSyntax.authoredSource
    SelectedNativeTypeAuthoredOccurrenceSyntax.authoredPattern
  rw [slot29_typing_exact]
  rfl

private theorem slot29_authored_target_exact :
    SelectedNativeTypeAuthoredOccurrenceSyntax.authoredTarget demand slot29 =
      .apply "petta-call-guard:compile-halted"
        [.apply "petta-call-guard:outside-fragment" []] := by
  unfold SelectedNativeTypeAuthoredOccurrenceSyntax.authoredTarget
    SelectedNativeTypeAuthoredOccurrenceSyntax.authoredPattern
  rw [slot29_typing_exact]
  rfl

private def sourceIndexedDefinition : CalculusLanguageDef :=
  SelectedNativeTypeSourceIndexedCalculus.definition demand separated

private def localRuleBatch (offset : Nat) : List RuleSchema :=
  (sourceIndexedDefinition.rules.drop offset).take 8

#eval sourceIndexedDefinition.rules.length
#eval (sourceIndexedDefinition.rules.filter fun rule =>
  !RuleSchema.isLocallyValid rule).length
#eval RuleSchema.metavariableNames
  (ContextualInference.lowerRule
    (SelectedNativeTypeSourceIndexedIntroduction.introductionRule demand slot29))
#eval (RuleSchema.occurrences
  (ContextualInference.lowerRule
    (SelectedNativeTypeSourceIndexedIntroduction.introductionRule demand slot29))).eraseDups

example :
    (localRuleBatch 72).all RuleSchema.isLocallyValid = true := by
  unfold localRuleBatch sourceIndexedDefinition
  decide +kernel

end Scratch.Co5SourceIndexedSlot29
