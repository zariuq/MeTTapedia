import Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus

/-!
# Authored-syntax boundary for selected native-type introduction

The contextual calculus currently represents the subject and reduct of its
introduction rule by two private metavariables.  This module records the exact
consequence of that representation without assigning it a semantic meaning:
the generated subject coincides with the selected authored focus only when the
focus is literally the private `focus` metavariable, and the generated body
coincides with the authored right-hand side only when that side is literally
the private `reduct` metavariable.

These theorems are a structural discriminator for a later source-indexed
introduction rule.  They do not treat the current generated calculus as its own
semantic authority.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeIntroductionBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ContextualInference
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus

/-! ## Exact current rule shape -/

/-- The conclusion subject of the current introduction rule is the private
`focus` metavariable, independently of the selected authored focus. -/
theorem introduction_conclusion_uses_private_focus
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    (introductionRule demand slot).conclusion.conclusion =
      ContextualCarrierClaims.typingClaim
        (carrierAt demand (typingAt demand slot).focusType)
        (.fvar "focus")
        (modalType demand slot (.fvar "result-family")) := by
  rfl

/-- The current introduction conclusion uses the selected authored focus
exactly in the special case where that focus is the private metavariable. -/
theorem introduction_conclusion_matches_authored_focus_iff
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    (introductionRule demand slot).conclusion.conclusion =
        ContextualCarrierClaims.typingClaim
          (carrierAt demand (typingAt demand slot).focusType)
          (typingAt demand slot).site.focus
          (modalType demand slot (.fvar "result-family")) ↔
      (typingAt demand slot).site.focus = .fvar "focus" := by
  simp [introductionRule, ContextualCarrierClaims.typingClaim, eq_comm]

/-- The final premise of the current introduction rule types the private
`reduct` metavariable. -/
theorem introduction_body_uses_private_reduct
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    (introductionRule demand slot).premises.getLast?.map Sequent.conclusion =
      some (ContextualCarrierClaims.typingClaim
        (carrierAt demand (typingAt demand slot).rewriteType)
        (.fvar "reduct")
        (familyApplication demand slot (.fvar "result-family"))) := by
  simp [introductionRule]

/-- The current introduction body types the authored right-hand side exactly
when that side is literally the private `reduct` metavariable. -/
theorem introduction_body_matches_authored_rhs_iff
    {source : ValidatedLanguageDef}
    (demand : SelectedNativeTypeDemand source) (slot : Occurrence demand) :
    (introductionRule demand slot).premises.getLast?.map Sequent.conclusion =
        some (ContextualCarrierClaims.typingClaim
          (carrierAt demand (typingAt demand slot).rewriteType)
          (typingAt demand slot).site.rewrite.right
          (familyApplication demand slot (.fvar "result-family"))) ↔
      (typingAt demand slot).site.rewrite.right = .fvar "reduct" := by
  simp [introductionRule, ContextualCarrierClaims.typingClaim, eq_comm]

/-! ## Discriminating witnesses -/

namespace Canary

open ContextualModalSignature.Canary
open SelectedNativeTypeContextualCalculus.Canary

/-- Root selection of the contextual witness.  Unlike the middle occurrence,
its authored focus is a compound source term rather than the private `focus`
metavariable. -/
def rootTyping : DisplayedRewriteTyping source where
  site := DisplayedRewriteSite.root source.language ⟨0, by decide⟩
  rewriteType := middleTyping.rewriteType
  focusBoundPrefix := []
  focusType := middleTyping.rewriteType
  rewriteLeftTyped := by
    simpa [middleTyping, DisplayedRewriteSite.root,
      DisplayedRewriteSite.rewrite] using middleTyping.rewriteLeftTyped
  rewriteRightTyped := by
    simpa [middleTyping, DisplayedRewriteSite.root,
      DisplayedRewriteSite.rewrite] using middleTyping.rewriteRightTyped
  sourceIsObject := by
    simpa [middleTyping, DisplayedRewriteSite.root,
      DisplayedRewriteSite.rewrite] using middleTyping.sourceIsObject
  focusTyped := by
    simpa [middleTyping, DisplayedRewriteSite.root,
      DisplayedRewriteSite.rewrite] using middleTyping.rewriteLeftTyped

theorem rootGrounded :
    SelectedNativeTypeFoundation.CarrierGrounded rootTyping := by
  intro object membership
  simp [SelectedNativeTypeFoundation.requiredCarrierRoots, rootTyping,
    middleTyping, DisplayedRewriteSite.root,
    DisplayedContextProfile.carrierTypes, DisplayedContextProfile.bindings,
    DisplayedContextProfile.variableNames,
    DisplayedContextProfile.externalFreeFvarNames] at membership
  subst object
  exact middleGrounded _ (by
    simp [SelectedNativeTypeFoundation.requiredCarrierRoots, middleTyping])

def rootDemand : SelectedNativeTypeDemand source where
  occurrences :=
    [ProfiledRewriteOccurrence.constant rootTyping rootGrounded .star]

private abbrev rootSlot : Occurrence rootDemand :=
  ⟨0, by simp [rootDemand]⟩

/-- A compound authored focus is observably different from the private focus
token used by the current generated introduction rule. -/
theorem root_introduction_conclusion_not_authored_focus :
    (introductionRule rootDemand rootSlot).conclusion.conclusion ≠
      ContextualCarrierClaims.typingClaim
        (carrierAt rootDemand (typingAt rootDemand rootSlot).focusType)
        (typingAt rootDemand rootSlot).site.focus
        (modalType rootDemand rootSlot (.fvar "result-family")) := by
  rw [Ne, introduction_conclusion_matches_authored_focus_iff]
  simp [typingAt, occurrenceAt, rootDemand, rootTyping,
    ProfiledRewriteOccurrence.constant, DisplayedRewriteSite.root, source,
    sourceLanguage, contextualRewrite]

private abbrev middleSlot : Occurrence (middleDemand .star) :=
  ⟨0, by simp [middleDemand]⟩

/-- The authored middle-occurrence rewrite returns `focus`, so the current
private `reduct` premise is not its specified right-hand side. -/
theorem middle_introduction_body_not_authored_rhs :
    (introductionRule (middleDemand .star) middleSlot).premises.getLast?.map
        Sequent.conclusion ≠
      some (ContextualCarrierClaims.typingClaim
        (carrierAt (middleDemand .star)
          (typingAt (middleDemand .star) middleSlot).rewriteType)
        (typingAt (middleDemand .star) middleSlot).site.rewrite.right
        (familyApplication (middleDemand .star) middleSlot
          (.fvar "result-family"))) := by
  rw [Ne, introduction_body_matches_authored_rhs_iff]
  simp [DisplayedRewriteSite.rewrite, source, sourceLanguage,
    contextualRewrite]

end Canary

#print axioms introduction_conclusion_matches_authored_focus_iff
#print axioms introduction_body_matches_authored_rhs_iff
#print axioms Canary.root_introduction_conclusion_not_authored_focus
#print axioms Canary.middle_introduction_body_not_authored_rhs

end Mettapedia.OSLF.Framework.SelectedNativeTypeIntroductionBoundary
