import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryMatchedFramesProvenancedAlignment

/-!
# The bichromatic recursive closure

The recursive results already in the tree each retain the compact pair
together with **one** semantic action: `RhoCanonicalPairRecursiveResult`
keeps the one-depth apex action, `RhoCanonicalPairRecursiveTwoDepthResult`
the separated-depth action.  Neither is reconstructible from the compact
pair alone — compact elaboration forgets parent atom slots — and neither
action substitutes for the other: the one-depth action serves the
same-colour matched-frame arms, while a foreign quote separates restoration
depth from canonical-key depth and demands the two-depth action.

Every route that projects one of the actions away before the recursion has
delivered both has failed at some arm.  The right recursive invariant is
therefore the *product*: retain the compact pair **and both actions**, and
only project at the point of consumption.

This module supplies that carrier, its syntax-directed step, and the
well-founded closure of the step — the exact analogue of
`RhoCanonicalPairRecursiveResult.nonempty_of_step`, whose measure argument
is unchanged because the extra retained action lives entirely inside the
result and never touches termination.  The projections connect the carrier
to every existing consumer of the two single-action results.

The step itself is the remaining semantic content; nothing here inhabits it.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- **Bichromatic recursive closure.**  The compact pair together with both
retained semantic actions.  The one-depth action serves same-colour
matched-frame consumption; the two-depth action serves the foreign-quote
arms, where restoration depth and canonical-key depth separate. -/
structure RhoCanonicalPairBichromaticResult
    (declarationColor : CostStaticColor)
    {targetFree : WellSorted.FreeTypeContext}
    (available outer : List TypeExpr) (leftPattern rightPattern : Pattern)
    (type : TypeExpr) : Type where
  pair : CostCanonicalPairElaboration rhoCIGSLT
    rhoHereditaryNormalizationKernel targetFree available outer leftPattern
      rightPattern type
  oneDepth : @RhoReachedPlanPairApexAction declarationColor targetFree
    available leftPattern rightPattern type
  twoDepth : @RhoReachedPlanPairTwoDepthApexAction declarationColor targetFree
    available leftPattern rightPattern type

namespace RhoCanonicalPairBichromaticResult

/-- Project to the one-depth recursive result. -/
def toRecursiveResult {declarationColor : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {leftPattern rightPattern : Pattern}
    {type : TypeExpr}
    (result : @RhoCanonicalPairBichromaticResult declarationColor targetFree
      available outer leftPattern rightPattern type) :
    @RhoCanonicalPairRecursiveResult declarationColor targetFree available
      outer leftPattern rightPattern type :=
  ⟨result.pair, result.oneDepth⟩

/-- Project to the separated-depth recursive result. -/
def toTwoDepthResult {declarationColor : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {leftPattern rightPattern : Pattern}
    {type : TypeExpr}
    (result : @RhoCanonicalPairBichromaticResult declarationColor targetFree
      available outer leftPattern rightPattern type) :
    @RhoCanonicalPairRecursiveTwoDepthResult declarationColor targetFree
      available outer leftPattern rightPattern type :=
  ⟨result.pair, result.twoDepth⟩

end RhoCanonicalPairBichromaticResult

/-- One syntax-directed layer for the bichromatic closure.  Identical
telescope to `RhoCanonicalPairRecursiveStep`; only the retained result is
richer, on both the callback side and the conclusion side. -/
def RhoCanonicalPairBichromaticStep
    (declarationColor : CostStaticColor) : Prop :=
  ∀ {targetFree : WellSorted.FreeTypeContext}
      {available outer : List TypeExpr} {leftPattern rightPattern : Pattern}
      {type : TypeExpr},
    rhoCanonicalRecursiveTypeDomain.Admissible type →
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type leftPattern →
    ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type rightPattern →
    canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation) leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation) rightPattern →
    (∀ {childAvailable childOuter : List TypeExpr}
        {leftChild rightChild : Pattern} {childType : TypeExpr},
      ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree childAvailable childType leftChild →
      ReflectiveWellSorted.OpenPatternWellSorted
        rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
        targetFree childAvailable childType rightChild →
      canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) leftChild =
        canonicalize
          (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
            rhoReflectivePresentation) rightChild →
      sizeOf leftChild + sizeOf rightChild <
        sizeOf leftPattern + sizeOf rightPattern →
      rhoCanonicalRecursiveTypeDomain.Admissible childType →
      Nonempty (@RhoCanonicalPairBichromaticResult declarationColor targetFree
        childAvailable childOuter leftChild rightChild childType)) →
    Nonempty (@RhoCanonicalPairBichromaticResult declarationColor targetFree
      available outer leftPattern rightPattern type)

/-- Close a bichromatic step by the same well-founded measure as the ordinary
paired elaborator.  Both retained actions live inside the result; the
recursion is untouched. -/
noncomputable def RhoCanonicalPairBichromaticResult.nonempty_of_step
    {declarationColor : CostStaticColor}
    (step : RhoCanonicalPairBichromaticStep declarationColor)
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {leftPattern rightPattern : Pattern}
    {type : TypeExpr}
    (admissible : rhoCanonicalRecursiveTypeDomain.Admissible type)
    (leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type leftPattern)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type rightPattern)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation) leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation) rightPattern) :
    Nonempty (@RhoCanonicalPairBichromaticResult declarationColor targetFree
      available outer leftPattern rightPattern type) := by
  apply step (targetFree := targetFree) admissible leftWellSorted
    rightWellSorted canonical
  intro childAvailable childOuter leftChild rightChild childType
    leftChildWellSorted rightChildWellSorted childCanonical _smaller
    childAdmissible
  exact RhoCanonicalPairBichromaticResult.nonempty_of_step step
    childAdmissible leftChildWellSorted rightChildWellSorted childCanonical
termination_by sizeOf leftPattern + sizeOf rightPattern

/-- The bichromatic step subsumes the one-depth recursive step: projecting
the closure gives every consumer of `RhoCanonicalPairRecursiveResult` its
input. -/
theorem RhoCanonicalPairBichromaticStep.toRecursiveNonempty
    {declarationColor : CostStaticColor}
    (step : RhoCanonicalPairBichromaticStep declarationColor)
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {leftPattern rightPattern : Pattern}
    {type : TypeExpr}
    (admissible : rhoCanonicalRecursiveTypeDomain.Admissible type)
    (leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type leftPattern)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type rightPattern)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation) leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation) rightPattern) :
    Nonempty (@RhoCanonicalPairRecursiveResult declarationColor targetFree
      available outer leftPattern rightPattern type) := by
  obtain ⟨result⟩ := RhoCanonicalPairBichromaticResult.nonempty_of_step step
    admissible leftWellSorted rightWellSorted canonical
    (outer := outer)
  exact ⟨result.toRecursiveResult⟩

/-- Likewise for the separated-depth consumers. -/
theorem RhoCanonicalPairBichromaticStep.toTwoDepthNonempty
    {declarationColor : CostStaticColor}
    (step : RhoCanonicalPairBichromaticStep declarationColor)
    {targetFree : WellSorted.FreeTypeContext}
    {available outer : List TypeExpr} {leftPattern rightPattern : Pattern}
    {type : TypeExpr}
    (admissible : rhoCanonicalRecursiveTypeDomain.Admissible type)
    (leftWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type leftPattern)
    (rightWellSorted : ReflectiveWellSorted.OpenPatternWellSorted
      rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage
      targetFree available type rightPattern)
    (canonical : canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation) leftPattern =
      canonicalize
        (costStaticReflectivePresentationDecl rhoCIGSLT declarationColor
          rhoReflectivePresentation) rightPattern) :
    Nonempty (@RhoCanonicalPairRecursiveTwoDepthResult declarationColor
      targetFree available outer leftPattern rightPattern type) := by
  obtain ⟨result⟩ := RhoCanonicalPairBichromaticResult.nonempty_of_step step
    admissible leftWellSorted rightWellSorted canonical
    (outer := outer)
  exact ⟨result.toTwoDepthResult⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
