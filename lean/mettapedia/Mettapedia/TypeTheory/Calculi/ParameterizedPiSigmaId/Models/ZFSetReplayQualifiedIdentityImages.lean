import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayIdentityComparison
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedImageSearch
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedIdentityPaths

/-!
# Identity fibres compared through qualified endpoint evidence

An identity type reads the values of its two endpoints, not the spelling of
their retained certificates. Supported-image packages compare endpoints by
structural interpretation. A separate search theorem also covers endpoints
outside that structural fragment, including annotated lambdas: its successful
searches retain finite paths ending in neutral-elimination certificates.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment)

universe u
variable {Head : Type} {n : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
variable (R : Rules Head) [DecidableEq Head]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]
variable (successor : Head → Head)

/-- Two identity fibres agree on a valid context when their corresponding
endpoints are compared by independently checked qualified image packages.
The endpoints may be different computed expressions with different retained
certificates; this route requires supported common terminal terms. -/
theorem identity_qualified_image_paths_coherent
    (universes : FormationSensitive.UniverseRegularity R)
    (successorQualified : ∀ level, R.isUniverse level →
      R.isUniverse (successor level) ∧ R.headTyping level (successor level))
    (model : UniverseModel R heads) (constantModel : ConstantsModel heads constants R)
    (context : Ctx Head n) (contextCode : ContextCode Head NoConversion n)
    {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (A firstType secondType : Tm Head n)
    (leftFirst leftSecond rightFirst rightSecond : Meaning.{u} n)
    (leftImages : QualifiedImagePaths heads constants R successor context contextCode
      leftFirst leftSecond)
    (rightImages : QualifiedImagePaths heads constants R successor context contextCode
      rightFirst rightSecond)
    (leftFirstType : leftImages.leftDisplayed = A)
    (leftSecondType : leftImages.rightDisplayed = A)
    (rightFirstType : rightImages.leftDisplayed = A)
    (rightSecondType : rightImages.rightDisplayed = A)
    (firstCode secondCode : Code Head NoConversion n)
    (firstLevel secondLevel : Head)
    (firstFormation secondFormation : Code Head NoConversion n)
    (firstTail secondTail : ResultTail Head NoConversion n)
    (first second : Meaning.{u} n)
    (firstView : firstCode.principalView firstType =
      some ⟨.head firstLevel, .idForm firstLevel firstFormation
        leftImages.leftCode rightImages.leftCode, firstTail⟩)
    (secondView : secondCode.principalView secondType =
      some ⟨.head secondLevel, .idForm secondLevel secondFormation
        leftImages.rightCode rightImages.rightCode, secondTail⟩)
    (atFirst : assemble heads constants firstCode
      (.id A leftImages.leftTerm rightImages.leftTerm) firstType = some first)
    (atSecond : assemble heads constants secondCode
      (.id A leftImages.rightTerm rightImages.rightTerm) secondType = some second)
    (env : Environment.{u} n) (admitted : valid env) :
    first.value env = second.value env := by
  have atFirstLeft : assemble heads constants leftImages.leftCode leftImages.leftTerm A =
      some leftFirst := by simpa only [leftFirstType] using leftImages.atLeft
  have atSecondLeft : assemble heads constants leftImages.rightCode leftImages.rightTerm A =
      some leftSecond := by simpa only [leftSecondType] using leftImages.atRight
  have atFirstRight : assemble heads constants rightImages.leftCode rightImages.leftTerm A =
      some rightFirst := by simpa only [rightFirstType] using rightImages.atLeft
  have atSecondRight : assemble heads constants rightImages.rightCode rightImages.rightTerm A =
      some rightSecond := by simpa only [rightSecondType] using rightImages.atRight
  have leftEqual := qualified_paths_supported_terminal_values heads constants R successor
    universes successorQualified model constantModel contextCode
    leftImages.leftPath leftImages.rightPath contextChecked leftImages.leftChecked
    leftImages.rightChecked atContext leftFirst leftSecond leftImages.atLeft
    leftImages.atRight leftImages.terminalSupported env admitted
  have rightEqual := qualified_paths_supported_terminal_values heads constants R successor
    universes successorQualified model constantModel contextCode
    rightImages.leftPath rightImages.rightPath contextChecked rightImages.leftChecked
    rightImages.rightChecked atContext rightFirst rightSecond rightImages.atLeft
    rightImages.atRight rightImages.terminalSupported env admitted
  exact identity_values_eq_of_endpoints heads constants firstCode secondCode A
    leftImages.leftTerm rightImages.leftTerm leftImages.rightTerm rightImages.rightTerm
    firstType secondType firstLevel secondLevel firstFormation
    leftImages.leftCode rightImages.leftCode secondFormation
    leftImages.rightCode rightImages.rightCode firstTail secondTail
    first second leftFirst rightFirst leftSecond rightSecond firstView secondView
    atFirst atSecond atFirstLeft atFirstRight atSecondLeft atSecondRight
    env leftEqual rightEqual

#print axioms identity_qualified_image_paths_coherent

/-- Four bounded searches supply the endpoint paths for the existing
identity-fibre comparison. Unlike the supported-image route, this also
covers a common terminal lambda whose meaning needs its retained annotation.
The original identity formations and endpoint certificates still check
independently; search success is not admission. -/
theorem identity_qualified_search_endpoints_coherent
    (universes : FormationSensitive.UniverseRegularity R)
    (successorQualified : ∀ level, R.isUniverse level →
      R.isUniverse (successor level) ∧ R.headTyping level (successor level))
    (model : UniverseModel R heads) (constantModel : ConstantsModel heads constants R)
    {context : Ctx Head n}
    {A firstLeftTerm firstRightTerm secondLeftTerm secondRightTerm
      firstType secondType leftTerminal rightTerminal : Tm Head n}
    (contextCode : ContextCode Head NoConversion n)
    (firstCode secondCode : Code Head NoConversion n)
    (firstLevel secondLevel : Head)
    (firstFormation firstLeft firstRight secondFormation secondLeft secondRight :
      Code Head NoConversion n)
    (firstTail secondTail : ResultTail Head NoConversion n)
    (firstLeftTerminal secondLeftTerminal firstRightTerminal secondRightTerminal :
      Code Head NoConversion n)
    (firstLeftFuel secondLeftFuel firstRightFuel secondRightFuel : Nat)
    (firstLeftFound : (firstLeft.qualifiedBetaPath? R successor contextCode
      firstLeftFuel firstLeftTerm A).map Subtype.val =
        some (leftTerminal, firstLeftTerminal))
    (secondLeftFound : (secondLeft.qualifiedBetaPath? R successor contextCode
      secondLeftFuel secondLeftTerm A).map Subtype.val =
        some (leftTerminal, secondLeftTerminal))
    (firstRightFound : (firstRight.qualifiedBetaPath? R successor contextCode
      firstRightFuel firstRightTerm A).map Subtype.val =
        some (rightTerminal, firstRightTerminal))
    (secondRightFound : (secondRight.qualifiedBetaPath? R successor contextCode
      secondRightFuel secondRightTerm A).map Subtype.val =
        some (rightTerminal, secondRightTerminal))
    {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (firstChecked : check R noConversionCheck context
      (.id A firstLeftTerm firstRightTerm) firstType firstCode = true)
    (secondChecked : check R noConversionCheck context
      (.id A secondLeftTerm secondRightTerm) secondType secondCode = true)
    (firstView : firstCode.principalView firstType =
      some ⟨.head firstLevel,
        .idForm firstLevel firstFormation firstLeft firstRight, firstTail⟩)
    (secondView : secondCode.principalView secondType =
      some ⟨.head secondLevel,
        .idForm secondLevel secondFormation secondLeft secondRight, secondTail⟩)
    (first second : Meaning.{u} n)
    (atFirst : assemble heads constants firstCode
      (.id A firstLeftTerm firstRightTerm) firstType = some first)
    (atSecond : assemble heads constants secondCode
      (.id A secondLeftTerm secondRightTerm) secondType = some second)
    (env : Environment.{u} n) (admitted : valid env) :
    first.value env = second.value env := by
  exact identity_qualified_paths_endpoints_coherent heads constants R successor
    universes successorQualified model constantModel contextCode firstCode secondCode
    firstLevel secondLevel firstFormation firstLeft firstRight secondFormation
    secondLeft secondRight firstTail secondTail
    firstLeftTerminal secondLeftTerminal firstRightTerminal secondRightTerminal
    (QualifiedBetaPath.ofSearch R successor contextCode A firstLeftTerm
      leftTerminal firstLeft firstLeftTerminal firstLeftFuel firstLeftFound)
    (QualifiedBetaPath.ofSearch R successor contextCode A secondLeftTerm
      leftTerminal secondLeft secondLeftTerminal secondLeftFuel secondLeftFound)
    (QualifiedBetaPath.ofSearch R successor contextCode A firstRightTerm
      rightTerminal firstRight firstRightTerminal firstRightFuel firstRightFound)
    (QualifiedBetaPath.ofSearch R successor contextCode A secondRightTerm
      rightTerminal secondRight secondRightTerminal secondRightFuel secondRightFound)
    contextChecked atContext firstChecked secondChecked firstView secondView
    first second atFirst atSecond env admitted

#print axioms identity_qualified_search_endpoints_coherent

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
