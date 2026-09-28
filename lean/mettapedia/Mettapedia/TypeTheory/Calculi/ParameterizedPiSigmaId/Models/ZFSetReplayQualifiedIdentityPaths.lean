import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayIdentityComparison
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedBetaPath

/-!
# Identity fibres with independently computed endpoints

The two accepted identity formations may contain different raw expressions
at both endpoints. The original principal-view receipts determine their
actual checked endpoint certificates. Finite qualified contractions compare
those endpoints at common neutral terminals, and the identity-fibre
comparison transports the resulting equalities into the truth codes.

All four paths and the validity of the source context are explicit. This
does not claim unrestricted certificate coherence or identity conversion.
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
variable (successor : Head → Head) (universes : FormationSensitive.UniverseRegularity R)
variable (successorQualified : ∀ level, R.isUniverse level →
  R.isUniverse (successor level) ∧ R.headTyping level (successor level))
variable (model : UniverseModel R heads) (constantModel : ConstantsModel heads constants R)

include universes successorQualified model constantModel

/-- Two genuinely different identity subjects have the same interpreted
identity fibre whenever corresponding checked endpoints follow qualified
certificate paths to shared neutral terms. Their endpoint certificates and
intermediate lambda domains may all differ. -/
theorem identity_qualified_paths_endpoints_coherent
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
    (firstLeftPath : QualifiedBetaPath R successor contextCode A
      firstLeftTerm firstLeft leftTerminal firstLeftTerminal)
    (secondLeftPath : QualifiedBetaPath R successor contextCode A
      secondLeftTerm secondLeft leftTerminal secondLeftTerminal)
    (firstRightPath : QualifiedBetaPath R successor contextCode A
      firstRightTerm firstRight rightTerminal firstRightTerminal)
    (secondRightPath : QualifiedBetaPath R successor contextCode A
      secondRightTerm secondRight rightTerminal secondRightTerminal)
    {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (firstChecked : check R noConversionCheck context
      (.id A firstLeftTerm firstRightTerm) firstType firstCode = true)
    (secondChecked : check R noConversionCheck context
      (.id A secondLeftTerm secondRightTerm) secondType secondCode = true)
    (firstView : firstCode.principalView firstType =
      some ⟨.head firstLevel, .idForm firstLevel firstFormation firstLeft firstRight, firstTail⟩)
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
  obtain ⟨firstLeftChecked, firstRightChecked⟩ :=
    identity_endpoint_checks R firstCode firstLevel firstFormation firstLeft firstRight
      firstTail firstChecked firstView
  obtain ⟨secondLeftChecked, secondRightChecked⟩ :=
    identity_endpoint_checks R secondCode secondLevel secondFormation secondLeft secondRight
      secondTail secondChecked secondView
  obtain ⟨a, b, atA, atB, _⟩ := assemble_identity_endpoints heads constants firstCode
    A firstLeftTerm firstRightTerm firstType firstLevel firstFormation firstLeft firstRight
    firstTail first firstView atFirst
  obtain ⟨c, d, atC, atD, _⟩ := assemble_identity_endpoints heads constants secondCode
    A secondLeftTerm secondRightTerm secondType secondLevel secondFormation secondLeft
    secondRight secondTail second secondView atSecond
  have leftEqual := qualified_paths_common_terminal_values heads constants R successor
    universes successorQualified model constantModel contextCode firstLeftPath secondLeftPath
    contextChecked firstLeftChecked secondLeftChecked atContext a c atA atC env admitted
  have rightEqual := qualified_paths_common_terminal_values heads constants R successor
    universes successorQualified model constantModel contextCode firstRightPath secondRightPath
    contextChecked firstRightChecked secondRightChecked atContext b d atB atD env admitted
  exact identity_values_eq_of_endpoints heads constants firstCode secondCode A
    firstLeftTerm firstRightTerm secondLeftTerm secondRightTerm firstType secondType
    firstLevel secondLevel firstFormation firstLeft firstRight secondFormation secondLeft
    secondRight firstTail secondTail first second a b c d firstView secondView atFirst
    atSecond atA atB atC atD env leftEqual rightEqual

#print axioms identity_qualified_paths_endpoints_coherent

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
