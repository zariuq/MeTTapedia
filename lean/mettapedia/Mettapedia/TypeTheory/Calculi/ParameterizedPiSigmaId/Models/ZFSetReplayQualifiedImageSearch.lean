import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayQualifiedBetaSearch
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedBetaPath

/-!
# Replaying bounded search receipts as qualified image evidence

The executable path search returns a dependent pair: a terminal term and
certificate together with the path that produced them. Equality of its
observable endpoint with an expected supported term lets an independently
checked source image enter the existing semantic comparison interface.
Search itself grants no typing authority.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay

universe u
variable {Head : Type} {n : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
variable (R : Rules Head) [DecidableEq Head]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]
variable (successor : Head → Head)

/-- Convert two actual successful bounded searches into the existing
certificate-and-semantics package. Both sources must independently check;
the common endpoint must be supported by the set interpretation. -/
def QualifiedImagePaths.ofSearch
    (context : Ctx Head n) (contextCode : ContextCode Head NoConversion n)
    (leftMeaning rightMeaning : Meaning.{u} n)
    (leftDisplayed rightDisplayed leftTerm rightTerm terminalTerm : Tm Head n)
    (leftCode rightCode leftTerminal rightTerminal : Code Head NoConversion n)
    (leftFuel rightFuel : Nat)
    (leftFound : (leftCode.qualifiedBetaPath? R successor contextCode
      leftFuel leftTerm leftDisplayed).map Subtype.val = some (terminalTerm, leftTerminal))
    (rightFound : (rightCode.qualifiedBetaPath? R successor contextCode
      rightFuel rightTerm rightDisplayed).map Subtype.val = some (terminalTerm, rightTerminal))
    (leftChecked : check R noConversionCheck context leftTerm leftDisplayed leftCode = true)
    (rightChecked : check R noConversionCheck context rightTerm rightDisplayed rightCode = true)
    (atLeft : assemble heads constants leftCode leftTerm leftDisplayed = some leftMeaning)
    (atRight : assemble heads constants rightCode rightTerm rightDisplayed = some rightMeaning)
    (terminalSupported : ZFSetTypeExpressionInterpretation.supported terminalTerm = true) :
    QualifiedImagePaths heads constants R successor context contextCode
      leftMeaning rightMeaning := by
  exact {
    leftDisplayed := leftDisplayed
    rightDisplayed := rightDisplayed
    leftTerm := leftTerm
    rightTerm := rightTerm
    terminalTerm := terminalTerm
    leftCode := leftCode
    rightCode := rightCode
    leftTerminal := leftTerminal
    rightTerminal := rightTerminal
    leftPath := QualifiedBetaPath.ofSearch R successor contextCode leftDisplayed
      leftTerm terminalTerm leftCode leftTerminal leftFuel leftFound
    rightPath := QualifiedBetaPath.ofSearch R successor contextCode rightDisplayed
      rightTerm terminalTerm rightCode rightTerminal rightFuel rightFound
    leftChecked := leftChecked
    rightChecked := rightChecked
    atLeft := atLeft
    atRight := atRight
    terminalSupported := terminalSupported }

#print axioms QualifiedImagePaths.ofSearch

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
