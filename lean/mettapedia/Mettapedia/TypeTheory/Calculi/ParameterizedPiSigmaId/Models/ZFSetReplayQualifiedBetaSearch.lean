import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayQualifiedBetaSearch
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedBetaPath

/-!
# Meaning of successfully searched certificate paths

Two independently accepted source certificates whose executable searches
reach the same supported raw endpoint have equal interpretations on valid
context environments. Search returns finite syntactic path evidence; source
acceptance and the set model remain separate premises.
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

/-- Search-produced paths, not merely hand-built paths, preserve agreement of
the accepted interpretations. The fuel bounds are explicit; an unsuccessful
bounded search has no logical converse. -/
theorem qualified_searched_supported_terminal_values
    (universes : FormationSensitive.UniverseRegularity R)
    (successorQualified : ∀ level, R.isUniverse level →
      R.isUniverse (successor level) ∧ R.headTyping level (successor level))
    (model : UniverseModel R heads) (constantModel : ConstantsModel heads constants R)
    {context : Ctx Head n}
    {leftDisplayed rightDisplayed leftTerm rightTerm terminalTerm : Tm Head n}
    {leftCode rightCode leftTerminal rightTerminal : Code Head NoConversion n}
    (contextCode : ContextCode Head NoConversion n)
    (leftFuel rightFuel : Nat)
    (leftFound : (leftCode.qualifiedBetaPath? R successor contextCode
      leftFuel leftTerm leftDisplayed).map Subtype.val = some (terminalTerm, leftTerminal))
    (rightFound : (rightCode.qualifiedBetaPath? R successor contextCode
      rightFuel rightTerm rightDisplayed).map Subtype.val = some (terminalTerm, rightTerminal))
    {valid : Environment.{u} n → Prop}
    (contextChecked : checkContext R noConversionCheck context contextCode = true)
    (leftChecked : check R noConversionCheck context leftTerm leftDisplayed leftCode = true)
    (rightChecked : check R noConversionCheck context rightTerm rightDisplayed rightCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (left right : Meaning.{u} n)
    (atLeft : assemble heads constants leftCode leftTerm leftDisplayed = some left)
    (atRight : assemble heads constants rightCode rightTerm rightDisplayed = some right)
    (terminalSupported : ZFSetTypeExpressionInterpretation.supported terminalTerm = true)
    (env : Environment.{u} n) (admitted : valid env) :
    left.value env = right.value env := by
  exact qualified_paths_supported_terminal_values heads constants R successor
    universes successorQualified model constantModel contextCode
    (QualifiedBetaPath.ofSearch R successor contextCode leftDisplayed
      leftTerm terminalTerm leftCode leftTerminal leftFuel leftFound)
    (QualifiedBetaPath.ofSearch R successor contextCode rightDisplayed
      rightTerm terminalTerm rightCode rightTerminal rightFuel rightFound)
    contextChecked leftChecked rightChecked atContext left right atLeft atRight
    terminalSupported env admitted

#print axioms qualified_searched_supported_terminal_values

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
