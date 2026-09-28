import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedBetaPath

/-!
# Comparing qualified computations in different valid contexts

Two accepted computations can use distinct context certificates, displayed
types, and typing trees. If both reach the same structurally interpreted
expression, their values agree wherever both context predicates admit the
environment. Neither predicate is silently identified with the other.
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

/-- The two computations need only share a structurally interpreted terminal,
not a context formation, displayed type, or terminal certificate. Agreement is
restricted to environments admitted by both actual context interpretations. -/
theorem qualified_paths_supported_terminal_values_across_contexts
    {leftContext rightContext : Ctx Head n}
    {leftDisplayed rightDisplayed leftTerm rightTerm terminal : Tm Head n}
    {leftCode rightCode leftTerminal rightTerminal : Code Head NoConversion n}
    (leftContextCode rightContextCode : ContextCode Head NoConversion n)
    (leftPath : QualifiedBetaPath R successor leftContextCode leftDisplayed
      leftTerm leftCode terminal leftTerminal)
    (rightPath : QualifiedBetaPath R successor rightContextCode rightDisplayed
      rightTerm rightCode terminal rightTerminal)
    {leftValid rightValid : Environment.{u} n → Prop}
    (leftContextChecked : checkContext R noConversionCheck leftContext leftContextCode = true)
    (rightContextChecked : checkContext R noConversionCheck rightContext rightContextCode = true)
    (leftChecked : check R noConversionCheck leftContext leftTerm leftDisplayed leftCode = true)
    (rightChecked : check R noConversionCheck rightContext rightTerm rightDisplayed rightCode = true)
    (atLeftContext : assembleContext heads constants leftContextCode leftContext = some leftValid)
    (atRightContext : assembleContext heads constants rightContextCode rightContext = some rightValid)
    (left right : Meaning.{u} n)
    (atLeft : assemble heads constants leftCode leftTerm leftDisplayed = some left)
    (atRight : assemble heads constants rightCode rightTerm rightDisplayed = some right)
    (terminalSupported : ZFSetTypeExpressionInterpretation.supported terminal = true)
    (env : Environment.{u} n) (leftAdmitted : leftValid env)
    (rightAdmitted : rightValid env) :
    left.value env = right.value env := by
  obtain ⟨leftEnd, atLeftEnd, leftValues⟩ :=
    QualifiedBetaPath.values heads constants R successor universes successorQualified
      model constantModel leftContextCode leftPath leftContextChecked leftChecked
      atLeftContext left atLeft
  obtain ⟨rightEnd, atRightEnd, rightValues⟩ :=
    QualifiedBetaPath.values heads constants R successor universes successorQualified
      model constantModel rightContextCode rightPath rightContextChecked rightChecked
      atRightContext right atRight
  have terminalValues := assemble_supported_values heads constants terminalSupported
    atLeftEnd atRightEnd
  calc
    left.value env = leftEnd.value env := leftValues env leftAdmitted
    _ = rightEnd.value env := congrFun terminalValues env
    _ = right.value env := (rightValues env rightAdmitted).symm

#print axioms qualified_paths_supported_terminal_values_across_contexts

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
