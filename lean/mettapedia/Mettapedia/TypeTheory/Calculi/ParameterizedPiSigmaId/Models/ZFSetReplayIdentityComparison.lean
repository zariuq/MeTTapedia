import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayIdentityGeneration
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayBetaReduction

/-!
# Identity fibres compared through checked endpoint certificates

Principal-view receipts identify the actual endpoint trees beneath result
wrappers. Their checks use exactly the common carrier in the raw identity
subject. Endpoint comparisons established by neutral replay or checked root
beta contraction therefore extend to equality of whole identity fibres.

Root beta comparisons retain their local argument-membership premises and
an independently checked qualified reduct. These are proved fragments of
certificate comparison, not unrestricted coherence or semantic typing.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofDecoding (truthCode)

universe u
variable {Head : Type} {ConversionCode : Nat → Type} {n : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})

/-- Exact endpoint-assembly receipts compare identity fibres even when the
two raw endpoint expressions differ. The common carrier remains the same
object-theory type; equality of its two endpoint interpretations is earned
separately, not assumed from syntactic equality of the expressions. -/
theorem identity_values_eq_of_endpoints
    (firstCode secondCode : Code Head ConversionCode n)
    (A firstLeftTerm firstRightTerm secondLeftTerm secondRightTerm firstType secondType :
      Tm Head n) (firstLevel secondLevel : Head)
    (firstFormation firstLeft firstRight secondFormation secondLeft secondRight :
      Code Head ConversionCode n)
    (firstTail secondTail : ResultTail Head ConversionCode n)
    (first second a b c d : Meaning.{u} n)
    (firstView : firstCode.principalView firstType =
      some ⟨.head firstLevel, .idForm firstLevel firstFormation firstLeft firstRight, firstTail⟩)
    (secondView : secondCode.principalView secondType =
      some ⟨.head secondLevel, .idForm secondLevel secondFormation secondLeft secondRight, secondTail⟩)
    (atFirst : assemble heads constants firstCode
      (.id A firstLeftTerm firstRightTerm) firstType = some first)
    (atSecond : assemble heads constants secondCode
      (.id A secondLeftTerm secondRightTerm) secondType = some second)
    (atA : assemble heads constants firstLeft firstLeftTerm A = some a)
    (atB : assemble heads constants firstRight firstRightTerm A = some b)
    (atC : assemble heads constants secondLeft secondLeftTerm A = some c)
    (atD : assemble heads constants secondRight secondRightTerm A = some d)
    (env : Environment.{u} n)
    (leftEqual : a.value env = c.value env) (rightEqual : b.value env = d.value env) :
    first.value env = second.value env := by
  rw [assemble_identity_principalView heads constants firstCode A firstLeftTerm firstRightTerm
    firstType firstLevel firstFormation firstLeft firstRight firstTail firstView, atA, atB] at atFirst
  rw [assemble_identity_principalView heads constants secondCode A secondLeftTerm secondRightTerm
    secondType secondLevel secondFormation secondLeft secondRight secondTail secondView,
    atC, atD] at atSecond
  change some (.plain (fun env => truthCode (a.value env = b.value env))) = some first at atFirst
  change some (.plain (fun env => truthCode (c.value env = d.value env))) = some second at atSecond
  cases Option.some.inj atFirst
  cases Option.some.inj atSecond
  change truthCode (a.value env = b.value env) = truthCode (c.value env = d.value env)
  rw [leftEqual, rightEqual]

/-- Exact endpoint assembly receipts lift pointwise endpoint equalities to
the identity fibre, including any result wrappers retained by extraction. -/
theorem identity_values_eq
    (firstCode secondCode : Code Head ConversionCode n)
    (A left right firstType secondType : Tm Head n) (firstLevel secondLevel : Head)
    (firstFormation firstLeft firstRight secondFormation secondLeft secondRight :
      Code Head ConversionCode n)
    (firstTail secondTail : ResultTail Head ConversionCode n)
    (first second a b c d : Meaning.{u} n)
    (firstView : firstCode.principalView firstType =
      some ⟨.head firstLevel, .idForm firstLevel firstFormation firstLeft firstRight, firstTail⟩)
    (secondView : secondCode.principalView secondType =
      some ⟨.head secondLevel, .idForm secondLevel secondFormation secondLeft secondRight, secondTail⟩)
    (atFirst : assemble heads constants firstCode (.id A left right) firstType = some first)
    (atSecond : assemble heads constants secondCode (.id A left right) secondType = some second)
    (atA : assemble heads constants firstLeft left A = some a)
    (atB : assemble heads constants firstRight right A = some b)
    (atC : assemble heads constants secondLeft left A = some c)
    (atD : assemble heads constants secondRight right A = some d)
    (env : Environment.{u} n)
    (leftEqual : a.value env = c.value env) (rightEqual : b.value env = d.value env) :
    first.value env = second.value env := by
  exact identity_values_eq_of_endpoints heads constants firstCode secondCode A
    left right left right firstType secondType firstLevel secondLevel
    firstFormation firstLeft firstRight secondFormation secondLeft secondRight
    firstTail secondTail first second a b c d firstView secondView atFirst atSecond
    atA atB atC atD env leftEqual rightEqual

variable (R : Rules Head) [DecidableEq Head]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]

/-- The supplied extraction receipt names the very endpoint certificates
checked by the original accepted identity formation. -/
theorem identity_endpoint_checks
    (code : Code Head NoConversion n) {context : Ctx Head n}
    {A left right displayed : Tm Head n} (level : Head)
    (formation leftCode rightCode : Code Head NoConversion n)
    (tail : ResultTail Head NoConversion n)
    (checked : check R noConversionCheck context (.id A left right) displayed code = true)
    (view : code.principalView displayed =
      some ⟨.head level, .idForm level formation leftCode rightCode, tail⟩) :
    check R noConversionCheck context left A leftCode = true ∧
      check R noConversionCheck context right A rightCode = true := by
  obtain ⟨actual, computed, principalChecked, _⟩ :=
    code.principalView_checked R noConversionCheck checked
  rw [view] at computed
  cases Option.some.inj computed
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at principalChecked
  exact ⟨principalChecked.1.1.2, principalChecked.1.2⟩

/-- Qualified endpoint trees in one accepted identity formation determine its
fibre against independently accepted endpoint trees in the other. No
qualification is imposed on the carrier-formation subtrees. -/
theorem identity_neutral_endpoints_coherent
    (firstCode secondCode : Code Head NoConversion n)
    {context : Ctx Head n} {A left right firstType secondType : Tm Head n}
    (firstLevel secondLevel : Head)
    (firstFormation firstLeft firstRight secondFormation secondLeft secondRight :
      Code Head NoConversion n)
    (firstTail secondTail : ResultTail Head NoConversion n) (first second : Meaning.{u} n)
    (firstChecked : check R noConversionCheck context (.id A left right) firstType firstCode = true)
    (secondChecked : check R noConversionCheck context (.id A left right) secondType secondCode = true)
    (firstView : firstCode.principalView firstType =
      some ⟨.head firstLevel, .idForm firstLevel firstFormation firstLeft firstRight, firstTail⟩)
    (secondView : secondCode.principalView secondType =
      some ⟨.head secondLevel, .idForm secondLevel secondFormation secondLeft secondRight, secondTail⟩)
    (atFirst : assemble heads constants firstCode (.id A left right) firstType = some first)
    (atSecond : assemble heads constants secondCode (.id A left right) secondType = some second)
    (leftNormal : firstLeft.neutralEliminations left A = true)
    (rightNormal : firstRight.neutralEliminations right A = true) : first = second := by
  obtain ⟨firstLeftChecked, firstRightChecked⟩ := identity_endpoint_checks R firstCode firstLevel
    firstFormation firstLeft firstRight firstTail firstChecked firstView
  obtain ⟨secondLeftChecked, secondRightChecked⟩ := identity_endpoint_checks R secondCode secondLevel
    secondFormation secondLeft secondRight secondTail secondChecked secondView
  obtain ⟨a, b, atA, atB, firstValue⟩ := assemble_identity_endpoints heads constants firstCode
    A left right firstType firstLevel firstFormation firstLeft firstRight firstTail first firstView atFirst
  obtain ⟨c, d, atC, atD, secondValue⟩ := assemble_identity_endpoints heads constants secondCode
    A left right secondType secondLevel secondFormation secondLeft secondRight secondTail second secondView atSecond
  have leftEqual := assemble_neutralEliminations_coherent heads constants R firstLeft
    firstLeftChecked leftNormal atA secondLeftChecked atC (EqualOrHeads.refl A)
  have rightEqual := assemble_neutralEliminations_coherent heads constants R firstRight
    firstRightChecked rightNormal atB secondRightChecked atD (EqualOrHeads.refl A)
  rw [firstValue, secondValue, leftEqual, rightEqual]

/-- Root beta endpoints may use distinct hidden lambda domains and different
argument values. Their independently checked common reducts suffice to
compare the identity fibres, using local admission at the actual domains. -/
theorem identity_rootBeta_endpoints_coherent
    (firstCode secondCode : Code Head NoConversion n)
    {context : Ctx Head n} {A firstType secondType : Tm Head n}
    (leftBody rightBody : Tm Head (n + 1)) (leftArgument rightArgument : Tm Head n)
    (firstLevel secondLevel : Head)
    (firstFormation firstLeft firstRight secondFormation secondLeft secondRight :
      Code Head NoConversion n)
    (firstTail secondTail : ResultTail Head NoConversion n)
    (first second : Meaning.{u} n) (leftNormalCode rightNormalCode : Code Head NoConversion n)
    (firstChecked : check R noConversionCheck context
      (.id A (.app (.lam leftBody) leftArgument) (.app (.lam rightBody) rightArgument)) firstType firstCode = true)
    (secondChecked : check R noConversionCheck context
      (.id A (.app (.lam leftBody) leftArgument) (.app (.lam rightBody) rightArgument)) secondType secondCode = true)
    (firstView : firstCode.principalView firstType =
      some ⟨.head firstLevel, .idForm firstLevel firstFormation firstLeft firstRight, firstTail⟩)
    (secondView : secondCode.principalView secondType =
      some ⟨.head secondLevel, .idForm secondLevel secondFormation secondLeft secondRight, secondTail⟩)
    (atFirst : assemble heads constants firstCode
      (.id A (.app (.lam leftBody) leftArgument) (.app (.lam rightBody) rightArgument)) firstType = some first)
    (atSecond : assemble heads constants secondCode
      (.id A (.app (.lam leftBody) leftArgument) (.app (.lam rightBody) rightArgument)) secondType = some second)
    (leftNormalChecked : check R noConversionCheck context (inst0 leftArgument leftBody) A leftNormalCode = true)
    (rightNormalChecked : check R noConversionCheck context (inst0 rightArgument rightBody) A rightNormalCode = true)
    (leftNormal : leftNormalCode.neutralEliminations (inst0 leftArgument leftBody) A = true)
    (rightNormal : rightNormalCode.neutralEliminations (inst0 rightArgument rightBody) A = true)
    (env : Environment.{u} n)
    (firstLeftAdmitted : RootBetaAdmitted heads constants leftArgument A env firstLeft)
    (secondLeftAdmitted : RootBetaAdmitted heads constants leftArgument A env secondLeft)
    (firstRightAdmitted : RootBetaAdmitted heads constants rightArgument A env firstRight)
    (secondRightAdmitted : RootBetaAdmitted heads constants rightArgument A env secondRight) :
    first.value env = second.value env := by
  obtain ⟨firstLeftChecked, firstRightChecked⟩ := identity_endpoint_checks R firstCode firstLevel
    firstFormation firstLeft firstRight firstTail firstChecked firstView
  obtain ⟨secondLeftChecked, secondRightChecked⟩ := identity_endpoint_checks R secondCode secondLevel
    secondFormation secondLeft secondRight secondTail secondChecked secondView
  obtain ⟨a, b, atA, atB, firstValue⟩ := assemble_identity_endpoints heads constants firstCode
    A _ _ firstType firstLevel firstFormation firstLeft firstRight firstTail first firstView atFirst
  obtain ⟨c, d, atC, atD, secondValue⟩ := assemble_identity_endpoints heads constants secondCode
    A _ _ secondType secondLevel secondFormation secondLeft secondRight secondTail second secondView atSecond
  obtain ⟨leftMeaning, atLeftNormal, _⟩ :=
    accepted_assembles heads constants R noConversionCheck leftNormalCode leftNormalChecked
  obtain ⟨rightMeaning, atRightNormal, _⟩ :=
    accepted_assembles heads constants R noConversionCheck rightNormalCode rightNormalChecked
  have leftEqual := rootBeta_coherent_of_normal_reduct heads constants R
    firstLeft secondLeft leftNormalCode a c leftMeaning firstLeftChecked secondLeftChecked atA atC
    leftNormalChecked leftNormal atLeftNormal env firstLeftAdmitted secondLeftAdmitted
  have rightEqual := rootBeta_coherent_of_normal_reduct heads constants R
    firstRight secondRight rightNormalCode b d rightMeaning firstRightChecked secondRightChecked atB atD
    rightNormalChecked rightNormal atRightNormal env firstRightAdmitted secondRightAdmitted
  rw [firstValue, secondValue]
  change truthCode (a.value env = b.value env) = truthCode (c.value env = d.value env)
  rw [leftEqual, rightEqual]

/-- Mixed endpoint qualification: the left endpoint contracts to an
independently checked qualified reduct, while the right endpoint already
has one qualified source tree. The competing right tree is unrestricted. -/
theorem identity_rootBeta_left_neutral_right_coherent
    (firstCode secondCode : Code Head NoConversion n)
    {context : Ctx Head n} {A right firstType secondType : Tm Head n}
    (body : Tm Head (n + 1)) (argument : Tm Head n)
    (firstLevel secondLevel : Head)
    (firstFormation firstLeft firstRight secondFormation secondLeft secondRight :
      Code Head NoConversion n)
    (firstTail secondTail : ResultTail Head NoConversion n)
    (first second : Meaning.{u} n) (normalCode : Code Head NoConversion n)
    (firstChecked : check R noConversionCheck context
      (.id A (.app (.lam body) argument) right) firstType firstCode = true)
    (secondChecked : check R noConversionCheck context
      (.id A (.app (.lam body) argument) right) secondType secondCode = true)
    (firstView : firstCode.principalView firstType =
      some ⟨.head firstLevel, .idForm firstLevel firstFormation firstLeft firstRight, firstTail⟩)
    (secondView : secondCode.principalView secondType =
      some ⟨.head secondLevel, .idForm secondLevel secondFormation secondLeft secondRight, secondTail⟩)
    (atFirst : assemble heads constants firstCode
      (.id A (.app (.lam body) argument) right) firstType = some first)
    (atSecond : assemble heads constants secondCode
      (.id A (.app (.lam body) argument) right) secondType = some second)
    (normalChecked : check R noConversionCheck context (inst0 argument body) A normalCode = true)
    (normal : normalCode.neutralEliminations (inst0 argument body) A = true)
    (rightNormal : firstRight.neutralEliminations right A = true)
    (env : Environment.{u} n)
    (firstAdmitted : RootBetaAdmitted heads constants argument A env firstLeft)
    (secondAdmitted : RootBetaAdmitted heads constants argument A env secondLeft) :
    first.value env = second.value env := by
  obtain ⟨firstLeftChecked, firstRightChecked⟩ := identity_endpoint_checks R firstCode firstLevel
    firstFormation firstLeft firstRight firstTail firstChecked firstView
  obtain ⟨secondLeftChecked, secondRightChecked⟩ := identity_endpoint_checks R secondCode secondLevel
    secondFormation secondLeft secondRight secondTail secondChecked secondView
  obtain ⟨a, b, atA, atB, firstValue⟩ := assemble_identity_endpoints heads constants firstCode
    A _ right firstType firstLevel firstFormation firstLeft firstRight firstTail first firstView atFirst
  obtain ⟨c, d, atC, atD, secondValue⟩ := assemble_identity_endpoints heads constants secondCode
    A _ right secondType secondLevel secondFormation secondLeft secondRight secondTail second secondView atSecond
  obtain ⟨normalMeaning, atNormal, _⟩ :=
    accepted_assembles heads constants R noConversionCheck normalCode normalChecked
  have leftEqual := rootBeta_coherent_of_normal_reduct heads constants R
    firstLeft secondLeft normalCode a c normalMeaning firstLeftChecked secondLeftChecked atA atC
    normalChecked normal atNormal env firstAdmitted secondAdmitted
  have rightEqual := assemble_neutralEliminations_coherent heads constants R firstRight
    firstRightChecked rightNormal atB secondRightChecked atD (EqualOrHeads.refl A)
  rw [firstValue, secondValue, rightEqual]
  change truthCode (a.value env = d.value env) = truthCode (c.value env = d.value env)
  rw [leftEqual]

#print axioms identity_values_eq
#print axioms identity_values_eq_of_endpoints
#print axioms identity_endpoint_checks
#print axioms identity_neutral_endpoints_coherent
#print axioms identity_rootBeta_endpoints_coherent
#print axioms identity_rootBeta_left_neutral_right_coherent

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
