import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayComputation

/-!
# Comparing checked dependent second projections

The checker can accept two different retained certificates for the same
dependent pair and its second projection. Their first components may have
different interpretations. The second projection preserves a relation
established between the actually assembled second components; the result
types remain tied to the checked first projections, not erased by the
comparison.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.Logic.HOL.Embedding

universe u
variable {Head : Type} {ConversionCode : Nat → Type} {n : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
variable (R : Rules Head) [DecidableEq Head]
variable [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)]
variable (conversionCheck : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool)

/-- Checked second projection transports any relation on the values of two
independently assembled second components. The checker supplies assembly of
the resulting programs; the pair equation supplies the relation. Neither a
relation between first-component values nor equality of retained formation
certificates is required. -/
theorem checked_second_projections_related
    (context : Ctx Head n) (levelLeft levelRight : Head)
    (A first second : Tm Head n) (B : Tm Head (n + 1))
    (formationLeft formationRight firstLeft firstRight secondLeft secondRight :
      Code Head ConversionCode n)
    (firstLeftMeaning firstRightMeaning secondLeftMeaning secondRightMeaning : Meaning.{u} n)
    (atFirstLeft : assemble heads constants firstLeft first A = some firstLeftMeaning)
    (atFirstRight : assemble heads constants firstRight first A = some firstRightMeaning)
    (atSecondLeft : assemble heads constants secondLeft second (inst0 first B) =
      some secondLeftMeaning)
    (atSecondRight : assemble heads constants secondRight second (inst0 first B) =
      some secondRightMeaning)
    (leftChecked : check R conversionCheck context (.snd (.pair first second))
      (inst0 (.fst (.pair first second)) B)
      (.sndElim A B (.pairIntro levelLeft formationLeft firstLeft secondLeft)) = true)
    (rightChecked : check R conversionCheck context (.snd (.pair first second))
      (inst0 (.fst (.pair first second)) B)
      (.sndElim A B (.pairIntro levelRight formationRight firstRight secondRight)) = true)
    (valid : Environment.{u} n → Prop)
    (relation : ZFSet.{u} → ZFSet.{u} → Prop)
    (componentsRelated : ∀ env, valid env →
      relation (secondLeftMeaning.value env) (secondRightMeaning.value env)) :
    ∃ left right,
      assemble heads constants
        (.sndElim A B (.pairIntro levelLeft formationLeft firstLeft secondLeft))
        (.snd (.pair first second)) (inst0 (.fst (.pair first second)) B) = some left ∧
      assemble heads constants
        (.sndElim A B (.pairIntro levelRight formationRight firstRight secondRight))
        (.snd (.pair first second)) (inst0 (.fst (.pair first second)) B) = some right ∧
      ∀ env, valid env → relation (left.value env) (right.value env) := by
  obtain ⟨left, atLeft, _⟩ := accepted_assembles heads constants R conversionCheck
    (.sndElim A B (.pairIntro levelLeft formationLeft firstLeft secondLeft)) leftChecked
  obtain ⟨right, atRight, _⟩ := accepted_assembles heads constants R conversionCheck
    (.sndElim A B (.pairIntro levelRight formationRight firstRight secondRight)) rightChecked
  refine ⟨left, right, atLeft, atRight, ?_⟩
  intro env admitted
  have leftValue := second_pair_value heads constants levelLeft A first second B
    formationLeft firstLeft secondLeft firstLeftMeaning secondLeftMeaning left
    atFirstLeft atSecondLeft atLeft env
  have rightValue := second_pair_value heads constants levelRight A first second B
    formationRight firstRight secondRight firstRightMeaning secondRightMeaning right
    atFirstRight atSecondRight atRight env
  rw [leftValue, rightValue]
  exact componentsRelated env admitted

omit [DecidableEq Head]
  [∀ h v, Decidable (R.headTyping h v)] [∀ h, Decidable (R.isUniverse h)]
  [∀ v w z, Decidable (R.join v w z)] [∀ v w, Decidable (R.cumulative v w)] in
/-- The second projection cannot hide a difference in the second component.
This is the negative boundary of the relational theorem; its first component
may be entirely unrelated. -/
theorem second_projections_reflect_difference
    (levelLeft levelRight : Head) (A first second : Tm Head n) (B : Tm Head (n + 1))
    (formationLeft formationRight firstLeft firstRight secondLeft secondRight :
      Code Head ConversionCode n)
    (firstLeftMeaning firstRightMeaning secondLeftMeaning secondRightMeaning
      left right : Meaning.{u} n)
    (atFirstLeft : assemble heads constants firstLeft first A = some firstLeftMeaning)
    (atFirstRight : assemble heads constants firstRight first A = some firstRightMeaning)
    (atSecondLeft : assemble heads constants secondLeft second (inst0 first B) =
      some secondLeftMeaning)
    (atSecondRight : assemble heads constants secondRight second (inst0 first B) =
      some secondRightMeaning)
    (atLeft : assemble heads constants
      (.sndElim A B (.pairIntro levelLeft formationLeft firstLeft secondLeft))
      (.snd (.pair first second)) (inst0 (.fst (.pair first second)) B) = some left)
    (atRight : assemble heads constants
      (.sndElim A B (.pairIntro levelRight formationRight firstRight secondRight))
      (.snd (.pair first second)) (inst0 (.fst (.pair first second)) B) = some right)
    (env : Environment.{u} n)
    (different : secondLeftMeaning.value env ≠ secondRightMeaning.value env) :
    left.value env ≠ right.value env := by
  rw [second_pair_value heads constants levelLeft A first second B formationLeft
      firstLeft secondLeft firstLeftMeaning secondLeftMeaning left
      atFirstLeft atSecondLeft atLeft env,
    second_pair_value heads constants levelRight A first second B formationRight
      firstRight secondRight firstRightMeaning secondRightMeaning right
      atFirstRight atSecondRight atRight env]
  exact different

#print axioms checked_second_projections_related
#print axioms second_projections_reflect_difference

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
