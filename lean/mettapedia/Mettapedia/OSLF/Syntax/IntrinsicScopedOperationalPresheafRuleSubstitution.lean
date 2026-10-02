import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafRuleNaturality
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafBoundSubstitution
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafActions
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafRuleLawReduction

/-!
# Contextual substitution passes beneath actual generalized rule firings

The original ordered binder-context substitution square preserves each bound
premise function. The full occurrence specializes at the same actual clone
point, so the resulting rule function commutes with every semantic environment.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafRuleSubstitution

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open BindingSubstitutionAlgebra
open IntrinsicScopedConditionalPresheaf (Base)
open IntrinsicScopedOperationalPresheafPrograms (target model)
open IntrinsicScopedOperationalPresheafEvents (sortEvents)
open IntrinsicScopedOperationalPresheafBoundContexts
open IntrinsicScopedOperationalPresheafBoundSubstitution
open IntrinsicScopedOperationalPresheafSubstitution (substitutionArrow)
open IntrinsicScopedOperationalPresheafRulePoints
open IntrinsicScopedOperationalPresheafRuleFunctions
open IntrinsicScopedOperationalPresheafRuleFirings
open IntrinsicScopedOperationalPresheafRuleNaturality
open IntrinsicScopedOperationalPresheafRuleSubstitutionPoints
open IntrinsicScopedOperationalPresheafReadback (extendedStage canonicalPoint)
open IntrinsicScopedOperationalPresheafActions (naturalAction)
open IntrinsicScopedLocalPolynomial (LocalRule Instance conclusionJudgment childJudgment childJudgment_subst)
open IntrinsicScopedLocalSubstitutionModel (SubstitutionModel RulesLaw rulesAct_heq)
open AuthoredPositionedRulePolynomial (Judgment)
open IntrinsicScopedConditionalSubstitution (substJudgment heq_transport)

universe u
variable {S : Signature} {A : BindingCloneAlgebra.Algebra.{u} S}
variable (R : List (LocalRule S)) (Y : SubstitutionModel.{u,u} R A)

/-- Substitute each retained premise under its exact authored ordered binder list. -/
def substituteChildren {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (children : Children R Y occurrence) {Δ : Ctx S}
    (σ : Environment S ((model A).stage Z).substitution.Carrier occurrence.ambient Δ) :
    Children R Y (Instance.subst R occurrence σ) :=
  fun position => (naturalAction Y.toAction Z).act _ (children position)
    (((model A).stage Z).substitution.liftEnvironment σ
      ((R.get occurrence.index).2.premises.get position).binders)
    (childJudgment R ((model A).stage Z) (Instance.subst R occurrence σ) position)
    (childJudgment_subst R occurrence σ position).symm

/-- Each bound child function follows the actual context substitution arrow. -/
theorem boundChild_substitution {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (children : Children R Y occurrence) {Δ : Ctx S}
    (σ : Environment S ((model A).stage Z).substitution.Carrier occurrence.ambient Δ)
    (position : Fin (R.get occurrence.index).2.premises.length) :
    boundChild A R Y.toAction (Instance.subst R occurrence σ) position
        (substituteChildren R Y occurrence children σ position) =
      ((model A).ctx ((R.get occurrence.index).2.premises.get position).binders ◁
        substitutionArrow (model A) σ) ≫
        boundChild A R Y.toAction occurrence position (children position) := by
  let bs : Ctx S := ((R.get occurrence.index).2.premises.get position).binders
  have value : (substituteChildren R Y occurrence children σ position).1 =
      substitutionArrow (model A) (((model A).stage Z).substitution.liftEnvironment σ bs) ≫
        (children position).1 :=
    eq_of_heq (IntrinsicScopedOperationalPresheafNaturalEvidence.act_val _ (children position)
      (((model A).stage Z).substitution.liftEnvironment σ bs) _
      (childJudgment_subst R occurrence σ position).symm)
  change boundContextArrow (model A) bs Δ Z ≫
      (substituteChildren R Y occurrence children σ position).1 =
    ((model A).ctx bs ◁ substitutionArrow (model A) σ) ≫
      (boundContextArrow (model A) bs occurrence.ambient Z ≫ (children position).1)
  have precomposed := congrArg (boundContextArrow (model A) bs Δ Z ≫ ·) value
  have geometry := congrArg (fun arrow => arrow ≫ (children position).1)
    (boundContextArrow_substitution (model A) bs σ)
  exact precomposed.trans ((Category.assoc _ _ _).symm.trans
    (geometry.trans (Category.assoc _ _ _)))

/-- At every canonical binder point, contextual substitution preserves the
original retained sorted premise event at its substituted ordinary context. -/
theorem childAtPoint_substitution {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (children : Children R Y occurrence) {Δ : Ctx S}
    (σ : Environment S ((model A).stage Z).substitution.Carrier occurrence.ambient Δ)
    (position : Fin (R.get occurrence.index).2.premises.length)
    (X : Base A) (point : ((model A).ctx Δ ⊗ Z).obj X) :
    childAtPoint A R Y.toAction (Instance.subst R occurrence σ) position
        (substituteChildren R Y occurrence children σ position) X point =
      childAtPoint A R Y.toAction occurrence position (children position) X
        ((substitutionArrow (model A) σ).app X point) := by
  exact canonicalEvaluation_stageMap (substitutionArrow (model A) σ)
    ((R.get occurrence.index).2.premises.get position).binders
    (boundChild A R Y.toAction occurrence position (children position))
    (boundChild A R Y.toAction (Instance.subst R occurrence σ) position
      (substituteChildren R Y occurrence children σ position))
    (boundChild_substitution R Y occurrence children σ position) X point

/-- Every original ordered premise witness survives arbitrary semantic substitution. -/
theorem pointChildEvidence_substitution {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (children : Children R Y occurrence) {Δ : Ctx S}
    (σ : Environment S ((model A).stage Z).substitution.Carrier occurrence.ambient Δ)
    (position : Fin (R.get occurrence.index).2.premises.length)
    (X : Base A) (point : ((model A).ctx Δ ⊗ Z).obj X) :
    HEq (pointChildEvidence A R Y.toAction (Instance.subst R occurrence σ)
      position (substituteChildren R Y occurrence children σ position) X point)
      (pointChildEvidence A R Y.toAction occurrence position (children position) X
        ((substitutionArrow (model A) σ).app X point)) := by
  have first := pointChildEvidence_raw R Y (Instance.subst R occurrence σ)
    (substituteChildren R Y occurrence children σ) position X point
  have raw := sortEventEvidence_congr A Y.toAction _
    (childAtPoint_substitution R Y occurrence children σ position X point)
  have second := pointChildEvidence_raw R Y occurrence children position X
    ((substitutionArrow (model A) σ).app X point)
  exact first.trans (raw.trans second.symm)

/-- The original local model fires the same complete occurrence after contextual substitution. -/
theorem pointFire_substitution {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (children : Children R Y occurrence) {Δ : Ctx S}
    (σ : Environment S ((model A).stage Z).substitution.Carrier occurrence.ambient Δ)
    (X : Base A) (point : ((model A).ctx Δ ⊗ Z).obj X) :
    pointFire R Y (Instance.subst R occurrence σ) (substituteChildren R Y occurrence children σ) X point =
      pointFire R Y occurrence children X ((substitutionArrow (model A) σ).app X point) := by
  have same := pointInstance_substitution R occurrence σ X point
  apply sortedEvent_ext R Y X
  · exact congrArg (conclusionJudgment R A) same
  · exact rulesAct_heq R Y.rules (congrArg (conclusionJudgment R A) same) same rfl rfl _ _
      (by
        intro position otherPosition samePosition
        cases samePosition
        exact pointChildEvidence_substitution R Y occurrence children σ position X point)

/-- The actual full rule function commutes with every semantic contextual substitution. -/
theorem ruleFunction_substitution {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (children : Children R Y occurrence) {Δ : Ctx S}
    (σ : Environment S ((model A).stage Z).substitution.Carrier occurrence.ambient Δ) :
    ruleFunction R Y (Instance.subst R occurrence σ) (substituteChildren R Y occurrence children σ) =
      substitutionArrow (model A) σ ≫ ruleFunction R Y occurrence children := by
  ext X point
  exact pointFire_substitution R Y occurrence children σ X point

/-- The implemented generalized rule evidence obeys contextual substitution
beneath every actual ordered premise binder list. -/
theorem ruleEvidence_substitution {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (children : Children R Y occurrence) {Δ : Ctx S}
    (σ : Environment S ((model A).stage Z).substitution.Carrier occurrence.ambient Δ) :
    HEq ((naturalAction Y.toAction Z).act (conclusionJudgment R ((model A).stage Z) occurrence)
      (ruleEvidence R Y occurrence children) σ
      (substJudgment (conclusionJudgment R ((model A).stage Z) occurrence) σ) rfl)
      (ruleEvidence R Y (Instance.subst R occurrence σ) (substituteChildren R Y occurrence children σ)) :=
  evidence_heq_of_val R Y
    (IntrinsicScopedLocalPolynomial.conclusionJudgment_subst R occurrence σ).symm
    _ _ (heq_of_eq (ruleFunction_substitution R Y occurrence children σ).symm)

/-- The actual original local rule actions and the genuine context-arrow
action satisfy the full operational substitution law at every generalized stage. -/
theorem naturalRules_act_rules (Z : target A) :
    RulesLaw R ((model A).stage Z) (naturalAction Y.toAction Z).act (naturalRules R Y Z) := by
  apply IntrinsicScopedOperationalPresheafRuleLawReduction.rulesLaw_of_occurrences
  intro occurrence children Δ σ
  exact ruleEvidence_substitution R Y occurrence children σ

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafRuleSubstitution
