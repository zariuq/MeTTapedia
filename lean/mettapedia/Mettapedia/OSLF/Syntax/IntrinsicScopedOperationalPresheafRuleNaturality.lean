import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafRuleFirings
import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafRuleStagePoints
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalLawTransfer

/-!
# Actual rule firings commute with every generalized stage map

All contextual bodies and individual bound premise functions are retained under
restaging. The resulting natural rule function agrees with precomposition by
the original ordinary-context and stage map at every clone context.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafRuleNaturality

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open IntrinsicScopedConditionalPresheaf (Base)
open IntrinsicScopedOperationalPresheafPrograms (target model)
open IntrinsicScopedOperationalPresheafEvents (sortEvents)
open IntrinsicScopedOperationalPresheafReadback (extendedStage canonicalPoint)
open IntrinsicScopedOperationalPresheafBoundContexts
open IntrinsicScopedOperationalPresheafRulePoints
open IntrinsicScopedOperationalPresheafRuleFunctions
open IntrinsicScopedOperationalPresheafRuleFirings
open IntrinsicScopedOperationalPresheafRuleStagePoints
open IntrinsicScopedLocalPolynomial (LocalRule Instance conclusionJudgment childJudgment mapInstance mapInstance_child)
open IntrinsicScopedLocalSubstitutionModel (SubstitutionModel rulesAct_heq)
open AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open IntrinsicScopedConditionalSubstitution (heq_transport)

universe u
variable {S : Signature} {A : BindingCloneAlgebra.Algebra.{u} S}
variable (R : List (LocalRule S)) (Y : SubstitutionModel.{u,u} R A)

/-- Opening binders commutes with every map of the retained stage parameter. -/
theorem canonicalPoint_stageMap {W W' : target A} (h : W' ⟶ W)
    (bs : Ctx S) (X : Base A) (point : W'.obj X) :
    (((model A).ctx bs ◁ h).app (extendedStage A bs X))
        (canonicalPoint A bs X point) = canonicalPoint A bs X (h.app X point) := by
  apply Prod.ext
  · rfl
  · exact h.naturality_apply
      (Quiver.Hom.op (sndProjection A.substitution.toClone
        (ContextObject.ofList A.substitution.toClone bs) X.unop)) point

/-- Transporting a natural-evidence judgment keeps its full underlying event arrow. -/
theorem evidence_transport_val {Z : target A}
    {first second : Judgment ((model A).stage Z)} (same : first = second)
    (event : IntrinsicScopedOperationalPresheafNaturalEvidence.Evidence (model A)
      (sortEvents Y.toAction) (IntrinsicScopedOperationalPresheafEventPowers.source Y.toAction)
      (IntrinsicScopedOperationalPresheafEventPowers.target Y.toAction) Z first) :
    HEq ((same ▸ event : IntrinsicScopedOperationalPresheafNaturalEvidence.Evidence (model A)
      (sortEvents Y.toAction) (IntrinsicScopedOperationalPresheafEventPowers.source Y.toAction)
      (IntrinsicScopedOperationalPresheafEventPowers.target Y.toAction) Z second).1) event.1 := by
  cases same
  rfl

/-- Restage every original ordered bound premise without changing its retained witness. -/
def restageChildren {Z Z' : target A} (h : Z' ⟶ Z)
    (occurrence : Instance R ((model A).stage Z)) (children : Children R Y occurrence) :
    Children R Y (mapInstance R ((model A).stageRestage h) occurrence) :=
  fun position => (mapInstance_child R ((model A).stageRestage h) occurrence position).symm ▸
    IntrinsicScopedOperationalPresheafNaturalEvidence.restage h (children position)

/-- The bound child arrow is precomposed by the actual ordered-context stage map. -/
theorem boundChild_stageRestage {Z Z' : target A} (h : Z' ⟶ Z)
    (occurrence : Instance R ((model A).stage Z)) (children : Children R Y occurrence)
    (position : Fin (R.get occurrence.index).2.premises.length) :
    boundChild A R Y.toAction (mapInstance R ((model A).stageRestage h) occurrence) position
        (restageChildren R Y h occurrence children position) =
      ((model A).ctx ((R.get occurrence.index).2.premises.get position).binders ◁
        ((model A).ctx occurrence.ambient ◁ h)) ≫
        boundChild A R Y.toAction occurrence position (children position) := by
  let bs : Ctx S := ((R.get occurrence.index).2.premises.get position).binders
  have value : (restageChildren R Y h occurrence children position).1 =
      ((model A).ctx (bs ++ occurrence.ambient) ◁ h) ≫ (children position).1 :=
    eq_of_heq (evidence_transport_val R Y
    (mapInstance_child R ((model A).stageRestage h) occurrence position).symm
    (IntrinsicScopedOperationalPresheafNaturalEvidence.restage h (children position)))
  change boundContextArrow (model A) bs occurrence.ambient Z' ≫
      (restageChildren R Y h occurrence children position).1 =
    ((model A).ctx bs ◁ ((model A).ctx occurrence.ambient ◁ h)) ≫
      (boundContextArrow (model A) bs occurrence.ambient Z ≫ (children position).1)
  have precomposed := congrArg (boundContextArrow (model A) bs occurrence.ambient Z' ≫ ·) value
  have geometry := congrArg (fun arrow => arrow ≫ (children position).1)
    (boundContextArrow_restage (model A) bs occurrence.ambient h).symm
  exact precomposed.trans ((Category.assoc _ _ _).symm.trans
    (geometry.trans (Category.assoc _ _ _)))

/-- Canonical evaluation of any natural function commutes with a stage map. -/
theorem canonicalEvaluation_stageMap {W W' F : target A} (h : W' ⟶ W)
    (bs : Ctx S) (original : (model A).ctx bs ⊗ W ⟶ F)
    (restaged : (model A).ctx bs ⊗ W' ⟶ F)
    (same : restaged = ((model A).ctx bs ◁ h) ≫ original)
    (X : Base A) (point : W'.obj X) :
    restaged.app (extendedStage A bs X) (canonicalPoint A bs X point) =
      original.app (extendedStage A bs X) (canonicalPoint A bs X (h.app X point)) :=
  (congrArg (fun (arrow : (model A).ctx bs ⊗ W' ⟶ F) =>
    arrow.app (extendedStage A bs X) (canonicalPoint A bs X point)) same).trans
      (congrArg (original.app (extendedStage A bs X)) (canonicalPoint_stageMap h bs X point))

/-- At any canonical binder point, the restaged child is the same retained sorted event. -/
theorem childAtPoint_stageRestage {Z Z' : target A} (h : Z' ⟶ Z)
    (occurrence : Instance R ((model A).stage Z)) (children : Children R Y occurrence)
    (position : Fin (R.get occurrence.index).2.premises.length)
    (X : Base A) (point : ((model A).ctx occurrence.ambient ⊗ Z').obj X) :
    childAtPoint A R Y.toAction (mapInstance R ((model A).stageRestage h) occurrence) position
        (restageChildren R Y h occurrence children position) X point =
      childAtPoint A R Y.toAction occurrence position (children position) X
        (((model A).ctx occurrence.ambient ◁ h).app X point) := by
  exact canonicalEvaluation_stageMap ((model A).ctx occurrence.ambient ◁ h)
    ((R.get occurrence.index).2.premises.get position).binders
    (boundChild A R Y.toAction occurrence position (children position))
    (boundChild A R Y.toAction (mapInstance R ((model A).stageRestage h) occurrence) position
      (restageChildren R Y h occurrence children position))
    (boundChild_stageRestage R Y h occurrence children position) X point

/-- Equal retained sorted events preserve evidence through arbitrary endpoint transports. -/
theorem sortEventTransport_congr {s : S.Srt} (X : Base A)
    {first second : (sortEvents Y.toAction s).obj X} (same : first = second)
    {j j' : Judgment A} (firstJudgment : sortEventJudgment A Y.toAction X first = j)
    (secondJudgment : sortEventJudgment A Y.toAction X second = j') :
    HEq (firstJudgment ▸ sortEventEvidence A Y.toAction X first : Y.carrier j)
      (secondJudgment ▸ sortEventEvidence A Y.toAction X second : Y.carrier j') :=
  (heq_transport firstJudgment _).trans
    ((sortEventEvidence_congr A Y.toAction X same).trans (heq_transport secondJudgment _).symm)

/-- The actual point child retains the raw sorted event's individual witness. -/
theorem pointChildEvidence_raw {Z : target A}
    (occurrence : Instance R ((model A).stage Z)) (children : Children R Y occurrence)
    (position : Fin (R.get occurrence.index).2.premises.length)
    (X : Base A) (point : (occurrenceStage R occurrence).obj X) :
    HEq (pointChildEvidence A R Y.toAction occurrence position (children position) X point)
      (sortEventEvidence A Y.toAction _
        (childAtPoint A R Y.toAction occurrence position (children position) X point)) :=
  heq_transport (childAtPoint_judgment A R Y.toAction occurrence position (children position) X point) _

/-- Every original ordered child witness is preserved under arbitrary stage maps. -/
theorem pointChildEvidence_stageRestage {Z Z' : target A} (h : Z' ⟶ Z)
    (occurrence : Instance R ((model A).stage Z)) (children : Children R Y occurrence)
    (position : Fin (R.get occurrence.index).2.premises.length)
    (X : Base A) (point : ((model A).ctx occurrence.ambient ⊗ Z').obj X) :
    HEq (pointChildEvidence A R Y.toAction (mapInstance R ((model A).stageRestage h) occurrence)
      position (restageChildren R Y h occurrence children position) X point)
      (pointChildEvidence A R Y.toAction occurrence position (children position) X
        (((model A).ctx occurrence.ambient ◁ h).app X point)) := by
  have first := pointChildEvidence_raw R Y (mapInstance R ((model A).stageRestage h) occurrence)
    (restageChildren R Y h occurrence children) position X point
  have raw := sortEventEvidence_congr A Y.toAction _
    (childAtPoint_stageRestage R Y h occurrence children position X point)
  have second := pointChildEvidence_raw R Y occurrence children position X
    (((model A).ctx occurrence.ambient ◁ h).app X point)
  exact first.trans (raw.trans second.symm)

/-- The original local model fires the same complete occurrence after any stage change. -/
theorem pointFire_stageRestage {Z Z' : target A} (h : Z' ⟶ Z)
    (occurrence : Instance R ((model A).stage Z)) (children : Children R Y occurrence)
    (X : Base A) (point : ((model A).ctx occurrence.ambient ⊗ Z').obj X) :
    pointFire R Y (mapInstance R ((model A).stageRestage h) occurrence)
        (restageChildren R Y h occurrence children) X point =
      pointFire R Y occurrence children X
        (((model A).ctx occurrence.ambient ◁ h).app X point) := by
  have same := pointInstance_stageRestage R h occurrence X point
  apply sortedEvent_ext R Y X
  · exact congrArg (conclusionJudgment R A) same
  · exact rulesAct_heq R Y.rules (congrArg (conclusionJudgment R A) same) same rfl rfl _ _
      (by
        intro position otherPosition samePosition
        cases samePosition
        exact pointChildEvidence_stageRestage R Y h occurrence children position X point)

/-- The actual natural rule function commutes with every map of generalized stages. -/
theorem ruleFunction_stageRestage {Z Z' : target A} (h : Z' ⟶ Z)
    (occurrence : Instance R ((model A).stage Z)) (children : Children R Y occurrence) :
    ruleFunction R Y (mapInstance R ((model A).stageRestage h) occurrence)
        (restageChildren R Y h occurrence children) =
      ((model A).ctx occurrence.ambient ◁ h) ≫ ruleFunction R Y occurrence children := by
  ext X point
  exact pointFire_stageRestage R Y h occurrence children X point

/-- Equal judgment indices and equal full event arrows give equal natural evidence. -/
theorem evidence_heq_of_val {Z : target A}
    {first second : Judgment ((model A).stage Z)} (same : first = second)
    (event : IntrinsicScopedOperationalPresheafNaturalEvidence.Evidence (model A)
      (sortEvents Y.toAction) (IntrinsicScopedOperationalPresheafEventPowers.source Y.toAction)
      (IntrinsicScopedOperationalPresheafEventPowers.target Y.toAction) Z first)
    (other : IntrinsicScopedOperationalPresheafNaturalEvidence.Evidence (model A)
      (sortEvents Y.toAction) (IntrinsicScopedOperationalPresheafEventPowers.source Y.toAction)
      (IntrinsicScopedOperationalPresheafEventPowers.target Y.toAction) Z second)
    (value : HEq event.1 other.1) : HEq event other := by
  subst same
  exact heq_of_eq (Subtype.ext (eq_of_heq value))

/-- The implemented generalized rule evidence preserves every stage map and both endpoints. -/
theorem ruleEvidence_stageRestage {Z Z' : target A} (h : Z' ⟶ Z)
    (occurrence : Instance R ((model A).stage Z)) (children : Children R Y occurrence) :
    HEq (ruleEvidence R Y (mapInstance R ((model A).stageRestage h) occurrence)
      (restageChildren R Y h occurrence children))
      (IntrinsicScopedOperationalPresheafNaturalEvidence.restage h (ruleEvidence R Y occurrence children)) :=
  evidence_heq_of_val R Y
    (IntrinsicScopedLocalPolynomial.mapInstance_conclusion R ((model A).stageRestage h) occurrence)
    _ _ (heq_of_eq (ruleFunction_stageRestage R Y h occurrence children))

/-- The actual rule algebra commutes with arbitrary generalized stage maps,
with all authored ordered premise positions mapped to their genuine child fibers. -/
theorem naturalRules_stageRestage {Z Z' : target A} (h : Z' ⟶ Z)
    {j : Judgment ((model A).stage Z)}
    (shape : IntrinsicScopedLocalPolynomial.Shape R ((model A).stage Z) j)
    (children : ∀ position : Fin (R.get shape.1.index).2.premises.length,
      IntrinsicScopedOperationalPresheafNaturalEvidence.Evidence (model A)
        (sortEvents Y.toAction) (IntrinsicScopedOperationalPresheafEventPowers.source Y.toAction)
        (IntrinsicScopedOperationalPresheafEventPowers.target Y.toAction) Z
        (childJudgment R ((model A).stage Z) shape.1 position)) :
    IntrinsicScopedOperationalPresheafNaturalEvidence.restage h
        ((naturalRules R Y Z).act () j ⟨shape, children⟩) =
      (naturalRules R Y Z').act () (mapJudgment ((model A).stageRestage h) j)
        ⟨IntrinsicScopedLocalPolynomial.mapShape R ((model A).stageRestage h) shape,
          restageChildren R Y h shape.1 children⟩ := by
  obtain ⟨occurrence, same⟩ := shape
  subst same
  exact eq_of_heq ((ruleEvidence_stageRestage R Y h occurrence children).symm.trans
    (heq_transport
      (IntrinsicScopedLocalPolynomial.mapInstance_conclusion R ((model A).stageRestage h) occurrence)
      (ruleEvidence R Y (mapInstance R ((model A).stageRestage h) occurrence)
        (restageChildren R Y h occurrence children))).symm)

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafRuleNaturality
