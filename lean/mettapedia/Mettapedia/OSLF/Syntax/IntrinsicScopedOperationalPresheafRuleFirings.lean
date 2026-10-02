import Mettapedia.OSLF.Syntax.IntrinsicScopedOperationalPresheafRuleFunctions
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalSubstitutionModel

/-!
# Actual retained rule firings in the operational presheaf

A generalized occurrence and its ordered bound evidence functions are evaluated
at each actual clone context. The original local model then fires that actual
occurrence with every individual premise witness. Its genuine substitution law
makes the resulting retained event natural.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafRuleFirings

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open BindingSubstitutionAlgebra
open AuthoredPositionedRulePolynomial (Judgment)
open IntrinsicScopedConditionalPresheaf (Base programsAtEquiv)
open IntrinsicScopedOperationalPresheafPrograms (target model)
open IntrinsicScopedOperationalPresheafEvents (sortEvents)
open IntrinsicScopedOperationalPresheafRulePoints
open IntrinsicScopedOperationalPresheafRuleFunctions
open IntrinsicScopedLocalPolynomial (LocalRule Instance conclusionJudgment childJudgment)
open IntrinsicScopedLocalSubstitutionModel (SubstitutionModel rulesAct_congr_instance)
open IntrinsicScopedConditionalSubstitution (substJudgment heq_transport)

universe u
variable {S : Signature} {A : BindingCloneAlgebra.Algebra.{u} S}
variable (R : List (LocalRule S)) (Y : SubstitutionModel.{u,u} R A)

/-- The complete ordered premise family at its actual generalized child judgments. -/
abbrev Children {Z : target A} (occurrence : Instance R ((model A).stage Z)) :=
  ∀ position : Fin (R.get occurrence.index).2.premises.length,
    IntrinsicScopedOperationalPresheafNaturalEvidence.Evidence (model A)
      (sortEvents Y.toAction) (IntrinsicScopedOperationalPresheafEventPowers.source Y.toAction)
      (IntrinsicScopedOperationalPresheafEventPowers.target Y.toAction) Z
      (childJudgment R ((model A).stage Z) occurrence position)

/-- Fire the actual original occurrence with every retained ordered premise witness. -/
def pointFire {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (children : Children R Y occurrence) (X : Base A)
    (point : (occurrenceStage R occurrence).obj X) :
    (sortEvents Y.toAction (conclusionJudgment R ((model A).stage Z) occurrence).2.1).obj X :=
  ⟨⟨(conclusionJudgment R A (pointInstance R occurrence X point)).2.1,
    (conclusionJudgment R A (pointInstance R occurrence X point)).2.2,
      Y.rules.act () _ ⟨⟨pointInstance R occurrence X point, rfl⟩,
        fun position => pointChildEvidence A R Y.toAction occurrence position
          (children position) X point⟩⟩, rfl⟩

/-- The actual firing retains precisely the actual occurrence's conclusion. -/
theorem pointFire_judgment {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (children : Children R Y occurrence) (X : Base A)
    (point : (occurrenceStage R occurrence).obj X) :
    sortEventJudgment A Y.toAction X (pointFire R Y occurrence children X point) =
      conclusionJudgment R A (pointInstance R occurrence X point) := rfl

/-- The actual firing witness is the original rule action on every ordered child. -/
theorem pointFire_evidence {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (children : Children R Y occurrence) (X : Base A)
    (point : (occurrenceStage R occurrence).obj X) :
    sortEventEvidence A Y.toAction X (pointFire R Y occurrence children X point) =
      Y.rules.act () _ ⟨⟨pointInstance R occurrence X point, rfl⟩,
        fun position => pointChildEvidence A R Y.toAction occurrence position
          (children position) X point⟩ := rfl

/-- Equal endpoints and equal individual witnesses identify retained sorted events. -/
theorem sortedEvent_ext {s : S.Srt} (X : Base A)
    {first second : (sortEvents Y.toAction s).obj X}
    (sameJudgment : sortEventJudgment A Y.toAction X first =
      sortEventJudgment A Y.toAction X second)
    (sameEvidence : HEq (sortEventEvidence A Y.toAction X first)
      (sortEventEvidence A Y.toAction X second)) : first = second := by
  rcases first with ⟨⟨sort₁, pair₁, witness₁⟩, same₁⟩
  rcases second with ⟨⟨sort₂, pair₂, witness₂⟩, same₂⟩
  cases same₁
  cases same₂
  change (⟨X.unop.context, sort₁, pair₁⟩ : Judgment A) = ⟨X.unop.context, sort₁, pair₂⟩ at sameJudgment
  change HEq witness₁ witness₂ at sameEvidence
  have inner := eq_of_heq (Sigma.mk.inj_iff.mp sameJudgment).2
  have pairSame : pair₁ = pair₂ := eq_of_heq (Sigma.mk.inj_iff.mp inner).2
  cases pairSame
  cases sameEvidence
  rfl

/-- Every actual rule firing is natural under the original ambient clone substitution. -/
theorem pointFire_reindex {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (children : Children R Y occurrence) {X V : Base A} (f : X ⟶ V)
    (point : (occurrenceStage R occurrence).obj X) :
    (sortEvents Y.toAction _).map f (pointFire R Y occurrence children X point) =
      pointFire R Y occurrence children V ((occurrenceStage R occurrence).map f point) := by
  let σ := fromPositions X.unop.context f.unop
  let first := pointInstance R occurrence X point
  let second := pointInstance R occurrence V ((occurrenceStage R occurrence).map f point)
  have sameInstance : second = Instance.subst R first σ :=
    pointInstance_reindex R occurrence f point
  have sameConclusion : substJudgment (conclusionJudgment R A first) σ =
      conclusionJudgment R A second :=
    (IntrinsicScopedLocalPolynomial.conclusionJudgment_subst R first σ).symm.trans
      (congrArg (conclusionJudgment R A) sameInstance.symm)
  apply sortedEvent_ext R Y V
  · exact (sortEventJudgment_reindex A Y.toAction f _).trans sameConclusion
  · have original := sortEventEvidence_reindex A Y.toAction f
      (pointFire R Y occurrence children X point)
    have changeTarget := Y.toAction.act_heq
      (value₁ := sortEventEvidence A Y.toAction X (pointFire R Y occurrence children X point))
      rfl HEq.rfl HEq.rfl sameConclusion rfl sameConclusion
    have law := Y.act_rules ⟨first, rfl⟩
      (fun position => pointChildEvidence A R Y.toAction occurrence position
        (children position) X point) σ (conclusionJudgment R A second) sameConclusion
    have compare := rulesAct_congr_instance A Y.rules sameInstance.symm
      ((IntrinsicScopedLocalPolynomial.conclusionJudgment_subst R first σ).trans sameConclusion)
      rfl
      (fun position => Y.act _
        (pointChildEvidence A R Y.toAction occurrence position (children position) X point)
        (A.substitution.liftEnvironment σ ((R.get occurrence.index).2.premises.get position).binders)
        (childJudgment R A (Instance.subst R first σ) position)
        (IntrinsicScopedLocalPolynomial.childJudgment_subst R first σ position).symm)
      (fun position => pointChildEvidence A R Y.toAction occurrence position
        (children position) V ((occurrenceStage R occurrence).map f point))
      (by
        intro position otherPosition samePosition
        cases samePosition
        exact (Y.toAction.act_heq
          (value₁ := pointChildEvidence A R Y.toAction occurrence position (children position) X point)
          rfl HEq.rfl HEq.rfl
          (IntrinsicScopedLocalPolynomial.childJudgment_subst R first σ position)
          (IntrinsicScopedLocalPolynomial.childJudgment_subst R first σ position).symm rfl).trans
            (pointChildEvidence_reindex A R Y.toAction occurrence position (children position) f point).symm)
    exact original.trans (changeTarget.trans ((heq_of_eq law).trans (heq_of_eq compare)))

/-- The original local rule firing yields a genuine natural retained-event function. -/
def ruleFunction {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (children : Children R Y occurrence) : occurrenceStage R occurrence ⟶
      sortEvents Y.toAction (conclusionJudgment R ((model A).stage Z) occurrence).2.1 where
  app X := TypeCat.ofHom (pointFire R Y occurrence children X)
  naturality X V f := by
    apply ConcreteCategory.hom_ext
    intro point
    exact (pointFire_reindex R Y occurrence children f point).symm

/-- The two evaluated generalized conclusion endpoints are the actual point occurrence's pair. -/
theorem pointConclusion_pair {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (X : Base A) (point : (occurrenceStage R occurrence).obj X) :
    (programsAtEquiv A _ X
        (((model A).elemValue (conclusionJudgment R ((model A).stage Z) occurrence).2.2.1).app X point),
      programsAtEquiv A _ X
        (((model A).elemValue (conclusionJudgment R ((model A).stage Z) occurrence).2.2.2).app X point)) =
      (conclusionJudgment R A (pointInstance R occurrence X point)).2.2 := by
  have original := pointInstance_conclusion R occurrence X point
  have inner := eq_of_heq (Sigma.mk.inj_iff.mp original).2
  exact eq_of_heq (Sigma.mk.inj_iff.mp inner).2

/-- The rule function's actual source is the generalized original rule conclusion. -/
theorem ruleFunction_source {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (children : Children R Y occurrence) :
    ruleFunction R Y occurrence children ≫ IntrinsicScopedOperationalPresheafEventPowers.source Y.toAction _ =
      (model A).elemValue (conclusionJudgment R ((model A).stage Z) occurrence).2.2.1 := by
  ext X point
  apply (programsAtEquiv A _ X).injective
  exact (congrArg Prod.fst (pointConclusion_pair R occurrence X point)).symm

/-- The same firing function retains the generalized original target. -/
theorem ruleFunction_target {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (children : Children R Y occurrence) :
    ruleFunction R Y occurrence children ≫ IntrinsicScopedOperationalPresheafEventPowers.target Y.toAction _ =
      (model A).elemValue (conclusionJudgment R ((model A).stage Z) occurrence).2.2.2 := by
  ext X point
  apply (programsAtEquiv A _ X).injective
  exact (congrArg Prod.snd (pointConclusion_pair R occurrence X point)).symm

/-- Actual generalized rule firing, with both endpoint conditions proved. -/
def ruleEvidence {Z : target A} (occurrence : Instance R ((model A).stage Z))
    (children : Children R Y occurrence) :
    IntrinsicScopedOperationalPresheafNaturalEvidence.Evidence (model A)
      (sortEvents Y.toAction) (IntrinsicScopedOperationalPresheafEventPowers.source Y.toAction)
      (IntrinsicScopedOperationalPresheafEventPowers.target Y.toAction) Z
      (conclusionJudgment R ((model A).stage Z) occurrence) :=
  ⟨ruleFunction R Y occurrence children, ruleFunction_source R Y occurrence children,
    ruleFunction_target R Y occurrence children⟩

/-- The rule algebra at every stage fires the original local model pointwise. -/
def naturalRules (Z : target A) :
    (IntrinsicScopedLocalPolynomial.rules R ((model A).stage Z)).Algebra
      (fun _ judgment => IntrinsicScopedOperationalPresheafNaturalEvidence.Evidence (model A)
        (sortEvents Y.toAction) (IntrinsicScopedOperationalPresheafEventPowers.source Y.toAction)
        (IntrinsicScopedOperationalPresheafEventPowers.target Y.toAction) Z judgment) where
  act _ _judgment layer := layer.1.2 ▸ ruleEvidence R Y layer.1.1 layer.2

end Mettapedia.OSLF.Binding.IntrinsicScopedOperationalPresheafRuleFirings
