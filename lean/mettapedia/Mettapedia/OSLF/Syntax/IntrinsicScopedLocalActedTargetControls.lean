import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTargetOperations
import Mettapedia.OSLF.Syntax.CategoricalBindingDiagonalTargetControl
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTypeComparisonControls

/-!
# Operational diagonal target controls

The existing Boolean Lambda interpretation is transported into a product
category. Its LamCong rule acts on an actual premise under a binder, at a
mixed generalized stage. Both classification and the mapped free operation
arrow are compared with the transported model's actual rule action.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedTargetControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoricalBindingModel
open IntrinsicScopedLocalPolynomial
open IntrinsicScopedLocalActedClassifier
open IntrinsicScopedLocalActedCategoricalModels
open IntrinsicScopedLocalActedTypeComparisonControls
open CategoricalBindingDiagonalTargetControl
open AuthoredPositionedRulePolynomial (Judgment mapJudgment)

universe u v w w'

section ProductLimits

variable {D : Type u} [Category.{v} D]
variable {J : Type w} [Category.{w'} J] [HasLimitsOfShape J D]

/-- Limits of pairs of diagrams are formed from their componentwise limits. -/
def componentLimitCone (F : J ⥤ D × D) : LimitCone F where
  cone :=
    { pt := (limit (F ⋙ CategoryTheory.Prod.fst D D), limit (F ⋙ CategoryTheory.Prod.snd D D))
      π :=
        { app j := (limit.π (F ⋙ CategoryTheory.Prod.fst D D) j,
            limit.π (F ⋙ CategoryTheory.Prod.snd D D) j)
          naturality i j f := by
            apply Prod.hom_ext
            · exact (Category.id_comp _).trans (limit.w (F ⋙ CategoryTheory.Prod.fst D D) f).symm
            · exact (Category.id_comp _).trans (limit.w (F ⋙ CategoryTheory.Prod.snd D D) f).symm } }
  isLimit :=
    { lift s := (limit.lift _ ((CategoryTheory.Prod.fst D D).mapCone s),
        limit.lift _ ((CategoryTheory.Prod.snd D D).mapCone s))
      fac s j := Prod.hom_ext (limit.lift_π _ j) (limit.lift_π _ j)
      uniq s m hm := by
        apply Prod.hom_ext
        · apply limit.hom_ext
          intro j
          exact (congrArg (fun f => f.1) (hm j)).trans
            (limit.lift_π ((CategoryTheory.Prod.fst D D).mapCone s) j).symm
        · apply limit.hom_ext
          intro j
          exact (congrArg (fun f => f.2) (hm j)).trans
            (limit.lift_π ((CategoryTheory.Prod.snd D D).mapCone s) j).symm }

instance productHasLimitsOfShape : HasLimitsOfShape J (D × D) where
  has_limit F := HasLimit.mk (componentLimitCone F)

end ProductLimits

/-- The actual nonidentity target-change functor. -/
abbrev duplicate := diagonal (Type)

/-- The model has the actual image program sorts, powers and event objects. -/
def imageModel : CategoricalModel lambdaRules noEquations (D := Type × Type) :=
  boolModel.targetModel duplicate

/-- The actual image binding model, used independently of its rule structure. -/
abbrev imagePrograms : Model LambdaContextualRung.sig (Type × Type) :=
  (boolModel.imageProgram duplicate).interpretation.model

/-- This stage has two different component types. -/
abbrev mixedStage : Type × Type := (PUnit, Bool)

/-- This generalized stage is outside the diagonal functor's essential image. -/
theorem mixedStage_not_in_diagonal_image (Z : Type) :
    ¬ Nonempty (duplicate.obj Z ≅ mixedStage) := by
  rintro ⟨e⟩
  let first : Z ≅ PUnit := (CategoryTheory.Prod.fst Type Type).mapIso e
  let second : Z ≅ Bool := (CategoryTheory.Prod.snd Type Type).mapIso e
  let impossible : Bool ≅ PUnit := second.symm ≪≫ first
  have same : impossible.toEquiv false = impossible.toEquiv true := Subsingleton.elim _ _
  have contradiction : (false : Bool) = true := impossible.toEquiv.injective same
  cases contradiction

/-- The actual image event object carries two independent endpoint pairs. -/
theorem imageModel_event (Γ : Ctx LambdaContextualRung.sig) :
    imageModel.objects.event Γ .term =
      ((boolPrograms.power Γ .term × boolPrograms.power Γ .term),
        (boolPrograms.power Γ .term × boolPrograms.power Γ .term)) := rfl

/-- Generalized endpoint pairs at the mixed stage. -/
def pairEvent (j : Judgment (imagePrograms.stage mixedStage)) :
    imageModel.objects.StageEvent mixedStage j :=
  ⟨(TypeCat.ofHom (fun z => ((imagePrograms.elemEquiv j.2.2.1).1 z,
        (imagePrograms.elemEquiv j.2.2.2).1 z)),
      TypeCat.ofHom (fun z => ((imagePrograms.elemEquiv j.2.2.1).2 z,
        (imagePrograms.elemEquiv j.2.2.2).2 z))),
    by apply Prod.hom_ext <;> apply TypeCat.Hom.ext <;> apply TypeCat.Fun.ext <;> funext z <;> rfl,
    by apply Prod.hom_ext <;> apply TypeCat.Hom.ext <;> apply TypeCat.Fun.ext <;> funext z <;> rfl⟩

/-- Endpoints determine a pair-model event, also at the mixed target stage. -/
instance mixedStageEventSubsingleton (j : Judgment (imagePrograms.stage mixedStage)) :
    Subsingleton (imageModel.objects.StageEvent mixedStage j) := by
  constructor
  intro e e'
  apply Subtype.ext
  apply Prod.hom_ext
  · apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext z
    apply Prod.ext
    · exact (congrArg (fun f => f.1 z) e.2.1).trans
        (congrArg (fun f => f.1 z) e'.2.1).symm
    · exact (congrArg (fun f => f.1 z) e.2.2).trans
        (congrArg (fun f => f.1 z) e'.2.2).symm
  · apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext z
    apply Prod.ext
    · exact (congrArg (fun f => f.2 z) e.2.1).trans
        (congrArg (fun f => f.2 z) e'.2.1).symm
    · exact (congrArg (fun f => f.2 z) e.2.2).trans
        (congrArg (fun f => f.2 z) e'.2.2).symm

open LambdaContextualRung (sig Srt Op)

/-- The first body depends on both the local binder and the second stage value. -/
def leftPoint : mixedStage ⟶
    (boolPrograms.power [.term] .term, boolPrograms.power [.term] .term) :=
  (TypeCat.ofHom (fun _ => leftBody),
    TypeCat.ofHom (fun z => if z then leftBody else rightBody))

/-- The second body has the opposite local behavior in each component. -/
def rightPoint : mixedStage ⟶
    (boolPrograms.power [.term] .term, boolPrograms.power [.term] .term) :=
  (TypeCat.ofHom (fun _ => rightBody),
    TypeCat.ofHom (fun z => if z then rightBody else leftBody))

def falsePoint : mixedStage ⟶
    (boolPrograms.power [] .term, boolPrograms.power [] .term) :=
  (TypeCat.ofHom (fun _ _ => false), TypeCat.ofHom (fun _ _ => false))

def truePoint : mixedStage ⟶
    (boolPrograms.power [] .term, boolPrograms.power [] .term) :=
  (TypeCat.ofHom (fun _ _ => true), TypeCat.ofHom (fun _ _ => true))

/-- Values for the unchanged rule telescope at the mixed target stage. -/
def mixedValues : SemanticContextualMetavariables.Valuation
    (M := IntrinsicLambdaFourRulePresentation.metas) (imagePrograms.stage mixedStage) []
  | ⟨0, _⟩ => imagePrograms.elemEquiv.symm leftPoint
  | ⟨1, _⟩ => imagePrograms.elemEquiv.symm rightPoint
  | ⟨2, _⟩ => imagePrograms.elemEquiv.symm falsePoint
  | ⟨3, _⟩ => imagePrograms.elemEquiv.symm truePoint
  | ⟨4, _⟩ => imagePrograms.elemEquiv.symm truePoint
  | ⟨_ + 5, impossible⟩ => by
      simp [IntrinsicLambdaFourRulePresentation.metas] at impossible

/-- The actual authored LamCong occurrence in the transported model. -/
def mixedOccurrence : Instance lambdaRules (imagePrograms.stage mixedStage) where
  index := lamIndex
  ambient := []
  valuation := mixedValues
  close := fun _ var => nomatch var

/-- Its premise lives under the declared term binder. -/
theorem mixed_child_context :
    (childJudgment lambdaRules _ mixedOccurrence ⟨0, by decide⟩).1 = [.term] := rfl

/-- The ordered premise events are actual image-event values. -/
def mixedChildren (position : Fin (lambdaRules.get lamIndex).2.premises.length) :
    (boolModel.imageEvents duplicate).StageEvent mixedStage
      (childJudgment lambdaRules _ mixedOccurrence position) :=
  pairEvent _

/-- The transported rule algebra, with its program and event indices explicit. -/
def mixedRules : (IntrinsicScopedLocalPolynomial.rules lambdaRules
    (imagePrograms.stage mixedStage)).Algebra
      (fun _ j => imageModel.objects.StageEvent mixedStage j) :=
  imageModel.rules mixedStage

/-- The independently defined source operation for the LamCong constructor. -/
def lamOperation : boolModel.classifyingObject lamObject ⟶ boolModel.objects.event [] .term :=
  boolModel.foldOperation _ (ruleTree lambdaRules noEquations lamIndex [])

/-- The rule produces the actual endpoint pair specified by its conclusion. -/
theorem mixed_rule_action_pair :
    mixedRules.act () (conclusionJudgment lambdaRules _ mixedOccurrence)
      ⟨⟨mixedOccurrence, rfl⟩, mixedChildren⟩ =
        pairEvent (conclusionJudgment lambdaRules _ mixedOccurrence) :=
  @Subsingleton.elim _ (mixedStageEventSubsingleton _) _ _

/-- The premise's interpreted source is the supplied local body. -/
theorem mixed_child_sourcePoint :
    imagePrograms.elemEquiv
      (childJudgment lambdaRules _ mixedOccurrence ⟨0, by decide⟩).2.2.1 = leftPoint := by
  apply Eq.trans ?_ (imagePrograms.elemEquiv.apply_symm_apply leftPoint)
  apply congrArg imagePrograms.elemEquiv
  change (imagePrograms.stage mixedStage).substitution.substitute _
    (imagePrograms.elemEquiv.symm leftPoint) = imagePrograms.elemEquiv.symm leftPoint
  trans (imagePrograms.stage mixedStage).substitution.substitute
    (fun _ v => (imagePrograms.stage mixedStage).substitution.injectVar v)
    (imagePrograms.elemEquiv.symm leftPoint)
  · congr 1
    funext s v
    cases v with
    | zero => rfl
    | succ old => nomatch old
  · exact (imagePrograms.stage mixedStage).substitution.substitute_identity _

/-- The premise's interpreted target is its supplied replacement body. -/
theorem mixed_child_targetPoint :
    imagePrograms.elemEquiv
      (childJudgment lambdaRules _ mixedOccurrence ⟨0, by decide⟩).2.2.2 = rightPoint := by
  apply Eq.trans ?_ (imagePrograms.elemEquiv.apply_symm_apply rightPoint)
  apply congrArg imagePrograms.elemEquiv
  change (imagePrograms.stage mixedStage).substitution.substitute _
    (imagePrograms.elemEquiv.symm rightPoint) = imagePrograms.elemEquiv.symm rightPoint
  trans (imagePrograms.stage mixedStage).substitution.substitute
    (fun _ v => (imagePrograms.stage mixedStage).substitution.injectVar v)
    (imagePrograms.elemEquiv.symm rightPoint)
  · congr 1
    funext s v
    cases v with
    | zero => rfl
    | succ old => nomatch old
  · exact (imagePrograms.stage mixedStage).substitution.substitute_identity _

/-- The actual child evidence reads both local-body values in both coordinates. -/
theorem mixed_children_coordinates :
    (mixedChildren ⟨0, by decide⟩).1.1 PUnit.unit = (leftBody, rightBody) ∧
      (mixedChildren ⟨0, by decide⟩).1.2 false = (rightBody, leftBody) := by
  change
    ((imagePrograms.elemEquiv
      (childJudgment lambdaRules _ mixedOccurrence ⟨0, by decide⟩).2.2.1).1 PUnit.unit,
      (imagePrograms.elemEquiv
        (childJudgment lambdaRules _ mixedOccurrence ⟨0, by decide⟩).2.2.2).1 PUnit.unit) = _ ∧
    ((imagePrograms.elemEquiv
      (childJudgment lambdaRules _ mixedOccurrence ⟨0, by decide⟩).2.2.1).2 false,
      (imagePrograms.elemEquiv
        (childJudgment lambdaRules _ mixedOccurrence ⟨0, by decide⟩).2.2.2).2 false) = _
  rw [mixed_child_sourcePoint, mixed_child_targetPoint]
  constructor <;> rfl

/-- These are distinct programs beneath the local binder. -/
theorem mixed_child_programs_distinct :
    ((mixedChildren ⟨0, by decide⟩).1.1 PUnit.unit).1 ≠
      ((mixedChildren ⟨0, by decide⟩).1.1 PUnit.unit).2 := by
  have coordinates := mixed_children_coordinates.1
  intro same
  exact bodies_distinct ((congrArg Prod.fst coordinates).symm.trans
    (same.trans (congrArg Prod.snd coordinates)))

/-- Endpoint-pair construction respects equality of judgments. -/
theorem pairEvent_heq {j j' : Judgment (imagePrograms.stage mixedStage)}
    (same : j = j') : HEq (pairEvent j) (pairEvent j') := by
  cases same
  rfl

/-- The program point and the ordered binder-local witnesses of the mixed firing. -/
def mixedValuation : imageModel.StageValuation mixedStage lamObject where
  point := imagePrograms.rulePoint lambdaRules mixedOccurrence
  event := fun position => pairEvent
    (mapJudgment ((imageModel.stageTarget mixedStage).program
      (imagePrograms.rulePoint lambdaRules mixedOccurrence))
        ((events lambdaRules noEquations lamObject).listed.label position))

/-- The actual program point recovers the declared mixed-stage occurrence. -/
theorem mixed_program_occurrence_comparison :
    mapInstance lambdaRules ((imageModel.stageTarget mixedStage).program mixedValuation.point)
      (ruleInstance lambdaRules noEquations lamIndex []) = mixedOccurrence :=
  imagePrograms.mapInstance_rulePoint lambdaRules noEquations imageModel.program.satisfies mixedOccurrence

/-- The generic ordered premises are the supplied mixed-stage witnesses. -/
theorem mixed_premise_comparison
    (p : Fin (lambdaRules.get mixedOccurrence.index).2.premises.length)
    (q : Fin (lambdaRules.get lamIndex).2.premises.length) (same : HEq p q) :
    HEq (mixedChildren p) (mixedValuation.event q) := by
  have sameIndex : p = q := eq_of_heq same
  subst q
  apply pairEvent_heq
  exact (childJudgment_congr lambdaRules mixed_program_occurrence_comparison.symm p p HEq.rfl).trans
    (mapInstance_child lambdaRules ((imageModel.stageTarget mixedStage).program mixedValuation.point)
      (ruleInstance lambdaRules noEquations lamIndex []) p)

/-- The represented categorical point of the mixed-stage program/event valuation. -/
def mixedClassifierPoint : mixedStage ⟶ imageModel.classifyingObject lamObject :=
  (imageModel.valuationsRepresentableBy lamObject).homEquiv.symm mixedValuation

/-- The actual classifying rule arrow evaluates the supplied binder-local firing tree. -/
theorem mixed_classifying_rule_fold :
    (mixedClassifierPoint ≫ imageModel.classifyingFunctor.map
      (ruleRep lambdaRules noEquations lamIndex [])) ≫ (imageModel.eventIso [] .term).inv =
      (mixedValuation.evaluate _ (ruleTree lambdaRules noEquations lamIndex [])).1 := by
  have read := imageModel.comp_rep_eventIso_inv mixedClassifierPoint _
    (ruleTree lambdaRules noEquations lamIndex [])
  have valuation : (imageModel.valuationsRepresentableBy lamObject).homEquiv mixedClassifierPoint =
      mixedValuation := (imageModel.valuationsRepresentableBy lamObject).homEquiv.apply_symm_apply _
  rw [valuation] at read
  exact read

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedTargetControls
