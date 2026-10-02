import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedFunctorModelLaws
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedModelMaps

/-!
# Maps of structure-preserving functors are maps of their models

A natural transformation of structure-preserving functors gives a map of
their models: on programs, the map of binding models its restriction to
event-free objects determines; on events, its components at the generic event
objects. Naturality at the generic substitutions and generic occurrences of
rules makes these components commute with the substitution and rule actions.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.CategoricalBindingInterpretationMaps

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.CategoricalBindingModel

universe u v

variable {S : Signature} {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

/-- The identity transformation of classifying functors is the identity map. -/
theorem Hom.ofNat_id (M : Model S D) : Hom.ofNat (𝟙 M.classifyingFunctor) = Hom.id M := by
  have identity : classifyingMap (Hom.id M) = 𝟙 M.classifyingFunctor := by
    apply NatTrans.ext
    funext X
    exact Model.familyMap_id M X.arities
  rw [← identity]
  exact Hom.ofNat_classifyingMap (Hom.id M)

/-- Composite transformations of classifying functors are composite maps. -/
theorem Hom.ofNat_comp {M N P : Model S D} (first : M.classifyingFunctor ⟶ N.classifyingFunctor)
    (second : N.classifyingFunctor ⟶ P.classifyingFunctor) :
    Hom.ofNat (first ≫ second) = Hom.comp (Hom.ofNat first) (Hom.ofNat second) := by
  have composite : classifyingMap (Hom.comp (Hom.ofNat first) (Hom.ofNat second)) =
      first ≫ second := by
    have functorial := (classifyingFunctor (S := S) (D := D)).map_comp (X := ⟨M⟩) (Y := ⟨N⟩)
      (Z := ⟨P⟩) (Hom.ofNat first) (Hom.ofNat second)
    change classifyingMap (Hom.comp _ _) = classifyingMap _ ≫ classifyingMap _ at functorial
    rw [functorial, Hom.classifyingMap_ofNat, Hom.classifyingMap_ofNat]
  rw [← composite]
  exact Hom.ofNat_classifyingMap _

end Mettapedia.OSLF.Binding.CategoricalBindingInterpretationMaps

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext (Context seeds)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFibres
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
  (substJudgment heq_transport mapJudgment_substJudgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFree (Tree)

universe u v

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {S : Signature} {R : List (LocalRule S)}
variable {M' : List (MetaArity S)} {equations : List (EqAxiom S M')}

/-- Maps of generalized events agree at equal judgments on equal events. -/
theorem EventObjects.Hom.stage_heq {M N : Model S D} {E : EventObjects M} {E' : EventObjects N}
    {h : CategoricalBindingInterpretationMaps.Hom M N} (f : E.Hom E' h) (Z : D)
    {j j' : Judgment (M.stage Z)} (same : j = j') {e : E.StageEvent Z j} {e' : E.StageEvent Z j'}
    (sameEvent : HEq e e') : HEq (f.stage Z j e) (f.stage Z j' e') := by
  subst same
  cases sameEvent
  rfl

namespace StructuredFunctor

variable {F G H : StructuredFunctor R equations (D := D)}

/-! ## Programs -/

/-- The transformation of program classifiers of a map of structure-preserving
functors. -/
noncomputable def programNat (α : F ⟶ G) :
    F.programModel.classifyingFunctor ⟶ G.programModel.classifyingFunctor :=
  F.program.isoClassifying.inv ≫
    Functor.whiskerLeft ((authoredEquationPresentation S equations).quotientFunctor ⋙
      programSection R equations) α ≫ G.program.isoClassifying.hom

/-- **The map of program interpretations of a map of structure-preserving
functors.** -/
noncomputable def programHom (α : F ⟶ G) : F.programInterpretation ⟶ G.programInterpretation :=
  CategoricalBindingInterpretationMaps.Hom.ofNat (programNat α)

/-- On program objects the transformation is the product of its function-object
components. -/
theorem programIso_naturality (α : F ⟶ G) (X : Base equations) :
    α.app ((programSection R equations).obj X) ≫ (G.programIso X).hom =
      (F.programIso X).hom ≫ Model.familyMap (programHom α).underlying.power X.as.arities := by
  have components := Model.app_eq_familyMap (programNat α) X.as
  refine Eq.trans ?_ (congrArg ((F.programIso X).hom ≫ ·) components)
  change _ = (F.programIso X).hom ≫ ((F.programIso X).inv ≫ α.app _ ≫ (G.programIso X).hom)
  rw [Iso.hom_inv_id_assoc]

/-- The program point of a value moves along the transformation by the map of
function objects. -/
theorem programPoint_naturality (α : F ⟶ G) (a : Classifier R equations) :
    α.app a ≫ G.programPoint a =
      F.programPoint a ≫ Model.familyMap (programHom α).underlying.power a.base.as.arities :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (G.programIso a.base).hom)
    (α.naturality (toProgram R equations a)).symm).trans ((Category.assoc _ _ _).trans
      ((congrArg (F.carrier.map (toProgram R equations a) ≫ ·) (programIso_naturality α a.base)).trans
        (Category.assoc _ _ _).symm)))

theorem programHom_id (F : StructuredFunctor R equations (D := D)) :
    programHom (𝟙 F) = 𝟙 F.programInterpretation := by
  have identity : programNat (𝟙 F) = 𝟙 F.programModel.classifyingFunctor := by
    apply NatTrans.ext
    funext X
    change F.program.isoClassifying.inv.app X ≫ 𝟙 _ ≫ F.program.isoClassifying.hom.app X = 𝟙 _
    rw [Category.id_comp, Iso.inv_hom_id_app]
  unfold programHom
  rw [identity]
  exact CategoricalBindingInterpretationMaps.Hom.ofNat_id F.programModel

theorem programHom_comp (α : F ⟶ G) (β : G ⟶ H) :
    programHom (α ≫ β) = programHom α ≫ programHom β := by
  have composite : programNat (α ≫ β) = programNat α ≫ programNat β := by
    apply NatTrans.ext
    funext X
    change F.program.isoClassifying.inv.app X ≫ (α.app _ ≫ β.app _) ≫
        H.program.isoClassifying.hom.app X =
      (F.program.isoClassifying.inv.app X ≫ α.app _ ≫ G.program.isoClassifying.hom.app X) ≫
        (G.program.isoClassifying.inv.app X ≫ β.app _ ≫ H.program.isoClassifying.hom.app X)
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  unfold programHom
  rw [composite]
  exact CategoricalBindingInterpretationMaps.Hom.ofNat_comp _ _

/-! ## Events -/

/-- The source of an event is read off the program point of the generic event
object. -/
theorem source_eq (F : StructuredFunctor R equations (D := D)) (Γ : Ctx S) (s : S.Srt) :
    F.eventModel.objects.source Γ s = F.programPoint (eventObject R equations Γ s) ≫ fst _ _ :=
  (Category.assoc _ _ _).symm

theorem target_eq (F : StructuredFunctor R equations (D := D)) (Γ : Ctx S) (s : S.Srt) :
    F.eventModel.objects.target Γ s =
      F.programPoint (eventObject R equations Γ s) ≫ snd _ _ ≫ fst _ _ :=
  (Category.assoc _ _ _).symm

/-- **The map of event objects of a map of structure-preserving functors**:
its components at the generic event objects. -/
noncomputable def eventHom (α : F ⟶ G) :
    F.eventModel.objects.Hom G.eventModel.objects (programHom α) where
  event Γ s := α.app (eventObject R equations Γ s)
  source Γ s :=
    (congrArg (α.app _ ≫ ·) (source_eq G Γ s)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ fst _ _) (programPoint_naturality α _)).trans ((Category.assoc _ _ _).trans
        ((congrArg (F.programPoint _ ≫ ·) (tensorHom_fst _ _)).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ _) (source_eq F Γ s).symm))))))
  target Γ s := by
    have product : Model.familyMap (programHom α).underlying.power [(Γ, s), (Γ, s)] ≫
        snd _ _ ≫ fst _ _ = (snd _ _ ≫ fst _ _) ≫ (programHom α).underlying.power Γ s :=
      (tensorHom_snd_assoc _ _ _).trans ((congrArg (snd _ _ ≫ ·) (tensorHom_fst _ _)).trans
        (Category.assoc _ _ _).symm)
    exact (congrArg (α.app _ ≫ ·) (target_eq G Γ s)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ snd _ _ ≫ fst _ _) (programPoint_naturality α _)).trans
        ((Category.assoc _ _ _).trans ((congrArg (F.programPoint _ ≫ ·) product).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (target_eq F Γ s).symm))))))

/-- The stage clone map of a map of structure-preserving functors. -/
abbrev stageClone (α : F ⟶ G) (Z : D) :=
  stageMap (programHom α) Z

/-- **The value at a tree moves along the transformation by the map of
events.** -/
theorem treeEvent_map (α : F ⟶ G) {a : Classifier R equations}
    (J : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) J) {Z : D} (g : Z ⟶ F.carrier.obj a) :
    HEq (G.treeEvent J tree (g ≫ α.app a)) ((eventHom α).stage Z _ (F.treeEvent J tree g)) := by
  have point : (g ≫ α.app a) ≫ G.programPoint a =
      (g ≫ F.programPoint a) ≫ Model.familyMap (programHom α).underlying.power a.base.as.arities :=
    (Category.assoc _ _ _).trans ((congrArg (g ≫ ·) (programPoint_naturality α a)).trans
      (Category.assoc _ _ _).symm)
  have judgmentEq : mapJudgment (G.pointProgram ((g ≫ α.app a) ≫ G.programPoint a)) J =
      mapJudgment (stageClone α Z) (mapJudgment (F.pointProgram (g ≫ F.programPoint a)) J) :=
    (congrArg (fun y => mapJudgment (G.pointProgram y) J) point).trans
      ((congrArg (fun h => mapJudgment h J) (pointProgram_stageMap _
        F.programInterpretation.satisfies G.programInterpretation.satisfies (programHom α) a.base.as
          (g ≫ F.programPoint a))).trans (AuthoredPositionedRulePolynomial.mapJudgment_comp _ _ _))
  exact G.eventModel.objects.stageEvent_heq judgmentEq (heq_of_eq ((Category.assoc _ _ _).trans
    ((congrArg (g ≫ ·) (α.naturality (rep R equations J tree)).symm).trans
      (Category.assoc _ _ _).symm)))

/-- **Lifts of events and environments move along the transformation.** -/
theorem map_substitutionLift (α : F ⟶ G) {Z : D} (j : Judgment (F.programModel.stage Z))
    (e : F.eventModel.objects.StageEvent Z j) {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S (F.programModel.stage Z).substitution.Carrier j.1 Δ) :
    F.substitutionLift j e σ ≫ α.app (substitutionObject R equations j.1 Δ j.2.1) =
      G.substitutionLift (mapJudgment (stageClone α Z) j) ((eventHom α).stage Z j e)
        (fun t v => (stageClone α Z).raw.map (σ t v)) := by
  have point : (F.substitutionLift j e σ ≫ α.app (substitutionObject R equations j.1 Δ j.2.1)) ≫
      G.programPoint _ = G.programModel.substitutionPoint ((stageClone α Z).raw.map j.2.2.1)
        ((stageClone α Z).raw.map j.2.2.2) (fun t v => (stageClone α Z).raw.map (σ t v)) :=
    (Category.assoc _ _ _).trans ((congrArg (F.substitutionLift j e σ ≫ ·)
      (programPoint_naturality α _)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) (F.substitutionLift_point j e σ)).trans
          ((mapPoints (programHom α) Z).substitutionPoint _ _ σ))))
  have event : HEq ((F.substitutionLift j e σ ≫ α.app (substitutionObject R equations j.1 Δ j.2.1)) ≫
      G.carrier.map (rep R equations (a := substitutionObject R equations j.1 Δ j.2.1)
        (substitutionJudgment equations j.1 Δ j.2.1)
        (leaf R ((Context.empty R _).cons R _ (substitutionJudgment equations j.1 Δ j.2.1))
          (first R _ (Context.empty R _))))) ((eventHom α).stage Z j e).1 :=
    heq_of_eq ((Category.assoc _ _ _).trans ((congrArg (F.substitutionLift j e σ ≫ ·)
      (α.naturality _).symm).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ α.app _) (F.substitutionLift_event j e σ)))))
  exact G.eq_substitutionLift (mapJudgment (stageClone α Z) j) ((eventHom α).stage Z j e)
    (fun t v => (stageClone α Z).raw.map (σ t v))
    (F.substitutionLift j e σ ≫ α.app (substitutionObject R equations j.1 Δ j.2.1)) point event

/-- **Lifts of points and premises move along the transformation.** -/
theorem map_premiseLift (α : F ⟶ G) {X : Base equations} {Z : D}
    (x : Z ⟶ F.programModel.family X.as.arities) {x' : Z ⟶ G.programModel.family X.as.arities}
    (point : x ≫ Model.familyMap (programHom α).underlying.power X.as.arities = x')
    (I : Instance R (modelAt equations X))
    (children : ∀ position : Fin (R.get I.index).2.premises.length,
      F.eventModel.objects.StageEvent Z
        (childJudgment R _ (mapInstance R (F.pointProgram x) I) position))
    (mapped : ∀ position : Fin (R.get I.index).2.premises.length,
      G.eventModel.objects.StageEvent Z
        (childJudgment R _ (mapInstance R (G.pointProgram x') I) position))
    (same : ∀ position, HEq (mapped position) ((eventHom α).stage Z _ (children position))) :
    F.premiseLift x I children ≫ α.app (object R equations X ⟨⟨_, childJudgment R _ I⟩⟩) =
      G.premiseLift x' I mapped := by
  subst point
  refine G.eq_premiseLift _ I mapped _ ((Category.assoc _ _ _).trans
    ((congrArg (F.premiseLift x I children ≫ ·) (programPoint_naturality α _)).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ _) (F.premiseLift_point x I children))))) ?_
  intro position
  have read : F.premiseLift x I children ≫ F.carrier.map (rep R equations
      (a := object R equations X ⟨⟨_, childJudgment R _ I⟩⟩) (childJudgment R _ I position)
      (leaf R ⟨⟨_, childJudgment R _ I⟩⟩ position)) = (F.premiseEvents x I children position).1 :=
    (F.contextCones X).lift_event _ _ x (F.premiseEvents x I children) position
  have moved : HEq ((eventHom α).stage Z _ (F.premiseEvents x I children position))
      (mapped position) :=
    ((eventHom α).stage_heq Z (mapInstance_child R (F.pointProgram x) I position).symm
      (cast_heq _ _)).trans (same position).symm
  have judgmentEq : mapJudgment (stageClone α Z)
      (mapJudgment (F.pointProgram x) (childJudgment R _ I position)) =
        childJudgment R _ (mapInstance R (G.pointProgram
          (x ≫ Model.familyMap (programHom α).underlying.power X.as.arities)) I) position :=
    (congrArg (fun h => mapJudgment h (childJudgment R _ I position))
      (pointProgram_stageMap _ F.programInterpretation.satisfies G.programInterpretation.satisfies
        (programHom α) X.as x).symm).trans
      (mapInstance_child R _ I position).symm
  exact HEq.trans (heq_of_eq ((Category.assoc _ _ _).trans ((congrArg (F.premiseLift x I children ≫ ·)
    (α.naturality _).symm).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ α.app _) read)))))
    (G.eventModel.objects.stageEvent_val_heq judgmentEq moved)

/-- **Lifts of occurrences and premises move along the transformation.** -/
theorem map_ruleLift (α : F ⟶ G) {Z : D} (occurrence : Instance R (F.programModel.stage Z))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      F.eventModel.objects.StageEvent Z (childJudgment R _ occurrence position))
    (mapped : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      G.eventModel.objects.StageEvent Z
        (childJudgment R _ (mapInstance R (stageClone α Z) occurrence) position))
    (same : ∀ position, HEq (mapped position) ((eventHom α).stage Z _ (children position))) :
    F.ruleLift occurrence children ≫ α.app (ruleObject R equations occurrence.index occurrence.ambient) =
      G.ruleLift (mapInstance R (stageClone α Z) occurrence) mapped := by
  have moved : ∀ position, HEq
      (G.rulePremises (mapInstance R (stageClone α Z) occurrence) mapped position)
      ((eventHom α).stage Z _ (F.rulePremises occurrence children position)) := by
    intro position
    have one := G.rulePremises_heq (mapInstance R (stageClone α Z) occurrence) mapped position
    have two := F.rulePremises_heq occurrence children position
    have judgmentEq : childJudgment R _ occurrence position = childJudgment R _ (mapInstance R
        (F.pointProgram (F.programModel.rulePoint R occurrence))
        (ruleInstance R equations occurrence.index occurrence.ambient)) position :=
      childJudgment_congr R (F.programModel.mapInstance_rulePoint R equations
          F.programInterpretation.satisfies occurrence).symm position position HEq.rfl
    have three := (eventHom α).stage_heq Z judgmentEq two.symm
    exact one.trans ((same position).trans three)
  exact F.map_premiseLift α (F.programModel.rulePoint R occurrence)
    ((mapPoints (programHom α) Z).rulePoint R (stageClone α Z) (fun _ => rfl) occurrence)
    (ruleInstance R equations occurrence.index occurrence.ambient) (F.rulePremises occurrence children)
    (G.rulePremises (mapInstance R (stageClone α Z) occurrence) mapped) moved

/-! ## The maps of models -/

/-- **Maps of events commute with substitution.** -/
theorem actsAlong_map (α : F ⟶ G) (Z : D) :
    ActsAlong (stageClone α Z) (F.model.stageModel Z) (G.model.stageModel Z).act
      ((eventHom α).stage Z) := by
  intro j e Δ σ
  have one := (eventHom α).stage_heq Z (F.substitutionLift_judgment j e σ).symm
    (F.act_heq_treeEvent j e σ (substJudgment j σ) rfl)
  have two := (treeEvent_map α _ (substitutionTree R equations j.1 Δ j.2.1)
    (F.substitutionLift j e σ)).symm
  have three := congr_arg_heq (fun g => G.treeEvent _ (substitutionTree R equations j.1 Δ j.2.1) g)
    (map_substitutionLift α j e σ)
  have four := (G.act_heq_treeEvent (mapJudgment (stageClone α Z) j) ((eventHom α).stage Z j e)
    (fun t v => (stageClone α Z).raw.map (σ t v)) (mapJudgment (stageClone α Z) (substJudgment j σ))
    (mapJudgment_substJudgment _ j σ).symm).symm
  exact eq_of_heq (one.trans (two.trans (three.trans four)))

/-- **Maps of events commute with the rule actions.** -/
theorem rulesAlong_map (α : F ⟶ G) (Z : D) :
    RulesAlong (stageClone α Z) (F.model.stageModel Z) (G.model.stageModel Z).rules
      ((eventHom α).stage Z) := by
  intro j shape children
  have atTarget : j = mapJudgment (valuePoint (F.ruleLift shape.1 children))
      (conclusionJudgment R _ (ruleInstance R equations shape.1.index shape.1.ambient)) :=
    ((F.ruleLift_judgment shape.1 children).trans shape.2).symm
  have one := (eventHom α).stage_heq Z atTarget (F.rulesAlgebra_heq_treeEvent j ⟨shape, children⟩)
  have two := (treeEvent_map α _ (ruleTree R equations shape.1.index shape.1.ambient)
    (F.ruleLift shape.1 children)).symm
  let premises : ∀ position : Fin (R.get shape.1.index).2.premises.length,
      G.eventModel.objects.StageEvent Z
        (childJudgment R _ (mapInstance R (stageClone α Z) shape.1) position) := fun position =>
    ((mapInstance_child R (stageClone α Z) shape.1 position).symm ▸
      (eventHom α).stage Z _ (children position) :
        G.eventModel.objects.StageEvent Z
          (childJudgment R _ (mapInstance R (stageClone α Z) shape.1) position))
  have three := congr_arg_heq (fun g => G.treeEvent _ (ruleTree R equations shape.1.index
    shape.1.ambient) g) (map_ruleLift α shape.1 children premises (fun position => heq_transport _ _))
  have four := (G.rulesAlgebra_heq_treeEvent (mapJudgment (stageClone α Z) j)
    ⟨mapShape R (stageClone α Z) shape, premises⟩).symm
  exact eq_of_heq (one.trans (two.trans (three.trans four)))

/-- **The map of models of a map of structure-preserving functors.** -/
noncomputable def modelHom (α : F ⟶ G) : F.model ⟶ G.model where
  program := programHom α
  events := eventHom α
  stage Z := isHom_of_along (actsAlong_map α Z) (rulesAlong_map α Z)

end StructuredFunctor

/-- **Models of structure-preserving functors, on all their maps.** -/
noncomputable def modelFunctor :
    StructuredFunctor R equations (D := D) ⥤ CategoricalModel R equations (D := D) where
  obj F := F.model
  map α := StructuredFunctor.modelHom α
  map_id F := CategoricalModel.Hom.ext' (StructuredFunctor.programHom_id F) (fun _ _ => rfl)
  map_comp α β := CategoricalModel.Hom.ext' (StructuredFunctor.programHom_comp α β) (fun _ _ => rfl)

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

end
