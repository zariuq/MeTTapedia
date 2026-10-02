import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedTargetObjects
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedModelTransport

/-!
# Transport of operational models through qualified target functors

Recovery supplies the operations at every stage of the new target. The
canonical program and event comparisons then put those operations on the
actual image objects of the original model. Both actions and all model maps
are transported through the same comparisons.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial

universe u v u' v'

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D] [HasPullbacks D]
variable {D' : Type u'} [Category.{v'} D'] [CartesianMonoidalCategory D']
variable {S : Signature} {R : List (LocalRule S)}
variable {M' : List (MetaArity S)} {equations : List (EqAxiom S M')}
variable (H : D ⥤ D') [PreservesFiniteProducts H] [PreservesLimitsOfShape WalkingCospan H]
variable [ExponentialPreservation H]

namespace CategoricalModel

variable (M : CategoricalModel R equations (D := D))

/-- The actual image objects compare to the postcomposed interpretation's
generic objects, with the original endpoint laws. -/
def imageEventsIso : (M.imageEvents H).IsomorphicAlong
    (M.structured.postcompose H).eventModel.objects (M.imageProgramIso H) where
  event Γ s := H.mapIso (M.eventIso Γ s)
  source := (M.imageEventsHom H).source
  target := (M.imageEventsHom H).target

/-- The operational model on actual image sorts, powers and event objects. -/
def targetModel : CategoricalModel R equations (D := D') :=
  rehost (M.structured.postcompose H).model (M.imageProgram H) (M.imageEvents H)
    (M.imageProgramIso H) (M.imageEventsIso H)

/-- The image model has all the operations recovered from the postcomposed
classifier, through the specified image-object comparisons. -/
def targetModelIso : M.targetModel H ≅ (M.structured.postcompose H).model :=
  rehostIso (M.structured.postcompose H).model (M.imageProgram H) (M.imageEvents H)
    (M.imageProgramIso H) (M.imageEventsIso H)

@[simp] theorem targetModelIso_hom_program :
    (M.targetModelIso H).hom.program = (M.imageProgramIso H).hom := rfl

@[simp] theorem targetModelIso_hom_event (Γ : Ctx S) (s : S.Srt) :
    (M.targetModelIso H).hom.events.event Γ s = H.map (M.eventIso Γ s).hom := rfl

theorem targetModelIso_inv_program :
    (M.targetModelIso H).inv.program = (M.imageProgramIso H).inv := by
  apply (cancel_epi (M.imageProgramIso H).hom).mp
  have back : (M.imageProgramIso H).hom ≫ (M.targetModelIso H).inv.program = 𝟙 _ :=
    congrArg (fun f => f.program) (M.targetModelIso H).hom_inv_id
  exact back.trans (M.imageProgramIso H).hom_inv_id.symm

theorem targetModelIso_inv_event (Γ : Ctx S) (s : S.Srt) :
    (M.targetModelIso H).inv.events.event Γ s = H.map (M.eventIso Γ s).inv := by
  apply (cancel_epi (H.mapIso (M.eventIso Γ s)).hom).mp
  have back : H.map (M.eventIso Γ s).hom ≫ (M.targetModelIso H).inv.events.event Γ s = 𝟙 _ :=
    congrArg (fun f => f.events.event Γ s) (M.targetModelIso H).hom_inv_id
  exact back.trans (H.mapIso (M.eventIso Γ s)).hom_inv_id.symm

@[simp] theorem targetModel_sort (s : S.Srt) :
    (M.targetModel H).programModel.sort s = H.obj (M.programModel.sort s) := rfl

@[simp] theorem targetModel_power (Γ : Ctx S) (s : S.Srt) :
    (M.targetModel H).programModel.power Γ s = H.obj (M.programModel.power Γ s) := rfl

@[simp] theorem targetModel_event (Γ : Ctx S) (s : S.Srt) :
    (M.targetModel H).objects.event Γ s = H.obj (M.objects.event Γ s) := rfl

@[simp] theorem targetModel_source (Γ : Ctx S) (s : S.Srt) :
    (M.targetModel H).objects.source Γ s = H.map (M.objects.source Γ s) := rfl

@[simp] theorem targetModel_target (Γ : Ctx S) (s : S.Srt) :
    (M.targetModel H).objects.target Γ s = H.map (M.objects.target Γ s) := rfl

end CategoricalModel

variable [HasPullbacks D']

/-- Recovery of postcomposed interpretations, before replacing generic
objects by the actual image objects. -/
abbrev recoveredTargetTransport :
    CategoricalModel R equations (D := D) ⥤ CategoricalModel R equations (D := D') :=
  classifyFunctor ⋙ postcomposeStructured H ⋙ modelFunctor

/-- Change of target for the independently defined models and all their
maps. Its objects are the actual image models. -/
def transportModels :
    CategoricalModel R equations (D := D) ⥤ CategoricalModel R equations (D := D') :=
  (recoveredTargetTransport H).copyObj (fun M => M.targetModel H)
    (fun M => (M.targetModelIso H).symm)

/-- The replacement comparisons are natural on every model map. -/
def transportModelsRecoveryIso : transportModels (R := R) (equations := equations) H ≅
    recoveredTargetTransport H :=
  ((recoveredTargetTransport H).isoCopyObj (fun M => M.targetModel H)
    (fun M => (M.targetModelIso H).symm)).symm

omit [HasPullbacks D'] in
/-- Every model map acts on the actual image events by the image of its
original event component. The target may merge events lawfully. -/
theorem transportModels_map_event {M N : CategoricalModel R equations (D := D)}
    (f : M ⟶ N) (Γ : Ctx S) (s : S.Srt) :
    ((transportModels H).map f).events.event Γ s = H.map (f.events.event Γ s) := by
  change (M.targetModelIso H).hom.events.event Γ s ≫
    (StructuredFunctor.modelHom (Functor.whiskerRight (CategoricalModel.classifyingMap f) H)).events.event Γ s ≫
      (N.targetModelIso H).inv.events.event Γ s = _
  rw [M.targetModelIso_hom_event H Γ s, N.targetModelIso_inv_event H Γ s]
  change H.map (M.eventIso Γ s).hom ≫
    H.map ((CategoricalModel.classifyingMap f).app
      (IntrinsicScopedLocalActedClassifier.eventObject R equations Γ s)) ≫
        H.map (N.eventIso Γ s).inv = _
  have original : (M.eventIso Γ s).hom ≫ (CategoricalModel.classifyingMap f).app
      (IntrinsicScopedLocalActedClassifier.eventObject R equations Γ s) ≫ (N.eventIso Γ s).inv =
        f.events.event Γ s := by
    exact (congrArg ((M.eventIso Γ s).hom ≫ ·)
      (CategoricalModel.classifyingMap_eventIso_inv f Γ s)).trans
        ((M.eventIso Γ s).hom_inv_id_assoc (f.events.event Γ s))
  exact ((congrArg (H.map (M.eventIso Γ s).hom ≫ ·) (H.map_comp _ _).symm).trans
    (H.map_comp _ _).symm).trans (congrArg H.map original)

/-- Classifying the transported model agrees naturally with postcomposing
the original classifier, on all maps. -/
def targetClassificationIso :
    transportModels (R := R) (equations := equations) H ⋙ classifyFunctor ≅
      classifyFunctor ⋙ postcomposeStructured H :=
  Functor.isoWhiskerRight (transportModelsRecoveryIso H) classifyFunctor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (classifyFunctor ⋙ postcomposeStructured H) counitNatIso ≪≫
    Functor.rightUnitor _

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels
