import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedPresheafEventsPair
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedUniversalProperty

/-!
# Reduction observation in an actual categorical interpretation

An extension's genuine comparison on the Yoneda restriction identifies the
transported endpoint arrow with the existing model's endpoint arrow, through
explicit event and pair isomorphisms. Coequalizer preservation then gives an
epimorphism from the transported generic reduction to the model's endpoint
image. The additional relevant mono hypothesis alone upgrades it to an
isomorphism.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

universe w u v

variable {S : Signature} {R : List (LocalRule S)}
variable {schema : List (MetaArity S)} {equations : List (EqAxiom S schema)}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D] [HasPullbacks D]
variable (N : CategoricalModel R equations (D := D))
variable (L : Presheaf.{w} R equations ⥤ D)
variable (restriction : embedding.{w} R equations ⋙ L ≅ N.classifyingFunctor)
variable (Γ : Ctx S) (s : S.Srt)

/-- Individual events are compared through the actual classifying-event
isomorphism, rather than through their reduction relation. -/
def interpretationEventIso :
    L.obj (event.{w} R equations Γ s) ≅ N.objects.event Γ s :=
  restriction.app (eventObject R equations Γ s) ≪≫ (N.eventIso Γ s).symm

/-- The extension acts on the represented pair comparison; it need not
preserve arbitrary products in the presheaf category. -/
def interpretationPairIso :
    L.obj (FunctorToTypes.prod (program.{w} R equations Γ s) (program R equations Γ s)) ≅
      N.programModel.power Γ s ⊗ N.programModel.power Γ s :=
  (L.mapIso (genericProgramPairIso R equations Γ s)).symm ≪≫
    restriction.app ((programSection R equations).obj (pairBase equations Γ s)) ≪≫
      N.programModel.pairComponentsIso Γ s

private theorem model_projection_endpoints :
    N.programProjection (eventObject R equations Γ s) ≫
        (N.programModel.pairComponentsIso Γ s).hom =
      (N.eventIso Γ s).inv ≫ N.toEventModel.eventEndpoints Γ s := by
  apply (cancel_epi (N.eventIso Γ s).hom).1
  rw [← Category.assoc, N.eventIso_hom_programProjection]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]

omit [CartesianMonoidalCategory D] [HasPullbacks D] in
private theorem extension_pair_cancel :
    L.map (genericEndpointMap R equations Γ s) ≫
      (L.mapIso (genericProgramPairIso R equations Γ s)).inv =
        L.map (genericEventProjection R equations Γ s) := by
  exact (congrArg (· ≫ (L.mapIso (genericProgramPairIso R equations Γ s)).inv)
    (extension_genericEndpointMap R equations Γ s L)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (L.map (genericEventProjection R equations Γ s) ≫ ·)
          (L.mapIso (genericProgramPairIso R equations Γ s)).hom_inv_id).trans
            (Category.comp_id _)))

/-- The actual endpoint arrow follows from naturality at the existing
generic event projection and the proved represented-pair comparison. -/
theorem interpretation_endpoint :
    L.map (genericEndpointMap R equations Γ s) ≫
        (interpretationPairIso N L restriction Γ s).hom =
      (interpretationEventIso N L restriction Γ s).hom ≫
        N.toEventModel.eventEndpoints Γ s := by
  change L.map (genericEndpointMap R equations Γ s) ≫
      (L.mapIso (genericProgramPairIso R equations Γ s)).inv ≫
        restriction.hom.app ((programSection R equations).obj (pairBase equations Γ s)) ≫
          (N.programModel.pairComponentsIso Γ s).hom =
    (restriction.hom.app (eventObject R equations Γ s) ≫ (N.eventIso Γ s).inv) ≫ _
  have natural := restriction.hom.naturality (toProgram R equations (eventObject R equations Γ s))
  change L.map (genericEventProjection R equations Γ s) ≫
      restriction.hom.app ((programSection R equations).obj (pairBase equations Γ s)) =
    restriction.hom.app (eventObject R equations Γ s) ≫
      N.classifyingFunctor.map (toProgram R equations (eventObject R equations Γ s)) at natural
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (restriction.hom.app
        ((programSection R equations).obj (pairBase equations Γ s)) ≫
          (N.programModel.pairComponentsIso Γ s).hom))
      (extension_pair_cancel L Γ s)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ (N.programModel.pairComponentsIso Γ s).hom) natural).trans
            ((Category.assoc _ _ _).trans
              ((congrArg (restriction.hom.app (eventObject R equations Γ s) ≫ ·)
                ((congrArg (· ≫ (N.programModel.pairComponentsIso Γ s).hom)
                  (N.map_toProgram (eventObject R equations Γ s))).trans
                    (model_projection_endpoints N Γ s))).trans
                      (Category.assoc _ _ _).symm)))))

variable [HasEqualizers D]
variable [HasImage (L.map (genericEndpointMap R equations Γ s))]
variable [HasImage (N.toEventModel.eventEndpoints Γ s)]

/-- The image of the transported endpoint arrow is the image of the
model's existing endpoint arrow, after the actual carrier comparisons. -/
def interpretationEndpointImageIso :
    image (L.map (genericEndpointMap R equations Γ s) ≫
      (interpretationPairIso N L restriction Γ s).hom) ≅
        image (N.toEventModel.eventEndpoints Γ s) :=
  image.eqToIso (interpretation_endpoint N L restriction Γ s) ≪≫
    asIso (image.preComp (interpretationEventIso N L restriction Γ s).hom
      (N.toEventModel.eventEndpoints Γ s))

/-- The codomain comparison also identifies the image before changing its
program-pair coordinates. -/
def interpretationOriginalEndpointImageIso :
    image (L.map (genericEndpointMap R equations Γ s)) ≅
      image (N.toEventModel.eventEndpoints Γ s) :=
  image.compIso (L.map (genericEndpointMap R equations Γ s))
    (interpretationPairIso N L restriction Γ s).hom ≪≫
      interpretationEndpointImageIso N L restriction Γ s

theorem interpretationEndpointImageIso_ι :
    (interpretationEndpointImageIso N L restriction Γ s).hom ≫
        image.ι (N.toEventModel.eventEndpoints Γ s) =
      image.ι (L.map (genericEndpointMap R equations Γ s) ≫
        (interpretationPairIso N L restriction Γ s).hom) := by
  change ((image.eqToIso (interpretation_endpoint N L restriction Γ s)).hom ≫
      image.preComp (interpretationEventIso N L restriction Γ s).hom
        (N.toEventModel.eventEndpoints Γ s)) ≫ image.ι _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg ((image.eqToIso (interpretation_endpoint N L restriction Γ s)).hom ≫ ·)
      (image.preComp_ι (interpretationEventIso N L restriction Γ s).hom
        (N.toEventModel.eventEndpoints Γ s))).trans
          (image.eq_fac (interpretation_endpoint N L restriction Γ s)).symm)

variable [PreservesColimitsOfShape WalkingParallelPair L]

/-- The transported generic reduction covers the actual semantic endpoint
image, even when the transported generic inclusion is not mono. -/
def interpretationReductionComparison :
    L.obj (genericReduction R equations Γ s).toFunctor ⟶
      image (N.toEventModel.eventEndpoints Γ s) :=
  PresheafEventImageComparison.transportedImageComparisonPostIso
    (genericEndpointMap R equations Γ s) L (interpretationPairIso N L restriction Γ s) ≫
      (interpretationEndpointImageIso N L restriction Γ s).hom

theorem interpretationReductionComparison_ι :
    interpretationReductionComparison N L restriction Γ s ≫
        image.ι (N.toEventModel.eventEndpoints Γ s) =
      L.map (genericReduction R equations Γ s).ι ≫
        (interpretationPairIso N L restriction Γ s).hom := by
  rw [interpretationReductionComparison, Category.assoc, interpretationEndpointImageIso_ι]
  exact PresheafEventImageComparison.transportedImageComparisonPostIso_ι
    (genericEndpointMap R equations Γ s) L (interpretationPairIso N L restriction Γ s)

theorem interpretationReductionComparison_events :
    L.map (Subfunctor.toRange (genericEndpointMap R equations Γ s)) ≫
        interpretationReductionComparison N L restriction Γ s =
      (interpretationEventIso N L restriction Γ s).hom ≫
        factorThruImage (N.toEventModel.eventEndpoints Γ s) := by
  have factor : L.map (Subfunctor.toRange (genericEndpointMap R equations Γ s)) ≫
      L.map (genericReduction R equations Γ s).ι =
        L.map (genericEndpointMap R equations Γ s) :=
    (L.map_comp _ _).symm.trans
      (congrArg L.map (Subfunctor.toRange_ι (genericEndpointMap R equations Γ s)))
  apply (cancel_mono (image.ι (N.toEventModel.eventEndpoints Γ s))).1
  exact (Category.assoc _ _ _).trans
    ((congrArg (L.map (Subfunctor.toRange (genericEndpointMap R equations Γ s)) ≫ ·)
      (interpretationReductionComparison_ι N L restriction Γ s)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ (interpretationPairIso N L restriction Γ s).hom) factor).trans
            ((interpretation_endpoint N L restriction Γ s).trans
              ((congrArg ((interpretationEventIso N L restriction Γ s).hom ≫ ·)
                (image.fac (N.toEventModel.eventEndpoints Γ s)).symm).trans
                  (Category.assoc _ _ _).symm)))))

theorem interpretationReductionComparison_epi :
    Epi (interpretationReductionComparison N L restriction Γ s) := by
  let := PresheafEventImageComparison.transportedImageComparisonPostIso_epi
    (genericEndpointMap R equations Γ s) L (interpretationPairIso N L restriction Γ s)
  exact epi_comp _ _

/-- Identification requires preservation of the relevant reduction
inclusion, rather than following from cocontinuity alone. -/
theorem interpretationReductionComparison_isIso
    [mono : Mono (L.map (genericReduction R equations Γ s).ι)] :
    IsIso (interpretationReductionComparison N L restriction Γ s) := by
  let : Mono (L.map (Subfunctor.range (genericEndpointMap R equations Γ s)).ι) := mono
  let := PresheafEventImageComparison.transportedImageComparisonPostIso_isIso
    (genericEndpointMap R equations Γ s) L (interpretationPairIso N L restriction Γ s)
  change IsIso (_ ≫ (interpretationEndpointImageIso N L restriction Γ s).hom)
  infer_instance

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf

end
