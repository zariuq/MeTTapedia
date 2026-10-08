import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationBaseExtension
import Mettapedia.CategoryTheory.RelativeClosedSyntaxBaseExtensionCoherent
import Mettapedia.CategoryTheory.RelativeClosedSyntaxBaseExtensionModels
import Mettapedia.GSLT.Core.RelativeClosedWeakBaseControls
import Mettapedia.GSLT.Core.LambdaTheoryStructuredControls

/-!
# Nonidentity weak-base translation controls

The actual constant-top map on the Boolean order is finite-limit closed.
Fresh Boolean data and both independent arrow declarations are retained.
Its augmented generated map is then interpreted by the independent varying
truth-fibre model. The false base scope becomes inhabited under the supplied
map, while the target's original false scope remains empty. Complete
negation values remain distinct after the coherent original-diagram reading.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedSyntaxTranslationBaseControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.SemilatticeInf
open scoped Mettapedia.CategoryTheory.PredicateDoctrine.HeytingClosed
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open GeneratedCategory Interpretation
open RelativeClosedWeakBaseControls

abbrev weakBase := LambdaTheoryStructuredControls.topFunctor

def headers : HeaderFormation signature where
  source _ := .objectName (signature := signature) ()
  target _ := .objectName (signature := signature) ()
  left origin := origin.elim
  right origin := origin.elim

def translation : Translation signature signature where
  data := ⟨weakBase, ObjectCode.name, ArrowCode.name⟩
  objectTyped origin := .objectName (signature := signature) origin
  arrowTyped origin := .arrowName (signature := signature) origin
    (.objectName (signature := signature) ()) (.objectName (signature := signature) ())
  equationTyped origin := origin.elim

private instance translation_base_lex : PreservesFiniteLimits translation.data.base := by
  change PreservesFiniteLimits weakBase
  infer_instance

private instance translation_base_closed : MonoidalClosedFunctor translation.data.base := by
  change MonoidalClosedFunctor weakBase
  infer_instance

def augmentation : Object augmented ⥤ Object augmented :=
  Translation.BaseExtended.augmentation translation headers

instance augmentation_lex : PreservesFiniteLimits augmentation :=
  Translation.BaseExtended.augmentation_lex translation headers

instance augmentation_closed : MonoidalClosedFunctor augmentation :=
  Translation.BaseExtended.augmentation_closed translation headers

def diagram : Object augmented ⥤ Type := augmentation ⋙ completeInterpretation

theorem complete_base : baseFunctor augmented ⋙ diagram = weakBase ⋙ truthFunctor :=
  (congrArg (fun mapping : Bool ⥤ Object augmented => mapping ⋙ completeInterpretation)
    (Translation.BaseExtended.base_readback translation headers)).trans
      (congrArg (fun mapping : Bool ⥤ Type => weakBase ⋙ mapping) complete_weak_base)

theorem mapped_false_scope_inhabited : Nonempty (diagram.obj (baseObject augmented false)) := by
  have same : diagram.obj (baseObject augmented false) = truthFunctor.obj true :=
    congrArg (fun mapping : Bool ⥤ Type => mapping.obj false) complete_base
  exact ⟨same.symm ▸ trueValue⟩

theorem ignoring_weak_base_rejected :
    diagram.obj (baseObject augmented false) ≠ completeInterpretation.obj (baseObject augmented false) := by
  intro same
  obtain ⟨value⟩ := mapped_false_scope_inhabited
  exact old_false_scope_remains_empty.false (same ▸ value)

abbrev oldData : Object signature :=
  ⟨.name (), ⟨.objectName (signature := signature) ()⟩⟩

def oldNegation : RawHom oldData oldData :=
  ⟨.name true, ⟨.arrowName (signature := signature) true
    (.objectName (signature := signature) ()) (.objectName (signature := signature) ())⟩⟩

def originalComparison :
    (BaseExtension.originalMap signature).functor ⋙ diagram ≅
      translation.functor ⋙ Interpretation.functor meanings realized :=
  Functor.isoWhiskerRight
    (Translation.BaseExtended.originalComparison translation headers) completeInterpretation ≪≫
      eqToIso (congrArg (fun following : Object signature ⥤ Type => translation.functor ⋙ following)
        complete_original_diagram)

def suppliedObjectComparison : diagram.obj dataObject ≅ ULift.{0} Bool :=
  originalComparison.app oldData

def transportedNegation : ULift.{0} Bool ⟶ ULift.{0} Bool :=
  suppliedObjectComparison.inv ≫ diagram.map (classOf originalNegation) ≫ suppliedObjectComparison.hom

theorem transportedNegation_complete : transportedNegation = negate := by
  have mapped : (translation.functor ⋙ Interpretation.functor meanings realized).map
      (classOf oldNegation) = negate :=
    rawArrowValue_unique meanings realized (translation.rawArrow oldNegation) negate rfl
  have natural := originalComparison.hom.naturality (classOf oldNegation)
  rw [mapped] at natural
  change diagram.map (classOf originalNegation) ≫ suppliedObjectComparison.hom =
    suppliedObjectComparison.hom ≫ negate at natural
  have read := congrArg (fun value => suppliedObjectComparison.inv ≫ value) natural
  simpa only [transportedNegation, Category.assoc, Iso.inv_hom_id_assoc] using read

theorem both_supplied_values_retained :
    (transportedNegation (ULift.up false)).down = true ∧
      (transportedNegation (ULift.up true)).down = false := by
  rw [transportedNegation_complete]
  exact ⟨rfl, rfl⟩

theorem replacing_complete_data_rejected :
    transportedNegation (ULift.up false) ≠ transportedNegation (ULift.up true) := by
  intro same
  have read := congrArg ULift.down same
  rw [both_supplied_values_retained.1, both_supplied_values_retained.2] at read
  exact Bool.false_ne_true read.symm

def independentAugmentedModel : SemanticModels.Model augmented Type := ⟨extended, extended_realized⟩

theorem complete_model_recovered :
    BaseExtension.Models.extendModel (BaseExtension.Models.restrict independentAugmentedModel) =
      independentAugmentedModel :=
  BaseExtension.Models.augmented_model_recovered independentAugmentedModel

theorem recovered_negation_readout :
    (BaseExtension.Models.extendModel (BaseExtension.Models.restrict independentAugmentedModel)).meanings.evaluateArrow
      (BaseExtension.originalArrowCode (C := Bool) (symbols := names) (.name true)) =
        some (⟨ULift Bool, ULift Bool, negate⟩ : ArrowValue Type) := by
  rw [complete_model_recovered]
  exact supplied_negation_read

def canonicalImages := CanonicalExtension.images extended extended_realized

private instance complete_interpretation_lex : PreservesFiniteLimits completeInterpretation := by
  change PreservesFiniteLimits (Interpretation.functor extended extended_realized)
  infer_instance

private instance complete_interpretation_closed : MonoidalClosedFunctor completeInterpretation := by
  change MonoidalClosedFunctor (Interpretation.functor extended extended_realized)
  infer_instance

theorem oldDeclarationReadings : BaseExtension.Coherent.OldArrowImages meanings headers
    completeInterpretation canonicalImages where
  arrow origin := (CanonicalExtension.arrow_images extended extended_realized
    (BaseExtension.headers signature headers)).arrow (BaseExtension.originalArrows origin)

@[instance_reducible] def complete_admitted_cell_unique : Unique
    (BaseExtension.Coherent.AdmittedCell meanings realized completeInterpretation canonicalImages) :=
  BaseExtension.Coherent.admittedCellUnique meanings realized headers completeInterpretation canonicalImages
    oldDeclarationReadings

end Mettapedia.GSLT.Core.RelativeClosedSyntaxTranslationBaseControls
