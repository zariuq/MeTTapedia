import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationModels
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorModelEquivalence
import Mettapedia.CategoryTheory.RelativeClosedSyntaxBaseExtensionWeakInterpretation

/-!
# Weak native base extension of a complete expression translation

The independently reconstructed target inclusion gives a locally realized
model of the old target presentation inside its actual base-comparison
extension. A complete source translation restricts this model. The actual
weak closed base map then supplies the four native inverse comparisons,
whose local equations have already been proved independently.

This constructs a genuine finite-limit closed map between the two augmented
generated categories, with full old-diagram and base comparisons. Chosen raw
equalizer presentations are retained; their equality is never presumed.
The modal layer and its free-forgetful universal construction are separate.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation.BaseExtended

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory Interpretation SemanticModels

universe k

variable {C D : Type k} [Category.{k} C] [Category.{k} D]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable {symbols nextSymbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {next : Signature (C := D) (symbols := nextSymbols)}
variable (mapping : Translation signature next) (headers : HeaderFormation next)

abbrev targetDiagram : ClosedModels.Diagram next (Object (BaseExtension.extend next)) :=
  ⟨(BaseExtension.originalMap next).functor, inferInstance, inferInstance⟩

def targetModel : Model next (Object (BaseExtension.extend next)) :=
  FunctorModelEquivalence.extracted headers (targetDiagram (next := next))

theorem target_base : (targetModel headers).meanings.base =
    baseFunctor (BaseExtension.extend next) :=
  BaseExtension.original_base_recovery next

private instance target_base_lex : PreservesFiniteLimits (targetModel headers).meanings.base := by
  rw [target_base headers]
  infer_instance

private instance target_base_closed : MonoidalClosedFunctor (targetModel headers).meanings.base :=
  CartesianClosedFunctorCoherence.closed_of_naturalIso (eqToIso (target_base headers))

def targetComparison : (targetModel headers).diagram ≅ (BaseExtension.originalMap next).functor :=
  (FunctorModelEquivalence.comparison headers (targetDiagram (next := next))).symm

def sourceModel : Model signature (Object (BaseExtension.extend next)) :=
  mapping.precomposeModel (targetModel headers)

omit [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C] in
theorem source_base : (sourceModel mapping headers).meanings.base =
    mapping.data.base ⋙ baseFunctor (BaseExtension.extend next) :=
  congrArg (fun following => mapping.data.base ⋙ following) (target_base headers)

variable [PreservesFiniteLimits mapping.data.base] [MonoidalClosedFunctor mapping.data.base]

private instance source_base_lex :
    PreservesFiniteLimits (sourceModel mapping headers).meanings.base := by
  change PreservesFiniteLimits (mapping.data.base ⋙ (targetModel headers).meanings.base)
  exact comp_preservesFiniteLimits _ _

private instance source_base_closed :
    MonoidalClosedFunctor (sourceModel mapping headers).meanings.base := by
  change MonoidalClosedFunctor (mapping.data.base ⋙ (targetModel headers).meanings.base)
  exact CartesianClosedFunctorCoherence.closed_composition _ _

def augmentedModel : Model (BaseExtension.extend signature) (Object (BaseExtension.extend next)) :=
  ⟨BaseExtension.WeakExtension.assignment (sourceModel mapping headers).meanings,
    BaseExtension.WeakExtension.realization (sourceModel mapping headers).meanings
      (sourceModel mapping headers).realization⟩

def augmentation : Object (BaseExtension.extend signature) ⥤ Object (BaseExtension.extend next) :=
  (augmentedModel mapping headers).diagram

instance augmentation_lex : PreservesFiniteLimits (augmentation mapping headers) := by
  change PreservesFiniteLimits (augmentedModel mapping headers).diagram
  infer_instance

instance augmentation_closed : MonoidalClosedFunctor (augmentation mapping headers) := by
  change MonoidalClosedFunctor (augmentedModel mapping headers).diagram
  infer_instance

theorem original_readback :
    (BaseExtension.originalMap signature).functor ⋙ augmentation mapping headers =
      (sourceModel mapping headers).diagram :=
  BaseExtension.WeakExtension.original_diagram_readback (sourceModel mapping headers).meanings
    (sourceModel mapping headers).realization

def originalComparison :
    (BaseExtension.originalMap signature).functor ⋙ augmentation mapping headers ≅
      mapping.functor ⋙ (BaseExtension.originalMap next).functor :=
  eqToIso (original_readback mapping headers) ≪≫
    (mapping.precomposeComparison (targetModel headers)).symm ≪≫
      Functor.isoWhiskerLeft mapping.functor (targetComparison headers)

theorem base_readback : baseFunctor (BaseExtension.extend signature) ⋙ augmentation mapping headers =
    mapping.data.base ⋙ baseFunctor (BaseExtension.extend next) :=
  (Interpretation.functor_base (augmentedModel mapping headers).meanings
    (augmentedModel mapping headers).realization).trans (source_base mapping headers)

def baseComparison : baseFunctor (BaseExtension.extend signature) ⋙ augmentation mapping headers ≅
    mapping.data.base ⋙ baseFunctor (BaseExtension.extend next) :=
  eqToIso (base_readback mapping headers)

theorem complete_original_arrow {source target : Object signature} (input : source ⟶ target) :
    (augmentation mapping headers).map ((BaseExtension.originalMap signature).functor.map input) =
      (originalComparison mapping headers).hom.app source ≫
        (BaseExtension.originalMap next).functor.map (mapping.functor.map input) ≫
          (originalComparison mapping headers).inv.app target := by
  have natural := (originalComparison mapping headers).hom.naturality input
  change (augmentation mapping headers).map ((BaseExtension.originalMap signature).functor.map input) ≫
      (originalComparison mapping headers).hom.app target =
    (originalComparison mapping headers).hom.app source ≫
      (BaseExtension.originalMap next).functor.map (mapping.functor.map input) at natural
  have complete := congrArg (fun value => value ≫ (originalComparison mapping headers).inv.app target) natural
  simpa only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id] using complete

end Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation.BaseExtended
