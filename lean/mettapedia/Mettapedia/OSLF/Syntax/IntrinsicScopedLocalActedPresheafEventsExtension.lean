import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedPresheafEventsInterpretation
import Mettapedia.OSLF.Syntax.PresheafStructuredExtensionCore

/-!
# Endpoint images in the actual left Kan extension

The canonical extension uses the original model's classifying functor.
Its restriction comparison is the actual Kan unit, and its preservation of
density colimits supplies the coequalizer preservation used by the reduction
comparison. These constructions do not require a structured Yoneda model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

universe w u v

variable {S : Signature} {R : List (LocalRule S)}
variable {schema : List (MetaArity S)} {equations : List (EqAxiom S schema)}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D] [HasPullbacks D]
variable [HasColimitsOfSize.{0, max w v} D]
variable (N : CategoricalModel R equations (D := D))

/-- The actual left Kan extension of the existing classifying carrier. -/
abbrev modelPresheafExtension : Presheaf.{max w v} R equations ⥤ D :=
  (embedding.{max w v} R equations).lan.obj N.classifyingFunctor

/-- The comparison is constructed by the invertible Kan unit. -/
def modelPresheafExtensionRestriction :
    embedding.{max w v} R equations ⋙ modelPresheafExtension.{w} N ≅ N.classifyingFunctor :=
  ((Mettapedia.CategoryTheory.PresheafStructuredExtension.unitIso.{w, 0, 0, v, u}).app
    N.classifyingFunctor).symm

theorem modelPresheafExtension_cocontinuous :
    PreservesColimitsOfSize.{0, max w v} (modelPresheafExtension.{w} N) :=
  Mettapedia.CategoryTheory.PresheafStructuredExtension.extension_cocontinuous N.classifyingFunctor

variable (Γ : Ctx S) (s : S.Srt)
variable [HasEqualizers D] [HasImages D]

/-- The canonical extension sends the generic reduction onto the model's
actual endpoint image. Its inclusion need not remain mono. -/
def extensionReductionComparison :
    (modelPresheafExtension.{w} N).obj
        (genericReduction.{max w v} R equations Γ s).toFunctor ⟶
      image (N.toEventModel.eventEndpoints Γ s) := by
  let := modelPresheafExtension_cocontinuous.{w} N
  let : PreservesColimitsOfSize.{0, 0} (modelPresheafExtension.{w} N) :=
    preservesColimitsOfSize_shrink (modelPresheafExtension.{w} N)
  exact interpretationReductionComparison N (modelPresheafExtension N)
    (modelPresheafExtensionRestriction N) Γ s

theorem extensionReductionComparison_epi :
    Epi (extensionReductionComparison.{w} N Γ s) := by
  let := modelPresheafExtension_cocontinuous.{w} N
  let : PreservesColimitsOfSize.{0, 0} (modelPresheafExtension.{w} N) :=
    preservesColimitsOfSize_shrink (modelPresheafExtension.{w} N)
  exact interpretationReductionComparison_epi N (modelPresheafExtension N)
    (modelPresheafExtensionRestriction N) Γ s

theorem extensionReductionComparison_ι :
    extensionReductionComparison.{w} N Γ s ≫ image.ι (N.toEventModel.eventEndpoints Γ s) =
      (modelPresheafExtension.{w} N).map (genericReduction.{max w v} R equations Γ s).ι ≫
        (interpretationPairIso N (modelPresheafExtension N)
          (modelPresheafExtensionRestriction N) Γ s).hom := by
  let := modelPresheafExtension_cocontinuous.{w} N
  let : PreservesColimitsOfSize.{0, 0} (modelPresheafExtension.{w} N) :=
    preservesColimitsOfSize_shrink (modelPresheafExtension.{w} N)
  exact interpretationReductionComparison_ι N (modelPresheafExtension N)
    (modelPresheafExtensionRestriction N) Γ s

theorem extensionReductionComparison_events :
    (modelPresheafExtension.{w} N).map
        (Subfunctor.toRange (genericEndpointMap.{max w v} R equations Γ s)) ≫
      extensionReductionComparison N Γ s =
        (interpretationEventIso N (modelPresheafExtension N)
          (modelPresheafExtensionRestriction N) Γ s).hom ≫
          factorThruImage (N.toEventModel.eventEndpoints Γ s) := by
  let := modelPresheafExtension_cocontinuous.{w} N
  let : PreservesColimitsOfSize.{0, 0} (modelPresheafExtension.{w} N) :=
    preservesColimitsOfSize_shrink (modelPresheafExtension.{w} N)
  exact interpretationReductionComparison_events N (modelPresheafExtension N)
    (modelPresheafExtensionRestriction N) Γ s

theorem extensionReductionComparison_isIso
    [Mono ((modelPresheafExtension.{w} N).map
      (genericReduction.{max w v} R equations Γ s).ι)] :
    IsIso (extensionReductionComparison.{w} N Γ s) := by
  let := modelPresheafExtension_cocontinuous.{w} N
  let : PreservesColimitsOfSize.{0, 0} (modelPresheafExtension.{w} N) :=
    preservesColimitsOfSize_shrink (modelPresheafExtension.{w} N)
  exact interpretationReductionComparison_isIso N (modelPresheafExtension N)
    (modelPresheafExtensionRestriction N) Γ s

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf

end
