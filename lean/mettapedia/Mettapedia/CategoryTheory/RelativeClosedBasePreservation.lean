import Mettapedia.CategoryTheory.RelativeClosedBaseComparison
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# Finite-limit base preservation derived from local comparison diagrams

The authored comparison equations earn the complete equalizer inclusion
square. Transporting the independently proved target limit through that
isomorphism proves preservation of the actual source equalizer. Terminal and
product preservation then give genuine finite-limit preservation.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseComparisons

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open GeneratedCategory

universe u v

variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]

def mappedEqualizerIsLimit {source target : C} (before after : source ⟶ target) :
    IsLimit (Fork.ofι ((base (C := C)).map (equalizer.ι before after))
      (by simp only [← (base (C := C)).map_comp]; rw [equalizer.condition]) :
        Fork ((base (C := C)).map before) ((base (C := C)).map after)) := by
  let chosen := equalizerIsLimit ((base (C := C)).map before) ((base (C := C)).map after)
  apply chosen.ofIsoLimit
  refine Fork.ext (completeEqualizerComparison before after).symm ?_
  change (completeEqualizerComparison before after).inv ≫
      (base (C := C)).map (equalizer.ι before after) =
    equalizerInclusion ((base (C := C)).map before) ((base (C := C)).map after)
  exact (congrArg
    (fun incoming => (completeEqualizerComparison before after).inv ≫ incoming)
    (completeEqualizerComparison_inclusion before after).symm).trans
      ((completeEqualizerComparison before after).inv_hom_id_assoc _)

instance base_preservesEqualizer {source target : C} (before after : source ⟶ target) :
    PreservesLimit (parallelPair before after) (base (C := C)) :=
  preservesLimit_of_preserves_limit_cone (equalizerIsEqualizer before after)
    ((isLimitMapConeForkEquiv (base (C := C)) (equalizer.condition before after)).symm
      (mappedEqualizerIsLimit before after))

instance base_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair (base (C := C)) where
  preservesLimit {diagram} := by
    exact preservesLimit_of_iso_diagram (base (C := C)) (diagramIsoParallelPair diagram).symm

instance base_preservesFiniteLimits : PreservesFiniteLimits (base (C := C)) :=
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts (base (C := C))

def canonicalExponentialComparison (argument result : C) :
    (base (C := C)).obj (argument ⟶[C] result) ⟶
      exponentialObject ((base (C := C)).obj argument) ((base (C := C)).obj result) :=
  GeneratedCategory.abstraction
    ((comparison (.product (argument ⟶[C] result) argument)).inv ≫
      (base (C := C)).map (Interpretation.evaluation argument result))

theorem canonicalExponentialComparison_eq (argument result : C) :
    canonicalExponentialComparison argument result = (comparison (.exponential argument result)).hom := rfl

instance canonicalExponentialComparison_isIso (argument result : C) :
    IsIso (canonicalExponentialComparison argument result) := by
  rw [canonicalExponentialComparison_eq]
  exact (comparison (.exponential argument result)).isIso_hom

theorem canonicalExponentialComparison_evaluation (argument result : C) :
    pairing
        (GeneratedCategory.first ((base (C := C)).obj (argument ⟶[C] result))
          ((base (C := C)).obj argument) ≫ canonicalExponentialComparison argument result)
        (GeneratedCategory.second ((base (C := C)).obj (argument ⟶[C] result))
          ((base (C := C)).obj argument)) ≫
      GeneratedCategory.evaluation ((base (C := C)).obj argument) ((base (C := C)).obj result) =
        (comparison (.product (argument ⟶[C] result) argument)).inv ≫
          (base (C := C)).map (Interpretation.evaluation argument result) :=
  unabstract_abstraction _

end Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseComparisons
