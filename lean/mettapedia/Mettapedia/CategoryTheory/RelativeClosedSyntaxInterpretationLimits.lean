import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretationReadout
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# Finite-limit preservation of the independent interpretation

The canonical terminal and product comparisons are the earned object
comparison arrows. Equalizer lifting in the target gives a full universal
cone for the mapped source equalizer, with both defining quotient arrows
retained. Finite-limit preservation follows for every locally realized
assignment; it is not a model field.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open GeneratedCategory

universe u v a w z

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (assignment : Assignment C symbols D) (realization : Realization signature assignment)

theorem functor_terminalComparison :
    CartesianMonoidalCategory.terminalComparison (functor assignment realization) =
      eqToHom (functor_terminal_object assignment realization) := by
  change CartesianMonoidalCategory.toUnit (𝟙_ D) = 𝟙 (𝟙_ D)
  exact CartesianMonoidalCategory.toUnit_unit

instance functor_terminalComparison_isIso :
    IsIso (CartesianMonoidalCategory.terminalComparison (functor assignment realization)) := by
  rw [functor_terminalComparison]
  infer_instance

instance functor_preservesTerminal :
    PreservesLimit (Functor.empty.{0} (Object signature)) (functor assignment realization) :=
  CartesianMonoidalCategory.preservesLimit_empty_of_isIso_terminalComparison _

theorem functor_productComparison (left right : Object signature) :
    CartesianMonoidalCategory.prodComparison (functor assignment realization) left right =
      eqToHom (functor_product_object assignment realization left right) := by
  apply CartesianMonoidalCategory.hom_ext
  · exact (CartesianMonoidalCategory.prodComparison_fst (functor assignment realization) left right).trans
      (functor_first assignment realization left right)
  · exact (CartesianMonoidalCategory.prodComparison_snd (functor assignment realization) left right).trans
      (functor_second assignment realization left right)

instance functor_productComparison_isIso (left right : Object signature) :
    IsIso (CartesianMonoidalCategory.prodComparison (functor assignment realization) left right) := by
  rw [functor_productComparison]
  infer_instance

instance functor_preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) (functor assignment realization) :=
  CartesianMonoidalCategory.preservesLimitsOfShape_discrete_walkingPair_of_isIso_prodComparison _

instance functor_preservesEmpty :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (functor assignment realization) :=
  preservesLimitsOfShape_pempty_of_preservesTerminal _

instance functor_preservesFiniteProducts : PreservesFiniteProducts (functor assignment realization) :=
  PreservesFiniteProducts.of_preserves_binary_and_terminal _

def functor_mappedEqualizerIsLimit {source target : Object signature} (before after : source ⟶ target) :
    IsLimit (Fork.ofι ((functor assignment realization).map (equalizerInclusion before after))
      (by simp only [← Functor.map_comp]; rw [equalizer_condition]) :
        Fork ((functor assignment realization).map before) ((functor assignment realization).map after)) := by
  let same := functor_equalizer_object assignment realization before after
  refine Fork.IsLimit.mk _
    (fun cone => equalizer.lift cone.ι cone.condition ≫ eqToHom same.symm) ?_ ?_
  · intro cone
    change (equalizer.lift cone.ι cone.condition ≫ eqToHom same.symm) ≫
      (functor assignment realization).map (equalizerInclusion before after) = cone.ι
    rw [functor_equalizerInclusion]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, equalizer.lift_ι]
  · intro cone candidate factors
    change candidate ≫ (functor assignment realization).map (equalizerInclusion before after) = cone.ι at factors
    apply (cancel_mono (eqToHom same)).mp
    apply equalizer.hom_ext
    have complete : candidate ≫ eqToHom same ≫
        equalizer.ι ((functor assignment realization).map before)
          ((functor assignment realization).map after) = cone.ι :=
      (congrArg (candidate ≫ ·) (functor_equalizerInclusion assignment realization before after)).symm.trans
        factors
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp, equalizer.lift_ι] using complete

instance functor_preservesEqualizer {source target : Object signature} (before after : source ⟶ target) :
    PreservesLimit (parallelPair before after) (functor assignment realization) :=
  preservesLimit_of_preserves_limit_cone (equalizerIsLimit before after)
    ((isLimitMapConeForkEquiv (functor assignment realization) (equalizer_condition before after)).symm
      (functor_mappedEqualizerIsLimit assignment realization before after))

instance functor_preservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair (functor assignment realization) where
  preservesLimit {diagram} :=
    preservesLimit_of_iso_diagram (functor assignment realization) (diagramIsoParallelPair diagram).symm

instance functor_preservesFiniteLimits : PreservesFiniteLimits (functor assignment realization) :=
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts _

end Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation
