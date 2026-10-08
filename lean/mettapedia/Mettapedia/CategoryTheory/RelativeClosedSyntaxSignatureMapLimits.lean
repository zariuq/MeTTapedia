import Mettapedia.CategoryTheory.RelativeClosedSyntaxSignatureMap
import Mettapedia.CategoryTheory.RelativeClosedSyntaxClosed
import Mettapedia.CategoryTheory.RelativeClosedSyntaxPresentedEqualizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# Finite-limit preservation of the generated presentation functor

The forty-rule transport retains the actual formal terminal and product
objects and arrows. For equalizers it retains the mapped authored defining
arrows; their independently proved presented equalizer has the full target
universal property. Selected quotient representatives therefore need not
coincide. These facts earn finite-limit preservation for every declaration-
local presentation map, including independently sized base categories.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.SignatureMap

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open GeneratedCategory

universe u v a w z b

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {D : Type w} [Category.{z} D] {nextSymbols : Symbols.{b}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {next : Signature (C := D) (symbols := nextSymbols)}
variable (mapping : SignatureMap signature next)

theorem terminalComparison_identity :
    CartesianMonoidalCategory.terminalComparison mapping.functor = 𝟙 (terminal next) :=
  (terminalIsTerminal next).hom_ext _ _

instance terminalComparison_isIso :
    IsIso (CartesianMonoidalCategory.terminalComparison mapping.functor) := by
  rw [mapping.terminalComparison_identity]
  exact (inferInstance : IsIso (𝟙 (terminal next) : terminal next ⟶ terminal next))

instance functor_preservesTerminal :
    PreservesLimit (Functor.empty.{0} (Object signature)) mapping.functor :=
  CartesianMonoidalCategory.preservesLimit_empty_of_isIso_terminalComparison mapping.functor

theorem productComparison_identity (left right : Object signature) :
    CartesianMonoidalCategory.prodComparison mapping.functor left right =
      𝟙 (product (mapping.functor.obj left) (mapping.functor.obj right)) := by
  apply CartesianMonoidalCategory.hom_ext
  · have read : mapping.functor.map (CartesianMonoidalCategory.fst left right) =
        CartesianMonoidalCategory.fst (mapping.functor.obj left) (mapping.functor.obj right) := rfl
    exact (CartesianMonoidalCategory.prodComparison_fst mapping.functor left right).trans
      (read.trans (Category.id_comp
        (first (mapping.functor.obj left) (mapping.functor.obj right))).symm)
  · have read : mapping.functor.map (CartesianMonoidalCategory.snd left right) =
        CartesianMonoidalCategory.snd (mapping.functor.obj left) (mapping.functor.obj right) := rfl
    exact (CartesianMonoidalCategory.prodComparison_snd mapping.functor left right).trans
      (read.trans (Category.id_comp
        (second (mapping.functor.obj left) (mapping.functor.obj right))).symm)

instance productComparison_isIso (left right : Object signature) :
    IsIso (CartesianMonoidalCategory.prodComparison mapping.functor left right) := by
  rw [mapping.productComparison_identity]
  exact (inferInstance : IsIso
    (𝟙 (product (mapping.functor.obj left) (mapping.functor.obj right)) :
      product (mapping.functor.obj left) (mapping.functor.obj right) ⟶
        product (mapping.functor.obj left) (mapping.functor.obj right)))

instance functor_preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) mapping.functor :=
  CartesianMonoidalCategory.preservesLimitsOfShape_discrete_walkingPair_of_isIso_prodComparison
    mapping.functor

instance functor_preservesEmpty : PreservesLimitsOfShape (Discrete PEmpty.{1}) mapping.functor :=
  preservesLimitsOfShape_pempty_of_preservesTerminal mapping.functor

instance functor_preservesFiniteProducts : PreservesFiniteProducts mapping.functor :=
  PreservesFiniteProducts.of_preserves_binary_and_terminal mapping.functor

theorem mapped_representative {source target : Object signature} (value : source ⟶ target) :
    classOf (mapping.rawArrow (representative value)) = mapping.functor.map value :=
  (mapping.functor_classOf (representative value)).symm.trans
    (congrArg mapping.functor.map (classOf_representative value))

theorem functor_equalizerInclusion {source target : Object signature} (before after : source ⟶ target) :
    mapping.functor.map (equalizerInclusion before after) =
      PresentedEqualizer.inclusion (mapping.rawArrow (representative before))
        (mapping.rawArrow (representative after)) := rfl

def mappedEqualizerIsLimit {source target : Object signature} (before after : source ⟶ target) :
    IsLimit (Fork.ofι (mapping.functor.map (equalizerInclusion before after))
      (by simp only [← mapping.functor.map_comp]; rw [equalizer_condition]) :
        Fork (mapping.functor.map before) (mapping.functor.map after)) := by
  let first := mapping.rawArrow (representative before)
  let second := mapping.rawArrow (representative after)
  have condition (cone : Fork (mapping.functor.map before) (mapping.functor.map after)) :
      cone.ι ≫ classOf first = cone.ι ≫ classOf second :=
    (congrArg (cone.ι ≫ ·) (mapping.mapped_representative before)).trans
      (cone.condition.trans (congrArg (cone.ι ≫ ·) (mapping.mapped_representative after).symm))
  refine Fork.IsLimit.mk _
    (fun cone => PresentedEqualizer.lift first second cone.ι (condition cone)) ?_ ?_
  · intro cone
    exact (congrArg (PresentedEqualizer.lift first second cone.ι (condition cone) ≫ ·)
      (mapping.functor_equalizerInclusion before after)).trans
        (PresentedEqualizer.lift_inclusion first second cone.ι (condition cone))
  · intro cone candidate factors
    apply PresentedEqualizer.joint_cancel first second
    exact (congrArg (candidate ≫ ·) (mapping.functor_equalizerInclusion before after).symm).trans
      (factors.trans (PresentedEqualizer.lift_inclusion first second cone.ι (condition cone)).symm)

instance functor_preservesEqualizer {source target : Object signature} (before after : source ⟶ target) :
    PreservesLimit (parallelPair before after) mapping.functor :=
  preservesLimit_of_preserves_limit_cone (equalizerIsLimit before after)
    ((isLimitMapConeForkEquiv mapping.functor (equalizer_condition before after)).symm
      (mapping.mappedEqualizerIsLimit before after))

instance functor_preservesEqualizers : PreservesLimitsOfShape WalkingParallelPair mapping.functor where
  preservesLimit {diagram} := by
    exact preservesLimit_of_iso_diagram mapping.functor (diagramIsoParallelPair diagram).symm

instance functor_preservesFiniteLimits : PreservesFiniteLimits mapping.functor :=
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts mapping.functor

end Mettapedia.CategoryTheory.RelativeClosedSyntax.SignatureMap
