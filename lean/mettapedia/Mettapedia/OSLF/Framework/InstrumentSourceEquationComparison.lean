import Mettapedia.OSLF.Framework.InstrumentSourceRelativePushout
import Mettapedia.OSLF.Syntax.SortedConstructorPaddingRelativePushout

/-!
# Source contexts in the independently generated unary-unit quotient

The functor is constructed on actual term and frame-list classes. Its complete
filling readout commutes with source traversal, and its faithfulness follows
from the independently earned term/context normalization roundtrips. The
literal IPO comparison retains every source bound and both actual context
maps, rather than replacing contexts by their ground actions.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentCutContexts

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors
open Mettapedia.OSLF.SortedConstructors.Padding
open Mettapedia.CategoryTheory
open Mettapedia.GSLT.RelativePushout

universe u

variable {Symbols : Type u} (arity : Symbols → Nat)

local instance instrumentSourceEquationComparisonQuiver : Quiver (Srt Symbols arity) := frameQuiver (signature arity)

def sourceEquationObjectImage : SourceObject Symbols arity → EquationObject (signature arity) (.base : Srt Symbols arity)
  | .origin => .origin
  | .base => .interface .base

def sourceEquationArrowImage {source target : SourceObject Symbols arity} (arrow : source ⟶ target) :
    sourceEquationObjectImage arity source ⟶ sourceEquationObjectImage arity target := by
  cases source <;> cases target
  · cases arrow; exact .identity
  · cases arrow with
    | value supplied => exact .value (classOf (embed (signature arity) .base (embedSource arity supplied)))
  · cases arrow
  · cases arrow with
    | context supplied => exact .context (contextClassOf (embedContext (signature arity) .base (sourceContextImage arity supplied)))

theorem sourceEquationArrow_down {source target : SourceObject Symbols arity} (arrow : source ⟶ target) :
    HEq (EquationArrow.down (sourceEquationArrowImage arity arrow)) ((sourceFunctor arity).map arrow) := by
  cases arrow with
  | identity => exact HEq.rfl
  | value supplied => exact heq_of_eq (congrArg GroundPath.Arrow.value (normalize_embed _ _ _))
  | context supplied => exact heq_of_eq (congrArg GroundPath.Arrow.context
      (normalize_embedContext (signature arity) .base (sourceContextImage arity supplied)))

theorem sourceEquationValue_down (supplied : InstrumentObservations.Tree Symbols arity) :
    EquationArrow.down (sourceEquationArrowImage arity (sourceValueArrow arity supplied)) =
      (sourceFunctor arity).map (sourceValueArrow arity supplied) :=
  eq_of_heq (sourceEquationArrow_down arity (sourceValueArrow arity supplied))

theorem sourceEquationContext_down (supplied : SourceContext arity) :
    EquationArrow.down (sourceEquationArrowImage arity (sourceContextArrow arity supplied)) =
      (sourceFunctor arity).map (sourceContextArrow arity supplied) :=
  eq_of_heq (sourceEquationArrow_down arity (sourceContextArrow arity supplied))

def sourceEquationFunctor : SourceObject Symbols arity ⥤ EquationObject (signature arity) (.base : Srt Symbols arity) where
  obj := sourceEquationObjectImage arity
  map := sourceEquationArrowImage arity
  map_id object := by cases object <;> rfl
  map_comp first second := by
    cases first with
    | identity => rfl
    | value supplied =>
      cases second with
      | context suppliedContext =>
        apply EquationArrow.down_injective
        change EquationArrow.down (sourceEquationArrowImage arity
          (sourceValueArrow arity (SourceContext.fill arity suppliedContext supplied))) =
          EquationArrow.down (EquationArrow.comp
            (sourceEquationArrowImage arity (sourceValueArrow arity supplied))
            (sourceEquationArrowImage arity (sourceContextArrow arity suppliedContext)))
        rw [EquationArrow.down_comp, sourceEquationValue_down, sourceEquationValue_down, sourceEquationContext_down]
        exact (sourceFunctor arity).map_comp (sourceValueArrow arity supplied) (sourceContextArrow arity suppliedContext)
    | context first =>
      cases second with
      | context second =>
        apply EquationArrow.down_injective
        change EquationArrow.down (sourceEquationArrowImage arity (sourceContextArrow arity (second ++ first))) =
          EquationArrow.down (EquationArrow.comp
            (sourceEquationArrowImage arity (sourceContextArrow arity first))
            (sourceEquationArrowImage arity (sourceContextArrow arity second)))
        rw [EquationArrow.down_comp, sourceEquationContext_down, sourceEquationContext_down, sourceEquationContext_down]
        exact (sourceFunctor arity).map_comp (sourceContextArrow arity first) (sourceContextArrow arity second)

instance sourceEquationFunctor_faithful : (sourceEquationFunctor arity).Faithful where
  map_injective := by
    intro source target first second same
    cases first with
    | identity => cases second; rfl
    | value supplied =>
      cases second with
      | value other =>
        apply (sourceFunctor arity).map_injective
        exact (sourceEquationValue_down arity supplied).symm.trans
          ((congrArg EquationArrow.down same).trans (sourceEquationValue_down arity other))
    | context supplied =>
      cases second with
      | context other =>
        apply (sourceFunctor arity).map_injective
        exact (sourceEquationContext_down arity supplied).symm.trans
          ((congrArg EquationArrow.down same).trans (sourceEquationContext_down arity other))

theorem sourceEquation_fill_readout (supplied : InstrumentObservations.Tree Symbols arity)
    (context : SourceContext arity) :
    classFill (classOf (embed (signature arity) .base (embedSource arity supplied)))
      (contextClassOf (embedContext (signature arity) .base (sourceContextImage arity context))) =
      classOf (embed (signature arity) .base (embedSource arity (SourceContext.fill arity context supplied))) := by
  have actual := (sourceEquationFunctor arity).map_comp (sourceValueArrow arity supplied) (sourceContextArrow arity context)
  exact (EquationArrow.value.inj actual).symm

set_option backward.isDefEq.respectTransparency false in
theorem sourceEquation_idemPushout_iff
    (first second : InstrumentObservations.Tree Symbols arity) (left right : SourceContext arity)
    (square : sourceValueArrow arity first ≫ sourceContextArrow arity left =
      sourceValueArrow arity second ≫ sourceContextArrow arity right) :
    IsIdemPushout (sourceValueArrow arity first) (sourceValueArrow arity second)
      (sourceContextArrow arity left) (sourceContextArrow arity right) square ↔
      IsIdemPushout ((sourceEquationFunctor arity).map (sourceValueArrow arity first))
        ((sourceEquationFunctor arity).map (sourceValueArrow arity second))
        ((sourceEquationFunctor arity).map (sourceContextArrow arity left))
        ((sourceEquationFunctor arity).map (sourceContextArrow arity right))
        (by rw [← Functor.map_comp, square, Functor.map_comp]) := by
  have quotientComparison := equation_idemPushout_iff (signature arity) .base
    ((sourceEquationFunctor arity).map (sourceValueArrow arity first))
    ((sourceEquationFunctor arity).map (sourceValueArrow arity second))
    ((sourceEquationFunctor arity).map (sourceContextArrow arity left))
    ((sourceEquationFunctor arity).map (sourceContextArrow arity right))
    (by rw [← Functor.map_comp, square, Functor.map_comp])
  change _ ↔ IsIdemPushout
    (EquationArrow.down (sourceEquationArrowImage arity (sourceValueArrow arity first)))
    (EquationArrow.down (sourceEquationArrowImage arity (sourceValueArrow arity second)))
    (EquationArrow.down (sourceEquationArrowImage arity (sourceContextArrow arity left)))
    (EquationArrow.down (sourceEquationArrowImage arity (sourceContextArrow arity right))) _ at quotientComparison
  simp only [sourceEquationValue_down, sourceEquationContext_down] at quotientComparison
  exact (source_idemPushout_iff arity first second left right square).trans quotientComparison.symm

end Mettapedia.OSLF.Framework.InstrumentCutContexts
