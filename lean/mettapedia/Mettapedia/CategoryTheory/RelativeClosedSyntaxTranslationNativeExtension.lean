import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationNativeEquations

/-!
# Actual coded augmentation of weak closed expression translations

Every added native inverse is a genuine target expression: the target-native
inverse followed by the base inverse comparison. Its independently earned
equation trees, together with the supplied old local trees, construct an
actual admitted translation. The forty-rule transport then gives its real
finite-limit closed quotient functor. The complete old diagram and all base
arrows are recovered without collapsing raw object codes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation.NativeExtension

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory NativeData NativeEquations

universe k

variable {C D : Type k} [Category.{k} C] [Category.{k} D]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable {symbols nextSymbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {next : Signature (C := D) (symbols := nextSymbols)}
variable (mapping : Translation signature next)
variable [PreservesFiniteLimits mapping.data.base] [MonoidalClosedFunctor mapping.data.base]

def extended : Translation (BaseExtension.extend signature) (BaseExtension.extend next) where
  data := NativeData.data mapping
  objectTyped origin := (BaseExtension.originalMap next).derivation (mapping.objectTyped origin.down)
  arrowTyped origin := match origin with
    | .inl choice => native_arrow_typed mapping choice
    | .inr name => by
        change Derivation (BaseExtension.extend next)
          (.arrow ((BaseExtension.originalObjectCode (signature.source name.down)).translate (NativeData.data mapping))
            ((BaseExtension.originalObjectCode (signature.target name.down)).translate (NativeData.data mapping))
            (BaseExtension.originalArrowCode (mapping.data.arrows name.down)))
        rw [NativeData.original_object, NativeData.original_object]
        have actual := (BaseExtension.originalMap next).derivation (mapping.arrowTyped name.down)
        exact actual
  equationTyped origin := match origin with
    | .inl choice => native_equation_typed mapping choice
    | .inr name => by
        change Derivation (BaseExtension.extend next)
          (.equation
            ((BaseExtension.originalObjectCode (signature.equationSource name.down)).translate (NativeData.data mapping))
            ((BaseExtension.originalObjectCode (signature.equationTarget name.down)).translate (NativeData.data mapping))
            ((BaseExtension.originalArrowCode (signature.left name.down)).translate (NativeData.data mapping))
            ((BaseExtension.originalArrowCode (signature.right name.down)).translate (NativeData.data mapping)))
        rw [NativeData.original_object, NativeData.original_object,
          NativeData.original_arrow, NativeData.original_arrow]
        have actual := (BaseExtension.originalMap next).derivation (mapping.equationTyped name.down)
        exact actual

instance extended_lex : PreservesFiniteLimits (extended mapping).functor := inferInstance

instance extended_closed : MonoidalClosedFunctor (extended mapping).functor := inferInstance

theorem original_object (source : Object signature) :
    (extended mapping).object ((BaseExtension.originalMap signature).object source) =
      (BaseExtension.originalMap next).object (mapping.object source) :=
  Object.ext (NativeData.original_object mapping source.code)

private theorem classOf_heq {E : Type k} [Category.{k} E]
    {names : Symbols.{k}} {presentation : Signature (C := E) (symbols := names)}
    {source target before after : Object presentation}
    (first : RawHom source target) (second : RawHom before after)
    (sourceSame : source = before) (targetSame : target = after)
    (codes : first.code = second.code) : HEq (classOf first) (classOf second) := by
  subst before
  subst after
  exact heq_of_eq (congrArg classOf (RawHom.ext codes))

theorem original_readback :
    (BaseExtension.originalMap signature).functor ⋙ (extended mapping).functor =
      mapping.functor ⋙ (BaseExtension.originalMap next).functor := by
  refine _root_.CategoryTheory.Functor.hext
    (F := (BaseExtension.originalMap signature).functor ⋙ (extended mapping).functor)
    (G := mapping.functor ⋙ (BaseExtension.originalMap next).functor)
    (original_object mapping) ?_
  intro source target arrow
  refine Quotient.inductionOn arrow ?_
  intro representative
  exact classOf_heq ((extended mapping).rawArrow ((BaseExtension.originalMap signature).rawArrow representative))
    ((BaseExtension.originalMap next).rawArrow (mapping.rawArrow representative))
    (original_object mapping source) (original_object mapping target)
    (NativeData.original_arrow mapping representative.code)

theorem base_readback :
    baseFunctor (BaseExtension.extend signature) ⋙ (extended mapping).functor =
      mapping.data.base ⋙ baseFunctor (BaseExtension.extend next) :=
  (extended mapping).functor_base

end Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation.NativeExtension
