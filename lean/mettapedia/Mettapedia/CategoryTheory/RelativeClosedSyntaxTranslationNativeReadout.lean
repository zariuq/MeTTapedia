import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationNativeComparison

/-!
# Independent atomic readings of native translation comparisons

The earned identity and composition isomorphisms read as the actual object
equality arrows at embedded base objects and fresh names. Only these atomic
codes agree literally. General equalizer presentations retain the coherent
comparison obtained from independent models.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation.NativeReadout

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory SemanticModels FunctorNormalization

universe k

variable {C D H : Type k} [Category.{k} C] [Category.{k} D] [Category.{k} H]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable [CartesianMonoidalCategory H] [MonoidalClosed H] [HasFiniteLimits H]
variable {symbols nextSymbols lastSymbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {next : Signature (C := D) (symbols := nextSymbols)}
variable {final : Signature (C := H) (symbols := lastSymbols)}

theorem identity_component (headers : HeaderFormation signature)
    (source : Object (BaseExtension.extend signature))
    (objects : (NativeExtension.extended (Translation.identity headers)).object source = source) :
    (NativeComparison.identity headers).hom.app source = eqToHom objects := by
  let augmentedHeaders := BaseExtension.headers signature headers
  let before := NativeExtension.extended (Translation.identity headers)
  let after := Translation.identity augmentedHeaders
  let model := NativeComparison.selfModel augmentedHeaders
  let same := (NativeModelAction.identity_model headers model).trans
    (ModelLaws.identity augmentedHeaders model).symm
  let middleObjects := objects.trans (Translation.object_identity augmentedHeaders source).symm
  have firstRead := NativeComparison.ofModelEquality_hom_component before after augmentedHeaders same
    source middleObjects
  have lastRead : (eqToIso (Translation.functor_identity augmentedHeaders)).hom.app source =
      eqToHom (Translation.object_identity augmentedHeaders source) :=
    eqToHom_app (Translation.functor_identity augmentedHeaders) source
  change (NativeComparison.ofModelEquality before after augmentedHeaders same).hom.app source ≫
      (eqToIso (Translation.functor_identity augmentedHeaders)).hom.app source = eqToHom objects
  exact (congrArg₂ (fun first last => first ≫ last) firstRead lastRead).trans
    (eqToHom_trans middleObjects (Translation.object_identity augmentedHeaders source))

theorem identity_base_objects (headers : HeaderFormation signature) (source : C) :
    (NativeExtension.extended (Translation.identity headers)).object
      (baseObject (BaseExtension.extend signature) source) = baseObject (BaseExtension.extend signature) source := rfl

theorem identity_name_objects (headers : HeaderFormation signature)
    (origin : (BaseExtension.extendedSymbols C symbols).ObjectName) :
    (NativeExtension.extended (Translation.identity headers)).object (namedObject origin) = namedObject origin := by
  apply Object.ext
  cases origin
  rfl

theorem identity_base (headers : HeaderFormation signature) (source : C) :
    (NativeComparison.identity headers).hom.app (baseObject (BaseExtension.extend signature) source) =
      eqToHom (identity_base_objects headers source) :=
  identity_component headers _ (identity_base_objects headers source)

theorem identity_name (headers : HeaderFormation signature)
    (origin : (BaseExtension.extendedSymbols C symbols).ObjectName) :
    (NativeComparison.identity headers).hom.app (namedObject origin) =
      eqToHom (identity_name_objects headers origin) :=
  identity_component headers _ (identity_name_objects headers origin)

theorem identity_original_objects (headers : HeaderFormation signature) (source : Object signature) :
    (NativeExtension.extended (Translation.identity headers)).object
      ((BaseExtension.originalMap signature).object source) =
        (BaseExtension.originalMap signature).object source :=
  (NativeExtension.original_object (Translation.identity headers) source).trans
    (congrArg (BaseExtension.originalMap signature).object (Translation.object_identity headers source))

theorem identity_original (headers : HeaderFormation signature) (source : Object signature) :
    (NativeComparison.identity headers).hom.app ((BaseExtension.originalMap signature).object source) =
      eqToHom (identity_original_objects headers source) :=
  identity_component headers _ (identity_original_objects headers source)

variable (first : Translation signature next) (last : Translation next final)
variable [PreservesFiniteLimits first.data.base] [MonoidalClosedFunctor first.data.base]
variable [PreservesFiniteLimits last.data.base] [MonoidalClosedFunctor last.data.base]

private instance composite_lex : PreservesFiniteLimits (first.compose last).data.base :=
  comp_preservesFiniteLimits first.data.base last.data.base

private instance composite_closed : MonoidalClosedFunctor (first.compose last).data.base :=
  CartesianClosedFunctorCoherence.closed_composition first.data.base last.data.base

theorem compose_component (headers : HeaderFormation final)
    (source : Object (BaseExtension.extend signature))
    (objects : ((NativeExtension.extended first).functor ⋙ (NativeExtension.extended last).functor).obj source =
      (NativeExtension.extended (first.compose last)).object source) :
    (NativeComparison.compose first last headers).hom.app source = eqToHom objects := by
  let augmentedHeaders := BaseExtension.headers final headers
  let model := NativeComparison.selfModel augmentedHeaders
  let before := (NativeExtension.extended first).compose (NativeExtension.extended last)
  let after := NativeExtension.extended (first.compose last)
  let same := (ModelLaws.compose (NativeExtension.extended first) (NativeExtension.extended last) model).symm.trans
    (NativeModelAction.compose_model first last model)
  let initialObjects := Translation.object_compose (NativeExtension.extended first) (NativeExtension.extended last) source
  let middleObjects := initialObjects.symm.trans objects
  have initialRead :
      (eqToIso (Translation.functor_compose (NativeExtension.extended first)
        (NativeExtension.extended last))).hom.app source = eqToHom initialObjects :=
    eqToHom_app (Translation.functor_compose (NativeExtension.extended first) (NativeExtension.extended last)) source
  have finalRead := NativeComparison.ofModelEquality_hom_component before after augmentedHeaders same
    source middleObjects
  change (eqToIso (Translation.functor_compose (NativeExtension.extended first)
      (NativeExtension.extended last))).hom.app source ≫
        (NativeComparison.ofModelEquality before after augmentedHeaders same).hom.app source = eqToHom objects
  exact (congrArg₂ (fun initial ending => initial ≫ ending) initialRead finalRead).trans
    (eqToHom_trans initialObjects middleObjects)

theorem compose_base_objects (source : C) :
    ((NativeExtension.extended first).functor ⋙ (NativeExtension.extended last).functor).obj
      (baseObject (BaseExtension.extend signature) source) =
        (NativeExtension.extended (first.compose last)).object (baseObject (BaseExtension.extend signature) source) := rfl

theorem compose_name_objects (origin : (BaseExtension.extendedSymbols C symbols).ObjectName) :
    ((NativeExtension.extended first).functor ⋙ (NativeExtension.extended last).functor).obj (namedObject origin) =
      (NativeExtension.extended (first.compose last)).object (namedObject origin) :=
  Object.ext (NativeData.original_object last (first.data.objects origin.down))

theorem compose_base (headers : HeaderFormation final) (source : C) :
    (NativeComparison.compose first last headers).hom.app (baseObject (BaseExtension.extend signature) source) =
      eqToHom (compose_base_objects first last source) :=
  compose_component first last headers _ (compose_base_objects first last source)

theorem compose_name (headers : HeaderFormation final)
    (origin : (BaseExtension.extendedSymbols C symbols).ObjectName) :
    (NativeComparison.compose first last headers).hom.app (namedObject origin) =
      eqToHom (compose_name_objects first last origin) :=
  compose_component first last headers _ (compose_name_objects first last origin)

theorem compose_original_objects (source : Object signature) :
    ((NativeExtension.extended first).functor ⋙ (NativeExtension.extended last).functor).obj
      ((BaseExtension.originalMap signature).object source) =
        (NativeExtension.extended (first.compose last)).object ((BaseExtension.originalMap signature).object source) :=
  (congrArg (NativeExtension.extended last).object (NativeExtension.original_object first source)).trans
    ((NativeExtension.original_object last (first.object source)).trans
      ((congrArg (BaseExtension.originalMap final).object (Translation.object_compose first last source)).trans
        (NativeExtension.original_object (first.compose last) source).symm))

theorem compose_original (headers : HeaderFormation final) (source : Object signature) :
    (NativeComparison.compose first last headers).hom.app ((BaseExtension.originalMap signature).object source) =
      eqToHom (compose_original_objects first last source) :=
  compose_component first last headers _ (compose_original_objects first last source)

end Mettapedia.CategoryTheory.RelativeClosedSyntax.Translation.NativeReadout
