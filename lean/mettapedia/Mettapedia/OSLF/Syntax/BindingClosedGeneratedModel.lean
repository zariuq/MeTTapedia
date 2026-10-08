import Mettapedia.OSLF.Syntax.BindingClosedSchemaGeneric
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorNormalizationRealization

/-!
# Binding operations recovered from actual generated arrows

A finite-limit closed functor out of the independent constructor presentation
determines sort objects and complete primitive operations in its target. The
normalization comparisons compute every ordered context and argument family.
They transport the actual mapped primitive arrows, rather than supplying a
whole binding interpretation as input.

The resulting recursive binding parser is canonically isomorphic to the
original functor. Consequently equality of independently encoded schema
arrows is exactly equality of the complete binding-family readings. This
also applies to a generated equation guest's own syntax inclusion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Binding.ClosedPresentation.GeneratedModel

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open GeneratedCategory
open CategoricalBindingModel

universe k w

variable {binding : Mettapedia.OSLF.Binding.Signature}
variable {D : Type w} [Category.{k} D] [CartesianMonoidalCategory D]
variable [MonoidalClosed D] [HasFiniteLimits D]
variable (mapping : Object (signature.{k} binding) ⥤ D)
variable [PreservesFiniteLimits mapping] [MonoidalClosedFunctor mapping]

def sort (result : binding.Srt) : D := mapping.obj (sortObject binding result)

theorem sort_native (result : binding.Srt) :
    (FunctorNormalization.normalizedFunctor mapping).obj (sortObject binding result) =
      sort mapping result :=
  congrArg FunctorNormalization.ObjectImage.value
    (FunctorNormalization.objectImage_named mapping (ULift.up result))

theorem context_native : (scope : Ctx binding) →
    (FunctorNormalization.normalizedFunctor mapping).obj (contextObject binding scope) =
      contextOf (sort mapping) scope
  | [] => FunctorNormalization.normalized_terminal_object mapping
  | result :: rest => by
      change (FunctorNormalization.normalizedFunctor mapping).obj
        (product (sortObject binding result) (contextObject binding rest)) = _
      rw [FunctorNormalization.normalized_product_object, sort_native, context_native rest]

theorem power_native (scope : Ctx binding) (result : binding.Srt) :
    (FunctorNormalization.normalizedFunctor mapping).obj (powerObject binding scope result) =
      (contextOf (sort mapping) scope ⟶[D] sort mapping result) := by
  change (FunctorNormalization.normalizedFunctor mapping).obj
    (exponentialObject (contextObject binding scope) (sortObject binding result)) = _
  rw [FunctorNormalization.normalized_exponential_object, context_native, sort_native]

theorem family_native : (arities : List (Ctx binding × binding.Srt)) →
    (FunctorNormalization.normalizedFunctor mapping).obj (familyObject binding arities) =
      familyOf (fun scope result => contextOf (sort mapping) scope ⟶[D] sort mapping result) arities
  | [] => FunctorNormalization.normalized_terminal_object mapping
  | arity :: rest => by
      change (FunctorNormalization.normalizedFunctor mapping).obj
        (product (powerObject binding arity.1 arity.2) (familyObject binding rest)) = _
      rw [FunctorNormalization.normalized_product_object, power_native, family_native rest]

def operations : Operations binding D where
  sort := sort mapping
  operation operator :=
    eqToHom (family_native mapping (binding.arity operator)).symm ≫
      (FunctorNormalization.normalizedFunctor mapping).map (classOf (ClosedPresentation.operator binding operator)) ≫
        eqToHom (sort_native mapping _)

omit [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D] in
private theorem cast_value {source target before after : D} (arrow : source ⟶ target)
    (sourceSame : source = before) (targetSame : target = after) :
    (⟨before, after, eqToHom sourceSame.symm ≫ arrow ≫ eqToHom targetSame⟩ : Interpretation.ArrowValue D) =
      ⟨source, target, arrow⟩ := by
  cases sourceSame
  cases targetSame
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

theorem primitive_value (origin : Sigma binding.Op) :
    (operations mapping).primitiveValue origin =
      ⟨(FunctorNormalization.normalizedFunctor mapping).obj (familyObject binding (binding.arity origin.2)),
        (FunctorNormalization.normalizedFunctor mapping).obj (sortObject binding origin.1),
        (FunctorNormalization.normalizedFunctor mapping).map
          (classOf (ClosedPresentation.operator binding origin.2))⟩ :=
  cast_value _ (family_native mapping _) (sort_native mapping _)

omit [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D] in
private theorem assignment_ext
    (first second : Interpretation.Assignment Base.{k} (symbols binding) D)
    (baseSame : first.base = second.base) (objectSame : first.object = second.object)
    (arrowSame : first.arrow = second.arrow) : first = second := by
  cases first
  cases second
  cases baseSame
  cases objectSame
  cases arrowSame
  rfl

theorem assignment_equal : (operations mapping).assignment =
    FunctorNormalization.assignment mapping (headers binding) := by
  have baseSame : (operations mapping).assignment.base =
      (FunctorNormalization.assignment mapping (headers binding)).base := by
    apply Functor.hext
    · intro object
      exact isEmptyElim object
    · intro source target arrow
      exact False.elim (isEmptyElim source : False)
  have objectSame : (operations mapping).assignment.object =
      (FunctorNormalization.assignment mapping (headers binding)).object := by
    funext origin
    rfl
  have arrowSame : (operations mapping).assignment.arrow =
      (FunctorNormalization.assignment mapping (headers binding)).arrow := by
    funext origin
    exact primitive_value mapping origin.down
  exact assignment_ext _ _ baseSame objectSame arrowSame

private theorem interpretation_equal {before after : Interpretation.Assignment Base.{k} (symbols binding) D}
    (first : Interpretation.Realization (signature binding) before)
    (second : Interpretation.Realization (signature binding) after) (same : before = after) :
    Interpretation.functor before first = Interpretation.functor after second := by
  cases same
  rfl

def comparison : mapping ≅ (operations mapping).interpretation.functor :=
  FunctorNormalization.parserComparison mapping (headers binding) ≪≫
    eqToIso (interpretation_equal (FunctorNormalization.reconstruction_realization mapping (headers binding))
      (operations mapping).realization (assignment_equal mapping).symm)

theorem mapped_arrow_eq_iff {source target : Object (signature.{k} binding)}
    (first second : source ⟶ target) :
    mapping.map first = mapping.map second ↔
      (operations mapping).interpretation.functor.map first =
        (operations mapping).interpretation.functor.map second := by
  constructor
  · intro same
    apply (cancel_epi ((comparison mapping).hom.app source)).mp
    rw [← (comparison mapping).hom.naturality, ← (comparison mapping).hom.naturality, same]
  · intro same
    apply (cancel_mono ((comparison mapping).hom.app target)).mp
    rw [(comparison mapping).hom.naturality, (comparison mapping).hom.naturality, same]

theorem schema_eq_iff {metavariables : List (MetaArity binding)} {context : Ctx binding}
    {result : binding.Srt} (first second : Term (withMetas binding metavariables) context result) :
    mapping.map (classOf (SchemaExpressions.expression binding first)) =
        mapping.map (classOf (SchemaExpressions.expression binding second)) ↔
      (operations mapping).model.interp metavariables first =
        (operations mapping).model.interp metavariables second :=
  (mapped_arrow_eq_iff mapping _ _).trans ((operations mapping).schema_arrow_eq_iff first second)

end Mettapedia.OSLF.Binding.ClosedPresentation.GeneratedModel
