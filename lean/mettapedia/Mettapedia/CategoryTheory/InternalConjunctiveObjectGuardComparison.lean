import Mettapedia.CategoryTheory.InternalConjunctiveObjectMaps
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!+# Guard comparisons earned from equalizer preservation

The satisfying-context comparison of a declaration-preserving map is the
actual isomorphism of two limiting forks. The source fork is preserved by
the functor, and the supplied proposition isomorphism compares its complete
predicate/truth pair with the independently chosen target pair.

The isomorphism has the same full inclusion and factorization readings as
the already constructed guarded-arrow action. Identity and composition of
the guarded action are consequences of monicity, including the necessary
predicate-equality transport in the composite target.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalConjunctiveObject.Map

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w k l m

variable {C : Type u} [Category.{k} C] [CartesianMonoidalCategory C] [HasEqualizers C]
variable {D : Type v} [Category.{l} D] [CartesianMonoidalCategory D] [HasEqualizers D]
variable {E : Type w} [Category.{m} E] [CartesianMonoidalCategory E] [HasEqualizers E]
variable {source : Operations C} {target : Operations D} {last : Operations E}
variable (mapping : Map source target)

def mappedGuard {context : C} (predicate : source.Fiber context) :
    Fork (mapping.image predicate) (target.top (mapping.functor.obj context)) :=
  Fork.ofι (mapping.functor.map (source.inclusion predicate))
    ((mapping.guarded_image predicate (source.inclusion predicate) (source.inclusion_satisfies predicate)).trans
      (target.reindex_top (mapping.functor.map (source.inclusion predicate))).symm)

def mappedGuardIsLimit {context : C} (predicate : source.Fiber context)
    [PreservesLimit (parallelPair predicate (source.top context)) mapping.functor] :
    IsLimit (mapping.mappedGuard predicate) :=
  Fork.isLimitOfIsos _
    (isLimitOfHasEqualizerOfPreservesLimit mapping.functor predicate (source.top context))
    (mapping.mappedGuard predicate) (Iso.refl _) mapping.proposition (Iso.refl _)
    (Category.id_comp _) ((Category.id_comp _).trans (mapping.image_top context).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)

def satisfyingIso {context : C} (predicate : source.Fiber context)
    [PreservesLimit (parallelPair predicate (source.top context)) mapping.functor] :
    mapping.functor.obj (source.satisfying predicate) ≅ target.satisfying (mapping.image predicate) :=
  IsLimit.conePointUniqueUpToIso (mapping.mappedGuardIsLimit predicate)
    (limit.isLimit (parallelPair (mapping.image predicate) (target.top (mapping.functor.obj context))))

theorem satisfyingIso_inclusion {context : C} (predicate : source.Fiber context)
    [PreservesLimit (parallelPair predicate (source.top context)) mapping.functor] :
    (mapping.satisfyingIso predicate).hom ≫ target.inclusion (mapping.image predicate) =
      mapping.functor.map (source.inclusion predicate) :=
  IsLimit.conePointUniqueUpToIso_hom_comp (mapping.mappedGuardIsLimit predicate)
    (limit.isLimit (parallelPair (mapping.image predicate) (target.top (mapping.functor.obj context)))) WalkingParallelPair.zero

theorem satisfyingIso_hom {context : C} (predicate : source.Fiber context)
    [PreservesLimit (parallelPair predicate (source.top context)) mapping.functor] :
    (mapping.satisfyingIso predicate).hom = mapping.satisfyingMap predicate :=
  mapping.satisfyingMap_unique predicate _ (mapping.satisfyingIso_inclusion predicate)

instance satisfyingMap_isIso {context : C} (predicate : source.Fiber context)
    [PreservesLimit (parallelPair predicate (source.top context)) mapping.functor] :
    IsIso (mapping.satisfyingMap predicate) := by
  rw [← mapping.satisfyingIso_hom predicate]
  infer_instance

theorem satisfyingIso_inv_inclusion {context : C} (predicate : source.Fiber context)
    [PreservesLimit (parallelPair predicate (source.top context)) mapping.functor] :
    (mapping.satisfyingIso predicate).inv ≫ mapping.functor.map (source.inclusion predicate) =
      target.inclusion (mapping.image predicate) := by
  rw [← mapping.satisfyingIso_inclusion predicate, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

theorem satisfyingIso_factor {context before : C} (predicate : source.Fiber before) (arrow : context ⟶ before)
    (guard : source.reindex arrow predicate = source.top context)
    [PreservesLimit (parallelPair predicate (source.top before)) mapping.functor] :
    mapping.functor.map (source.factor predicate arrow guard) ≫ (mapping.satisfyingIso predicate).hom =
      target.factor (mapping.image predicate) (mapping.functor.map arrow) (mapping.guarded_image predicate arrow guard) := by
  rw [mapping.satisfyingIso_hom]
  exact mapping.factor_image predicate arrow guard

private theorem satisfying_transport_inclusion {context : E}
    (first second : last.Fiber context) (same : first = second) :
    eqToHom (congrArg last.satisfying same) ≫ last.inclusion second = last.inclusion first := by
  cases same
  rw [eqToHom_refl, Category.id_comp]

theorem satisfyingMap_identity {context : C} (predicate : source.Fiber context) :
    (identity source).satisfyingMap predicate =
      eqToHom (congrArg source.satisfying (identity_image predicate).symm) := by
  apply (cancel_mono (source.inclusion ((identity source).image predicate))).mp
  rw [(identity source).satisfyingMap_inclusion,
    satisfying_transport_inclusion _ _ (identity_image predicate).symm]
  rfl

theorem satisfyingMap_comp (before : Map source target) (after : Map target last)
    {context : C} (predicate : source.Fiber context) :
    (comp before after).satisfyingMap predicate ≫
        eqToHom (congrArg last.satisfying (comp_image before after predicate)) =
      after.functor.map (before.satisfyingMap predicate) ≫ after.satisfyingMap (before.image predicate) := by
  apply (cancel_mono (last.inclusion (after.image (before.image predicate)))).mp
  rw [Category.assoc, satisfying_transport_inclusion _ _ (comp_image before after predicate),
    (comp before after).satisfyingMap_inclusion,
    Category.assoc, after.satisfyingMap_inclusion, ← after.functor.map_comp, before.satisfyingMap_inclusion]
  rfl

end Mettapedia.CategoryTheory.InternalConjunctiveObject.Map
