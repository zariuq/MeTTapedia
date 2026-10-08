import Mettapedia.TypeTheory.ProjectionIndexedComprehension
import Mettapedia.CategoryTheory.FibrationCodomainAction
import Mettapedia.CategoryTheory.CodomainSliceFibres

/-!
# Actual monomorphism slices as predicate fibres

The fibre objects are actual monomorphisms into the fixed base. Its full
slice maps retain their entire domain maps. The inclusion is proved fully
faithful and essentially surjective onto the actual categorical fibre.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.TypeTheory.ProjectionIndexedMonomorphismComprehension

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Functor
open HasFibers
open Mettapedia.CategoryTheory Mettapedia.CategoryTheory.FibrationTwoCategory
open MonoArrowImageAdjunction

universe u v
variable {C : Type (max u v)} [Category.{v} C]

def monicSliceProperty (base : C) : ObjectProperty (Over base) := fun object => Mono object.hom

abbrev MonicSlice (base : C) := (monicSliceProperty base).FullSubcategory

instance monicSlice_mono {base : C} (object : MonicSlice base) : Mono object.obj.hom :=
  object.property

instance monicSlice_hom_subsingleton {base : C} (first second : MonicSlice base) :
    Subsingleton (first ⟶ second) where
  allEq left right := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply (cancel_mono second.obj.hom).mp
    exact (Over.w left.hom).trans (Over.w right.hom).symm

def fibreInclusion (base : C) : MonicSlice base ⥤ Predicate C where
  obj object := ⟨Arrow.mk object.obj.hom, object.property⟩
  map arrow := ObjectProperty.homMk (Arrow.homMk arrow.hom.left (𝟙 base) (by
    exact (Over.w arrow.hom).trans (Category.comp_id _).symm))
  map_id _ := predicate_hom_ext rfl
  map_comp _ _ := by
    apply predicate_hom_ext
    change 𝟙 base = 𝟙 base ≫ 𝟙 base
    exact (Category.id_comp _).symm

theorem fibreInclusion_projection (base : C) :
    fibreInclusion base ⋙ projection C = (Functor.const (MonicSlice base)).obj base := rfl

def fibreFunctor (base : C) :
    MonicSlice base ⥤ Fiber (projection C) base :=
  Fiber.inducedFunctor (fibreInclusion_projection base)

instance fibreFunctor_faithful (base : C) : (fibreFunctor base).Faithful where
  map_injective same := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact congrArg (fun square => square.val.hom.left) same

instance fibreFunctor_full (base : C) : (fibreFunctor base).Full where
  map_surjective {first second} supplied := by
    have := supplied.property
    have based : 𝟙 base = supplied.val.hom.right :=
      IsHomLift.eq_of_isHomLift (projection C)
        (a := (fibreInclusion base).obj first) (b := (fibreInclusion base).obj second)
        (𝟙 base) supplied.val
    let selected : first ⟶ second := ObjectProperty.homMk
      (Over.homMk supplied.val.hom.left (by
        have commutes := Arrow.w supplied.val.hom
        change supplied.val.hom.left ≫ second.obj.hom =
          first.obj.hom ≫ supplied.val.hom.right at commutes
        rw [← based] at commutes
        exact commutes.trans (Category.comp_id _)))
    refine ⟨selected, ?_⟩
    apply Subtype.ext
    exact predicate_hom_ext based

instance fibreFunctor_essSurj (base : C) : (fibreFunctor base).EssSurj where
  mem_essImage supplied := by
    rcases supplied with ⟨supplied, based⟩
    change supplied.obj.right = base at based
    subst base
    let selected : MonicSlice supplied.obj.right :=
      ⟨Over.mk supplied.obj.hom, supplied.property⟩
    refine ⟨selected, ⟨eqToIso ?_⟩⟩
    apply Subtype.ext
    apply ObjectProperty.FullSubcategory.ext
    exact Arrow.mk_eq supplied.obj

instance fibreFunctor_isEquivalence (base : C) : (fibreFunctor base).IsEquivalence where

@[instance_reducible] def fibres : HasFibers.{v,max u v} (projection C) where
  Fib := MonicSlice
  category _ := inferInstance
  ι := fibreInclusion
  comp_const := fibreInclusion_projection
  equiv base := by
    change (fibreFunctor base).IsEquivalence
    infer_instance

variable [HasFiniteLimits C]

def pullback {source target : C} (route : source ⟶ target) :
    MonicSlice target ⥤ MonicSlice source where
  obj object := ⟨(Over.pullback route).obj object.obj, by
    change Mono (pullback.snd object.obj.hom route)
    infer_instance⟩
  map arrow := ObjectProperty.homMk ((Over.pullback route).map arrow.hom)
  map_id _ := by apply ObjectProperty.hom_ext; exact (Over.pullback route).map_id _
  map_comp _ _ := by apply ObjectProperty.hom_ext; exact (Over.pullback route).map_comp _ _

def pullbackLift {source target : C} (route : source ⟶ target) :
    pullback route ⋙ fibreInclusion source ⟶ fibreInclusion target where
  app object := ObjectProperty.homMk
    (Arrow.homMk (pullback.fst object.obj.hom route) route pullback.condition)
  naturality _ _ _ := by
    apply predicate_hom_ext
    change 𝟙 source ≫ route = route ≫ 𝟙 target
    exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem pullbackLift_cartesian {source target : C} (route : source ⟶ target)
    (object : MonicSlice target) :
    (projection C).IsStronglyCartesian route ((pullbackLift route).app object) := by
  apply stronglyCartesian_of_pullback ((pullbackLift route).app object)
  exact IsPullback.of_hasPullback _ _

local instance predicateLimits : HasFiniteLimits (predicates C).Base :=
  inferInstanceAs (HasFiniteLimits C)

local instance selectedFibres : HasFibers.{v,max u v} (predicates C).functor := fibres

def substitution : FibrationComprehensionProfile.Substitution (predicates C) where
  reindex {source target} route := by
    change MonicSlice target ⥤ MonicSlice source
    exact pullback route
  lift {source target} route := by
    change pullback route ⋙ fibreInclusion source ⟶ fibreInclusion target
    exact pullbackLift route
  cartesian route object := by
    change (projection C).IsStronglyCartesian route ((pullbackLift route).app object)
    exact pullbackLift_cartesian route object

end Mettapedia.TypeTheory.ProjectionIndexedMonomorphismComprehension
