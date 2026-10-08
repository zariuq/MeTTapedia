import Mettapedia.TypeTheory.ProjectionIndexedMonomorphismOperations
import Mettapedia.TypeTheory.ProjectionIndexedCodomainComprehension

/-!

# Full comprehension and projection-indexed monomorphism operations

The complete monomorphism fibration has full comprehension and an actual
unit with both adjunctions. Strong sums are formed along its own monic
display projections, rather than along arbitrary base arrows.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.TypeTheory.ProjectionIndexedMonomorphismComprehension

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Functor
open HasFibers
open Mettapedia.CategoryTheory Mettapedia.CategoryTheory.FibrationTwoCategory
open MonoArrowImageAdjunction ProjectionIndexedComprehension

universe u v
variable {C : Type (max u v)} [Category.{v} C] [HasFiniteLimits C]

def unit : C ⥤ Predicate C where
  obj := truth
  map arrow := ObjectProperty.homMk (Arrow.homMk arrow arrow (by
    change arrow ≫ 𝟙 _ = 𝟙 _ ≫ arrow
    exact (Category.comp_id _).trans (Category.id_comp _).symm))
  map_id _ := predicate_hom_ext rfl
  map_comp _ _ := predicate_hom_ext rfl

instance unit_full : (unit (C := C)).Full where
  map_surjective supplied := ⟨supplied.hom.right, predicate_hom_ext rfl⟩

instance unit_faithful : (unit (C := C)).Faithful where
  map_injective same := congrArg (fun arrow => arrow.hom.right) same

def unitAdjunction : projection C ⊣ unit (C := C) :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun first second => {
      toFun arrow := ObjectProperty.homMk
        (Arrow.homMk (first.obj.hom ≫ arrow) arrow (by
          change (first.obj.hom ≫ arrow) ≫ 𝟙 second = first.obj.hom ≫ arrow
          exact Category.comp_id _))
      invFun arrow := arrow.hom.right
      left_inv _ := rfl
      right_inv _ := predicate_hom_ext rfl }
    homEquiv_naturality_left_symm := by intros; rfl
    homEquiv_naturality_right := by intros; apply predicate_hom_ext; rfl }

def domainAdjunction : unit (C := C) ⊣ comprehension C ⋙ Arrow.leftFunc :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun first second => {
      toFun arrow := arrow.hom.left
      invFun arrow := ObjectProperty.homMk
        (Arrow.homMk arrow (arrow ≫ second.obj.hom) (by
          change arrow ≫ second.obj.hom = 𝟙 first ≫ (arrow ≫ second.obj.hom)
          exact (Category.id_comp _).symm))
      left_inv arrow := by
        apply predicate_hom_ext
        change arrow.hom.left ≫ second.obj.hom = arrow.hom.right
        exact (Arrow.w arrow.hom).trans (Category.id_comp _)
      right_inv _ := rfl }
    homEquiv_naturality_left_symm := by
      intros
      apply predicate_hom_ext
      exact Category.assoc _ _ _
    homEquiv_naturality_right := by intros; rfl }

local instance comprehensionLimits : HasFiniteLimits (predicates C).Base :=
  inferInstanceAs (HasFiniteLimits C)

local instance comprehensionFibres : HasFibers.{v,max u v} (predicates C).functor := fibres

def fullComprehension : FibrationComprehensionProfile.Comprehension (predicates C) where
  display := comprehension C
  over := rfl
  full := inferInstanceAs (comprehension C).Full
  faithful := inferInstanceAs (comprehension C).Faithful
  cartesian arrow cartesian := by
    change (projection C).IsCartesian arrow.hom.right arrow at cartesian
    exact (cartesian_iff_pullback arrow).mp cartesian
  unit := unit
  unitFull := unit_full
  unitFaithful := unit_faithful
  unitOver := rfl
  unitAdjunction := unitAdjunction
  domainAdjunction := domainAdjunction

theorem projection_eq (object : Predicate C) :
    Comprehension.displayProjection fullComprehension object = object.obj.hom := by
  change object.obj.hom ≫ 𝟙 object.obj.right = object.obj.hom
  exact Category.comp_id _

theorem projection_mono (object : Predicate C) :
    Mono (Comprehension.displayProjection fullComprehension object) := by
  rw [projection_eq]
  infer_instance

variable (model : CodomainClosedComprehension C)

set_option backward.isDefEq.respectTransparency.types false in
def data : Data.{max u v,v,max u v,v} (predicates C) where
  comprehension := fullComprehension
  substitution := substitution
  terminal := inferInstance
  sum object := by
    haveI := projection_mono object
    change MonicSlice (fullComprehension.display.obj object).left ⥤
      MonicSlice ((predicates C).functor.obj object)
    exact map (Comprehension.displayProjection fullComprehension object)
  product object := by
    change MonicSlice (fullComprehension.display.obj object).left ⥤
      MonicSlice ((predicates C).functor.obj object)
    exact product model (Comprehension.displayProjection fullComprehension object)
  sumAdjunction object := by
    haveI := projection_mono object
    exact sumAdjunction (Comprehension.displayProjection fullComprehension object)
  productAdjunction object := by
    change pullback (Comprehension.displayProjection fullComprehension object) ⊣
      product model (Comprehension.displayProjection fullComprehension object)
    exact productAdjunction model (Comprehension.displayProjection fullComprehension object)
  strongSum object result := by
    have := projection_mono object
    change IsIso (((sumAdjunction
      (Comprehension.displayProjection fullComprehension object)).unit.app result).hom.left ≫
      _)
    rw [sumAdjunction_unit]
    change IsIso (CodomainComprehension.canonicalSumSquare
      (Comprehension.displayProjection fullComprehension object) result.obj).left
    rw [CodomainComprehension.canonicalSumSquare_domain]
    exact ⟨⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩⟩

end Mettapedia.TypeTheory.ProjectionIndexedMonomorphismComprehension
