import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Images and comprehension over varying bases

The predicate category here consists of actual monomorphisms, with arbitrary
commuting squares as maps. Its inclusion into the arrow category is right
adjoint to image factorization. Both functors retain the codomain; the unit,
counit, and universal factorization keep the complete square rather than only
an inclusion in a single fibre.

The construction applies to any category with images and image maps. These
hypotheses are supplied by strong epi images, independently of a choice of
classifier or a particular presheaf presentation.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.MonoArrowImageAdjunction

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C]

def monomorphismProperty (C : Type u) [Category.{v} C] : ObjectProperty (Arrow C) :=
  fun object => Mono object.hom

abbrev Predicate (C : Type u) [Category.{v} C] :=
  (monomorphismProperty C).FullSubcategory

instance predicate_mono (predicate : Predicate C) : Mono predicate.obj.hom :=
  predicate.property

abbrev comprehension (C : Type u) [Category.{v} C] : Predicate C ⥤ Arrow C :=
  (monomorphismProperty C).ι

abbrev projection (C : Type u) [Category.{v} C] : Predicate C ⥤ C :=
  comprehension C ⋙ Arrow.rightFunc

theorem square_into_predicate_ext {object : Arrow C} {predicate : Predicate C}
    {first second : object ⟶ predicate.obj} (same : first.right = second.right) :
    first = second := by
  apply Arrow.hom_ext
  · apply (cancel_mono predicate.obj.hom).mp
    rw [Arrow.w first, Arrow.w second, same]
  · exact same

theorem predicate_hom_ext {first second : Predicate C}
    {left right : first ⟶ second} (same : left.hom.right = right.hom.right) :
    left = right := by
  apply ObjectProperty.hom_ext
  exact square_into_predicate_ext same

instance projection_faithful : (projection C).Faithful where
  map_injective := predicate_hom_ext

variable [HasImages C] [HasImageMaps C]

def image : Arrow C ⥤ Predicate C where
  obj object := ⟨Arrow.mk (Limits.image.ι object.hom), by
    change Mono (Limits.image.ι object.hom)
    infer_instance⟩
  map square := ObjectProperty.homMk
    (Arrow.homMk (Limits.image.map square) square.right (Limits.image.map_ι square))
  map_id object := by
    apply predicate_hom_ext
    rfl
  map_comp first second := by
    apply predicate_hom_ext
    rfl

theorem image_codomain : image (C := C) ⋙ projection C = Arrow.rightFunc := rfl

def unitSquare (object : Arrow C) :
    object ⟶ (comprehension C).obj (image.obj object) :=
  Arrow.homMk (factorThruImage object.hom) (𝟙 object.right) (by
    change factorThruImage object.hom ≫ Limits.image.ι object.hom =
      object.hom ≫ 𝟙 object.right
    rw [Limits.image.fac, Category.comp_id])

@[simp] theorem unitSquare_left (object : Arrow C) :
    (unitSquare object).left = factorThruImage object.hom := rfl

@[simp] theorem unitSquare_right (object : Arrow C) :
    (unitSquare object).right = 𝟙 object.right := rfl

def descend {object : Arrow C} {predicate : Predicate C}
    (square : object ⟶ predicate.obj) : image.obj object ⟶ predicate :=
  ObjectProperty.homMk (Arrow.homMk
    (Limits.image.map square ≫ (imageMonoIsoSource predicate.obj.hom).hom)
    square.right (by
      change (Limits.image.map square ≫ (imageMonoIsoSource predicate.obj.hom).hom) ≫
        predicate.obj.hom = Limits.image.ι object.hom ≫ square.right
      rw [Category.assoc, imageMonoIsoSource_hom_self, Limits.image.map_ι]))

@[simp] theorem descend_right {object : Arrow C} {predicate : Predicate C}
    (square : object ⟶ predicate.obj) : (descend square).hom.right = square.right := rfl

theorem descend_factor {object : Arrow C} {predicate : Predicate C}
    (square : object ⟶ predicate.obj) :
    unitSquare object ≫ (comprehension C).map (descend square) = square := by
  apply square_into_predicate_ext
  exact Category.id_comp square.right

theorem descend_unique {object : Arrow C} {predicate : Predicate C}
    (square : object ⟶ predicate.obj) (candidate : image.obj object ⟶ predicate)
    (factorization : unitSquare object ≫ (comprehension C).map candidate = square) :
    candidate = descend square := by
  apply predicate_hom_ext
  have base := congrArg Arrow.Hom.right factorization
  change 𝟙 object.right ≫ candidate.hom.right = square.right at base
  change candidate.hom.right = square.right
  exact (Category.id_comp candidate.hom.right).symm.trans base

def homEquiv (object : Arrow C) (predicate : Predicate C) :
    (image.obj object ⟶ predicate) ≃ (object ⟶ (comprehension C).obj predicate) where
  toFun square := unitSquare object ≫ (comprehension C).map square
  invFun := descend
  left_inv square := (descend_unique _ square rfl).symm
  right_inv := descend_factor

def adjunction : image (C := C) ⊣ comprehension C :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv
      homEquiv_naturality_left_symm := by
        intro first second predicate square next
        apply predicate_hom_ext
        rfl
      homEquiv_naturality_right := by
        intro object first second square next
        apply square_into_predicate_ext
        change 𝟙 object.right ≫ (square.hom.right ≫ next.hom.right) =
          (𝟙 object.right ≫ square.hom.right) ≫ next.hom.right
        exact (Category.assoc _ _ _).symm }

theorem adjunction_unit (object : Arrow C) :
    adjunction.unit.app object = unitSquare object := by
  change homEquiv object (image.obj object) (𝟙 _) = unitSquare object
  simp only [homEquiv, Equiv.coe_fn_mk, Functor.map_id, Category.comp_id]

theorem adjunction_counit (predicate : Predicate C) :
    adjunction.counit.app predicate = descend (𝟙 predicate.obj) := by
  change (homEquiv predicate.obj predicate).symm (𝟙 predicate.obj) = _
  rfl

theorem unit_over_identity (object : Arrow C) :
    (adjunction.unit.app object).right = 𝟙 object.right := by
  rw [adjunction_unit]
  rfl

theorem counit_over_identity (predicate : Predicate C) :
    (adjunction.counit.app predicate).hom.right = 𝟙 predicate.obj.right := by
  rw [adjunction_counit]
  rfl

theorem image_comprehension_factorization (object : Arrow C) (predicate : Predicate C) :
    ∀ square : object ⟶ predicate.obj,
      ∃! candidate : image.obj object ⟶ predicate,
        unitSquare object ≫ (comprehension C).map candidate = square := by
  intro square
  exact ⟨descend square, descend_factor square,
    fun candidate proof => descend_unique square candidate proof⟩

end Mettapedia.CategoryTheory.MonoArrowImageAdjunction
