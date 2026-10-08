import Mettapedia.CategoryTheory.ElementaryToposPredicateDoctrine
import Mettapedia.CategoryTheory.MonoArrowFibration

/-!
# The actual based equivalence of predicate totals

The higher-order doctrine's Grothendieck total is equivalent, over its
unchanged base, to actual monomorphisms with commuting squares. A total
entailment determines the complete square through the selected pullback;
conversely a supplied square factors through that pullback. Every original
mono is recovered by its actual representative isomorphism.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.MonoArrowPredicateEquivalence

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open ElementaryToposPredicateAdjoints ElementaryToposPredicateDoctrine

universe u v
variable {C : Type u} [Category.{v} C]
variable [HasFiniteLimits C] [CartesianMonoidalCategory C] [MonoidalClosed C]
variable (classifier : Subobject.Classifier C)

abbrev Total := (doctrine classifier).toIndexedHeyting.Total

def predicate (object : Total classifier) : Subobject object.base := object.fiber

def square {first second : Total classifier} (arrow : first ⟶ second) :
    Arrow.mk (predicate classifier first).arrow ⟶ Arrow.mk (predicate classifier second).arrow := by
  have admitted : predicate classifier first ≤
      reindex arrow.base (predicate classifier second) :=
    ((doctrine classifier).toIndexedHeyting.totalHomEquiv first second arrow).property
  change predicate classifier first ≤
    (Subobject.pullback arrow.base).obj (predicate classifier second) at admitted
  refine Arrow.homMk
    (Subobject.ofLE _ _ admitted ≫ Subobject.pullbackπ arrow.base (predicate classifier second))
    arrow.base ?_
  change (Subobject.ofLE _ _ admitted ≫
      Subobject.pullbackπ arrow.base (predicate classifier second)) ≫
      (predicate classifier second).arrow = (predicate classifier first).arrow ≫ arrow.base
  rw [Category.assoc, (Subobject.isPullback arrow.base (predicate classifier second)).w,
    ← Category.assoc, Subobject.ofLE_arrow]

def toMonos : Total classifier ⥤ MonoArrowImageAdjunction.Predicate C where
  obj object := ⟨Arrow.mk (predicate classifier object).arrow, by
    change Mono (predicate classifier object).arrow
    infer_instance⟩
  map arrow := ObjectProperty.homMk (square classifier arrow)
  map_id _ := MonoArrowImageAdjunction.predicate_hom_ext rfl
  map_comp _ _ := MonoArrowImageAdjunction.predicate_hom_ext rfl

theorem square_base {first second : Total classifier} (arrow : first ⟶ second) :
    ((toMonos classifier).map arrow).hom.right = arrow.base := rfl

def fromSquare {first second : Total classifier}
    (supplied : (toMonos classifier).obj first ⟶ (toMonos classifier).obj second) :
    first ⟶ second := by
  let pull := Subobject.isPullback supplied.hom.right (predicate classifier second)
  have admitted : predicate classifier first ≤
      reindex supplied.hom.right (predicate classifier second) :=
    Subobject.le_of_comm
      (pull.lift supplied.hom.left (predicate classifier first).arrow (Arrow.w supplied.hom))
      (pull.lift_snd _ _ _)
  exact ((doctrine classifier).toIndexedHeyting.totalHomEquiv first second).symm
    ⟨supplied.hom.right, admitted⟩

theorem fromSquare_base {first second : Total classifier}
    (supplied : (toMonos classifier).obj first ⟶ (toMonos classifier).obj second) :
    (fromSquare classifier supplied).base = supplied.hom.right := rfl

instance toMonos_full : (toMonos classifier).Full where
  map_surjective supplied := ⟨fromSquare classifier supplied,
    MonoArrowImageAdjunction.predicate_hom_ext rfl⟩

instance toMonos_faithful : (toMonos classifier).Faithful where
  map_injective same := by
    apply ((doctrine classifier).toIndexedHeyting.totalHomEquiv _ _).injective
    apply Subtype.ext
    exact congrArg (fun arrow => arrow.hom.right) same

def representingObject (object : MonoArrowImageAdjunction.Predicate C) : Total classifier :=
  ⟨object.obj.right, Subobject.mk object.obj.hom⟩

def representingIso (object : MonoArrowImageAdjunction.Predicate C) :
    (toMonos classifier).obj (representingObject classifier object) ≅ object :=
  (MonoArrowImageAdjunction.monomorphismProperty C).isoMk
    (Arrow.isoMk (Subobject.underlyingIso object.obj.hom) (Iso.refl _)
      (by
        change (Subobject.underlyingIso object.obj.hom).hom ≫ object.obj.hom =
          (Subobject.mk object.obj.hom).arrow ≫ 𝟙 object.obj.right
        exact (Subobject.underlyingIso_hom_comp_eq_mk object.obj.hom).trans
          (Category.comp_id _).symm))

theorem representingIso_base (object : MonoArrowImageAdjunction.Predicate C) :
    (representingIso classifier object).hom.hom.right = 𝟙 object.obj.right := rfl

theorem representingIso_inv_base (object : MonoArrowImageAdjunction.Predicate C) :
    (representingIso classifier object).inv.hom.right = 𝟙 object.obj.right := rfl

theorem total_hom_ext {first second : Total classifier} {left right : first ⟶ second}
    (same : left.base = right.base) : left = right := by
  apply ((doctrine classifier).toIndexedHeyting.totalHomEquiv first second).injective
  exact Subtype.ext same

/-- The inverse retains the original mono's codomain and complete base maps. -/
def fromMonos : MonoArrowImageAdjunction.Predicate C ⥤ Total classifier where
  obj := representingObject classifier
  map {first second} arrow := fromSquare classifier
    ((representingIso classifier first).hom ≫ arrow ≫
      (representingIso classifier second).inv)
  map_id object := by
    apply total_hom_ext classifier
    change (𝟙 object.obj.right ≫ 𝟙 object.obj.right ≫ 𝟙 object.obj.right) =
      𝟙 object.obj.right
    simp only [Category.id_comp]
  map_comp {first middle second} earlier later := by
    apply total_hom_ext classifier
    change 𝟙 first.obj.right ≫ (earlier.hom.right ≫ later.hom.right) ≫
        𝟙 second.obj.right =
      (𝟙 first.obj.right ≫ earlier.hom.right ≫ 𝟙 middle.obj.right) ≫
        (𝟙 middle.obj.right ≫ later.hom.right ≫ 𝟙 second.obj.right)
    simp only [Category.id_comp, Category.comp_id]

theorem fromMonos_base {first second : MonoArrowImageAdjunction.Predicate C}
    (arrow : first ⟶ second) : ((fromMonos classifier).map arrow).base = arrow.hom.right := by
  change (𝟙 first.obj.right ≫ arrow.hom.right ≫ 𝟙 second.obj.right) = arrow.hom.right
  simp only [Category.id_comp, Category.comp_id]

def unitObjectIso (object : Total classifier) :
    object ≅ (toMonos classifier ⋙ fromMonos classifier).obj object where
  hom := ((doctrine classifier).toIndexedHeyting.totalHomEquiv _ _).symm
    ⟨𝟙 object.base, by
      change predicate classifier object ≤ reindex (𝟙 object.base)
        (Subobject.mk (predicate classifier object).arrow)
      rw [reindex_id, Subobject.mk_arrow]⟩
  inv := ((doctrine classifier).toIndexedHeyting.totalHomEquiv _ _).symm
    ⟨𝟙 object.base, by
      change Subobject.mk (predicate classifier object).arrow ≤
        reindex (𝟙 object.base) (predicate classifier object)
      rw [reindex_id, Subobject.mk_arrow]⟩
  hom_inv_id := by
    apply total_hom_ext classifier
    change (𝟙 object.base ≫ 𝟙 object.base) = 𝟙 object.base
    exact Category.id_comp _
  inv_hom_id := by
    apply total_hom_ext classifier
    change (𝟙 object.base ≫ 𝟙 object.base) = 𝟙 object.base
    exact Category.id_comp _

def unitIso : 𝟭 (Total classifier) ≅ toMonos classifier ⋙ fromMonos classifier :=
  NatIso.ofComponents (unitObjectIso classifier) (by
    intro first second arrow
    apply total_hom_ext classifier
    change arrow.base ≫ 𝟙 second.base =
      𝟙 first.base ≫ (𝟙 first.base ≫ arrow.base ≫ 𝟙 second.base)
    simp only [Category.id_comp, Category.comp_id])

def counitIso : fromMonos classifier ⋙ toMonos classifier ≅
    𝟭 (MonoArrowImageAdjunction.Predicate C) :=
  NatIso.ofComponents (representingIso classifier) (by
    intro first second arrow
    apply MonoArrowImageAdjunction.predicate_hom_ext
    change (𝟙 first.obj.right ≫ arrow.hom.right ≫ 𝟙 second.obj.right) ≫
        𝟙 second.obj.right = 𝟙 first.obj.right ≫ arrow.hom.right
    simp only [Category.id_comp, Category.comp_id])

def equivalence : Total classifier ≌ MonoArrowImageAdjunction.Predicate C where
  functor := toMonos classifier
  inverse := fromMonos classifier
  unitIso := unitIso classifier
  counitIso := counitIso classifier
  functor_unitIso_comp object := by
    apply MonoArrowImageAdjunction.predicate_hom_ext
    change (𝟙 object.base ≫ 𝟙 object.base) = 𝟙 object.base
    exact Category.id_comp _

theorem over_base :
    (equivalence classifier).functor ⋙ MonoArrowImageAdjunction.projection C =
      (doctrine classifier).toIndexedHeyting.projection := rfl

theorem inverse_over_base :
    (equivalence classifier).inverse ⋙ (doctrine classifier).toIndexedHeyting.projection =
      MonoArrowImageAdjunction.projection C := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro first second arrow
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change ((fromMonos classifier).map arrow).base = arrow.hom.right
  exact fromMonos_base classifier arrow

theorem unit_base (object : Total classifier) :
    ((equivalence classifier).unitIso.hom.app object).base = 𝟙 object.base := rfl

theorem unit_inverse_base (object : Total classifier) :
    ((equivalence classifier).unitIso.inv.app object).base = 𝟙 object.base := rfl

theorem counit_base (object : MonoArrowImageAdjunction.Predicate C) :
    ((equivalence classifier).counitIso.hom.app object).hom.right = 𝟙 object.obj.right := rfl

theorem counit_inverse_base (object : MonoArrowImageAdjunction.Predicate C) :
    ((equivalence classifier).counitIso.inv.app object).hom.right = 𝟙 object.obj.right := rfl

end Mettapedia.CategoryTheory.MonoArrowPredicateEquivalence
