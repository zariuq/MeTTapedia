import Mettapedia.GSLT.Topos.YonedaPredicateUniverseBridge
import Mathlib.CategoryTheory.FiberedCategory.Grothendieck

/-!
# The original mixed-universe Yoneda projection

Predicate inverse image gives actual strong Cartesian lifts in the original
category. The false-predicate functor is left adjoint to its projection.
Its complete Frobenius comparison is invertible: the false predicate is
retained and the base arrow is the inverse product comparison. This earns
the original projection's canonical exponential preservation, independently
of any equality between the original object and morphism universes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Topos.YonedaPredicateUniverseProjection

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory
open YonedaPredicateUniverseBridge

universe u v
variable {C : Type u} [Category.{v} C]

def liftDomain (predicate : Original C) {source : C} (arrow : source ⟶ predicate.base) :
    Original C := ⟨source, predicate.predicate.preimage (yoneda.map arrow)⟩

def lift (predicate : Original C) {source : C} (arrow : source ⟶ predicate.base) :
    liftDomain predicate arrow ⟶ predicate := ⟨arrow, le_rfl⟩

instance lift_stronglyCartesian (predicate : Original C) {source : C}
    (arrow : source ⟶ predicate.base) :
    (Original.projection C).IsStronglyCartesian arrow (lift predicate arrow) where
  toIsHomLift := by
    change (Original.projection C).IsHomLift ((Original.projection C).map (lift predicate arrow)) _
    infer_instance
  universal_property' := by
    intro object base supplied suppliedLift
    have := suppliedLift
    have same : base ≫ arrow = supplied.base :=
      IsHomLift.eq_of_isHomLift (Original.projection C) (base ≫ arrow) supplied
    let factor : object ⟶ liftDomain predicate arrow := {
      base := base
      entails := by
        intro world value held
        have output := supplied.entails world held
        change value ≫ supplied.base ∈ predicate.predicate.obj world at output
        change (value ≫ base) ≫ arrow ∈ predicate.predicate.obj world
        exact (Category.assoc value base arrow).symm ▸ (same.symm ▸ output) }
    refine ⟨factor, ⟨?_, ?_⟩, ?_⟩
    · change (Original.projection C).IsHomLift ((Original.projection C).map factor) factor
      infer_instance
    · exact Original.Hom.ext _ _ same
    · intro candidate properties
      have := properties.1
      apply Original.Hom.ext
      exact (IsHomLift.eq_of_isHomLift (Original.projection C) base candidate).symm

instance originalProjectionFibered : (Original.projection C).IsFibered :=
  Functor.IsFibered.of_exists_isStronglyCartesian
    (fun predicate _source arrow => ⟨liftDomain predicate arrow, lift predicate arrow, inferInstance⟩)

def falsePredicate (C : Type u) [Category.{v} C] : C ⥤ Original C where
  obj object := ⟨object, ⊥⟩
  map arrow := ⟨arrow, bot_le⟩
  map_id _object := Original.Hom.ext _ _ rfl
  map_comp _first _second := Original.Hom.ext _ _ rfl

def falseHomEquiv (object : C) (predicate : Original C) :
    ((falsePredicate C).obj object ⟶ predicate) ≃ (object ⟶ predicate.base) where
  toFun := Original.Hom.base
  invFun supplied := ⟨supplied, bot_le⟩
  left_inv _arrow := Original.Hom.ext _ _ rfl
  right_inv _ := rfl

def falseAdjunction (C : Type u) [Category.{v} C] :
    falsePredicate C ⊣ Original.projection C :=
  Adjunction.mkOfHomEquiv {
    homEquiv := falseHomEquiv
    homEquiv_naturality_left_symm := by intros; rfl
    homEquiv_naturality_right := by intros; rfl }

theorem falseAdjunction_counit (predicate : Original C) :
    ((falseAdjunction C).counit.app predicate).base = 𝟙 predicate.base := rfl

/-- Inverse arrows are admitted at both false-predicate endpoints. -/
def falseArrowIso {first second : Original C} (arrow : first ⟶ second)
    (firstFalse : first.predicate = ⊥) (secondFalse : second.predicate = ⊥)
    [IsIso arrow.base] : first ≅ second where
  hom := arrow
  inv := ⟨inv arrow.base, by rw [secondFalse, firstFalse]; exact bot_le⟩
  hom_inv_id := Original.Hom.ext _ _ (IsIso.hom_inv_id arrow.base)
  inv_hom_id := Original.Hom.ext _ _ (IsIso.inv_hom_id arrow.base)

variable [HasFiniteLimits C] [CartesianMonoidalCategory C]

theorem product_false_right (predicate : Original C) (object : C) :
    (predicate ⊗ (falsePredicate C).obj object).predicate = ⊥ := by
  apply le_antisymm
  · intro world value held
    exact (snd predicate ((falsePredicate C).obj object)).entails world held
  · exact bot_le

def frobenius (predicate : Original C) :=
  frobeniusMorphism (Original.projection C) (falseAdjunction C) predicate

theorem frobenius_base (predicate : Original C) (object : C) :
    ((frobenius predicate).natTrans.app object).base ≫
      CartesianMonoidalCategory.prodComparison (Original.projection C) predicate ((falsePredicate C).obj object) =
        𝟙 (predicate.base ⊗ object) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, CartesianMonoidalCategory.prodComparison_fst]
    change (Original.projection C).map
      ((frobenius predicate).natTrans.app object ≫ fst predicate ((falsePredicate C).obj object)) = _
    simp only [frobenius, frobeniusMorphism, NatTrans.comp_app,
      CartesianMonoidalCategory.prodComparisonNatTrans_app, Functor.whiskerLeft_app,
      curriedTensor_map_app, Category.assoc, whiskerRight_fst,
      CartesianMonoidalCategory.prodComparison_fst_assoc, Functor.map_comp]
    change fst predicate.base object ≫ ((falseAdjunction C).counit.app predicate).base =
      𝟙 (predicate.base ⊗ object) ≫ fst predicate.base object
    exact (congrArg (fun arrow => fst predicate.base object ≫ arrow)
      (falseAdjunction_counit predicate)).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)
  · rw [Category.assoc, CartesianMonoidalCategory.prodComparison_snd]
    change (Original.projection C).map
      ((frobenius predicate).natTrans.app object ≫ snd predicate ((falsePredicate C).obj object)) = _
    simp only [frobenius, frobeniusMorphism, NatTrans.comp_app,
      CartesianMonoidalCategory.prodComparisonNatTrans_app, Functor.whiskerLeft_app,
      curriedTensor_map_app, Category.assoc, whiskerRight_snd,
      CartesianMonoidalCategory.prodComparison_snd]
    change snd predicate.base object = 𝟙 (predicate.base ⊗ object) ≫ snd predicate.base object
    exact (Category.id_comp _).symm

instance frobenius_invertible (predicate : Original C) : IsIso (frobenius predicate).natTrans := by
  have (object : C) : IsIso ((frobenius predicate).natTrans.app object) := by
    let arrow := (frobenius predicate).natTrans.app object
    have baseRead : arrow.base =
        inv (CartesianMonoidalCategory.prodComparison (Original.projection C) predicate ((falsePredicate C).obj object)) := by
      apply (cancel_mono (CartesianMonoidalCategory.prodComparison
        (Original.projection C) predicate ((falsePredicate C).obj object))).mp
      exact (frobenius_base predicate object).trans (IsIso.inv_hom_id _).symm
    have : IsIso arrow.base := by rw [baseRead]; infer_instance
    exact (falseArrowIso arrow rfl (product_false_right predicate object)).isIso_hom
  exact NatIso.isIso_of_isIso_app _

variable [MonoidalClosed C]

instance originalProjectionClosed : MonoidalClosedFunctor (Original.projection C) where
  comparison_iso predicate := by
    have : IsIso (frobeniusMorphism (Original.projection C)
        (falseAdjunction C) predicate) := frobenius_invertible predicate
    exact expComparison_iso_of_frobeniusMorphism_iso (Original.projection C)
      (falseAdjunction C) predicate

def originalTheory (source : Core.LambdaTheory.{u,v}) : Core.LambdaTheory.{max u v,v} :=
  Core.LambdaTheory.ofCategory (Original source.Obj)

def originalProjectionMap (source : Core.LambdaTheory.{u,v}) :
    Core.LambdaTheoryMap (originalTheory source) source where
  functor := Original.projection source.Obj
  preservesFiniteLimits := originalProjectionFinite
  preservesExponentials := originalProjectionClosed

end Mettapedia.GSLT.Topos.YonedaPredicateUniverseProjection
