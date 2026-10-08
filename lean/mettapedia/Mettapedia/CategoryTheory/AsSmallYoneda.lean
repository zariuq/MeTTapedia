import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Subfunctor.Basic
import Mathlib.CategoryTheory.Subfunctor.Image
import Mathlib.CategoryTheory.Monoidal.Closed.Functor
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# Yoneda and predicates across independent category universes

The actual small category `AsSmall C` raises objects and arrows to the
common bound of their two universes. Presheaves are transported by
precomposition with the downward equivalence and by lifting their values.
The representable comparison retains every generalized element, and the
predicate correspondence has both inverse laws and commutes with reindexing.
Finite limits and cartesian closure are transported through the actual
category equivalence rather than supplied as new assumptions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.AsSmallYoneda

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v
variable {C : Type u} [Category.{v} C]

abbrev Small (C : Type u) [Category.{v} C] := AsSmall.{0} C

abbrev up (C : Type u) [Category.{v} C] : C ⥤ Small C := AsSmall.up

abbrev down (C : Type u) [Category.{v} C] : Small C ⥤ C := AsSmall.down

def equivalence (C : Type u) [Category.{v} C] : C ≌ Small C := AsSmall.equiv

instance upIsEquivalence : (up C).IsEquivalence := (equivalence C).isEquivalence_functor

instance downIsEquivalence : (down C).IsEquivalence := (equivalence C).isEquivalence_inverse

/-- Transport the complete presheaf, not only its object names. -/
def raisePresheaf (P : Cᵒᵖ ⥤ Type v) : (Small C)ᵒᵖ ⥤ Type (max u v) :=
  (down C).op ⋙ P ⋙ uliftFunctor.{u, v}

def raiseTransformation {P Q : Cᵒᵖ ⥤ Type v} (change : P ⟶ Q) :
    raisePresheaf P ⟶ raisePresheaf Q :=
  Functor.whiskerRight (Functor.whiskerLeft (down C).op change) uliftFunctor.{u, v}

theorem raisePresheaf_value (P : Cᵒᵖ ⥤ Type v) (X : C) (value : P.obj (op X)) :
    (ULift.up value : (raisePresheaf P).obj (op ((up C).obj X))).down = value := rfl

theorem raisePresheaf_map (P : Cᵒᵖ ⥤ Type v) {X Y : C}
    (arrow : X ⟶ Y) (value : P.obj (op Y)) :
    (raisePresheaf P).map ((up C).map arrow).op (ULift.up value) =
      ULift.up (P.map arrow.op value) := rfl

theorem raiseTransformation_readout {P Q : Cᵒᵖ ⥤ Type v} (change : P ⟶ Q)
    (X : C) (value : P.obj (op X)) :
    (raiseTransformation change).app (op ((up C).obj X)) (ULift.up value) =
      ULift.up (change.app (op X) value) := rfl

/-- The independent normalized representable and transported original
representable agree through the actual arrow/value lift. -/
def representableIso (X : C) :
    yoneda.obj ((up C).obj X) ≅ raisePresheaf (yoneda.obj X) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

theorem representable_hom_readout {X Y : C} (arrow : Y ⟶ X) :
    (representableIso X).hom.app (op ((up C).obj Y)) ((up C).map arrow) =
      ULift.up arrow := rfl

theorem representable_inv_readout {X Y : C} (arrow : Y ⟶ X) :
    (representableIso X).inv.app (op ((up C).obj Y)) (ULift.up arrow) =
      (up C).map arrow := rfl

/-- Predicate transport retains the complete original generalized element. -/
def raisePredicate {X : C} (predicate : Subfunctor (yoneda.obj X)) :
    Subfunctor (yoneda.obj ((up C).obj X)) where
  obj world := { arrow | arrow.down ∈ predicate.obj (op ((down C).obj world.unop)) }
  map change _ held := predicate.map change.unop.down.op held

/-- Read the original predicate by the upward world and arrow maps. -/
def lowerPredicate {X : Small C} (predicate : Subfunctor (yoneda.obj X)) :
    Subfunctor (yoneda.obj ((down C).obj X)) where
  obj world := { arrow | (ULift.up arrow : (up C).obj world.unop ⟶ X) ∈
    predicate.obj (op ((up C).obj world.unop)) }
  map change _ held := predicate.map ((up C).map change.unop).op held

theorem raised_membership {X Y : C} (predicate : Subfunctor (yoneda.obj X))
    (arrow : Y ⟶ X) :
    (up C).map arrow ∈ (raisePredicate predicate).obj (op ((up C).obj Y)) ↔
      arrow ∈ predicate.obj (op Y) := Iff.rfl

@[simp] theorem lower_raise {X : C} (predicate : Subfunctor (yoneda.obj X)) :
    lowerPredicate (raisePredicate predicate) = predicate := rfl

@[simp] theorem raise_lower {X : Small C} (predicate : Subfunctor (yoneda.obj X)) :
    raisePredicate (lowerPredicate predicate) = predicate := by
  ext world arrow
  rfl

def predicateEquiv (X : C) : Subfunctor (yoneda.obj X) ≃o
    Subfunctor (yoneda.obj ((up C).obj X)) where
  toFun := raisePredicate
  invFun := lowerPredicate
  left_inv := lower_raise
  right_inv := raise_lower
  map_rel_iff' := by
    intro first second
    constructor
    · intro included world arrow held
      exact included (op ((up C).obj world.unop)) held
    · intro included world arrow held
      exact included (op ((down C).obj world.unop)) held

theorem raisePredicate_reindex {X Y : C} (arrow : X ⟶ Y)
    (predicate : Subfunctor (yoneda.obj Y)) :
    raisePredicate (predicate.preimage (yoneda.map arrow)) =
      (raisePredicate predicate).preimage (yoneda.map ((up C).map arrow)) := rfl

theorem lowerPredicate_reindex {X Y : Small C} (arrow : X ⟶ Y)
    (predicate : Subfunctor (yoneda.obj Y)) :
    lowerPredicate (predicate.preimage (yoneda.map arrow)) =
      (lowerPredicate predicate).preimage (yoneda.map ((down C).map arrow)) := rfl

instance finite [HasFiniteLimits C] : HasFiniteLimits (Small C) where
  out _ := Adjunction.hasLimitsOfShape_of_equivalence (down C)

instance cartesian [HasFiniteLimits C] [CartesianMonoidalCategory C] :
    CartesianMonoidalCategory (Small C) := .ofHasFiniteProducts

instance closed [HasFiniteLimits C] [CartesianMonoidalCategory C] [MonoidalClosed C] :
    MonoidalClosed (Small C) := cartesianClosedOfEquiv (equivalence C)

end Mettapedia.CategoryTheory.AsSmallYoneda
