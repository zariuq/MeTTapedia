import Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerBaseChange
import Mettapedia.TypeTheory.PresheafSiteLift

/-!
# Full contextual power predicates on a raised site

The comparison raises and lowers worlds, actual context arrows, base
values and arguments. It has an explicit inverse on future-argument
categories, and therefore on stable predicates and compatible sections.
The new predicates live at the successor universe; no universe levels
are identified and no new upper family is claimed to be a lower image.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerSiteLift

open CategoryTheory FuturePowerFamilies
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u
variable {C : Type u} [Category.{u} C]
variable (P : Cᵒᵖ ⥤ Type u) (A : P.Elements ⥤ Type u)

def argumentsDown (point : (PresheafSiteLift.base P).Elements) :
    Arguments (PresheafSiteLift.family P A) point ⥤
      Arguments A ((PresheafSiteLift.elementsDown P).obj point) where
  obj argument := ⟨⟨(PresheafSiteLift.elementsDown P).obj argument.1.1,
    (PresheafSiteLift.elementsDown P).map argument.1.2⟩, argument.2.down⟩
  map move := ⟨⟨(PresheafSiteLift.elementsDown P).map move.1.1, by
    rw [← (PresheafSiteLift.elementsDown P).map_comp, move.1.2]⟩,
    congrArg ULift.down move.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def argumentsUp (point : (PresheafSiteLift.base P).Elements) :
    Arguments A ((PresheafSiteLift.elementsDown P).obj point) ⥤
      Arguments (PresheafSiteLift.family P A) point where
  obj argument := ⟨⟨(PresheafSiteLift.elementsUp P).obj argument.1.1,
    (PresheafSiteLift.elementsUp P).map argument.1.2⟩, ULift.up argument.2⟩
  map {first second} move := ⟨⟨(PresheafSiteLift.elementsUp P).map move.1.1, by
    exact ((PresheafSiteLift.elementsUp P).map_comp first.1.2 move.1.1).symm.trans
      (congrArg (PresheafSiteLift.elementsUp P).map move.1.2)⟩,
    congrArg ULift.up move.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem arguments_down_up (point : (PresheafSiteLift.base P).Elements) :
    PresheafSiteLift.compose (argumentsDown P A point) (argumentsUp P A point) =
      PresheafSiteLift.identity (Arguments (PresheafSiteLift.family P A) point) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem arguments_up_down (point : (PresheafSiteLift.base P).Elements) :
    PresheafSiteLift.compose (argumentsUp P A point) (argumentsDown P A point) =
      PresheafSiteLift.identity (Arguments A ((PresheafSiteLift.elementsDown P).obj point)) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

def lower (point : (PresheafSiteLift.base P).Elements)
    (predicate : Predicate (PresheafSiteLift.family P A) point) :
    Predicate A ((PresheafSiteLift.elementsDown P).obj point) where
  holds argument := predicate.holds ((argumentsUp P A point).obj argument)
  closed move available := predicate.closed ((argumentsUp P A point).map move) available

def raise (point : (PresheafSiteLift.base P).Elements)
    (predicate : Predicate A ((PresheafSiteLift.elementsDown P).obj point)) :
    Predicate (PresheafSiteLift.family P A) point where
  holds argument := predicate.holds ((argumentsDown P A point).obj argument)
  closed move available := predicate.closed ((argumentsDown P A point).map move) available

theorem lower_raise (point : (PresheafSiteLift.base P).Elements)
    (predicate : Predicate A ((PresheafSiteLift.elementsDown P).obj point)) :
    lower P A point (raise P A point predicate) = predicate := by
  apply Predicate.ext
  intro argument
  exact Iff.rfl

theorem raise_lower (point : (PresheafSiteLift.base P).Elements)
    (predicate : Predicate (PresheafSiteLift.family P A) point) :
    raise P A point (lower P A point predicate) = predicate := by
  apply Predicate.ext
  intro argument
  exact Iff.rfl

def predicateEquiv (point : (PresheafSiteLift.base P).Elements) :
    Predicate (PresheafSiteLift.family P A) point ≃
      Predicate A ((PresheafSiteLift.elementsDown P).obj point) where
  toFun := lower P A point
  invFun := raise P A point
  left_inv := raise_lower P A point
  right_inv := lower_raise P A point

theorem lower_restrict {first second : (PresheafSiteLift.base P).Elements} (step : first ⟶ second)
    (predicate : Predicate (PresheafSiteLift.family P A) first) :
    lower P A second (FuturePowerFamilies.restrict (PresheafSiteLift.family P A) step predicate) =
      FuturePowerFamilies.restrict A ((PresheafSiteLift.elementsDown P).map step)
        (lower P A first predicate) := by
  apply Predicate.ext
  intro argument
  exact Iff.rfl

theorem raise_restrict {first second : (PresheafSiteLift.base P).Elements} (step : first ⟶ second)
    (predicate : Predicate A ((PresheafSiteLift.elementsDown P).obj first)) :
    raise P A second
        (FuturePowerFamilies.restrict A ((PresheafSiteLift.elementsDown P).map step) predicate) =
      FuturePowerFamilies.restrict (PresheafSiteLift.family P A) step (raise P A first predicate) := by
  apply Predicate.ext
  intro argument
  exact Iff.rfl

def comparison : NatTrans (FuturePowerFamilies.family (PresheafSiteLift.family P A))
    (PresheafSiteLift.family P (FuturePowerFamilies.family A)) where
  app point := TypeCat.ofHom fun predicate => ULift.up (lower P A point predicate)
  naturality _ _ step := by
    apply ConcreteCategory.hom_ext
    intro predicate
    exact congrArg ULift.up (lower_restrict P A step predicate)

def inverse : NatTrans (PresheafSiteLift.family P (FuturePowerFamilies.family A))
    (FuturePowerFamilies.family (PresheafSiteLift.family P A)) where
  app point := TypeCat.ofHom fun predicate => raise P A point predicate.down
  naturality _ _ step := by
    apply ConcreteCategory.hom_ext
    intro predicate
    exact raise_restrict P A step predicate.down

theorem comparison_left : compose (comparison P A) (inverse P A) =
    identity (FuturePowerFamilies.family (PresheafSiteLift.family P A)) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  exact raise_lower P A point

theorem comparison_right : compose (inverse P A) (comparison P A) =
    identity (PresheafSiteLift.family P (FuturePowerFamilies.family A)) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro predicate
  exact congrArg ULift.up (lower_raise P A point predicate.down)

def sectionEquiv : (FuturePowerFamilies.family A).sections ≃
    (FuturePowerFamilies.family (PresheafSiteLift.family P A)).sections where
  toFun term := ⟨fun point => raise P A point (term.val ((PresheafSiteLift.elementsDown P).obj point)), by
    intro first second step
    exact (raise_restrict P A step _).symm.trans
      (congrArg (raise P A second) (term.property ((PresheafSiteLift.elementsDown P).map step)))⟩
  invFun term := ⟨fun point => lower P A ((PresheafSiteLift.elementsUp P).obj point)
      (term.val ((PresheafSiteLift.elementsUp P).obj point)), by
    intro first second step
    exact (lower_restrict P A ((PresheafSiteLift.elementsUp P).map step) _).symm.trans
      (congrArg (lower P A ((PresheafSiteLift.elementsUp P).obj second))
        (term.property ((PresheafSiteLift.elementsUp P).map step)))⟩
  left_inv term := Subtype.ext (funext fun point =>
    lower_raise P A ((PresheafSiteLift.elementsUp P).obj point) (term.val point))
  right_inv term := Subtype.ext (funext fun point => raise_lower P A point (term.val point))

def raiseStable (predicate : StablePredicate A) : StablePredicate (PresheafSiteLift.family P A) where
  holds argument := predicate.holds ((PresheafSiteLift.displayedElementsDown P A).obj argument)
  closed move available := predicate.closed
    ((PresheafSiteLift.displayedElementsDown P A).map move) available

theorem classifier_square (predicate : StablePredicate A) :
    sectionEquiv P A (classify A predicate) =
      classify (PresheafSiteLift.family P A) (raiseStable P A predicate) := by
  apply Subtype.ext
  funext point
  apply Predicate.ext
  intro argument
  change predicate.holds ⟨(PresheafSiteLift.elementsDown P).obj argument.1.1, argument.2.down⟩ ↔ _
  exact Iff.rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerSiteLift
