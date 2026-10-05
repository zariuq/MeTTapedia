import Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerBaseChange
import Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerSiteLift

/-!
# A substitution that omits a genuine future

Restricting a family from the natural-number chain to its initial world
erases a stable future predicate that differs from false. The missing
future also witnesses failure of outgoing argument lifting. This functor
is deliberately not the map of elements of a presheaf substitution.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerBaseChangeControls

open CategoryTheory FuturePowerFamilies FuturePowerBaseChange
open PowerClassPresheafBaseChange
open Mettapedia.GSLT.Topos.ConstructivePresheaf

abbrev One := Fin 1

def origin : One := ⟨0, Nat.zero_lt_one⟩

def currentOnly : One ⥤ Nat where
  obj _ := 0
  map _ := homOfLE (Nat.le_refl 0)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

def domain : Nat ⥤ Type where
  obj _ := PUnit
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def later : Predicate domain 0 where
  holds argument := 0 < argument.1.1
  closed move available := Nat.lt_of_lt_of_le available (leOfHom move.1.1)

def nowhere : Predicate domain 0 where
  holds _ := False
  closed _ unavailable := False.elim unavailable

def omittedFuture : Arguments domain 0 :=
  ⟨⟨1, homOfLE (Nat.zero_le 1)⟩, PUnit.unit⟩

theorem later_at_omitted : later.holds omittedFuture := Nat.zero_lt_one

theorem later_ne_nowhere : later ≠ nowhere := by
  intro same
  have truth := congrArg (fun predicate : Predicate domain 0 => predicate.holds omittedFuture) same
  exact Eq.mp truth later_at_omitted

theorem pullback_loses_future :
    pullback currentOnly domain origin later = pullback currentOnly domain origin nowhere := by
  apply Predicate.ext
  intro argument
  change (0 < 0) ↔ False
  exact ⟨fun impossible => (Nat.lt_irrefl 0) impossible, False.elim⟩

theorem pullback_not_injective : ¬ Function.Injective (pullback currentOnly domain origin) :=
  fun injective => later_ne_nowhere (injective pullback_loses_future)

theorem future_not_covered :
    ¬ ∃ argument, (argumentMap currentOnly domain origin).obj argument = omittedFuture := by
  rintro ⟨argument, same⟩
  have stage := congrArg (fun future : Arguments domain 0 => future.1.1) same
  exact Nat.zero_ne_one stage

theorem no_argument_coverage :
    ¬ Function.Surjective (argumentMap currentOnly domain origin).obj :=
  fun covers => future_not_covered (covers omittedFuture)

def presentArgument : Arguments (restrict currentOnly domain) origin :=
  current (restrict currentOnly domain) origin PUnit.unit

def presentToOmitted : (argumentMap currentOnly domain origin).obj presentArgument ⟶ omittedFuture :=
  ⟨⟨homOfLE (Nat.zero_le 1), Subsingleton.elim _ _⟩, rfl⟩

theorem no_argument_outgoing_lifts : ¬ OutgoingLifts (argumentMap currentOnly domain origin) := by
  intro lifts
  obtain ⟨argument, _, same⟩ := lifts presentArgument presentToOmitted
  exact future_not_covered ⟨argument, same⟩

def laterStable : StablePredicate domain where
  holds argument := 0 < argument.1
  closed move available := Nat.lt_of_lt_of_le available (leOfHom move.1)

def nowhereStable : StablePredicate domain where
  holds _ := False
  closed _ unavailable := False.elim unavailable

theorem classified_sections_differ : classify domain laterStable ≠ classify domain nowhereStable := by
  intro same
  have truth := congrArg (fun term : (family domain).sections =>
    (term.val 0).holds omittedFuture) same
  exact Eq.mp truth (show 0 < 1 from Nat.zero_lt_one)

theorem pulled_classified_sections_agree :
    pullSection currentOnly domain (classify domain laterStable) =
      pullSection currentOnly domain (classify domain nowhereStable) := by
  apply Subtype.ext
  funext point
  apply Predicate.ext
  intro argument
  change (0 < 0) ↔ False
  exact ⟨fun impossible => (Nat.lt_irrefl 0) impossible, False.elim⟩

namespace Growing

open PowerClassPresheafDescent.Controls

def family : growingTarget.Elements ⥤ Type where
  obj point := Fin (stageIndex point.1 + 1)
  map step := TypeCat.ofHom (Fin.castLE (Nat.succ_le_succ (growthLe step.1)))
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro argument
    exact Fin.ext rfl
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro argument
    exact Fin.ext rfl

def sourcePoint : growingSource.Elements :=
  ⟨world 0, stageValue 0 0 Nat.zero_lt_one true⟩

def targetPoint : growingTarget.Elements := (PowerClassPresheafProducts.elementMap growingObservation).obj sourcePoint

def nextPoint : growingTarget.Elements := ⟨world 1, ⟨0, Nat.zero_lt_succ 1⟩⟩

def extension : targetPoint ⟶ nextPoint :=
  ⟨(homOfLE (Nat.zero_le 1)).op.op, Fin.ext rfl⟩

def newArgument : Arguments family targetPoint :=
  ⟨⟨nextPoint, extension⟩, ⟨1, Nat.lt_succ_self 1⟩⟩

/-- This predicate detects a newly available dependent argument, not only
the advancement of its world. Actual argument transport preserves its index. -/
def positiveIndex : Predicate family targetPoint where
  holds argument := 0 < argument.2.val
  closed {first second} move available := by
    have same := congrArg Fin.val move.2
    change first.2.val = second.2.val at same
    exact same ▸ available

theorem new_argument_available : positiveIndex.holds newArgument := Nat.zero_lt_one

theorem no_present_argument (argument : family.obj targetPoint) :
    ¬ positiveIndex.holds (current family targetPoint argument) := by
  intro available
  change 0 < argument.val at available
  have small : argument.val < 1 := argument.isLt
  have zero : argument.val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ small)
  exact Nat.lt_irrefl 0 (zero ▸ available)

/-- The nonidentity observation erases the source tag but retains every
future argument from this particular source position, including the new one. -/
theorem new_argument_has_constructed_source :
    (argumentMap (PowerClassPresheafProducts.elementMap growingObservation) family sourcePoint).obj
      ((argumentBack growingObservation family sourcePoint).obj newArgument) = newArgument :=
  argument_right growingObservation family sourcePoint newArgument

theorem new_argument_truth_preserved :
    (substitutionEquiv growingObservation family sourcePoint positiveIndex).holds
      ((argumentBack growingObservation family sourcePoint).obj newArgument) := by
  change positiveIndex.holds
    ((argumentMap (PowerClassPresheafProducts.elementMap growingObservation) family sourcePoint).obj
      ((argumentBack growingObservation family sourcePoint).obj newArgument))
  exact (new_argument_has_constructed_source.symm ▸ new_argument_available)

theorem full_future_roundtrip (predicate : Predicate family targetPoint) :
    (substitutionEquiv growingObservation family sourcePoint).symm
      (substitutionEquiv growingObservation family sourcePoint predicate) = predicate :=
  (substitutionEquiv growingObservation family sourcePoint).symm_apply_apply predicate

def raisedPoint : (PresheafSiteLift.base growingTarget).Elements :=
  (PresheafSiteLift.elementsUp growingTarget).obj targetPoint

def raisedArgument : Arguments (PresheafSiteLift.family growingTarget family) raisedPoint :=
  (FuturePowerSiteLift.argumentsUp growingTarget family raisedPoint).obj newArgument

def raisedPredicate : Predicate (PresheafSiteLift.family growingTarget family) raisedPoint :=
  FuturePowerSiteLift.raise growingTarget family raisedPoint positiveIndex

theorem raised_new_argument_truth : raisedPredicate.holds raisedArgument := new_argument_available

theorem raised_no_present_argument
    (argument : (PresheafSiteLift.family growingTarget family).obj raisedPoint) :
    ¬ raisedPredicate.holds (current (PresheafSiteLift.family growingTarget family) raisedPoint argument) :=
  no_present_argument argument.down

def raisedSourcePoint : (PresheafSiteLift.base growingSource).Elements :=
  (PresheafSiteLift.elementsUp growingSource).obj sourcePoint

theorem raised_substitution_new_argument_truth :
    (substitutionEquiv (PresheafSiteLift.raiseChange growingObservation)
      (PresheafSiteLift.family growingTarget family) raisedSourcePoint raisedPredicate).holds
        ((argumentBack (PresheafSiteLift.raiseChange growingObservation)
          (PresheafSiteLift.family growingTarget family) raisedSourcePoint).obj raisedArgument) := by
  change raisedPredicate.holds
    ((argumentMap (PowerClassPresheafProducts.elementMap (PresheafSiteLift.raiseChange growingObservation))
      (PresheafSiteLift.family growingTarget family) raisedSourcePoint).obj
        ((argumentBack (PresheafSiteLift.raiseChange growingObservation)
          (PresheafSiteLift.family growingTarget family) raisedSourcePoint).obj raisedArgument))
  exact (argument_right (PresheafSiteLift.raiseChange growingObservation)
    (PresheafSiteLift.family growingTarget family) raisedSourcePoint raisedArgument).symm ▸ raised_new_argument_truth

end Growing

end Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerBaseChangeControls
