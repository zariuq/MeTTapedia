import Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerSiteLift
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualPowerBaseChange
import Mettapedia.TypeTheory.MaterialSets.Hypersets.UniverseLift

/-!
# Material full-future power comparison across the successor site

Faithful labels on the lower future arguments are lifted through the actual
inverse of raised future arguments. The independently constructed upper
stable-predicate model then has exactly the lifted old values and carrier.
Its decoder preserves the entire predicate and all argument membership.

Fresh upper labels still provide the semantic decoder comparison, but
literal material value equality is asserted only for transported labels.
This concerns translated interpreted families, not all successor families.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualPowerSiteLift

open CategoryTheory FuturePowerFamilies ContextualPowerFamilies
open Mettapedia.GSLT.Topos.ConstructivePresheaf

universe u
variable {C : Type u} [Category.{u} C]
variable (P : Cᵒᵖ ⥤ Type u) (A : P.Elements ⥤ Type u)
variable (point : (PresheafSiteLift.base P).Elements)
variable (coding : ArgumentCoding (Arguments A ((PresheafSiteLift.elementsDown P).obj point)))

def codingAbove : ArgumentCoding (Arguments (PresheafSiteLift.family P A) point) where
  graph argument := (coding.graph ((FuturePowerSiteLift.argumentsDown P A point).obj argument)).lift
  injective := by
    intro first second same
    have lowerSame := coding.injective (HSet.lift_injective same)
    exact congrArg (FuturePowerSiteLift.argumentsUp P A point).obj lowerSame

theorem codingAbove_reading (argument : Arguments (PresheafSiteLift.family P A) point) :
    (codingAbove P A point coding).reading argument =
      HSet.lift (coding.reading ((FuturePowerSiteLift.argumentsDown P A point).obj argument)) := rfl

def memberEquiv
    (upperCoding : ArgumentCoding (Arguments (PresheafSiteLift.family P A) point)) :
    ContextualPowerBaseChange.Member
        (predicateModel (PresheafSiteLift.family P A) point upperCoding).carrier ≃
      ContextualPowerBaseChange.Member
        (predicateModel A ((PresheafSiteLift.elementsDown P).obj point) coding).carrier :=
  (predicateModel (PresheafSiteLift.family P A) point upperCoding).decode.trans
    ((FuturePowerSiteLift.predicateEquiv P A point).trans
      (predicateModel A ((PresheafSiteLift.elementsDown P).obj point) coding).decode.symm)

theorem memberEquiv_truth
    (upperCoding : ArgumentCoding (Arguments (PresheafSiteLift.family P A) point))
    (member : ContextualPowerBaseChange.Member
      (predicateModel (PresheafSiteLift.family P A) point upperCoding).carrier)
    (argument : Arguments (PresheafSiteLift.family P A) point) :
    coding.reading ((FuturePowerSiteLift.argumentsDown P A point).obj argument) ∈
        (memberEquiv P A point coding upperCoding member).val ↔
      upperCoding.reading argument ∈ member.val := by
  change coding.reading ((FuturePowerSiteLift.argumentsDown P A point).obj argument) ∈
    predicateValue A ((PresheafSiteLift.elementsDown P).obj point) coding
      (FuturePowerSiteLift.lower P A point
        ((predicateModel (PresheafSiteLift.family P A) point upperCoding).decode member)) ↔ _
  rw [predicateValue_entry]
  exact predicateModel_decode_truth (PresheafSiteLift.family P A) point upperCoding member argument

theorem memberEquiv_decode
    (upperCoding : ArgumentCoding (Arguments (PresheafSiteLift.family P A) point))
    (member : ContextualPowerBaseChange.Member
      (predicateModel (PresheafSiteLift.family P A) point upperCoding).carrier) :
    (predicateModel A ((PresheafSiteLift.elementsDown P).obj point) coding).decode
        (memberEquiv P A point coding upperCoding member) =
      FuturePowerSiteLift.lower P A point
        ((predicateModel (PresheafSiteLift.family P A) point upperCoding).decode member) :=
  Equiv.apply_symm_apply _ _

theorem predicateValue_above
    (predicate : Predicate A ((PresheafSiteLift.elementsDown P).obj point)) :
    predicateValue (PresheafSiteLift.family P A) point (codingAbove P A point coding)
        (FuturePowerSiteLift.raise P A point predicate) =
      HSet.lift (predicateValue A ((PresheafSiteLift.elementsDown P).obj point) coding predicate) := by
  apply HSet.ext
  intro value
  rw [predicateValue, LabelSubsets.mem_subsetGraph, HSet.mem_lift_iff]
  constructor
  · rintro ⟨argument, available, same⟩
    refine ⟨coding.reading ((FuturePowerSiteLift.argumentsDown P A point).obj argument), ?_, same⟩
    exact (predicateValue_entry A _ coding predicate _).mpr available
  · rintro ⟨lowerValue, available, same⟩
    obtain ⟨argument, truth, label⟩ := (LabelSubsets.mem_subsetGraph coding predicate.holds lowerValue).mp available
    refine ⟨(FuturePowerSiteLift.argumentsUp P A point).obj argument, truth, ?_⟩
    change HSet.lift (coding.reading argument) = value
    exact (congrArg HSet.lift label).trans same

theorem predicateCarrier_above :
    (predicateModel (PresheafSiteLift.family P A) point (codingAbove P A point coding)).carrier =
      HSet.lift (predicateModel A ((PresheafSiteLift.elementsDown P).obj point) coding).carrier := by
  apply HSet.ext
  intro value
  constructor
  · intro available
    let member : ContextualPowerBaseChange.Member
      (predicateModel (PresheafSiteLift.family P A) point (codingAbove P A point coding)).carrier :=
        ⟨value, available⟩
    let oldPredicate := FuturePowerSiteLift.lower P A point
      ((predicateModel (PresheafSiteLift.family P A) point (codingAbove P A point coding)).decode member)
    have restored := FuturePowerSiteLift.raise_lower P A point
      ((predicateModel (PresheafSiteLift.family P A) point (codingAbove P A point coding)).decode member)
    have represented := congrArg Subtype.val
      ((predicateModel (PresheafSiteLift.family P A) point
        (codingAbove P A point coding)).decode.symm_apply_apply member)
    change predicateValue (PresheafSiteLift.family P A) point (codingAbove P A point coding)
      ((predicateModel (PresheafSiteLift.family P A) point (codingAbove P A point coding)).decode member) = value
        at represented
    rw [← restored, predicateValue_above] at represented
    exact HSet.mem_lift_iff.mpr ⟨predicateValue A _ coding oldPredicate,
      predicateValue_mem A _ coding oldPredicate, represented⟩
  · intro available
    obtain ⟨lowerValue, lowerMember, same⟩ := HSet.mem_lift_iff.mp available
    let member : ContextualPowerBaseChange.Member
      (predicateModel A ((PresheafSiteLift.elementsDown P).obj point) coding).carrier := ⟨lowerValue, lowerMember⟩
    let oldPredicate := (predicateModel A ((PresheafSiteLift.elementsDown P).obj point) coding).decode member
    have represented := congrArg Subtype.val
      ((predicateModel A ((PresheafSiteLift.elementsDown P).obj point) coding).decode.symm_apply_apply member)
    change predicateValue A ((PresheafSiteLift.elementsDown P).obj point) coding oldPredicate = lowerValue
      at represented
    have upperMember := predicateValue_mem (PresheafSiteLift.family P A) point
      (codingAbove P A point coding) (FuturePowerSiteLift.raise P A point oldPredicate)
    rw [predicateValue_above, represented, same] at upperMember
    exact upperMember

theorem memberEquiv_above_value
    (member : ContextualPowerBaseChange.Member
      (predicateModel (PresheafSiteLift.family P A) point (codingAbove P A point coding)).carrier) :
    HSet.lift (memberEquiv P A point coding (codingAbove P A point coding) member).val = member.val := by
  change HSet.lift (predicateValue A ((PresheafSiteLift.elementsDown P).obj point) coding
    (FuturePowerSiteLift.lower P A point
      ((predicateModel (PresheafSiteLift.family P A) point (codingAbove P A point coding)).decode member))) = member.val
  rw [← predicateValue_above, FuturePowerSiteLift.raise_lower]
  exact congrArg Subtype.val
    ((predicateModel (PresheafSiteLift.family P A) point
      (codingAbove P A point coding)).decode.symm_apply_apply member)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualPowerSiteLift
