import Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerBaseChange
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualPowerFamilies

/-!+# Material decoding under full future base change

The predicate comparison acts on actual members of the constructed material
power carriers. Arbitrary faithful future labels give a decoder equivalence
and exact truth preservation; they need not give equal material sets.

Transporting the original labels through the constructed inverse future
categories gives equality of the whole material values and carriers.
This equality uses coverage of complete future arguments, not only present
arguments, and never decodes a context or arrow from its material label.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualPowerBaseChange

open CategoryTheory FuturePowerFamilies FuturePowerBaseChange
open ContextualPowerFamilies ContextualGeneratedUniverse
open PowerClassPresheafBaseChange
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u

abbrev Member (carrier : HSet.{u}) := {value : HSet.{u} // value ∈ carrier}

section ArbitraryFunctor

variable {D E : Type u} [Category.{u} D] [Category.{u} E]
variable (change : D ⥤ E) (A : E ⥤ Type u) (point : D)
variable (oldCoding : ArgumentCoding (Arguments A (change.obj point)))
variable (newCoding : ArgumentCoding (Arguments (restrict change A) point))

def pullMember (member : Member (predicateModel A (change.obj point) oldCoding).carrier) :
    Member (predicateModel (restrict change A) point newCoding).carrier :=
  (predicateModel (restrict change A) point newCoding).decode.symm
    (pullback change A point ((predicateModel A (change.obj point) oldCoding).decode member))

theorem pullMember_truth (member : Member (predicateModel A (change.obj point) oldCoding).carrier)
    (argument : Arguments (restrict change A) point) :
    newCoding.reading argument ∈ (pullMember change A point oldCoding newCoding member).val ↔
      oldCoding.reading ((argumentMap change A point).obj argument) ∈ member.val := by
  change newCoding.reading argument ∈
    predicateValue (restrict change A) point newCoding
      (pullback change A point ((predicateModel A (change.obj point) oldCoding).decode member)) ↔ _
  exact (predicateValue_entry _ _ _ _ argument).trans
    (predicateModel_decode_truth A (change.obj point) oldCoding member
      ((argumentMap change A point).obj argument))

theorem pullMember_encode (predicate : Predicate A (change.obj point)) :
    pullMember change A point oldCoding newCoding
        ((predicateModel A (change.obj point) oldCoding).decode.symm predicate) =
      (predicateModel (restrict change A) point newCoding).decode.symm
        (pullback change A point predicate) := by
  unfold pullMember
  rw [Equiv.apply_symm_apply]

end ArbitraryFunctor

section PresheafSubstitution

open PowerClassPresheafProducts

variable {C : Type u} [Category.{u} C]
variable {P Q : Cᵒᵖ ⥤ Type u} (change : NatTrans Q P)
variable (A : P.Elements ⥤ Type u) (point : Q.Elements)
variable (oldCoding : ArgumentCoding (Arguments A ((elementMap change).obj point)))
variable (newCoding : ArgumentCoding (Arguments (PowerClassPresheafProducts.reindex change A) point))

/-- Both endpoints are actual material membership fibres. The middle
comparison retains the complete predicate rather than its present support. -/
def memberEquiv :
    Member (predicateModel A ((elementMap change).obj point) oldCoding).carrier ≃
      Member (predicateModel (PowerClassPresheafProducts.reindex change A) point newCoding).carrier :=
  (predicateModel A ((elementMap change).obj point) oldCoding).decode.trans
    ((substitutionEquiv change A point).trans
      (predicateModel (PowerClassPresheafProducts.reindex change A) point newCoding).decode.symm)

theorem memberEquiv_truth
    (member : Member (predicateModel A ((elementMap change).obj point) oldCoding).carrier)
    (argument : Arguments (PowerClassPresheafProducts.reindex change A) point) :
    newCoding.reading argument ∈ (memberEquiv change A point oldCoding newCoding member).val ↔
      oldCoding.reading ((argumentMap (elementMap change) A point).obj argument) ∈ member.val :=
  pullMember_truth (elementMap change) A point oldCoding newCoding member argument

theorem memberEquiv_decode
    (member : Member (predicateModel A ((elementMap change).obj point) oldCoding).carrier) :
    (predicateModel (PowerClassPresheafProducts.reindex change A) point newCoding).decode
        (memberEquiv change A point oldCoding newCoding member) =
      substitutionEquiv change A point
        ((predicateModel A ((elementMap change).obj point) oldCoding).decode member) :=
  Equiv.apply_symm_apply _ _

theorem memberEquiv_encode (predicate : Predicate A ((elementMap change).obj point)) :
    memberEquiv change A point oldCoding newCoding
        ((predicateModel A ((elementMap change).obj point) oldCoding).decode.symm predicate) =
      (predicateModel (PowerClassPresheafProducts.reindex change A) point newCoding).decode.symm
        (substitutionEquiv change A point predicate) :=
  pullMember_encode (elementMap change) A point oldCoding newCoding predicate

/-- Fresh lower labels are replaced by the original labels of their
complete mapped future arguments. Faithfulness is proved from the actual
constructed inverse on contexts and arguments. -/
def codingUnder : ArgumentCoding (Arguments (PowerClassPresheafProducts.reindex change A) point) where
  graph argument := oldCoding.graph ((argumentMap (elementMap change) A point).obj argument)
  injective _ _ same := argument_injective change A point (oldCoding.injective same)

theorem codingUnder_reading
    (argument : Arguments (PowerClassPresheafProducts.reindex change A) point) :
    (codingUnder change A point oldCoding).reading argument =
      oldCoding.reading ((argumentMap (elementMap change) A point).obj argument) := rfl

theorem predicateValue_under (predicate : Predicate A ((elementMap change).obj point)) :
    predicateValue (PowerClassPresheafProducts.reindex change A) point
        (codingUnder change A point oldCoding) (substitutionEquiv change A point predicate) =
      predicateValue A ((elementMap change).obj point) oldCoding predicate := by
  apply HSet.ext
  intro value
  rw [predicateValue, predicateValue, LabelSubsets.mem_subsetGraph, LabelSubsets.mem_subsetGraph]
  constructor
  · rintro ⟨argument, available, same⟩
    exact ⟨(argumentMap (elementMap change) A point).obj argument, available, same⟩
  · rintro ⟨argument, available, same⟩
    let lower := (argumentBack change A point).obj argument
    have image : (argumentMap (elementMap change) A point).obj lower = argument :=
      argument_right change A point argument
    refine ⟨lower, ?_, ?_⟩
    · change predicate.holds ((argumentMap (elementMap change) A point).obj lower)
      exact image.symm ▸ available
    · change oldCoding.reading ((argumentMap (elementMap change) A point).obj lower) = value
      exact (congrArg oldCoding.reading image).trans same

theorem predicateCarrier_under :
    (predicateModel (PowerClassPresheafProducts.reindex change A) point
        (codingUnder change A point oldCoding)).carrier =
      (predicateModel A ((elementMap change).obj point) oldCoding).carrier := by
  apply HSet.ext
  intro value
  constructor
  · intro member
    let lower : Member (predicateModel (PowerClassPresheafProducts.reindex change A) point
        (codingUnder change A point oldCoding)).carrier := ⟨value, member⟩
    let predicate := (substitutionEquiv change A point).symm
      ((predicateModel (PowerClassPresheafProducts.reindex change A) point
        (codingUnder change A point oldCoding)).decode lower)
    have lowerSame := (substitutionEquiv change A point).apply_symm_apply
      ((predicateModel (PowerClassPresheafProducts.reindex change A) point
        (codingUnder change A point oldCoding)).decode lower)
    have valueSame := congrArg Subtype.val
      ((predicateModel (PowerClassPresheafProducts.reindex change A) point
        (codingUnder change A point oldCoding)).decode.symm_apply_apply lower)
    change predicateValue (PowerClassPresheafProducts.reindex change A) point
      (codingUnder change A point oldCoding)
        ((predicateModel (PowerClassPresheafProducts.reindex change A) point
          (codingUnder change A point oldCoding)).decode lower) = value at valueSame
    rw [← lowerSame, predicateValue_under change A point oldCoding predicate] at valueSame
    exact valueSame ▸ predicateValue_mem A ((elementMap change).obj point) oldCoding predicate
  · intro member
    let upper : Member (predicateModel A ((elementMap change).obj point) oldCoding).carrier := ⟨value, member⟩
    let predicate := (predicateModel A ((elementMap change).obj point) oldCoding).decode upper
    have valueSame := congrArg Subtype.val
      ((predicateModel A ((elementMap change).obj point) oldCoding).decode.symm_apply_apply upper)
    change predicateValue A ((elementMap change).obj point) oldCoding predicate = value at valueSame
    have lowerMember := predicateValue_mem (PowerClassPresheafProducts.reindex change A) point
      (codingUnder change A point oldCoding) (substitutionEquiv change A point predicate)
    rw [predicateValue_under, valueSame] at lowerMember
    exact lowerMember

theorem memberEquiv_under_value
    (member : Member (predicateModel A ((elementMap change).obj point) oldCoding).carrier) :
    (memberEquiv change A point oldCoding (codingUnder change A point oldCoding) member).val = member.val := by
  change predicateValue (PowerClassPresheafProducts.reindex change A) point
    (codingUnder change A point oldCoding)
      (substitutionEquiv change A point
        ((predicateModel A ((elementMap change).obj point) oldCoding).decode member)) = member.val
  rw [predicateValue_under]
  exact congrArg Subtype.val
    ((predicateModel A ((elementMap change).obj point) oldCoding).decode.symm_apply_apply member)

end PresheafSubstitution

section MaterialFamilies

variable {C : Type u} [Category.{u} C]
variable {context other : LabelledContext C}
variable (domain : MaterialFamily context)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))
variable (change : NatTrans other.base context.base)

/-- A full power family formed with deliberately transported future labels.
The family functor is freshly formed on the restricted domain. -/
def powerUnder : MaterialFamily other where
  family := FuturePowerFamilies.family (domain.reindex change).family
  model point := predicateModel (domain.reindex change).family point
    (codingUnder change domain.family point
      (domain.futureCoding arrows ((PowerClassPresheafProducts.elementMap change).obj point)))

def powerComparison : NatTrans ((power domain arrows).reindex change).family
    (powerUnder domain arrows change).family := substitutionComparison change domain.family

def powerComparisonInverse : NatTrans (powerUnder domain arrows change).family
    ((power domain arrows).reindex change).family := substitutionInverse change domain.family

theorem powerUnder_value (point : other.base.Elements)
    (predicate : ((power domain arrows).reindex change).family.obj point) :
    ((powerUnder domain arrows change).model point).value
        ((powerComparison domain arrows change).app point predicate) =
      (((power domain arrows).reindex change).model point).value predicate :=
  predicateValue_under change domain.family point
    (domain.futureCoding arrows ((PowerClassPresheafProducts.elementMap change).obj point)) predicate

theorem powerUnder_carrier (point : other.base.Elements) :
    ((powerUnder domain arrows change).model point).carrier =
      (((power domain arrows).reindex change).model point).carrier :=
  predicateCarrier_under change domain.family point
    (domain.futureCoding arrows ((PowerClassPresheafProducts.elementMap change).obj point))

theorem powerUnder_section_value (term : ((power domain arrows).reindex change).family.sections)
    (point : other.base.Elements) :
    ((powerUnder domain arrows change).model point).value
        ((substitutionSectionEquiv change domain.family term).val point) =
      (((power domain arrows).reindex change).model point).value (term.val point) :=
  powerUnder_value domain arrows change point (term.val point)

/-- Actual fresh dictionaries retain full future truth, even when their
labels give different material values from the transported dictionaries. -/
def freshPowerMemberEquiv
    (newArrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))
    (point : other.base.Elements) :
    Member (((power domain arrows).reindex change).model point).carrier ≃
      Member ((power (domain.reindex change) newArrows).model point).carrier :=
  memberEquiv change domain.family point
    (domain.futureCoding arrows ((PowerClassPresheafProducts.elementMap change).obj point))
    ((domain.reindex change).futureCoding newArrows point)

theorem freshPowerMember_truth
    (newArrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))
    (point : other.base.Elements)
    (member : Member (((power domain arrows).reindex change).model point).carrier)
    (argument : Arguments (domain.reindex change).family point) :
    ((domain.reindex change).futureCoding newArrows point).reading argument ∈
        (freshPowerMemberEquiv domain arrows change newArrows point member).val ↔
      (domain.futureCoding arrows ((PowerClassPresheafProducts.elementMap change).obj point)).reading
        ((argumentMap (PowerClassPresheafProducts.elementMap change) domain.family point).obj argument) ∈
          member.val :=
  memberEquiv_truth change domain.family point
    (domain.futureCoding arrows ((PowerClassPresheafProducts.elementMap change).obj point))
    ((domain.reindex change).futureCoding newArrows point) member argument

end MaterialFamilies

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualPowerBaseChange
