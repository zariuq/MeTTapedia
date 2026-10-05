import Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerOperations
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualPowerFamilies

/-!
# Material singleton and union for contextual power families

The constructed singleton and union operations act on actual material
members through the independently proved fibre decoders. Their entry laws
retain every context and arrow label. Union tests an admitted predicate's
current truth at the retained future target; it is not identified with bare
union of the outer tagged label set.

Both material operations commute with the actual member restriction maps.
All graph carriers stay at the interpreted family's graph bound; member
types inhabit the successor universe.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualPowerOperations

open CategoryTheory
open ContextualGeneratedUniverse
open ContextualPowerFamilies
open FuturePowerFamilies
open FuturePowerOperations
open Mettapedia.TypeTheory.ContextualWitnessCover

universe u
variable {C : Type u} [Category.{u} C] {context : LabelledContext C}
variable (domain : MaterialFamily context)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))

def singletonMember (point : context.base.Elements)
    (member : {value : HSet.{u} // value ∈ (domain.model point).carrier}) :
    {value : HSet.{u} // value ∈ ((power domain arrows).model point).carrier} :=
  ((power domain arrows).model point).decode.symm
    (singleton domain.family point ((domain.model point).decode member))

theorem singletonMember_decode (point : context.base.Elements)
    (member : {value : HSet.{u} // value ∈ (domain.model point).carrier}) :
    ((power domain arrows).model point).decode (singletonMember domain arrows point member) =
      singleton domain.family point ((domain.model point).decode member) :=
  Equiv.apply_symm_apply _ _

theorem singletonMember_truth (point : context.base.Elements)
    (member : {value : HSet.{u} // value ∈ (domain.model point).carrier})
    (future : Arguments domain.family point) :
    (domain.futureCoding arrows point).reading future ∈ (singletonMember domain arrows point member).val ↔
      domain.family.map future.1.2 ((domain.model point).decode member) = future.2 :=
  power_truth domain arrows point
    (singleton domain.family point ((domain.model point).decode member)) future

theorem singletonMember_injective (point : context.base.Elements) :
    Function.Injective (singletonMember domain arrows point) := by
  intro first second same
  have predicates := congrArg ((power domain arrows).model point).decode same
  rw [singletonMember_decode, singletonMember_decode] at predicates
  exact (domain.model point).decode.injective (singleton_injective domain.family point predicates)

theorem singletonMember_restriction {first second : context.base.Elements} (step : first ⟶ second)
    (member : {value : HSet.{u} // value ∈ (domain.model first).carrier}) :
    (power domain arrows).memberRestriction step (singletonMember domain arrows first member) =
      singletonMember domain arrows second (domain.memberRestriction step member) := by
  apply ((power domain arrows).model second).decode.injective
  rw [MaterialFamily.memberRestriction_decode, singletonMember_decode, singletonMember_decode,
    MaterialFamily.memberRestriction_decode]
  exact singleton_restrict domain.family step ((domain.model first).decode member)

def singletonHom : NaturalHom domain.members (power domain arrows).members where
  app := singletonMember domain arrows
  naturality := singletonMember_restriction domain arrows

def flattenMember (point : context.base.Elements)
    (member : {value : HSet.{u} // value ∈ ((power (power domain arrows) arrows).model point).carrier}) :
    {value : HSet.{u} // value ∈ ((power domain arrows).model point).carrier} :=
  ((power domain arrows).model point).decode.symm
    (flatten domain.family point (((power (power domain arrows) arrows).model point).decode member))

theorem flattenMember_decode (point : context.base.Elements)
    (member : {value : HSet.{u} // value ∈ ((power (power domain arrows) arrows).model point).carrier}) :
    ((power domain arrows).model point).decode (flattenMember domain arrows point member) =
      flatten domain.family point (((power (power domain arrows) arrows).model point).decode member) :=
  Equiv.apply_symm_apply _ _

/-- Both levels of material membership are reflected. The outer level
uses the full future label of the inner predicate; the inner level uses
the current label of the actual retained argument. -/
theorem flattenMember_truth (point : context.base.Elements)
    (member : {value : HSet.{u} // value ∈ ((power (power domain arrows) arrows).model point).carrier})
    (future : Arguments domain.family point) :
    (domain.futureCoding arrows point).reading future ∈ (flattenMember domain arrows point member).val ↔
      ∃ inner : Predicate domain.family future.1.1,
        ((power domain arrows).futureCoding arrows point).reading ⟨future.1, inner⟩ ∈ member.val ∧
          (domain.futureCoding arrows future.1.1).reading (current domain.family future.1.1 future.2) ∈
            ((power domain arrows).model future.1.1).value inner := by
  let decoded := ((power (power domain arrows) arrows).model point).decode member
  change (domain.futureCoding arrows point).reading future ∈
      ((power domain arrows).model point).value (flatten domain.family point decoded) ↔ _
  refine (power_truth domain arrows point (flatten domain.family point decoded) future).trans ?_
  change (∃ inner : Predicate domain.family future.1.1,
    decoded.holds ⟨future.1, inner⟩ ∧ inner.holds (current domain.family future.1.1 future.2)) ↔ _
  have outerTruth (inner : Predicate domain.family future.1.1) :
      decoded.holds ⟨future.1, inner⟩ ↔
        ((power domain arrows).futureCoding arrows point).reading ⟨future.1, inner⟩ ∈ member.val := by
    have reflected := (power_truth (power domain arrows) arrows point decoded ⟨future.1, inner⟩).symm
    have recovered := ((power (power domain arrows) arrows).model point).value_decode member
    rw [recovered] at reflected
    exact reflected
  constructor
  · rintro ⟨inner, admitted, truth⟩
    exact ⟨inner, (outerTruth inner).mp admitted,
      (power_truth domain arrows future.1.1 inner (current domain.family future.1.1 future.2)).mpr truth⟩
  · rintro ⟨inner, admitted, truth⟩
    exact ⟨inner, (outerTruth inner).mpr admitted,
      (power_truth domain arrows future.1.1 inner (current domain.family future.1.1 future.2)).mp truth⟩

theorem flattenMember_restriction {first second : context.base.Elements} (step : first ⟶ second)
    (member : {value : HSet.{u} // value ∈ ((power (power domain arrows) arrows).model first).carrier}) :
    (power domain arrows).memberRestriction step (flattenMember domain arrows first member) =
      flattenMember domain arrows second ((power (power domain arrows) arrows).memberRestriction step member) := by
  apply ((power domain arrows).model second).decode.injective
  rw [MaterialFamily.memberRestriction_decode, flattenMember_decode, flattenMember_decode,
    MaterialFamily.memberRestriction_decode]
  exact flatten_restrict domain.family step
    (((power (power domain arrows) arrows).model first).decode member)

def flattenHom : NaturalHom (power (power domain arrows) arrows).members (power domain arrows).members where
  app := flattenMember domain arrows
  naturality := flattenMember_restriction domain arrows

/-- The material singleton followed by union recovers the entire original
material predicate member, using the substantive full-predicate unit law. -/
theorem flatten_singletonMember (point : context.base.Elements)
    (member : {value : HSet.{u} // value ∈ ((power domain arrows).model point).carrier}) :
    flattenMember domain arrows point (singletonMember (power domain arrows) arrows point member) = member := by
  apply ((power domain arrows).model point).decode.injective
  rw [flattenMember_decode, singletonMember_decode]
  exact flatten_singleton domain.family point (((power domain arrows).model point).decode member)

variable {source target : MaterialFamily context}

/-- The independently constructed argument-family image is interpreted in
the actual source and target material power carriers. -/
def imageMember (operation : NaturalHom source.family target.family) (point : context.base.Elements)
    (member : {value : HSet.{u} // value ∈ ((power source arrows).model point).carrier}) :
    {value : HSet.{u} // value ∈ ((power target arrows).model point).carrier} :=
  ((power target arrows).model point).decode.symm
    (FuturePowerFunctor.image operation point (((power source arrows).model point).decode member))

theorem imageMember_decode (operation : NaturalHom source.family target.family) (point : context.base.Elements)
    (member : {value : HSet.{u} // value ∈ ((power source arrows).model point).carrier}) :
    ((power target arrows).model point).decode (imageMember arrows operation point member) =
      FuturePowerFunctor.image operation point (((power source arrows).model point).decode member) :=
  Equiv.apply_symm_apply _ _

theorem imageMember_restriction (operation : NaturalHom source.family target.family)
    {first second : context.base.Elements} (step : first ⟶ second)
    (member : {value : HSet.{u} // value ∈ ((power source arrows).model first).carrier}) :
    (power target arrows).memberRestriction step (imageMember arrows operation first member) =
      imageMember arrows operation second ((power source arrows).memberRestriction step member) := by
  apply ((power target arrows).model second).decode.injective
  rw [MaterialFamily.memberRestriction_decode, imageMember_decode, imageMember_decode,
    MaterialFamily.memberRestriction_decode]
  exact FuturePowerFunctor.image_restrict operation step
    (((power source arrows).model first).decode member)

/-- The material image of singleton followed by union is the other unit
law. Its proof uses the independently constructed existential image. -/
theorem flatten_image_singletonMember (point : context.base.Elements)
    (member : {value : HSet.{u} // value ∈ ((power domain arrows).model point).carrier}) :
    flattenMember domain arrows point
      (imageMember (source := domain) (target := power domain arrows) arrows
        (unitHom domain.family) point member) = member := by
  apply ((power domain arrows).model point).decode.injective
  rw [flattenMember_decode]
  have decodedImage := imageMember_decode (source := domain) (target := power domain arrows)
    arrows (unitHom domain.family) point member
  exact (congrArg (flatten domain.family point) decodedImage).trans
    (flatten_image_singleton domain.family point (((power domain arrows).model point).decode member))

/-- The two union groupings recover exactly the same material member of
the full-future power carrier. No graph labels are discarded. -/
theorem flattenMember_associativity (point : context.base.Elements)
    (member : {value : HSet.{u} // value ∈
      ((power (power (power domain arrows) arrows) arrows).model point).carrier}) :
    flattenMember domain arrows point
      (flattenMember (power domain arrows) arrows point member) =
    flattenMember domain arrows point
      (imageMember (source := power (power domain arrows) arrows) (target := power domain arrows)
        arrows (multiplicationHom domain.family) point member) := by
  apply ((power domain arrows).model point).decode.injective
  rw [flattenMember_decode, flattenMember_decode, flattenMember_decode]
  have decodedImage := imageMember_decode
    (source := power (power domain arrows) arrows) (target := power domain arrows)
    arrows (multiplicationHom domain.family) point member
  exact (flatten_associativity domain.family point
    (((power (power (power domain arrows) arrows) arrows).model point).decode member)).trans
      (congrArg (flatten domain.family point) decodedImage).symm

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualPowerOperations
