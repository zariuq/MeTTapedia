import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSmallCoalgebraMaterialCarrier
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualEnumeratedCoalgebraReadout

/-!
# Covered coalgebra on the constructed material recipient

Future children range over all coded representatives of a material member.
Exact contextual matching proves independence of that representative at the
same actual future arrow. Original-bound child covers are constructed inside
their propositional existence proofs; no uniform representative is selected.

The computed context maps make this a natural coalgebra. The raw coproduct
observation satisfies its whole image equation, and the material coalgebra
is behaviorally separated. The collecting graph also supplies an actual
smaller class face with inverse member decoding and the same coalgebra laws.

Every originally small source, and every wider source with authored uniform
small branch-enumeration data, has a constructed unique coalgebra map into
these recipients. This is relative to the fixed context and branch bound;
unrestricted Collection and slice-indexed finality remain separate claims.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSmallCoalgebraMaterialCoalgebra

open _root_.CategoryTheory PowerClassPresheafBaseChange
open ContextualSmallCoalgebraGenerators
open ContextualSmallCoalgebraMaterialCarrier
open CoveredFuturePowerFunctor
open Mettapedia.TypeTheory.ContextualWitnessCover

universe u v
variable {D : Type u} [Category.{u} D]
variable (worlds : ArgumentCoding D)
variable (arrows : (source target : D) → ArgumentCoding (source ⟶ target))

def children (point : D) (member : ContextualSmallCoalgebraMaterialCarrier.Members worlds arrows point) :
    CoveredFuturePowerFamilies.Predicate (ContextualSmallCoalgebraMaterialCarrier.family worlds arrows) point where
  holds argument :=
    ∃ source : (coproduct (D := D)).obj point, observe worlds arrows point source = member ∧
      ∃ child : (coproduct (D := D)).obj argument.1.1,
        (coproductCoalgebra.app point source).val.holds ⟨argument.1, child⟩ ∧
          observe worlds arrows argument.1.1 child = argument.2
  closed {first second} move available := by
    obtain ⟨source, sourceValue, child, admitted, childValue⟩ := available
    refine ⟨source, sourceValue, (coproduct (D := D)).map move.1.1 child, ?_, ?_⟩
    · exact (coproductCoalgebra.app point source).val.closed ⟨move.1, rfl⟩ admitted
    · exact ((observation worlds arrows).naturality move.1.1 child).symm.trans
        ((congrArg ((ContextualSmallCoalgebraMaterialCarrier.family worlds arrows).map move.1.1) childValue).trans
          move.2)

theorem children_observe_iff (point : D) (argument : (coproduct (D := D)).obj point)
    (future : Future.Objects point) (member : ContextualSmallCoalgebraMaterialCarrier.Members worlds arrows future.1) :
    (children worlds arrows point (observe worlds arrows point argument)).holds ⟨future, member⟩ ↔
      ∃ child : (coproduct (D := D)).obj future.1, observe worlds arrows future.1 child = member ∧
        (coproductCoalgebra.app point argument).val.holds ⟨future, child⟩ := by
  constructor
  · rintro ⟨other, same, child, admitted, value⟩
    have related := (observe_eq_iff worlds arrows point other argument).mp same
    obtain ⟨matching, matched, childRelated⟩ :=
      (ContextualCoalgebraBisimulation.bisimilar_isBisimulation coproductCoalgebra).forth related future admitted
    have readings := (observe_eq_iff worlds arrows future.1 child matching).mpr childRelated
    exact ⟨matching, readings.symm.trans value, matched⟩
  · rintro ⟨child, value, admitted⟩
    exact ⟨argument, rfl, child, admitted, value⟩

theorem children_covered (point : D) (member : ContextualSmallCoalgebraMaterialCarrier.Members worlds arrows point) :
    Nonempty (CoveredFuturePowerFamilies.Enumeration (children worlds arrows point member)) := by
  obtain ⟨argument, rfl⟩ := observe_surjective worlds arrows point member
  let original := coproductEnumeration point argument
  refine ⟨{
    Carrier := original.Carrier
    value := fun future receipt => observe worlds arrows future.1 (original.value future receipt)
    covered := ?_ }⟩
  intro future member
  change ContextualSmallCoalgebraMaterialCarrier.Members worlds arrows future.1 at member
  refine (children_observe_iff worlds arrows point argument future member).trans ?_
  constructor
  · rintro ⟨child, same, admitted⟩
    obtain ⟨receipt, covers⟩ := (original.covered future child).mp admitted
    exact ⟨receipt, (congrArg (observe worlds arrows future.1) covers).trans same⟩
  · rintro ⟨receipt, same⟩
    exact ⟨original.value future receipt, same, (original.covered future _).mpr ⟨receipt, rfl⟩⟩

theorem coproduct_restrict_truth {first second : D} (step : first ⟶ second)
    (argument : (coproduct (D := D)).obj first) (future : Future.Objects second)
    (child : (coproduct (D := D)).obj future.1) :
    (coproductCoalgebra.app first argument).val.holds ⟨⟨future.1, step ≫ future.2⟩, child⟩ ↔
      (coproductCoalgebra.app second ((coproduct (D := D)).map step argument)).val.holds ⟨future, child⟩ := by
  have same := congrArg (fun power : CoveredFuturePowerFamilies.Power (coproduct (D := D)) second =>
    power.val.holds ⟨future, child⟩) (coproductCoalgebra.naturality step argument)
  exact ⟨fun admitted => same ▸ admitted, fun admitted => same.symm ▸ admitted⟩

theorem children_restrict {first second : D} (step : first ⟶ second)
    (member : ContextualSmallCoalgebraMaterialCarrier.Members worlds arrows first) :
    CoveredFuturePowerFamilies.restrict (ContextualSmallCoalgebraMaterialCarrier.family worlds arrows) step
        (children worlds arrows first member) =
      children worlds arrows second (ContextualSmallCoalgebraMaterialCarrier.transport worlds arrows step member) := by
  obtain ⟨argument, rfl⟩ := observe_surjective worlds arrows first member
  rw [transport_observe]
  apply CoveredFuturePowerFamilies.Predicate.ext
  rintro ⟨⟨target, arrow⟩, child⟩
  change ContextualSmallCoalgebraMaterialCarrier.Members worlds arrows target at child
  change (children worlds arrows first (observe worlds arrows first argument)).holds
      ⟨⟨target, step ≫ arrow⟩, child⟩ ↔
    (children worlds arrows second
      (observe worlds arrows second ((coproduct (D := D)).map step argument))).holds ⟨⟨target, arrow⟩, child⟩
  rw [children_observe_iff, children_observe_iff]
  exact exists_congr fun original => and_congr_right fun _ =>
    coproduct_restrict_truth step argument ⟨target, arrow⟩ original

def coalgebra : NaturalHom (ContextualSmallCoalgebraMaterialCarrier.family worlds arrows)
    (CoveredFuturePowerFamilies.family (ContextualSmallCoalgebraMaterialCarrier.family worlds arrows)) where
  app point member := ⟨children worlds arrows point member, children_covered worlds arrows point member⟩
  naturality step member := Subtype.ext (children_restrict worlds arrows step member)

theorem observation_square :
    coproductCoalgebra.comp (imageHom (observation worlds arrows)) =
      (observation worlds arrows).comp (coalgebra worlds arrows) := by
  apply NaturalHom.ext
  intro point argument
  apply Subtype.ext
  apply CoveredFuturePowerFamilies.Predicate.ext
  rintro ⟨future, member⟩
  exact (children_observe_iff worlds arrows point argument future member).symm

theorem separated : ContextualCoalgebraQuotient.BehaviorallySeparated (coalgebra worlds arrows) := by
  intro point left right related
  obtain ⟨first, rfl⟩ := observe_surjective worlds arrows point left
  obtain ⟨second, rfl⟩ := observe_surjective worlds arrows point right
  exact (observe_eq_iff worlds arrows point first second).mpr
    (ContextualCoalgebraBisimulation.bisimilar_reflected coproductCoalgebra (observation worlds arrows)
      (coalgebra worlds arrows) (observation_square worlds arrows) related)

def quotientReadout : NaturalHom (quotient (D := D)) (ContextualSmallCoalgebraMaterialCarrier.family worlds arrows) :=
  ContextualCoalgebraQuotient.descend coproductCoalgebra (observation worlds arrows)
    (fun point left right related => (observe_eq_iff worlds arrows point left right).mpr related)

theorem quotientReadout_projection (point : D) (argument : (coproduct (D := D)).obj point) :
    (quotientReadout worlds arrows).app point (quotientProjection.app point argument) =
      observe worlds arrows point argument := rfl

theorem quotientReadout_injective (point : D) :
    Function.Injective ((quotientReadout worlds arrows).app point) := by
  intro first second
  refine Quotient.inductionOn₂ first second ?_
  intro left right same
  exact Quotient.sound ((observe_eq_iff worlds arrows point left right).mp same)

theorem quotientReadout_surjective (point : D) :
    Function.Surjective ((quotientReadout worlds arrows).app point) := by
  intro member
  obtain ⟨argument, rfl⟩ := observe_surjective worlds arrows point member
  exact ⟨quotientProjection.app point argument, rfl⟩

theorem quotientReadout_square :
    quotientCoalgebra.comp (imageHom (quotientReadout worlds arrows)) =
      (quotientReadout worlds arrows).comp (coalgebra worlds arrows) :=
  ContextualCoalgebraQuotient.descend_coalgebra coproductCoalgebra (observation worlds arrows)
    (fun point left right related => (observe_eq_iff worlds arrows point left right).mpr related)
    (coalgebra worlds arrows) (observation_square worlds arrows)

def classCoalgebra : NaturalHom (classFamily worlds arrows)
    (CoveredFuturePowerFamilies.family (classFamily worlds arrows)) :=
  ((classToMembers worlds arrows).comp (coalgebra worlds arrows)).comp (imageHom (membersToClass worlds arrows))

theorem membersToClass_square :
    (coalgebra worlds arrows).comp (imageHom (membersToClass worlds arrows)) =
      (membersToClass worlds arrows).comp (classCoalgebra worlds arrows) := by
  apply NaturalHom.ext
  intro point member
  change imagePower (membersToClass worlds arrows) point ((coalgebra worlds arrows).app point member) =
    imagePower (membersToClass worlds arrows) point ((coalgebra worlds arrows).app point
      ((classToMembers worlds arrows).app point ((membersToClass worlds arrows).app point member)))
  exact congrArg (fun value => imagePower (membersToClass worlds arrows) point
    ((coalgebra worlds arrows).app point value)) (classToMembers_membersToClass worlds arrows point member).symm

theorem classToMembers_square :
    (classCoalgebra worlds arrows).comp (imageHom (classToMembers worlds arrows)) =
      (classToMembers worlds arrows).comp (coalgebra worlds arrows) := by
  have inverse : (membersToClass worlds arrows).comp (classToMembers worlds arrows) =
      identityHom (ContextualSmallCoalgebraMaterialCarrier.family worlds arrows) := by
    apply NaturalHom.ext
    exact classToMembers_membersToClass worlds arrows
  apply NaturalHom.ext
  intro point memberClass
  let predicate : CoveredFuturePowerFamilies.Power
      (ContextualSmallCoalgebraMaterialCarrier.family worlds arrows) point :=
    (coalgebra worlds arrows).app point ((classToMembers worlds arrows).app point memberClass)
  change imagePower (classToMembers worlds arrows) point
    (imagePower (membersToClass worlds arrows) point predicate) = predicate
  have composed := imagePower_comp (membersToClass worlds arrows) (classToMembers worlds arrows) point predicate
  have identical := congrArg (fun operation : NaturalHom
    (ContextualSmallCoalgebraMaterialCarrier.family worlds arrows)
    (ContextualSmallCoalgebraMaterialCarrier.family worlds arrows) => imagePower operation point predicate) inverse
  exact composed.trans (identical.trans (imagePower_identity point predicate))

theorem classObservation_square :
    coproductCoalgebra.comp (imageHom (classObservation worlds arrows)) =
      (classObservation worlds arrows).comp (classCoalgebra worlds arrows) :=
  ContextualSmallCoalgebraComparisons.compose_square coproductCoalgebra (coalgebra worlds arrows)
    (classCoalgebra worlds arrows) (observation worlds arrows) (membersToClass worlds arrows)
    (observation_square worlds arrows) (membersToClass_square worlds arrows)

theorem class_separated : ContextualCoalgebraQuotient.BehaviorallySeparated (classCoalgebra worlds arrows) := by
  intro point left right related
  apply (memberEquiv worlds arrows point).injective
  exact separated worlds arrows point _ _
    (ContextualCoalgebraBisimulation.bisimilar_preserved (classCoalgebra worlds arrows)
      (classToMembers worlds arrows) (coalgebra worlds arrows) (classToMembers_square worlds arrows) related)

def smallReadout (code : Code D) : NaturalHom code.carrier (classFamily worlds arrows) :=
  (inclusion code).comp (classObservation worlds arrows)

theorem smallReadout_square (code : Code D) :
    code.coalgebra.comp (imageHom (smallReadout worlds arrows code)) =
      (smallReadout worlds arrows code).comp (classCoalgebra worlds arrows) :=
  ContextualSmallCoalgebraComparisons.compose_square code.coalgebra coproductCoalgebra
    (classCoalgebra worlds arrows) (inclusion code) (classObservation worlds arrows)
    (inclusion_square code) (classObservation_square worlds arrows)

theorem smallReadout_value (code : Code D) (point : D) (argument : code.carrier.obj point) :
    ((classToMembers worlds arrows).app point ((smallReadout worlds arrows code).app point argument)).val =
      HSet.lift (ContextualCoalgebraMaterialReadout.value code.coalgebra worlds arrows ⟨point, argument⟩) :=
  classObservation_value worlds arrows point ⟨code, argument⟩

theorem smallReadout_eq_iff (code : Code D) (point : D) (first second : code.carrier.obj point) :
    (smallReadout worlds arrows code).app point first = (smallReadout worlds arrows code).app point second ↔
      ContextualCoalgebraBisimulation.Bisimilar code.coalgebra point first second := by
  constructor
  · intro same
    apply ContextualCoalgebraBisimulation.bisimilar_reflected code.coalgebra
      (smallReadout worlds arrows code) (classCoalgebra worlds arrows) (smallReadout_square worlds arrows code)
    rw [same]
    exact ContextualCoalgebraBisimulation.bisimilar_refl (classCoalgebra worlds arrows) point _
  · intro related
    exact class_separated worlds arrows point _ _
      (ContextualCoalgebraBisimulation.bisimilar_preserved code.coalgebra
        (smallReadout worlds arrows code) (classCoalgebra worlds arrows) (smallReadout_square worlds arrows code) related)

theorem unique_smallReadout (code : Code D) :
    ∃! operation : NaturalHom code.carrier (classFamily worlds arrows),
      code.coalgebra.comp (imageHom operation) = operation.comp (classCoalgebra worlds arrows) := by
  refine ⟨smallReadout worlds arrows code, smallReadout_square worlds arrows code, ?_⟩
  intro candidate square
  exact maps_equal_into_separated code.coalgebra (classCoalgebra worlds arrows)
    candidate (smallReadout worlds arrows code) square (smallReadout_square worlds arrows code)
    (class_separated worlds arrows)

def quotientClassReadout : NaturalHom (quotient (D := D)) (classFamily worlds arrows) :=
  (quotientReadout worlds arrows).comp (membersToClass worlds arrows)

theorem quotientClassReadout_square :
    quotientCoalgebra.comp (imageHom (quotientClassReadout worlds arrows)) =
      (quotientClassReadout worlds arrows).comp (classCoalgebra worlds arrows) :=
  ContextualSmallCoalgebraComparisons.compose_square quotientCoalgebra (coalgebra worlds arrows)
    (classCoalgebra worlds arrows) (quotientReadout worlds arrows) (membersToClass worlds arrows)
    (quotientReadout_square worlds arrows) (membersToClass_square worlds arrows)

variable (A : D ⥤ Type v) (source : NaturalHom A (CoveredFuturePowerFamilies.family A))
variable (enumeration : ∀ point argument, CoveredFuturePowerFamilies.Enumeration (source.app point argument).val)

def enumeratedReadout : NaturalHom A (classFamily worlds arrows) :=
  (ContextualEnumeratedCoalgebraReadout.readout A source enumeration).comp (quotientClassReadout worlds arrows)

theorem enumeratedReadout_value (point : D) (argument : A.obj point) :
    ((classToMembers worlds arrows).app point
      ((enumeratedReadout worlds arrows A source enumeration).app point argument)).val =
      HSet.lift (readValue worlds arrows point
        ⟨ContextualEnumeratedCoalgebraReadout.generatedCode A source enumeration ⟨point, argument⟩,
          ContextualGeneratedCoalgebras.rootMember A source enumeration ⟨point, argument⟩⟩) :=
  classObservation_value worlds arrows point
    ⟨ContextualEnumeratedCoalgebraReadout.generatedCode A source enumeration ⟨point, argument⟩,
      ContextualGeneratedCoalgebras.rootMember A source enumeration ⟨point, argument⟩⟩

theorem enumeratedReadout_square :
    source.comp (imageHom (enumeratedReadout worlds arrows A source enumeration)) =
      (enumeratedReadout worlds arrows A source enumeration).comp (classCoalgebra worlds arrows) :=
  ContextualSmallCoalgebraComparisons.compose_square source quotientCoalgebra (classCoalgebra worlds arrows)
    (ContextualEnumeratedCoalgebraReadout.readout A source enumeration) (quotientClassReadout worlds arrows)
    (ContextualEnumeratedCoalgebraReadout.readout_square A source enumeration) (quotientClassReadout_square worlds arrows)

include enumeration in
theorem unique_enumeratedReadout :
    ∃! operation : NaturalHom A (classFamily worlds arrows),
      source.comp (imageHom operation) = operation.comp (classCoalgebra worlds arrows) := by
  refine ⟨enumeratedReadout worlds arrows A source enumeration,
    enumeratedReadout_square worlds arrows A source enumeration, ?_⟩
  intro candidate square
  exact maps_equal_into_separated source (classCoalgebra worlds arrows) candidate
    (enumeratedReadout worlds arrows A source enumeration) square
    (enumeratedReadout_square worlds arrows A source enumeration) (class_separated worlds arrows)

theorem enumeratedReadout_eq_iff (point : D) (first second : A.obj point) :
    (enumeratedReadout worlds arrows A source enumeration).app point first =
        (enumeratedReadout worlds arrows A source enumeration).app point second ↔
      ContextualCoalgebraBisimulation.Bisimilar source point first second := by
  constructor
  · intro same
    apply ContextualCoalgebraBisimulation.bisimilar_reflected source
      (enumeratedReadout worlds arrows A source enumeration) (classCoalgebra worlds arrows)
      (enumeratedReadout_square worlds arrows A source enumeration)
    rw [same]
    exact ContextualCoalgebraBisimulation.bisimilar_refl (classCoalgebra worlds arrows) point _
  · intro related
    exact class_separated worlds arrows point _ _
      (ContextualCoalgebraBisimulation.bisimilar_preserved source
        (enumeratedReadout worlds arrows A source enumeration) (classCoalgebra worlds arrows)
        (enumeratedReadout_square worlds arrows A source enumeration) related)

theorem enumeratedReadout_independent
    (other : ∀ point argument, CoveredFuturePowerFamilies.Enumeration (source.app point argument).val) :
    enumeratedReadout worlds arrows A source enumeration = enumeratedReadout worlds arrows A source other :=
  maps_equal_into_separated source (classCoalgebra worlds arrows)
    (enumeratedReadout worlds arrows A source enumeration) (enumeratedReadout worlds arrows A source other)
    (enumeratedReadout_square worlds arrows A source enumeration)
    (enumeratedReadout_square worlds arrows A source other) (class_separated worlds arrows)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSmallCoalgebraMaterialCoalgebra
