import Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoalgebraQuotient
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualEnumeratedCoalgebraReadout

/-!
# Constructed small-source behavioral recipients in every parameter slice

Over an independently larger parameter family B, the recipient retains a
parameter and a value of the constructed universal small-coalgebra
quotient. Its future children have an actual behavioral child and exactly
the parameter transported along that same future arrow. The original
small receipt bound is retained.

Every originally small indexed source, and every larger indexed source
with authored uniform branch enumerations, has an actual unique map into
this recipient over B. No uniform enumeration is selected from mere
cover existence, and finality for the full covered class is not asserted.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedSmallCoalgebraRecipient

open _root_.CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open Mettapedia.TypeTheory.ContextualWitnessCover
open PowerClassPresheafBaseChange

universe u v w z
variable {D : Type u} [Category.{u} D]

abbrev Behavior := ContextualSmallCoalgebraGenerators.quotient (D := D)
abbrev behaviorCoalgebra := ContextualSmallCoalgebraGenerators.quotientCoalgebra (D := D)

variable (B : D ⥤ Type v)

abbrev family := CoveredFuturePowerClassifier.product B (Behavior (D := D))

def parameter : NaturalHom (family B) B := CoveredFuturePowerClassifier.firstProjection B Behavior
def behavior : NaturalHom (family B) Behavior := CoveredFuturePowerClassifier.secondProjection B Behavior

def children (point : D) (value : (family B).obj point) : Predicate (family B) point where
  holds future := (behaviorCoalgebra.app point value.2).val.holds ⟨future.1, future.2.2⟩ ∧
    future.2.1 = B.map future.1.2 value.1
  closed {first second} move admitted := by
    refine ⟨(behaviorCoalgebra.app point value.2).val.closed
      ((futureArguments (behavior B) point).map move) admitted.1, ?_⟩
    have coordinates := congrArg Prod.fst move.2
    exact coordinates.symm.trans ((congrArg (B.map move.1.1) admitted.2).trans
      ((B.map_comp_apply first.1.2 move.1.1 value.1).symm.trans
        (congrArg (fun arrow => B.map arrow value.1) move.1.2)))

def enumeration (point : D) (value : (family B).obj point)
    (receipt : Enumeration (behaviorCoalgebra.app point value.2).val) : Enumeration (children B point value) where
  Carrier := receipt.Carrier
  value future code := (B.map future.2 value.1, receipt.value future code)
  covered future argument := by
    constructor
    · rintro ⟨admitted, supported⟩
      obtain ⟨code, same⟩ := (receipt.covered future argument.2).mp admitted
      exact ⟨code, Prod.ext supported.symm same⟩
    · rintro ⟨code, same⟩
      exact ⟨(receipt.covered future argument.2).mpr ⟨code, congrArg Prod.snd same⟩,
        (congrArg Prod.fst same).symm⟩

def childPower (point : D) (value : (family B).obj point) : Power (family B) point :=
  ⟨children B point value, by
    obtain ⟨receipt⟩ := (behaviorCoalgebra.app point value.2).property
    exact ⟨enumeration B point value receipt⟩⟩

def coalgebra : NaturalHom (family B) (CoveredFuturePowerFamilies.family (family B)) where
  app := childPower B
  naturality {first second} step value := by
    apply Subtype.ext
    apply Predicate.ext
    intro argument
    have behaviorEq := congrArg (fun power : Power Behavior second => power.val.holds ⟨argument.1, argument.2.2⟩)
      (behaviorCoalgebra.naturality step value.2)
    constructor
    · rintro ⟨admitted, supported⟩
      exact ⟨Eq.mp behaviorEq admitted, supported.trans (B.map_comp_apply step argument.1.2 value.1)⟩
    · rintro ⟨admitted, supported⟩
      exact ⟨Eq.mpr behaviorEq admitted, supported.trans (B.map_comp_apply step argument.1.2 value.1).symm⟩

theorem behavior_square : (coalgebra B).comp (imageHom (behavior B)) = (behavior B).comp behaviorCoalgebra := by
  apply NaturalHom.ext
  intro point value
  apply Subtype.ext
  apply Predicate.ext
  intro future
  constructor
  · rintro ⟨child, same, admitted, _⟩
    change child.2 = future.2 at same
    rw [same] at admitted
    exact admitted
  · intro admitted
    exact ⟨(B.map future.1.2 value.1, future.2), rfl, admitted, rfl⟩

theorem supports (point : D) (value : (family B).obj point) :
    IndexedCoveredPower.Supports (parameter B) point value.1 ((coalgebra B).app point value) :=
  fun _ admitted => admitted.2

def indexedCoalgebra : NaturalHom (family B) (IndexedCoveredPower.family (parameter B)) where
  app point value := ⟨(value.1, (coalgebra B).app point value), supports B point value⟩
  naturality step value := by
    apply Subtype.ext
    exact Prod.ext rfl ((coalgebra B).naturality step value)

theorem parameter_square : (indexedCoalgebra B).comp (IndexedCoveredPower.projection (parameter B)) = parameter B := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem relative_separated (point : D) {left right : (family B).obj point}
    (related : ContextualCoalgebraBisimulation.Bisimilar (coalgebra B) point left right)
    (sameBase : left.1 = right.1) : left = right :=
  Prod.ext sameBase (ContextualSmallCoalgebraGenerators.quotient_separated point left.2 right.2
    (ContextualCoalgebraBisimulation.bisimilar_preserved (coalgebra B) (behavior B) behaviorCoalgebra
      (behavior_square B) related))

section Source

variable {A : D ⥤ Type w} (sourceParameter : NaturalHom A B)
variable (transition : NaturalHom A (IndexedCoveredPower.family sourceParameter))
variable (sourceSquare : transition.comp (IndexedCoveredPower.projection sourceParameter) = sourceParameter)

def pairReadout (reading : NaturalHom A Behavior) : NaturalHom A (family B) :=
  CoveredFuturePowerClassifier.pair B Behavior sourceParameter reading

theorem pairReadout_parameter (reading : NaturalHom A Behavior) :
    (pairReadout B sourceParameter reading).comp (parameter B) = sourceParameter := by
  apply NaturalHom.ext
  intro _ _
  rfl

include sourceSquare in
theorem pairReadout_square (reading : NaturalHom A Behavior)
    (readingSquare : (IndexedCoalgebraBisimulation.original sourceParameter transition).comp (imageHom reading) =
      reading.comp behaviorCoalgebra) :
    (IndexedCoalgebraBisimulation.original sourceParameter transition).comp
      (imageHom (pairReadout B sourceParameter reading)) = (pairReadout B sourceParameter reading).comp (coalgebra B) := by
  apply NaturalHom.ext
  intro point value
  apply Subtype.ext
  apply Predicate.ext
  intro future
  constructor
  · rintro ⟨child, same, admitted⟩
    refine ⟨(ContextualCoalgebraBisimulation.coalgebra_map_truth
      (IndexedCoalgebraBisimulation.original sourceParameter transition) reading behaviorCoalgebra readingSquare
      point value future.1 future.2.2).mpr ⟨child, congrArg Prod.snd same, admitted⟩, ?_⟩
    exact (congrArg Prod.fst same).symm.trans
      (IndexedCoalgebraBisimulation.future_support sourceParameter transition sourceSquare point value
        ⟨future.1, child⟩ admitted)
  · rintro ⟨admitted, supported⟩
    obtain ⟨child, same, available⟩ := (ContextualCoalgebraBisimulation.coalgebra_map_truth
      (IndexedCoalgebraBisimulation.original sourceParameter transition) reading behaviorCoalgebra readingSquare
      point value future.1 future.2.2).mp admitted
    exact ⟨child, Prod.ext
      ((IndexedCoalgebraBisimulation.future_support sourceParameter transition sourceSquare point value
        ⟨future.1, child⟩ available).trans supported.symm) same, available⟩

theorem maps_equal_over_base (first second : NaturalHom A (family B))
    (firstSquare : (IndexedCoalgebraBisimulation.original sourceParameter transition).comp (imageHom first) =
      first.comp (coalgebra B))
    (secondSquare : (IndexedCoalgebraBisimulation.original sourceParameter transition).comp (imageHom second) =
      second.comp (coalgebra B))
    (firstBase : first.comp (parameter B) = sourceParameter)
    (secondBase : second.comp (parameter B) = sourceParameter) : first = second := by
  apply NaturalHom.ext
  intro point value
  apply relative_separated B point
  · exact ContextualCoalgebraBisimulation.greatest (coalgebra B)
      (ContextualSmallCoalgebraGenerators.mixed_image_isBisimulation
        (IndexedCoalgebraBisimulation.original sourceParameter transition) (coalgebra B) first second
          firstSquare secondSquare) ⟨value, rfl, rfl⟩
  · exact (congrArg (fun operation : NaturalHom A B => operation.app point value) firstBase).trans
      (congrArg (fun operation : NaturalHom A B => operation.app point value) secondBase).symm

def fromEnumerated (receipts : ∀ point value,
    Enumeration ((IndexedCoalgebraBisimulation.original sourceParameter transition).app point value).val) :
    NaturalHom A (family B) :=
  pairReadout B sourceParameter (ContextualEnumeratedCoalgebraReadout.readout A
    (IndexedCoalgebraBisimulation.original sourceParameter transition) receipts)

include sourceSquare in
theorem unique_enumerated (receipts : ∀ point value,
    Enumeration ((IndexedCoalgebraBisimulation.original sourceParameter transition).app point value).val) :
    ∃! operation : NaturalHom A (family B),
      (IndexedCoalgebraBisimulation.original sourceParameter transition).comp (imageHom operation) =
        operation.comp (coalgebra B) ∧ operation.comp (parameter B) = sourceParameter := by
  let actual := fromEnumerated B sourceParameter transition receipts
  have square := pairReadout_square B sourceParameter transition sourceSquare
    (ContextualEnumeratedCoalgebraReadout.readout A (IndexedCoalgebraBisimulation.original sourceParameter transition) receipts)
    (ContextualEnumeratedCoalgebraReadout.readout_square A
      (IndexedCoalgebraBisimulation.original sourceParameter transition) receipts)
  have base := pairReadout_parameter B sourceParameter
    (ContextualEnumeratedCoalgebraReadout.readout A (IndexedCoalgebraBisimulation.original sourceParameter transition) receipts)
  refine ⟨actual, ⟨square, base⟩, ?_⟩
  intro candidate laws
  exact maps_equal_over_base B sourceParameter transition candidate actual laws.1 square laws.2 base

theorem enumerated_kernel (receipts : ∀ point value,
    Enumeration ((IndexedCoalgebraBisimulation.original sourceParameter transition).app point value).val)
    (point : D) (first second : A.obj point) :
    (fromEnumerated B sourceParameter transition receipts).app point first =
      (fromEnumerated B sourceParameter transition receipts).app point second ↔
        IndexedCoalgebraBisimulation.Related sourceParameter transition point first second := by
  constructor
  · intro same
    exact ⟨(ContextualEnumeratedCoalgebraReadout.value_eq_iff A
      (IndexedCoalgebraBisimulation.original sourceParameter transition) receipts point first second).mp
        (congrArg Prod.snd same), congrArg Prod.fst same⟩
  · intro related
    exact Prod.ext related.2
      ((ContextualEnumeratedCoalgebraReadout.value_eq_iff A
        (IndexedCoalgebraBisimulation.original sourceParameter transition) receipts point first second).mpr related.1)

include sourceSquare in
theorem paired_indexed_square (reading : NaturalHom A Behavior)
    (readingSquare : (IndexedCoalgebraBisimulation.original sourceParameter transition).comp (imageHom reading) =
      reading.comp behaviorCoalgebra) :
    transition.comp (IndexedCoveredPower.image sourceParameter (parameter B)
      (pairReadout B sourceParameter reading) (pairReadout_parameter B sourceParameter reading)) =
        (pairReadout B sourceParameter reading).comp (indexedCoalgebra B) := by
  apply NaturalHom.ext
  intro point value
  apply Subtype.ext
  exact Prod.ext (congrArg (fun operation : NaturalHom A B => operation.app point value) sourceSquare)
    (congrArg (fun operation : NaturalHom A (CoveredFuturePowerFamilies.family (family B)) =>
      operation.app point value) (pairReadout_square B sourceParameter transition sourceSquare reading readingSquare))

end Source

section SmallSource

variable {A : D ⥤ Type u} (sourceParameter : NaturalHom A B)
variable (transition : NaturalHom A (IndexedCoveredPower.family sourceParameter))
variable (sourceSquare : transition.comp (IndexedCoveredPower.projection sourceParameter) = sourceParameter)

def smallReceipts (point : D) (value : A.obj point) :
    Enumeration ((IndexedCoalgebraBisimulation.original sourceParameter transition).app point value).val :=
  smallEnumeration ((IndexedCoalgebraBisimulation.original sourceParameter transition).app point value).val

def fromSmall : NaturalHom A (family B) :=
  fromEnumerated B sourceParameter transition (smallReceipts B sourceParameter transition)

include sourceSquare in
theorem unique_small : ∃! operation : NaturalHom A (family B),
    (IndexedCoalgebraBisimulation.original sourceParameter transition).comp (imageHom operation) =
      operation.comp (coalgebra B) ∧ operation.comp (parameter B) = sourceParameter :=
  unique_enumerated B sourceParameter transition sourceSquare (smallReceipts B sourceParameter transition)

theorem small_kernel (point : D) (first second : A.obj point) :
    (fromSmall B sourceParameter transition).app point first =
      (fromSmall B sourceParameter transition).app point second ↔
        IndexedCoalgebraBisimulation.Related sourceParameter transition point first second :=
  enumerated_kernel B sourceParameter transition (smallReceipts B sourceParameter transition) point first second

end SmallSource

end Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedSmallCoalgebraRecipient
