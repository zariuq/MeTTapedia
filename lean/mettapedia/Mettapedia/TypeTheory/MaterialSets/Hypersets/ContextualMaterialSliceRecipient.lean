import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSmallCoalgebraMaterialCoalgebra
import Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoalgebraQuotient

/-!
# Material behavioral recipients in parameter slices

Each recipient retains a parameter and a class of the constructed material
behavior carrier. Its future children have an admitted material behavior
and exactly the parameter transported along that same actual future arrow.
The behavioral coordinate has an explicit member decoder and inverse.

Every originally small indexed source, and every wider indexed source
with authored uniform small branch enumerations, has a constructed unique
map over its parameter. The exact kernel is contextual bisimilarity together
with equality of the retained parameter. Branch cover existence remains
propositional; no representative or uniform enumeration is selected.

The context and branch bound is `u`. The behavioral collecting graph lies
at `u+1`, with its class face in `Type (u+1)` and actual members in
`Type (u+2)`. Parameter families may occupy an independent universe.
Finality for all merely covered sources and unrestricted Collection are
not established by these constructions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSliceRecipient

open _root_.CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open Mettapedia.TypeTheory.ContextualWitnessCover
open PowerClassPresheafBaseChange

universe u v w z
variable {D : Type u} [Category.{u} D]
variable (worlds : ArgumentCoding D)
variable (arrows : (source target : D) → ArgumentCoding (source ⟶ target))

abbrev Behavior := ContextualSmallCoalgebraMaterialCarrier.classFamily worlds arrows
abbrev behaviorCoalgebra := ContextualSmallCoalgebraMaterialCoalgebra.classCoalgebra worlds arrows

variable (B : D ⥤ Type v)

abbrev family := CoveredFuturePowerClassifier.product B ((Behavior worlds arrows))

def parameter : NaturalHom (family worlds arrows B) B := CoveredFuturePowerClassifier.firstProjection B (Behavior worlds arrows)
def behavior : NaturalHom (family worlds arrows B) (Behavior worlds arrows) := CoveredFuturePowerClassifier.secondProjection B (Behavior worlds arrows)

def children (point : D) (value : (family worlds arrows B).obj point) : Predicate (family worlds arrows B) point where
  holds future := ((behaviorCoalgebra worlds arrows).app point value.2).val.holds ⟨future.1, future.2.2⟩ ∧
    future.2.1 = B.map future.1.2 value.1
  closed {first second} move admitted := by
    refine ⟨((behaviorCoalgebra worlds arrows).app point value.2).val.closed
      ((futureArguments (behavior worlds arrows B) point).map move) admitted.1, ?_⟩
    have coordinates := congrArg Prod.fst move.2
    exact coordinates.symm.trans ((congrArg (B.map move.1.1) admitted.2).trans
      ((B.map_comp_apply first.1.2 move.1.1 value.1).symm.trans
        (congrArg (fun arrow => B.map arrow value.1) move.1.2)))

def enumeration (point : D) (value : (family worlds arrows B).obj point)
    (receipt : Enumeration ((behaviorCoalgebra worlds arrows).app point value.2).val) : Enumeration (children worlds arrows B point value) where
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

def childPower (point : D) (value : (family worlds arrows B).obj point) : Power (family worlds arrows B) point :=
  ⟨children worlds arrows B point value, by
    obtain ⟨receipt⟩ := ((behaviorCoalgebra worlds arrows).app point value.2).property
    exact ⟨enumeration worlds arrows B point value receipt⟩⟩

def coalgebra : NaturalHom (family worlds arrows B) (CoveredFuturePowerFamilies.family (family worlds arrows B)) where
  app := childPower worlds arrows B
  naturality {first second} step value := by
    apply Subtype.ext
    apply Predicate.ext
    intro argument
    have behaviorEq := congrArg (fun power : Power (Behavior worlds arrows) second => power.val.holds ⟨argument.1, argument.2.2⟩)
      ((behaviorCoalgebra worlds arrows).naturality step value.2)
    constructor
    · rintro ⟨admitted, supported⟩
      exact ⟨Eq.mp behaviorEq admitted, supported.trans (B.map_comp_apply step argument.1.2 value.1)⟩
    · rintro ⟨admitted, supported⟩
      exact ⟨Eq.mpr behaviorEq admitted, supported.trans (B.map_comp_apply step argument.1.2 value.1).symm⟩

theorem behavior_square : (coalgebra worlds arrows B).comp (imageHom (behavior worlds arrows B)) = (behavior worlds arrows B).comp (behaviorCoalgebra worlds arrows) := by
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

theorem supports (point : D) (value : (family worlds arrows B).obj point) :
    IndexedCoveredPower.Supports (parameter worlds arrows B) point value.1 ((coalgebra worlds arrows B).app point value) :=
  fun _ admitted => admitted.2

def indexedCoalgebra : NaturalHom (family worlds arrows B) (IndexedCoveredPower.family (parameter worlds arrows B)) where
  app point value := ⟨(value.1, (coalgebra worlds arrows B).app point value), supports worlds arrows B point value⟩
  naturality step value := by
    apply Subtype.ext
    exact Prod.ext rfl ((coalgebra worlds arrows B).naturality step value)

theorem parameter_square : (indexedCoalgebra worlds arrows B).comp (IndexedCoveredPower.projection (parameter worlds arrows B)) = parameter worlds arrows B := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem relative_separated (point : D) {left right : (family worlds arrows B).obj point}
    (related : ContextualCoalgebraBisimulation.Bisimilar (coalgebra worlds arrows B) point left right)
    (sameBase : left.1 = right.1) : left = right :=
  Prod.ext sameBase (ContextualSmallCoalgebraMaterialCoalgebra.class_separated worlds arrows point left.2 right.2
    (ContextualCoalgebraBisimulation.bisimilar_preserved (coalgebra worlds arrows B) (behavior worlds arrows B) (behaviorCoalgebra worlds arrows)
      (behavior_square worlds arrows B) related))

/-- The same retained parameter with the actual member subtype as its second
coordinate. -/
abbrev decodedFamily := CoveredFuturePowerClassifier.product B
  (ContextualSmallCoalgebraMaterialCarrier.family worlds arrows)

def memberDecode : NaturalHom (family worlds arrows B)
    (ContextualSmallCoalgebraMaterialCarrier.family worlds arrows) :=
  (behavior worlds arrows B).comp (ContextualSmallCoalgebraMaterialCarrier.classToMembers worlds arrows)

def decode : NaturalHom (family worlds arrows B) (decodedFamily worlds arrows B) :=
  CoveredFuturePowerClassifier.pair B (ContextualSmallCoalgebraMaterialCarrier.family worlds arrows)
    (parameter worlds arrows B) (memberDecode worlds arrows B)

def encode : NaturalHom (decodedFamily worlds arrows B) (family worlds arrows B) where
  app point value := (value.1, (ContextualSmallCoalgebraMaterialCarrier.membersToClass worlds arrows).app point value.2)
  naturality step value := Prod.ext rfl
    ((ContextualSmallCoalgebraMaterialCarrier.membersToClass worlds arrows).naturality step value.2)

theorem decode_encode (point : D) (value : (decodedFamily worlds arrows B).obj point) :
    (decode worlds arrows B).app point ((encode worlds arrows B).app point value) = value :=
  Prod.ext rfl (ContextualSmallCoalgebraMaterialCarrier.classToMembers_membersToClass worlds arrows point value.2)

theorem encode_decode (point : D) (value : (family worlds arrows B).obj point) :
    (encode worlds arrows B).app point ((decode worlds arrows B).app point value) = value :=
  Prod.ext rfl (ContextualSmallCoalgebraMaterialCarrier.membersToClass_classToMembers worlds arrows point value.2)

def decodedFibreEquiv (point : D) :
    (family worlds arrows B).obj point ≃ (decodedFamily worlds arrows B).obj point where
  toFun := (decode worlds arrows B).app point
  invFun := (encode worlds arrows B).app point
  left_inv := encode_decode worlds arrows B point
  right_inv := decode_encode worlds arrows B point

def decodedSectionEquiv : (family worlds arrows B).sections ≃ (decodedFamily worlds arrows B).sections where
  toFun := (decode worlds arrows B).mapSection
  invFun := (encode worlds arrows B).mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact encode_decode worlds arrows B point (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact decode_encode worlds arrows B point (term.val point)

theorem memberDecode_restriction {first second : D} (step : first ⟶ second)
    (value : (family worlds arrows B).obj first) :
    ContextualSmallCoalgebraMaterialCarrier.transport worlds arrows step
        ((memberDecode worlds arrows B).app first value) =
      (memberDecode worlds arrows B).app second ((family worlds arrows B).map step value) :=
  (memberDecode worlds arrows B).naturality step value

theorem eq_iff_material (point : D) (left right : (family worlds arrows B).obj point) :
    left = right ↔ left.1 = right.1 ∧
      ((memberDecode worlds arrows B).app point left).val =
        ((memberDecode worlds arrows B).app point right).val := by
  constructor
  · intro same
    cases same
    exact ⟨rfl, rfl⟩
  · rintro ⟨sameBase, sameValue⟩
    exact Prod.ext sameBase ((ContextualSmallCoalgebraMaterialCarrier.memberEquiv worlds arrows point).injective
      (Subtype.ext sameValue))

section Source

variable {A : D ⥤ Type w} (sourceParameter : NaturalHom A B)
variable (transition : NaturalHom A (IndexedCoveredPower.family sourceParameter))
variable (sourceSquare : transition.comp (IndexedCoveredPower.projection sourceParameter) = sourceParameter)

def pairReadout (reading : NaturalHom A (Behavior worlds arrows)) : NaturalHom A (family worlds arrows B) :=
  CoveredFuturePowerClassifier.pair B (Behavior worlds arrows) sourceParameter reading

theorem pairReadout_parameter (reading : NaturalHom A (Behavior worlds arrows)) :
    (pairReadout worlds arrows B sourceParameter reading).comp (parameter worlds arrows B) = sourceParameter := by
  apply NaturalHom.ext
  intro _ _
  rfl

include sourceSquare in
theorem pairReadout_square (reading : NaturalHom A (Behavior worlds arrows))
    (readingSquare : (IndexedCoalgebraBisimulation.original sourceParameter transition).comp (imageHom reading) =
      reading.comp (behaviorCoalgebra worlds arrows)) :
    (IndexedCoalgebraBisimulation.original sourceParameter transition).comp
      (imageHom (pairReadout worlds arrows B sourceParameter reading)) = (pairReadout worlds arrows B sourceParameter reading).comp (coalgebra worlds arrows B) := by
  apply NaturalHom.ext
  intro point value
  apply Subtype.ext
  apply Predicate.ext
  intro future
  constructor
  · rintro ⟨child, same, admitted⟩
    refine ⟨(ContextualCoalgebraBisimulation.coalgebra_map_truth
      (IndexedCoalgebraBisimulation.original sourceParameter transition) reading (behaviorCoalgebra worlds arrows) readingSquare
      point value future.1 future.2.2).mpr ⟨child, congrArg Prod.snd same, admitted⟩, ?_⟩
    exact (congrArg Prod.fst same).symm.trans
      (IndexedCoalgebraBisimulation.future_support sourceParameter transition sourceSquare point value
        ⟨future.1, child⟩ admitted)
  · rintro ⟨admitted, supported⟩
    obtain ⟨child, same, available⟩ := (ContextualCoalgebraBisimulation.coalgebra_map_truth
      (IndexedCoalgebraBisimulation.original sourceParameter transition) reading (behaviorCoalgebra worlds arrows) readingSquare
      point value future.1 future.2.2).mp admitted
    exact ⟨child, Prod.ext
      ((IndexedCoalgebraBisimulation.future_support sourceParameter transition sourceSquare point value
        ⟨future.1, child⟩ available).trans supported.symm) same, available⟩

theorem maps_equal_over_base (first second : NaturalHom A (family worlds arrows B))
    (firstSquare : (IndexedCoalgebraBisimulation.original sourceParameter transition).comp (imageHom first) =
      first.comp (coalgebra worlds arrows B))
    (secondSquare : (IndexedCoalgebraBisimulation.original sourceParameter transition).comp (imageHom second) =
      second.comp (coalgebra worlds arrows B))
    (firstBase : first.comp (parameter worlds arrows B) = sourceParameter)
    (secondBase : second.comp (parameter worlds arrows B) = sourceParameter) : first = second := by
  apply NaturalHom.ext
  intro point value
  apply relative_separated worlds arrows B point
  · exact ContextualCoalgebraBisimulation.greatest (coalgebra worlds arrows B)
      (ContextualSmallCoalgebraGenerators.mixed_image_isBisimulation
        (IndexedCoalgebraBisimulation.original sourceParameter transition) (coalgebra worlds arrows B) first second
          firstSquare secondSquare) ⟨value, rfl, rfl⟩
  · exact (congrArg (fun operation : NaturalHom A B => operation.app point value) firstBase).trans
      (congrArg (fun operation : NaturalHom A B => operation.app point value) secondBase).symm

def fromEnumerated (receipts : ∀ point value,
    Enumeration ((IndexedCoalgebraBisimulation.original sourceParameter transition).app point value).val) :
    NaturalHom A (family worlds arrows B) :=
  pairReadout worlds arrows B sourceParameter (ContextualSmallCoalgebraMaterialCoalgebra.enumeratedReadout worlds arrows A
    (IndexedCoalgebraBisimulation.original sourceParameter transition) receipts)

theorem fromEnumerated_member_value (receipts : ∀ point value,
    Enumeration ((IndexedCoalgebraBisimulation.original sourceParameter transition).app point value).val)
    (point : D) (value : A.obj point) :
    ((memberDecode worlds arrows B).app point
      ((fromEnumerated worlds arrows B sourceParameter transition receipts).app point value)).val =
      HSet.lift (ContextualSmallCoalgebraMaterialCarrier.readValue worlds arrows point
        ⟨ContextualEnumeratedCoalgebraReadout.generatedCode A
            (IndexedCoalgebraBisimulation.original sourceParameter transition) receipts ⟨point, value⟩,
          ContextualGeneratedCoalgebras.rootMember A
            (IndexedCoalgebraBisimulation.original sourceParameter transition) receipts ⟨point, value⟩⟩) :=
  ContextualSmallCoalgebraMaterialCoalgebra.enumeratedReadout_value worlds arrows A
    (IndexedCoalgebraBisimulation.original sourceParameter transition) receipts point value

include sourceSquare in
theorem fromEnumerated_square (receipts : ∀ point value,
    Enumeration ((IndexedCoalgebraBisimulation.original sourceParameter transition).app point value).val) :
    (IndexedCoalgebraBisimulation.original sourceParameter transition).comp
      (imageHom (fromEnumerated worlds arrows B sourceParameter transition receipts)) =
        (fromEnumerated worlds arrows B sourceParameter transition receipts).comp (coalgebra worlds arrows B) :=
  pairReadout_square worlds arrows B sourceParameter transition sourceSquare
    (ContextualSmallCoalgebraMaterialCoalgebra.enumeratedReadout worlds arrows A
      (IndexedCoalgebraBisimulation.original sourceParameter transition) receipts)
    (ContextualSmallCoalgebraMaterialCoalgebra.enumeratedReadout_square worlds arrows A
      (IndexedCoalgebraBisimulation.original sourceParameter transition) receipts)

theorem fromEnumerated_parameter (receipts : ∀ point value,
    Enumeration ((IndexedCoalgebraBisimulation.original sourceParameter transition).app point value).val) :
    (fromEnumerated worlds arrows B sourceParameter transition receipts).comp (parameter worlds arrows B) =
      sourceParameter :=
  pairReadout_parameter worlds arrows B sourceParameter
    (ContextualSmallCoalgebraMaterialCoalgebra.enumeratedReadout worlds arrows A
      (IndexedCoalgebraBisimulation.original sourceParameter transition) receipts)

include sourceSquare in
theorem unique_enumerated (receipts : ∀ point value,
    Enumeration ((IndexedCoalgebraBisimulation.original sourceParameter transition).app point value).val) :
    ∃! operation : NaturalHom A (family worlds arrows B),
      (IndexedCoalgebraBisimulation.original sourceParameter transition).comp (imageHom operation) =
        operation.comp (coalgebra worlds arrows B) ∧ operation.comp (parameter worlds arrows B) = sourceParameter := by
  let actual := fromEnumerated worlds arrows B sourceParameter transition receipts
  have square := pairReadout_square worlds arrows B sourceParameter transition sourceSquare
    (ContextualSmallCoalgebraMaterialCoalgebra.enumeratedReadout worlds arrows A (IndexedCoalgebraBisimulation.original sourceParameter transition) receipts)
    (ContextualSmallCoalgebraMaterialCoalgebra.enumeratedReadout_square worlds arrows A
      (IndexedCoalgebraBisimulation.original sourceParameter transition) receipts)
  have base := pairReadout_parameter worlds arrows B sourceParameter
    (ContextualSmallCoalgebraMaterialCoalgebra.enumeratedReadout worlds arrows A (IndexedCoalgebraBisimulation.original sourceParameter transition) receipts)
  refine ⟨actual, ⟨square, base⟩, ?_⟩
  intro candidate laws
  exact maps_equal_over_base worlds arrows B sourceParameter transition candidate actual laws.1 square laws.2 base

theorem enumerated_kernel (receipts : ∀ point value,
    Enumeration ((IndexedCoalgebraBisimulation.original sourceParameter transition).app point value).val)
    (point : D) (first second : A.obj point) :
    (fromEnumerated worlds arrows B sourceParameter transition receipts).app point first =
      (fromEnumerated worlds arrows B sourceParameter transition receipts).app point second ↔
        IndexedCoalgebraBisimulation.Related sourceParameter transition point first second := by
  constructor
  · intro same
    exact ⟨(ContextualSmallCoalgebraMaterialCoalgebra.enumeratedReadout_eq_iff worlds arrows A
      (IndexedCoalgebraBisimulation.original sourceParameter transition) receipts point first second).mp
        (congrArg Prod.snd same), congrArg Prod.fst same⟩
  · intro related
    exact Prod.ext related.2
      ((ContextualSmallCoalgebraMaterialCoalgebra.enumeratedReadout_eq_iff worlds arrows A
        (IndexedCoalgebraBisimulation.original sourceParameter transition) receipts point first second).mpr related.1)

theorem enumerated_material_kernel (receipts : ∀ point value,
    Enumeration ((IndexedCoalgebraBisimulation.original sourceParameter transition).app point value).val)
    (point : D) (first second : A.obj point) :
    (sourceParameter.app point first = sourceParameter.app point second ∧
      ((memberDecode worlds arrows B).app point
        ((fromEnumerated worlds arrows B sourceParameter transition receipts).app point first)).val =
      ((memberDecode worlds arrows B).app point
        ((fromEnumerated worlds arrows B sourceParameter transition receipts).app point second)).val) ↔
      IndexedCoalgebraBisimulation.Related sourceParameter transition point first second :=
  (eq_iff_material worlds arrows B point _ _).symm.trans
    (enumerated_kernel worlds arrows B sourceParameter transition receipts point first second)

theorem fromEnumerated_independent
    (first second : ∀ point value,
      Enumeration ((IndexedCoalgebraBisimulation.original sourceParameter transition).app point value).val) :
    fromEnumerated worlds arrows B sourceParameter transition first =
      fromEnumerated worlds arrows B sourceParameter transition second :=
  congrArg (pairReadout worlds arrows B sourceParameter)
    (ContextualSmallCoalgebraMaterialCoalgebra.enumeratedReadout_independent worlds arrows A
      (IndexedCoalgebraBisimulation.original sourceParameter transition) first second)

include sourceSquare in
theorem paired_indexed_square (reading : NaturalHom A (Behavior worlds arrows))
    (readingSquare : (IndexedCoalgebraBisimulation.original sourceParameter transition).comp (imageHom reading) =
      reading.comp (behaviorCoalgebra worlds arrows)) :
    transition.comp (IndexedCoveredPower.image sourceParameter (parameter worlds arrows B)
      (pairReadout worlds arrows B sourceParameter reading) (pairReadout_parameter worlds arrows B sourceParameter reading)) =
        (pairReadout worlds arrows B sourceParameter reading).comp (indexedCoalgebra worlds arrows B) := by
  apply NaturalHom.ext
  intro point value
  apply Subtype.ext
  exact Prod.ext (congrArg (fun operation : NaturalHom A B => operation.app point value) sourceSquare)
    (congrArg (fun operation : NaturalHom A (CoveredFuturePowerFamilies.family (family worlds arrows B)) =>
      operation.app point value) (pairReadout_square worlds arrows B sourceParameter transition sourceSquare reading readingSquare))

end Source

section SmallSource

variable {A : D ⥤ Type u} (sourceParameter : NaturalHom A B)
variable (transition : NaturalHom A (IndexedCoveredPower.family sourceParameter))
variable (sourceSquare : transition.comp (IndexedCoveredPower.projection sourceParameter) = sourceParameter)

def smallReceipts (point : D) (value : A.obj point) :
    Enumeration ((IndexedCoalgebraBisimulation.original sourceParameter transition).app point value).val :=
  smallEnumeration ((IndexedCoalgebraBisimulation.original sourceParameter transition).app point value).val

def fromSmall : NaturalHom A (family worlds arrows B) :=
  fromEnumerated worlds arrows B sourceParameter transition (smallReceipts B sourceParameter transition)

include sourceSquare in
theorem fromSmall_square :
    (IndexedCoalgebraBisimulation.original sourceParameter transition).comp
      (imageHom (fromSmall worlds arrows B sourceParameter transition)) =
        (fromSmall worlds arrows B sourceParameter transition).comp (coalgebra worlds arrows B) :=
  fromEnumerated_square worlds arrows B sourceParameter transition sourceSquare
    (smallReceipts B sourceParameter transition)

theorem fromSmall_parameter :
    (fromSmall worlds arrows B sourceParameter transition).comp (parameter worlds arrows B) = sourceParameter :=
  fromEnumerated_parameter worlds arrows B sourceParameter transition (smallReceipts B sourceParameter transition)

theorem fromSmall_behavior :
    (fromSmall worlds arrows B sourceParameter transition).comp (behavior worlds arrows B) =
      ContextualSmallCoalgebraMaterialCoalgebra.smallReadout worlds arrows
        ⟨A, IndexedCoalgebraBisimulation.original sourceParameter transition⟩ := by
  let code : ContextualSmallCoalgebraGenerators.Code D :=
    ⟨A, IndexedCoalgebraBisimulation.original sourceParameter transition⟩
  change ContextualSmallCoalgebraMaterialCoalgebra.enumeratedReadout worlds arrows A
      (IndexedCoalgebraBisimulation.original sourceParameter transition)
        (smallReceipts B sourceParameter transition) =
    ContextualSmallCoalgebraMaterialCoalgebra.smallReadout worlds arrows code
  exact ContextualSmallCoalgebraGenerators.maps_equal_into_separated
    (IndexedCoalgebraBisimulation.original sourceParameter transition) (behaviorCoalgebra worlds arrows)
    (ContextualSmallCoalgebraMaterialCoalgebra.enumeratedReadout worlds arrows A
      (IndexedCoalgebraBisimulation.original sourceParameter transition) (smallReceipts B sourceParameter transition))
    (ContextualSmallCoalgebraMaterialCoalgebra.smallReadout worlds arrows code)
    (ContextualSmallCoalgebraMaterialCoalgebra.enumeratedReadout_square worlds arrows A
      (IndexedCoalgebraBisimulation.original sourceParameter transition) (smallReceipts B sourceParameter transition))
    (ContextualSmallCoalgebraMaterialCoalgebra.smallReadout_square worlds arrows code)
    (ContextualSmallCoalgebraMaterialCoalgebra.class_separated worlds arrows)

theorem fromSmall_member_value (point : D) (value : A.obj point) :
    ((memberDecode worlds arrows B).app point
      ((fromSmall worlds arrows B sourceParameter transition).app point value)).val =
      HSet.lift (ContextualCoalgebraMaterialReadout.value
        (IndexedCoalgebraBisimulation.original sourceParameter transition) worlds arrows ⟨point, value⟩) := by
  have same := congrArg (fun operation : NaturalHom A (Behavior worlds arrows) =>
    ((ContextualSmallCoalgebraMaterialCarrier.classToMembers worlds arrows).app point
      (operation.app point value)).val) (fromSmall_behavior worlds arrows B sourceParameter transition)
  exact same.trans (ContextualSmallCoalgebraMaterialCoalgebra.smallReadout_value worlds arrows
    ⟨A, IndexedCoalgebraBisimulation.original sourceParameter transition⟩ point value)

include sourceSquare in
theorem unique_small : ∃! operation : NaturalHom A (family worlds arrows B),
    (IndexedCoalgebraBisimulation.original sourceParameter transition).comp (imageHom operation) =
      operation.comp (coalgebra worlds arrows B) ∧ operation.comp (parameter worlds arrows B) = sourceParameter :=
  unique_enumerated worlds arrows B sourceParameter transition sourceSquare (smallReceipts B sourceParameter transition)

theorem small_kernel (point : D) (first second : A.obj point) :
    (fromSmall worlds arrows B sourceParameter transition).app point first =
      (fromSmall worlds arrows B sourceParameter transition).app point second ↔
        IndexedCoalgebraBisimulation.Related sourceParameter transition point first second :=
  enumerated_kernel worlds arrows B sourceParameter transition (smallReceipts B sourceParameter transition) point first second

end SmallSource

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSliceRecipient
