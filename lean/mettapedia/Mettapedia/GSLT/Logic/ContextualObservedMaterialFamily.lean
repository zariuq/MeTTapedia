import Mettapedia.GSLT.Logic.ContextualObservedCoalgebraQuotient
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialReadoutFamilies

/-!
# Constructed material families for declared contextual executions

The observed execution graph, including declared atomic rows, supplies an
actual material member family and a smaller class face with inverse decoding.
The proved observed kernel constructs their context maps without choosing
source occurrences. Matching actual future children constructs a covered
coalgebra on these members at the original branch bound.

Observation has exactly the complete observed-bisimulation kernel. Context
transport and material membership are separate operations: new members may
appear later, while an existing member follows its constructed transport.
The class decoder is an inverse on members and compatible whole sections;
it is not an inverse into arbitrary occurrence/provenance data.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ContextualObservedMaterialFamily

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualWitnessCover
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualCoalgebraLabelledGraph ContextualObservedCoalgebra
open CoveredFuturePowerFunctor
open PowerClassPresheafBaseChange

universe u
variable {D : Type u} [Category.{u} D] {A : D ⥤ Type u}
variable (source : NaturalHom A (CoveredFuturePowerFamilies.family A))
variable {Atom : Type u} (atoms : Atom → State A → Prop)
variable (worlds : ArgumentCoding D)
variable (arrows : (first second : D) → ArgumentCoding (first ⟶ second))
variable (atomCoding : ArgumentCoding Atom)

abbrev graphs (point : D) (argument : A.obj point) : AccessiblePointedGraph.{u} :=
  valueGraph source atoms worlds arrows atomCoding ⟨point, argument⟩

theorem stable : ContextualMaterialReadoutFamilies.Stable A (graphs source atoms worlds arrows atomCoding) :=
  ContextualObservedCoalgebraQuotient.kernel_stable source atoms worlds arrows atomCoding

abbrev members : D ⥤ Type (u + 1) :=
  ContextualMaterialReadoutFamilies.family A (graphs source atoms worlds arrows atomCoding)
    (stable source atoms worlds arrows atomCoding)

abbrev classes : D ⥤ Type u :=
  ContextualMaterialReadoutFamilies.classFamily A (graphs source atoms worlds arrows atomCoding)
    (stable source atoms worlds arrows atomCoding)

abbrev observation : NaturalHom A (members source atoms worlds arrows atomCoding) :=
  ContextualMaterialReadoutFamilies.observation A (graphs source atoms worlds arrows atomCoding)
    (stable source atoms worlds arrows atomCoding)

abbrev classObservation : NaturalHom A (classes source atoms worlds arrows atomCoding) :=
  ContextualMaterialReadoutFamilies.classObservation A (graphs source atoms worlds arrows atomCoding)
    (stable source atoms worlds arrows atomCoding)

abbrev decode : NaturalHom (classes source atoms worlds arrows atomCoding)
    (members source atoms worlds arrows atomCoding) :=
  ContextualMaterialReadoutFamilies.decode A (graphs source atoms worlds arrows atomCoding)
    (stable source atoms worlds arrows atomCoding)

abbrev encode : NaturalHom (members source atoms worlds arrows atomCoding)
    (classes source atoms worlds arrows atomCoding) :=
  ContextualMaterialReadoutFamilies.encode A (graphs source atoms worlds arrows atomCoding)
    (stable source atoms worlds arrows atomCoding)

theorem observation_cover (point : D) : Function.Surjective
    ((observation source atoms worlds arrows atomCoding).app point) :=
  ContextualMaterialReadoutFamilies.observe_cover A (graphs source atoms worlds arrows atomCoding) point

theorem observation_value (point : D) (argument : A.obj point) :
    ((observation source atoms worlds arrows atomCoding).app point argument).val =
      value source atoms worlds arrows atomCoding ⟨point, argument⟩ := rfl

theorem observation_eq_iff (point : D) (left right : A.obj point) :
    (observation source atoms worlds arrows atomCoding).app point left =
        (observation source atoms worlds arrows atomCoding).app point right ↔
      ObservedBisimilar source atoms point left right :=
  (Iff.trans ⟨fun same => congrArg Subtype.val same, fun same => Subtype.ext same⟩
    (value_eq_iff source atoms worlds arrows atomCoding point left right))

theorem classObservation_eq_iff (point : D) (left right : A.obj point) :
    (classObservation source atoms worlds arrows atomCoding).app point left =
        (classObservation source atoms worlds arrows atomCoding).app point right ↔
      ObservedBisimilar source atoms point left right :=
  (ContextualMaterialReadoutFamilies.classObservation_eq_iff A
    (graphs source atoms worlds arrows atomCoding) (stable source atoms worlds arrows atomCoding) point left right).trans
      (value_eq_iff source atoms worlds arrows atomCoding point left right)

def children (point : D) (member : (members source atoms worlds arrows atomCoding).obj point) :
    CoveredFuturePowerFamilies.Predicate (members source atoms worlds arrows atomCoding) point where
  holds future := ∃ argument : A.obj point,
    (observation source atoms worlds arrows atomCoding).app point argument = member ∧
      ∃ child : A.obj future.1.1, (source.app point argument).val.holds ⟨future.1, child⟩ ∧
        (observation source atoms worlds arrows atomCoding).app future.1.1 child = future.2
  closed {first second} move available := by
    obtain ⟨argument, observes, child, admitted, childImage⟩ := available
    refine ⟨argument, observes, A.map move.1.1 child, ?_, ?_⟩
    · exact (source.app point argument).val.closed ⟨move.1, rfl⟩ admitted
    · exact ((observation source atoms worlds arrows atomCoding).naturality move.1.1 child).symm.trans
        ((congrArg ((members source atoms worlds arrows atomCoding).map move.1.1) childImage).trans move.2)

theorem children_observation_iff (point : D) (argument : A.obj point)
    (future : Future.Objects point) (member : (members source atoms worlds arrows atomCoding).obj future.1) :
    (children source atoms worlds arrows atomCoding point
      ((observation source atoms worlds arrows atomCoding).app point argument)).holds ⟨future, member⟩ ↔
      ∃ child : A.obj future.1, (observation source atoms worlds arrows atomCoding).app future.1 child = member ∧
        (source.app point argument).val.holds ⟨future, child⟩ := by
  constructor
  · rintro ⟨other, same, child, admitted, matched⟩
    obtain ⟨relation, bisimulation, related⟩ :=
      (observation_eq_iff source atoms worlds arrows atomCoding point other argument).mp same
    obtain ⟨matching, available, childrenRelated⟩ := bisimulation.underlying.forth related future admitted
    have sameChildren := (observation_eq_iff source atoms worlds arrows atomCoding future.1 child matching).mpr
      ⟨relation, bisimulation, childrenRelated⟩
    exact ⟨matching, sameChildren.symm.trans matched, available⟩
  · rintro ⟨child, same, admitted⟩
    exact ⟨argument, rfl, child, admitted, same⟩

theorem children_covered (point : D) (member : (members source atoms worlds arrows atomCoding).obj point) :
    Nonempty (CoveredFuturePowerFamilies.Enumeration (children source atoms worlds arrows atomCoding point member)) := by
  obtain ⟨argument, rfl⟩ := observation_cover source atoms worlds arrows atomCoding point member
  refine ⟨{
    Carrier := fun future => {child : A.obj future.1 // (source.app point argument).val.holds ⟨future, child⟩}
    value := fun future receipt => (observation source atoms worlds arrows atomCoding).app future.1 receipt.val
    covered := ?_ }⟩
  intro future member
  refine (children_observation_iff source atoms worlds arrows atomCoding point argument future member).trans ?_
  constructor
  · rintro ⟨child, same, admitted⟩
    exact ⟨⟨child, admitted⟩, same⟩
  · rintro ⟨receipt, same⟩
    exact ⟨receipt.val, same, receipt.property⟩

theorem children_restrict {first second : D} (step : first ⟶ second)
    (member : (members source atoms worlds arrows atomCoding).obj first) :
    CoveredFuturePowerFamilies.restrict (members source atoms worlds arrows atomCoding) step
        (children source atoms worlds arrows atomCoding first member) =
      children source atoms worlds arrows atomCoding second
        ((members source atoms worlds arrows atomCoding).map step member) := by
  obtain ⟨argument, rfl⟩ := observation_cover source atoms worlds arrows atomCoding first member
  rw [(observation source atoms worlds arrows atomCoding).naturality]
  apply CoveredFuturePowerFamilies.Predicate.ext
  rintro ⟨⟨target, arrow⟩, child⟩
  change (members source atoms worlds arrows atomCoding).obj target at child
  change (children source atoms worlds arrows atomCoding first
      ((observation source atoms worlds arrows atomCoding).app first argument)).holds
      ⟨⟨target, step ≫ arrow⟩, child⟩ ↔
    (children source atoms worlds arrows atomCoding second
      ((observation source atoms worlds arrows atomCoding).app second (A.map step argument))).holds ⟨⟨target, arrow⟩, child⟩
  rw [children_observation_iff, children_observation_iff]
  apply exists_congr
  intro original
  apply and_congr_right
  intro _
  have same := congrArg (fun power : CoveredFuturePowerFamilies.Power A second => power.val.holds ⟨⟨target, arrow⟩, original⟩)
    (source.naturality step argument)
  exact ⟨fun available => same ▸ available, fun available => same.symm ▸ available⟩

def coalgebra : NaturalHom (members source atoms worlds arrows atomCoding)
    (CoveredFuturePowerFamilies.family (members source atoms worlds arrows atomCoding)) where
  app point member := ⟨children source atoms worlds arrows atomCoding point member,
    children_covered source atoms worlds arrows atomCoding point member⟩
  naturality step member := Subtype.ext (children_restrict source atoms worlds arrows atomCoding step member)

theorem observation_square : source.comp (imageHom (observation source atoms worlds arrows atomCoding)) =
    (observation source atoms worlds arrows atomCoding).comp (coalgebra source atoms worlds arrows atomCoding) := by
  apply NaturalHom.ext
  intro point argument
  apply Subtype.ext
  apply CoveredFuturePowerFamilies.Predicate.ext
  rintro ⟨future, member⟩
  exact (children_observation_iff source atoms worlds arrows atomCoding point argument future member).symm

def classCoalgebra : NaturalHom (classes source atoms worlds arrows atomCoding)
    (CoveredFuturePowerFamilies.family (classes source atoms worlds arrows atomCoding)) :=
  ((decode source atoms worlds arrows atomCoding).comp (coalgebra source atoms worlds arrows atomCoding)).comp
    (imageHom (encode source atoms worlds arrows atomCoding))

theorem encode_square : (coalgebra source atoms worlds arrows atomCoding).comp
      (imageHom (encode source atoms worlds arrows atomCoding)) =
    (encode source atoms worlds arrows atomCoding).comp (classCoalgebra source atoms worlds arrows atomCoding) := by
  apply NaturalHom.ext
  intro point member
  change imagePower (encode source atoms worlds arrows atomCoding) point ((coalgebra source atoms worlds arrows atomCoding).app point member) =
    imagePower (encode source atoms worlds arrows atomCoding) point ((coalgebra source atoms worlds arrows atomCoding).app point
      ((decode source atoms worlds arrows atomCoding).app point ((encode source atoms worlds arrows atomCoding).app point member)))
  exact congrArg (fun value => imagePower (encode source atoms worlds arrows atomCoding) point
    ((coalgebra source atoms worlds arrows atomCoding).app point value))
      (ContextualMaterialReadoutFamilies.decode_encode A (graphs source atoms worlds arrows atomCoding)
        (stable source atoms worlds arrows atomCoding) point member).symm

theorem classObservation_square : source.comp (imageHom (classObservation source atoms worlds arrows atomCoding)) =
    (classObservation source atoms worlds arrows atomCoding).comp (classCoalgebra source atoms worlds arrows atomCoding) :=
  ContextualSmallCoalgebraComparisons.compose_square source (coalgebra source atoms worlds arrows atomCoding)
    (classCoalgebra source atoms worlds arrows atomCoding) (observation source atoms worlds arrows atomCoding)
    (encode source atoms worlds arrows atomCoding) (observation_square source atoms worlds arrows atomCoding)
    (encode_square source atoms worlds arrows atomCoding)

def classAtoms (atom : Atom) (state : State (classes source atoms worlds arrows atomCoding)) : Prop :=
  ∃ argument : A.obj state.1,
    (classObservation source atoms worlds arrows atomCoding).app state.1 argument = state.2 ∧ atoms atom ⟨state.1, argument⟩

theorem classAtoms_square (atom : Atom) (state : State A) : atoms atom state ↔
    classAtoms source atoms worlds arrows atomCoding atom
      (graphMap (classObservation source atoms worlds arrows atomCoding) state) := by
  constructor
  · intro observed
    exact ⟨state.2, rfl, observed⟩
  · rintro ⟨argument, same, observed⟩
    exact (observed_bisimilar_atoms source atoms
      ((classObservation_eq_iff source atoms worlds arrows atomCoding state.1 argument state.2).mp same) atom).mp observed

abbrev classValue := value (classCoalgebra source atoms worlds arrows atomCoding)
  (classAtoms source atoms worlds arrows atomCoding) worlds arrows atomCoding

theorem classValue_square (state : State A) : value source atoms worlds arrows atomCoding state =
    classValue source atoms worlds arrows atomCoding
      (graphMap (classObservation source atoms worlds arrows atomCoding) state) :=
  ContextualObservedCoalgebraTransport.value_preservation source (classCoalgebra source atoms worlds arrows atomCoding)
    (classObservation source atoms worlds arrows atomCoding) (classObservation_square source atoms worlds arrows atomCoding)
    atoms (classAtoms source atoms worlds arrows atomCoding) (classAtoms_square source atoms worlds arrows atomCoding)
    worlds arrows atomCoding state

theorem classValue_decode (point : D) (memberClass : (classes source atoms worlds arrows atomCoding).obj point) :
    classValue source atoms worlds arrows atomCoding ⟨point, memberClass⟩ =
      ((decode source atoms worlds arrows atomCoding).app point memberClass).val := by
  obtain ⟨argument, rfl⟩ := ContextualMaterialReadoutFamilies.classObservation_cover A
    (graphs source atoms worlds arrows atomCoding) (stable source atoms worlds arrows atomCoding) point memberClass
  exact (classValue_square source atoms worlds arrows atomCoding ⟨point, argument⟩).symm.trans
    (congrArg Subtype.val (ContextualMaterialReadoutFamilies.decode_encode A
      (graphs source atoms worlds arrows atomCoding) (stable source atoms worlds arrows atomCoding) point
        ((observation source atoms worlds arrows atomCoding).app point argument))).symm

theorem classValue_injective (point : D) : Function.Injective
    (fun memberClass => classValue source atoms worlds arrows atomCoding ⟨point, memberClass⟩) := by
  intro first second same
  apply (ContextualMaterialReadoutFamilies.memberEquiv A (graphs source atoms worlds arrows atomCoding) point).injective
  exact Subtype.ext ((classValue_decode source atoms worlds arrows atomCoding point first).symm.trans
    (same.trans (classValue_decode source atoms worlds arrows atomCoding point second)))

theorem classObservedBisimilar_iff_eq (point : D)
    (left right : (classes source atoms worlds arrows atomCoding).obj point) :
    ObservedBisimilar (classCoalgebra source atoms worlds arrows atomCoding)
        (classAtoms source atoms worlds arrows atomCoding) point left right ↔ left = right :=
  (value_eq_iff (classCoalgebra source atoms worlds arrows atomCoding) (classAtoms source atoms worlds arrows atomCoding)
    worlds arrows atomCoding point left right).symm.trans
      ⟨fun same => classValue_injective source atoms worlds arrows atomCoding point same,
        fun same => congrArg (fun memberClass => classValue source atoms worlds arrows atomCoding ⟨point, memberClass⟩) same⟩

abbrev sectionEquiv : (classes source atoms worlds arrows atomCoding).sections ≃
    (members source atoms worlds arrows atomCoding).sections :=
  ContextualMaterialReadoutFamilies.sectionEquiv A (graphs source atoms worlds arrows atomCoding)
    (stable source atoms worlds arrows atomCoding)

end Mettapedia.GSLT.ContextualObservedMaterialFamily
