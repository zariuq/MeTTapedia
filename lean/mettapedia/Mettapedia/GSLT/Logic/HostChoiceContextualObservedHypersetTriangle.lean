import Mettapedia.GSLT.Logic.ContextualObservedMaterialFamily
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualHypersetFamilyClosure

/-!
# Observed executions and actual sets over one context site

The constructed observed class is retained alongside the unlabelled final
set readout. Its first coordinate preserves precisely the declared atoms
and complete contextual behavior; its second coordinate is an actual
set-model value. Forgetting the observed coordinate is licensed exactly
when ordinary contextual bisimulation preserves every declared atom.

The class also retains its independently constructed material graph value.
Neither that value nor the final set readout recovers authored occurrences.
Natural atomic membership encoding is constructed by stable separation,
and exists exactly for transport-stable atomic truth. Arbitrary changing
observations remain in the structured interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.HostChoiceContextualObservedHypersetTriangle

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open HostChoiceContextualSetInterpretation HostChoiceContextualSetInterpretation.Finality
open ContextualCoalgebraLabelledGraph ContextualObservedCoalgebra

universe u v
variable {D : Type u} [Category.{u} D] {A : D ⥤ Type u}

noncomputable def setReadout {B : D ⥤ Type v}
    (operation : NaturalHom B (CoveredFuturePowerFamilies.family B)) : NaturalHom B (sets (D := D)) :=
  (HostChoiceContextualCoalgebraFinality.readout operation).comp
    (HostChoiceContextualCoalgebraFinality.raise.{u,0,u+1}
      (ContextualSmallCoalgebraGenerators.quotient (D := D)))

theorem setReadout_square {B : D ⥤ Type v}
    (operation : NaturalHom B (CoveredFuturePowerFamilies.family B)) :
    operation.comp (CoveredFuturePowerFunctor.imageHom (setReadout operation)) =
      (setReadout operation).comp unfold :=
  ContextualSmallCoalgebraComparisons.compose_square operation _ _ _ _
    (HostChoiceContextualCoalgebraFinality.readout_square operation)
    (HostChoiceContextualCoalgebraFinality.raise_square.{u,0,u+1} _)

theorem setReadout_kernel {B : D ⥤ Type v}
    (operation : NaturalHom B (CoveredFuturePowerFamilies.family B)) (point : D) (left right : B.obj point) :
    (setReadout operation).app point left = (setReadout operation).app point right ↔
      ContextualCoalgebraBisimulation.Bisimilar operation point left right := by
  change ULift.up ((HostChoiceContextualCoalgebraFinality.readout operation).app point left) =
    ULift.up ((HostChoiceContextualCoalgebraFinality.readout operation).app point right) ↔ _
  exact (Equiv.ulift.symm.injective.eq_iff).trans
    (HostChoiceContextualCoalgebraFinality.readout_kernel operation point left right)

theorem setReadout_future {B : D ⥤ Type v}
    (operation : NaturalHom B (CoveredFuturePowerFamilies.family B))
    (point target : D) (arrow : point ⟶ target) (argument : B.obj point) (child : sets.obj target) :
    FutureMember arrow child ((setReadout operation).app point argument) ↔
      ∃ original : B.obj target, (setReadout operation).app target original = child ∧
        (operation.app point argument).val.holds ⟨⟨target, arrow⟩, original⟩ :=
  ContextualCoalgebraBisimulation.coalgebra_map_truth operation (setReadout operation)
    unfold (setReadout_square operation) point argument ⟨target, arrow⟩ child

variable (source : NaturalHom A (CoveredFuturePowerFamilies.family A))
variable {Atom : Type u} (atoms : Atom → State A → Prop)
variable (worlds : ArgumentCoding D)
variable (arrows : (first second : D) → ArgumentCoding (first ⟶ second))
variable (atomCoding : ArgumentCoding Atom)

abbrev observedClasses := ContextualObservedMaterialFamily.classes source atoms worlds arrows atomCoding
abbrev observedProjection := ContextualObservedMaterialFamily.classObservation source atoms worlds arrows atomCoding
abbrev observedDecode := ContextualObservedMaterialFamily.decode source atoms worlds arrows atomCoding
abbrev observedCoalgebra := ContextualObservedMaterialFamily.classCoalgebra source atoms worlds arrows atomCoding

noncomputable def classSetReadout : NaturalHom (observedClasses source atoms worlds arrows atomCoding) sets :=
  setReadout (observedCoalgebra source atoms worlds arrows atomCoding)

theorem source_class_set_square :
    (observedProjection source atoms worlds arrows atomCoding).comp
      (classSetReadout source atoms worlds arrows atomCoding) = setReadout source :=
  HostChoiceContextualCoalgebraFinality.maps_equal_into_lift source
    ContextualSmallCoalgebraGenerators.quotientCoalgebra ContextualSmallCoalgebraGenerators.quotient_separated _ _
    (ContextualSmallCoalgebraComparisons.compose_square source
      (observedCoalgebra source atoms worlds arrows atomCoding) unfold _ _
      (ContextualObservedMaterialFamily.classObservation_square source atoms worlds arrows atomCoding)
      (setReadout_square _)) (setReadout_square source)

abbrev structured := CoveredFuturePowerClassifier.product
  (observedClasses source atoms worlds arrows atomCoding) (sets (D := D))

def retainedClass : NaturalHom (structured source atoms worlds arrows atomCoding)
    (observedClasses source atoms worlds arrows atomCoding) where
  app _ receipt := receipt.1
  naturality _ _ := rfl

def materialProjection : NaturalHom (structured source atoms worlds arrows atomCoding) (sets (D := D)) where
  app _ receipt := receipt.2
  naturality _ _ := rfl

noncomputable def retain : NaturalHom (observedClasses source atoms worlds arrows atomCoding)
    (structured source atoms worlds arrows atomCoding) where
  app point receipt := (receipt, (classSetReadout source atoms worlds arrows atomCoding).app point receipt)
  naturality step receipt := Prod.ext rfl ((classSetReadout source atoms worlds arrows atomCoding).naturality step receipt)

noncomputable def structuredReadout : NaturalHom A (structured source atoms worlds arrows atomCoding) :=
  (observedProjection source atoms worlds arrows atomCoding).comp (retain source atoms worlds arrows atomCoding)

theorem retain_class : (retain source atoms worlds arrows atomCoding).comp
    (retainedClass source atoms worlds arrows atomCoding) =
      ContextualSmallMapConstructions.identity (observedClasses source atoms worlds arrows atomCoding) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem retain_material : (retain source atoms worlds arrows atomCoding).comp
    (materialProjection source atoms worlds arrows atomCoding) = classSetReadout source atoms worlds arrows atomCoding := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem structured_kernel (point : D) (left right : A.obj point) :
    (structuredReadout source atoms worlds arrows atomCoding).app point left =
        (structuredReadout source atoms worlds arrows atomCoding).app point right ↔
      ObservedBisimilar source atoms point left right := by
  refine Iff.trans ?_ (ContextualObservedMaterialFamily.classObservation_eq_iff source atoms worlds arrows atomCoding point left right)
  constructor
  · exact fun same => congrArg Prod.fst same
  · intro same
    exact Prod.ext same (congrArg ((classSetReadout source atoms worlds arrows atomCoding).app point) same)

theorem structured_material_square : (structuredReadout source atoms worlds arrows atomCoding).comp
    (materialProjection source atoms worlds arrows atomCoding) = setReadout source :=
  source_class_set_square source atoms worlds arrows atomCoding

theorem structured_graph_square : (structuredReadout source atoms worlds arrows atomCoding).comp
    ((retainedClass source atoms worlds arrows atomCoding).comp (observedDecode source atoms worlds arrows atomCoding)) =
      ContextualObservedMaterialFamily.observation source atoms worlds arrows atomCoding := by
  apply NaturalHom.ext
  intro point argument
  exact ContextualMaterialReadoutFamilies.decode_encode A
    (ContextualObservedMaterialFamily.graphs source atoms worlds arrows atomCoding)
    (ContextualObservedMaterialFamily.stable source atoms worlds arrows atomCoding) point _

def PlainAtomInvariant : Prop := ∀ point (left right : A.obj point),
  ContextualCoalgebraBisimulation.Bisimilar source point left right →
    ∀ atom, atoms atom ⟨point, left⟩ ↔ atoms atom ⟨point, right⟩

theorem observed_implies_plain (point : D) (left right : A.obj point)
    (related : ObservedBisimilar source atoms point left right) :
    ContextualCoalgebraBisimulation.Bisimilar source point left right := by
  obtain ⟨relation, bisimulation, related⟩ := related
  exact ⟨relation, bisimulation.underlying, related⟩

theorem bare_value_exact_iff :
    (∀ point (left right : A.obj point),
      (setReadout source).app point left = (setReadout source).app point right ↔
        ObservedBisimilar source atoms point left right) ↔ PlainAtomInvariant source atoms := by
  constructor
  · intro exactKernel point left right related atom
    exact observed_bisimilar_atoms source atoms
      ((exactKernel point left right).mp ((setReadout_kernel source point left right).mpr related)) atom
  · intro invariant point left right
    refine (setReadout_kernel source point left right).trans ?_
    constructor
    · rintro ⟨relation, bisimulation, related⟩
      exact ⟨relation, {
        underlying := bisimulation
        atoms := fun {_ first second} relates atom => invariant _ first second ⟨relation, bisimulation, relates⟩ atom }, related⟩
    · exact observed_implies_plain source atoms point left right

def AtomStable (atom : Atom) : Prop := ∀ {first second : D} (step : first ⟶ second) (argument : A.obj first),
  atoms atom ⟨first, argument⟩ → atoms atom ⟨second, A.map step argument⟩

def classAtom (atom : Atom) (point : (observedClasses source atoms worlds arrows atomCoding).Elements) : Prop :=
  ContextualObservedMaterialFamily.classAtoms source atoms worlds arrows atomCoding atom ⟨point.1, point.2⟩

theorem classAtom_stable (atom : Atom) (stable : AtomStable atoms atom)
    {first second : (observedClasses source atoms worlds arrows atomCoding).Elements} (step : first ⟶ second)
    (available : classAtom source atoms worlds arrows atomCoding atom first) :
    classAtom source atoms worlds arrows atomCoding atom second := by
  obtain ⟨argument, represents, holds⟩ := available
  refine ⟨A.map step.1 argument, ?_, stable step.1 argument holds⟩
  exact ((observedProjection source atoms worlds arrows atomCoding).naturality step.1 argument).symm.trans
    ((congrArg ((observedClasses source atoms worlds arrows atomCoding).map step.1) represents).trans step.2)

def atomicTest (atom : Atom) (stable : AtomStable atoms atom) :
    CoveredFuturePowerClassifier.StablePredicate (CoveredFuturePowerClassifier.product
      (observedClasses source atoms worlds arrows atomCoding) (sets (D := D))) where
  holds point := classAtom source atoms worlds arrows atomCoding atom ⟨point.1, point.2.1⟩
  closed {first second} step available := classAtom_stable source atoms worlds arrows atomCoding atom stable
    (CategoryOfElements.homMk (F := observedClasses source atoms worlds arrows atomCoding)
      ⟨first.1, first.2.1⟩ ⟨second.1, second.2.1⟩ step.1 (congrArg Prod.fst step.2)) available

noncomputable def markerInput : NaturalHom (observedClasses source atoms worlds arrows atomCoding)
    (CoveredFuturePowerClassifier.product (observedClasses source atoms worlds arrows atomCoding) sets) where
  app point receipt := (receipt, singletonSet.app point (emptySet.val point))
  naturality step _ := Prod.ext rfl
    (((singletonSet (D := D)).naturality step (emptySet.val _)).trans
      (congrArg (singletonSet.app _) (emptySet.property step)))

noncomputable def atomicEncoding (atom : Atom) (stable : AtomStable atoms atom) :
    NaturalHom (observedClasses source atoms worlds arrows atomCoding) sets :=
  (markerInput source atoms worlds arrows atomCoding).comp
    (separationSet _ (atomicTest source atoms worlds arrows atomCoding atom stable))

theorem atomicEncoding_truth (atom : Atom) (stable : AtomStable atoms atom)
    (point : D) (receipt : (observedClasses source atoms worlds arrows atomCoding).obj point) :
    Member point (emptySet.val point) ((atomicEncoding source atoms worlds arrows atomCoding atom stable).app point receipt) ↔
      classAtom source atoms worlds arrows atomCoding atom ⟨point, receipt⟩ := by
  refine (member_separation _ (atomicTest source atoms worlds arrows atomCoding atom stable)
    point receipt (singletonSet.app point (emptySet.val point)) (emptySet.val point)).trans ?_
  exact ⟨fun available => available.2,
    fun available => ⟨(member_singleton _ _ _).mpr rfl, available⟩⟩

theorem natural_atomic_membership_iff_stable (atom : Atom) :
    (∃ encoding : NaturalHom (observedClasses source atoms worlds arrows atomCoding) sets,
      ∀ point argument, atoms atom ⟨point, argument⟩ ↔
        Member point (emptySet.val point)
          (encoding.app point ((observedProjection source atoms worlds arrows atomCoding).app point argument))) ↔
      AtomStable atoms atom := by
  constructor
  · rintro ⟨encoding, truth⟩ first second step argument available
    have transported := member_transport step ((truth first argument).mp available)
    rw [emptySet.property step, encoding.naturality step,
      (observedProjection source atoms worlds arrows atomCoding).naturality step] at transported
    exact (truth second (A.map step argument)).mpr transported
  · intro stable
    refine ⟨atomicEncoding source atoms worlds arrows atomCoding atom stable, ?_⟩
    intro point argument
    exact (ContextualObservedMaterialFamily.classAtoms_square source atoms worlds arrows atomCoding atom ⟨point, argument⟩).trans
      (atomicEncoding_truth source atoms worlds arrows atomCoding atom stable point _).symm

end Mettapedia.GSLT.HostChoiceContextualObservedHypersetTriangle
