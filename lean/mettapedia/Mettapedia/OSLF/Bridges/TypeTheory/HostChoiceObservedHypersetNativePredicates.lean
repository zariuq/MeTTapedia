import Mettapedia.GSLT.Logic.HostChoiceContextualObservedHypersetTypes
import Mettapedia.GSLT.Logic.HostChoiceContextualObservedHypersetContinuations
import Mettapedia.OSLF.Bridges.TypeTheory.ContextualObservedNativeReadout

/-!
# Existing native sieve classifiers on structured observed set values

The small observed-class face carries the established presheaf Ω classifier.
Its characteristic map is extended to the wider class/set product by the
actual retained-class projection. A source classifier factors through that
structured readout exactly when its native predicate is invariant under the
declared observed kernel. Existential images choose no representatives.

Actual displayed families on the product induce source support predicates
and comprehension images. Their class images agree with support of the
reindexed full family on the retained class. These are predicate comparisons;
the actual dependent terms and full future products remain in their families.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Bridges.TypeTheory.HostChoiceObservedHypersetNativePredicates

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.GSLT ContextualObservedCoalgebra ContextualCoalgebraLabelledGraph
open HostChoiceContextualObservedHypersetTriangle
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open ContextualObservedNativeTypes

universe u v
variable {C : Type u} [Category.{u} C] {A : Cᵒᵖ ⥤ Type u}
variable (source : NaturalHom A (CoveredFuturePowerFamilies.family A))
variable {Atom : Type u} (atoms : Atom → State A → Prop)
variable (worlds : ArgumentCoding Cᵒᵖ)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))
variable (atomCoding : ArgumentCoding Atom)

abbrev Invariant := ContextualObservedNativeReadout.Invariant source atoms

def classImage (predicate : Subfunctor A) : Subfunctor (observedClasses source atoms worlds arrows atomCoding) where
  obj point := {value | ∃ argument, argument ∈ predicate.obj point ∧
    (observedProjection source atoms worlds arrows atomCoding).app point argument = value}
  map {first second} step := by
    rintro _ ⟨argument, holds, rfl⟩
    exact ⟨A.map step argument, predicate.map step holds,
      ((observedProjection source atoms worlds arrows atomCoding).naturality step argument).symm⟩

theorem classImage_at (predicate : Subfunctor A) (point : Cᵒᵖ) (argument : A.obj point) :
    (observedProjection source atoms worlds arrows atomCoding).app point argument ∈
        (classImage source atoms worlds arrows atomCoding predicate).obj point ↔
      ∃ other, other ∈ predicate.obj point ∧ ObservedBisimilar source atoms point other argument :=
  exists_congr fun other => and_congr Iff.rfl
    (ContextualObservedMaterialFamily.classObservation_eq_iff source atoms worlds arrows atomCoding point other argument)

theorem classImage_exact_iff (predicate : Subfunctor A) :
    preimage (observedProjection source atoms worlds arrows atomCoding).toNatTrans
        (classImage source atoms worlds arrows atomCoding predicate) = predicate ↔
      Invariant source atoms predicate := by
  constructor
  · intro exactImage point left right related
    have reflects (argument : A.obj point) :
        (observedProjection source atoms worlds arrows atomCoding).app point argument ∈
          (classImage source atoms worlds arrows atomCoding predicate).obj point ↔ argument ∈ predicate.obj point := by
      change argument ∈ (preimage (observedProjection source atoms worlds arrows atomCoding).toNatTrans
        (classImage source atoms worlds arrows atomCoding predicate)).obj point ↔ _
      rw [exactImage]
    have same := (ContextualObservedMaterialFamily.classObservation_eq_iff source atoms worlds arrows atomCoding
      point left right).mpr related
    exact (reflects left).symm.trans
      ((Iff.of_eq (congrArg (fun receipt => receipt ∈
        (classImage source atoms worlds arrows atomCoding predicate).obj point) same)).trans (reflects right))
  · intro invariant
    ext point argument
    refine (classImage_at source atoms worlds arrows atomCoding predicate point argument).trans ?_
    exact ⟨fun ⟨other, holds, related⟩ => (invariant point other argument related).mp holds,
      fun holds => ⟨argument, holds,
        (ContextualObservedMaterialFamily.classObservation_eq_iff source atoms worlds arrows atomCoding point argument argument).mp rfl⟩⟩

def classClassifier (predicate : Subfunctor A) :
    NatTrans (observedClasses source atoms worlds arrows atomCoding)
      (Mettapedia.GSLT.Topos.omegaFunctor (C := C)) :=
  Classifier.characteristic (classImage source atoms worlds arrows atomCoding predicate)

noncomputable def structuredClassifier (predicate : Subfunctor A) :
    NaturalHom (structured source atoms worlds arrows atomCoding)
      (Mettapedia.GSLT.Topos.omegaFunctor (C := C)) :=
  (retainedClass source atoms worlds arrows atomCoding).comp
    (NaturalHom.ofNatTrans (classClassifier source atoms worlds arrows atomCoding predicate))

theorem classifier_square (predicate : Subfunctor A) (invariant : Invariant source atoms predicate)
    (point : Cᵒᵖ) (argument : A.obj point) :
    (structuredClassifier source atoms worlds arrows atomCoding predicate).app point
        ((structuredReadout source atoms worlds arrows atomCoding).app point argument) =
      (Classifier.characteristic predicate).app point argument := by
  have square := Classifier.characteristic_reindex
    (observedProjection source atoms worlds arrows atomCoding).toNatTrans
    (classImage source atoms worlds arrows atomCoding predicate) point argument
  rw [(classImage_exact_iff source atoms worlds arrows atomCoding predicate).mpr invariant] at square
  exact square.symm

theorem structured_classifier_factors_iff (predicate : Subfunctor A) :
    (∃ classifier : NaturalHom (structured source atoms worlds arrows atomCoding)
        (Mettapedia.GSLT.Topos.omegaFunctor (C := C)),
      ∀ point argument, classifier.app point
          ((structuredReadout source atoms worlds arrows atomCoding).app point argument) =
        (Classifier.characteristic predicate).app point argument) ↔ Invariant source atoms predicate := by
  constructor
  · rintro ⟨classifier, square⟩ point left right related
    have same := (structured_kernel source atoms worlds arrows atomCoding point left right).mpr related
    have sieves := (square point left).symm.trans ((congrArg (classifier.app point) same).trans (square point right))
    have truth := congrArg (fun sieve : Sieve point.unop => sieve.arrows (𝟙 point.unop)) sieves
    exact (Classifier.characteristic_truth predicate point left).symm.trans
      ((Iff.of_eq truth).trans (Classifier.characteristic_truth predicate point right))
  · intro invariant
    exact ⟨structuredClassifier source atoms worlds arrows atomCoding predicate,
      classifier_square source atoms worlds arrows atomCoding predicate invariant⟩

/-- The quotient classifier and the predicate-class classifier agree on
every source observation. No inverse from classes into source syntax is used. -/
theorem old_native_classifier_square (predicate : Subfunctor A) (invariant : Invariant source atoms predicate)
    (point : Cᵒᵖ) (argument : A.obj point) :
    (classClassifier source atoms worlds arrows atomCoding predicate).app point
        ((observedProjection source atoms worlds arrows atomCoding).app point argument) =
      (ContextualObservedNativeReadout.descendedClassifier source atoms worlds arrows atomCoding predicate).app point
        ((ContextualObservedNativeReadout.projection source atoms worlds arrows atomCoding).app point argument) :=
  (classifier_square source atoms worlds arrows atomCoding predicate invariant point argument).trans
    (ContextualObservedNativeReadout.descendedClassifier_square source atoms worlds arrows atomCoding
      predicate invariant point argument).symm

theorem classClassifier_unique
    (first second : NatTrans (observedClasses source atoms worlds arrows atomCoding)
      (Mettapedia.GSLT.Topos.omegaFunctor (C := C)))
    (same : ∀ point argument,
      first.app point ((observedProjection source atoms worlds arrows atomCoding).app point argument) =
        second.app point ((observedProjection source atoms worlds arrows atomCoding).app point argument)) : first = second := by
  ext point receipt
  obtain ⟨argument, rfl⟩ := ContextualMaterialReadoutFamilies.classObservation_cover A
    (ContextualObservedMaterialFamily.graphs source atoms worlds arrows atomCoding)
    (ContextualObservedMaterialFamily.stable source atoms worlds arrows atomCoding) point receipt
  exact same point argument

section ActualFamilies

variable (family : (structured source atoms worlds arrows atomCoding).Elements ⥤ Type u)

noncomputable def sourceDisplayed : A.Elements ⥤ Type u :=
  ContextualSmallFamilyUniverse.restrict
    (ContextualSmallFamilyUniverse.elementMap (structuredReadout source atoms worlds arrows atomCoding)) family

noncomputable def sourceSupport : Subfunctor A where
  obj point := {argument | Nonempty (family.obj
    ⟨point, (structuredReadout source atoms worlds arrows atomCoding).app point argument⟩)}
  map {first second} step := by
    rintro _ ⟨term⟩
    exact ⟨family.map (CategoryOfElements.homMk _ _ step
      ((structuredReadout source atoms worlds arrows atomCoding).naturality step _)) term⟩

theorem support_invariant : Invariant source atoms (sourceSupport source atoms worlds arrows atomCoding family) := by
  intro point left right related
  have same := (structured_kernel source atoms worlds arrows atomCoding point left right).mpr related
  change Nonempty (family.obj ⟨point, (structuredReadout source atoms worlds arrows atomCoding).app point left⟩) ↔
    Nonempty (family.obj ⟨point, (structuredReadout source atoms worlds arrows atomCoding).app point right⟩)
  rw [same]

/-- Class support is support of the complete family restricted along the
retained class, rather than a chosen representative or chosen term. -/
noncomputable def classSupport : Subfunctor (observedClasses source atoms worlds arrows atomCoding) where
  obj point := {receipt | Nonempty (family.obj
    ⟨point, (retain source atoms worlds arrows atomCoding).app point receipt⟩)}
  map {first second} step := by
    rintro _ ⟨term⟩
    exact ⟨family.map (CategoryOfElements.homMk _ _ step
      ((retain source atoms worlds arrows atomCoding).naturality step _)) term⟩

theorem classImage_support :
    classImage source atoms worlds arrows atomCoding (sourceSupport source atoms worlds arrows atomCoding family) =
      classSupport source atoms worlds arrows atomCoding family := by
  ext point receipt
  constructor
  · rintro ⟨argument, holds, observes⟩
    change Nonempty (family.obj ⟨point, (retain source atoms worlds arrows atomCoding).app point receipt⟩)
    change Nonempty (family.obj ⟨point, (retain source atoms worlds arrows atomCoding).app point
      ((observedProjection source atoms worlds arrows atomCoding).app point argument)⟩) at holds
    rw [observes] at holds
    exact holds
  · intro holds
    obtain ⟨argument, rfl⟩ := ContextualMaterialReadoutFamilies.classObservation_cover A
      (ContextualObservedMaterialFamily.graphs source atoms worlds arrows atomCoding)
      (ContextualObservedMaterialFamily.stable source atoms worlds arrows atomCoding) point receipt
    exact ⟨argument, holds, rfl⟩

theorem support_classifier_square (point : Cᵒᵖ) (argument : A.obj point) :
    (Classifier.characteristic (classSupport source atoms worlds arrows atomCoding family)).app point
        ((observedProjection source atoms worlds arrows atomCoding).app point argument) =
      (Classifier.characteristic (sourceSupport source atoms worlds arrows atomCoding family)).app point argument := by
  rw [← classImage_support]
  exact classifier_square source atoms worlds arrows atomCoding _
    (support_invariant source atoms worlds arrows atomCoding family) point argument

/-- The source predicate is the genuine comprehension image of the full
reindexed family. The witness is retained in the comprehension object. -/
theorem source_comprehension_image :
    image (ContextualSmallFamilyUniverse.projection
      (sourceDisplayed source atoms worlds arrows atomCoding family)).toNatTrans ⊤ =
        sourceSupport source atoms worlds arrows atomCoding family := by
  ext point argument
  constructor
  · rintro ⟨receipt, _, same⟩
    change receipt.1 = argument at same
    subst argument
    exact ⟨receipt.2⟩
  · rintro ⟨term⟩
    exact ⟨⟨argument, term⟩, trivial, rfl⟩

theorem full_family_decoder :
    ContextualSmallFamilyUniverse.decodedFamily
      (ContextualSmallFamilyUniverse.classifier
        (sourceDisplayed source atoms worlds arrows atomCoding family)) =
      sourceDisplayed source atoms worlds arrows atomCoding family :=
  ContextualSmallFamilyUniverse.decoded_classifier_eq _

end ActualFamilies

section Reindex

variable {B : Cᵒᵖ ⥤ Type u} (change : NatTrans B A)

def classImageUnder (predicate : Subfunctor A) : Subfunctor (observedClasses source atoms worlds arrows atomCoding) :=
  classImage source atoms worlds arrows atomCoding (image change (⊤ : Subfunctor B) ⊓ predicate)

/-- The native classifier square follows the actual context substitution at
every sieve arrow. Substitution does not require choosing class preimages. -/
theorem classifier_substitution (predicate : Subfunctor A) (invariant : Invariant source atoms predicate)
    (point : Cᵒᵖ) (argument : B.obj point) :
    (structuredClassifier source atoms worlds arrows atomCoding predicate).app point
        ((structuredReadout source atoms worlds arrows atomCoding).app point (change.app point argument)) =
      (Classifier.characteristic (preimage change predicate)).app point argument :=
  (classifier_square source atoms worlds arrows atomCoding predicate invariant point _).trans
    (Classifier.characteristic_reindex change predicate point argument).symm

end Reindex

end Mettapedia.OSLF.Bridges.TypeTheory.HostChoiceObservedHypersetNativePredicates
