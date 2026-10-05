import Mettapedia.GSLT.Logic.ContextualObservedCoalgebraQuotient
import Mettapedia.OSLF.Bridges.TypeTheory.ContextualObservedNativeTypes

/-!
# Native predicate classification through an actual observed quotient

The observed quotient is constructed from the full stable relation that
preserves declared atoms and execution futures together. Native subfunctor
images and their sieve classifiers factor through this actual quotient
exactly when their predicates respect that relation at every context.

For any displayed family on the quotient, the actual reindexed family has
the same full native support image. This identifies comprehension predicates
without replacing inhabited fibres by selected dependent sections.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Bridges.TypeTheory.ContextualObservedNativeReadout

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open Mettapedia.GSLT ContextualObservedCoalgebra
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open Mettapedia.OSLF.Bridges.TypeTheory.ContextualObservedNativeTypes

universe u
variable {C : Type u} [Category.{u} C] {A : Cᵒᵖ ⥤ Type u}
variable (source : NaturalHom A (CoveredFuturePowerFamilies.family A))
variable {Atom : Type u} (atoms : Atom → ContextualCoalgebraLabelledGraph.State A → Prop)
variable (worlds : ArgumentCoding Cᵒᵖ)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))
variable (atomCoding : ArgumentCoding Atom)

abbrev observed := ContextualObservedCoalgebraQuotient.family source atoms worlds arrows atomCoding
abbrev projection := ContextualObservedCoalgebraQuotient.projection source atoms worlds arrows atomCoding
def readout : NatTrans A (observed source atoms worlds arrows atomCoding) :=
  (projection source atoms worlds arrows atomCoding).toNatTrans

def Invariant (predicate : Subfunctor A) : Prop := ∀ point left right,
  ObservedBisimilar source atoms point left right →
    (left ∈ predicate.obj point ↔ right ∈ predicate.obj point)

def image (predicate : Subfunctor A) : Subfunctor (observed source atoms worlds arrows atomCoding) where
  obj point := {value | ∃ argument, argument ∈ predicate.obj point ∧
    (projection source atoms worlds arrows atomCoding).app point argument = value}
  map {first second} step := by
    rintro _ ⟨argument, holds, rfl⟩
    exact ⟨A.map step argument, predicate.map step holds,
      ((projection source atoms worlds arrows atomCoding).naturality step argument).symm⟩

theorem image_at (predicate : Subfunctor A) (point : Cᵒᵖ) (argument : A.obj point) :
    (projection source atoms worlds arrows atomCoding).app point argument ∈
      (image source atoms worlds arrows atomCoding predicate).obj point ↔
        ∃ other, other ∈ predicate.obj point ∧ ObservedBisimilar source atoms point other argument :=
  exists_congr fun other => and_congr Iff.rfl
    (ContextualObservedCoalgebraQuotient.projection_eq_iff source atoms worlds arrows atomCoding point other argument)

theorem image_exact_iff (predicate : Subfunctor A) :
    preimage (readout source atoms worlds arrows atomCoding)
      (image source atoms worlds arrows atomCoding predicate) = predicate ↔ Invariant source atoms predicate := by
  constructor
  · intro exactImage point left right related
    have reflects (argument : A.obj point) :
        (projection source atoms worlds arrows atomCoding).app point argument ∈
          (image source atoms worlds arrows atomCoding predicate).obj point ↔ argument ∈ predicate.obj point := by
      change argument ∈ (preimage (readout source atoms worlds arrows atomCoding)
        (image source atoms worlds arrows atomCoding predicate)).obj point ↔ _
      rw [exactImage]
    have equal := (ContextualObservedCoalgebraQuotient.projection_eq_iff
      source atoms worlds arrows atomCoding point left right).mpr related
    exact (reflects left).symm.trans
      ((Iff.of_eq (congrArg (fun value => value ∈
        (image source atoms worlds arrows atomCoding predicate).obj point) equal)).trans (reflects right))
  · intro invariant
    ext point argument
    refine (image_at source atoms worlds arrows atomCoding predicate point argument).trans ?_
    constructor
    · rintro ⟨other, holds, related⟩
      exact (invariant point other argument related).mp holds
    · intro holds
      exact ⟨argument, holds, (ContextualObservedCoalgebraQuotient.projection_eq_iff
        source atoms worlds arrows atomCoding point argument argument).mp rfl⟩

def descendedClassifier (predicate : Subfunctor A) :
    NatTrans (observed source atoms worlds arrows atomCoding) (Mettapedia.GSLT.Topos.omegaFunctor (C := C)) :=
  Classifier.characteristic (image source atoms worlds arrows atomCoding predicate)

theorem descendedClassifier_square (predicate : Subfunctor A) (invariant : Invariant source atoms predicate)
    (point : Cᵒᵖ) (argument : A.obj point) :
    (descendedClassifier source atoms worlds arrows atomCoding predicate).app point
        ((projection source atoms worlds arrows atomCoding).app point argument) =
      (Classifier.characteristic predicate).app point argument := by
  have exactImage := (image_exact_iff source atoms worlds arrows atomCoding predicate).mpr invariant
  have square := Classifier.characteristic_reindex (readout source atoms worlds arrows atomCoding)
    (image source atoms worlds arrows atomCoding predicate) point argument
  rw [exactImage] at square
  exact square.symm

theorem classifier_factors_iff (predicate : Subfunctor A) :
    (∃ classifier : NatTrans (observed source atoms worlds arrows atomCoding)
        (Mettapedia.GSLT.Topos.omegaFunctor (C := C)),
      ∀ point argument, classifier.app point ((projection source atoms worlds arrows atomCoding).app point argument) =
        (Classifier.characteristic predicate).app point argument) ↔ Invariant source atoms predicate := by
  constructor
  · rintro ⟨classifier, factors⟩ point left right related
    have equal := (ContextualObservedCoalgebraQuotient.projection_eq_iff
      source atoms worlds arrows atomCoding point left right).mpr related
    have sieves := (factors point left).symm.trans
      ((congrArg (classifier.app point) equal).trans (factors point right))
    have truths := congrArg (fun sieve : Sieve point.unop => sieve.arrows (𝟙 point.unop)) sieves
    exact (Classifier.characteristic_truth predicate point left).symm.trans
      ((Iff.of_eq truths).trans (Classifier.characteristic_truth predicate point right))
  · intro invariant
    exact ⟨descendedClassifier source atoms worlds arrows atomCoding predicate,
      descendedClassifier_square source atoms worlds arrows atomCoding predicate invariant⟩

theorem classifier_unique (predicate : Subfunctor A) (invariant : Invariant source atoms predicate) :
    ∃! classifier : NatTrans (observed source atoms worlds arrows atomCoding)
        (Mettapedia.GSLT.Topos.omegaFunctor (C := C)),
      ∀ point argument, classifier.app point ((projection source atoms worlds arrows atomCoding).app point argument) =
        (Classifier.characteristic predicate).app point argument := by
  refine ⟨descendedClassifier source atoms worlds arrows atomCoding predicate,
    descendedClassifier_square source atoms worlds arrows atomCoding predicate invariant, ?_⟩
  intro classifier factors
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro value
  obtain ⟨argument, rfl⟩ := ContextualObservedCoalgebraQuotient.projection_cover
    source atoms worlds arrows atomCoding point value
  exact (factors point argument).trans
    (descendedClassifier_square source atoms worlds arrows atomCoding predicate invariant point argument).symm

namespace Families

open Mettapedia.GSLT.Topos
open Mettapedia.TypeTheory.DisplayedPresheafTransport

variable (family : DisplayedFamily.{u, u, u, u} (observed source atoms worlds arrows atomCoding))

def sourceFamily : DisplayedFamily.{u, u, u, u} A :=
  PowerClassPresheafProducts.reindex (readout source atoms worlds arrows atomCoding) family

theorem source_support_invariant : Invariant source atoms
    (support (sourceFamily source atoms worlds arrows atomCoding family)) := by
  intro point left right related
  have same := (ContextualObservedCoalgebraQuotient.projection_eq_iff
    source atoms worlds arrows atomCoding point left right).mpr related
  change Nonempty (family.obj ⟨point, (projection source atoms worlds arrows atomCoding).app point left⟩) ↔
    Nonempty (family.obj ⟨point, (projection source atoms worlds arrows atomCoding).app point right⟩)
  exact Iff.of_eq (congrArg (fun value => Nonempty (family.obj ⟨point, value⟩)) same)

theorem source_support_image : image source atoms worlds arrows atomCoding
    (support (sourceFamily source atoms worlds arrows atomCoding family)) = support family := by
  ext point value
  change (∃ argument, Nonempty (family.obj ⟨point,
    (projection source atoms worlds arrows atomCoding).app point argument⟩) ∧
      (projection source atoms worlds arrows atomCoding).app point argument = value) ↔ Nonempty (family.obj ⟨point, value⟩)
  constructor
  · rintro ⟨argument, inhabited, rfl⟩
    exact inhabited
  · intro inhabited
    obtain ⟨argument, same⟩ := ContextualObservedCoalgebraQuotient.projection_cover
      source atoms worlds arrows atomCoding point value
    exact ⟨argument, same.symm ▸ inhabited, same⟩

theorem source_family_classifier_unique :
    ∃! classifier : NatTrans (observed source atoms worlds arrows atomCoding)
        (Mettapedia.GSLT.Topos.omegaFunctor (C := C)),
      ∀ point argument, classifier.app point ((projection source atoms worlds arrows atomCoding).app point argument) =
        (Classifier.characteristic (support (sourceFamily source atoms worlds arrows atomCoding family))).app point argument :=
  classifier_unique source atoms worlds arrows atomCoding _
    (source_support_invariant source atoms worlds arrows atomCoding family)

end Families

end Mettapedia.OSLF.Bridges.TypeTheory.ContextualObservedNativeReadout
