import Mathlib.CategoryTheory.Category.Basic
import Mettapedia.TypeTheory.ExtensionalReadout

/-!
# Morphisms of split extensional readouts

A split readout is an intensional carrier, an extensional carrier, a
surjective observation, and a selected canonical representative.  A morphism
must preserve both the observation square and the canonical representatives.
Preserving only one of the two is insufficient for transporting the intended
intensional/extensional interface.

Bundled split readouts and these morphisms form a category.  Exactness
reflects along a morphism whose intensional map is injective.  It transports
forward when the intensional map is surjective and the extensional map is
injective.  These hypotheses are explicit because a commuting square alone
may discard distinctions on either side.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.SplitReadoutMorphism

open CategoryTheory
open Mettapedia.TypeTheory.ExtensionalReadout

universe uSource uTarget

/-- A split extensional readout with both carriers bundled. -/
structure Object where
  Source : Type uSource
  Target : Type uTarget
  readout : SplitReadout Source Target

namespace Object

/-- A map of split readouts preserves the observation square and the selected
canonical representatives. -/
structure Hom (first second : Object.{uSource, uTarget}) where
  sourceMap : first.Source -> second.Source
  targetMap : first.Target -> second.Target
  observe_natural : forall source,
    second.readout.observe (sourceMap source) =
      targetMap (first.readout.observe source)
  representative_natural : forall target,
    sourceMap (first.readout.representative target) =
      second.readout.representative (targetMap target)

namespace Hom

variable {first second third fourth : Object.{uSource, uTarget}}

@[ext]
theorem ext {left right : Hom first second}
    (sameSource : left.sourceMap = right.sourceMap)
    (sameTarget : left.targetMap = right.targetMap) : left = right := by
  cases left
  cases right
  cases sameSource
  cases sameTarget
  rfl

/-- Identity map of a split readout. -/
def identity (object : Object.{uSource, uTarget}) : Hom object object where
  sourceMap := id
  targetMap := id
  observe_natural := fun _ => rfl
  representative_natural := fun _ => rfl

/-- Composition of split-readout maps. -/
def comp (earlier : Hom first second) (later : Hom second third) :
    Hom first third where
  sourceMap := later.sourceMap ∘ earlier.sourceMap
  targetMap := later.targetMap ∘ earlier.targetMap
  observe_natural := by
    intro source
    calc
      third.readout.observe
          (later.sourceMap (earlier.sourceMap source)) =
        later.targetMap
          (second.readout.observe (earlier.sourceMap source)) :=
        later.observe_natural _
      _ = later.targetMap
          (earlier.targetMap (first.readout.observe source)) :=
        congrArg later.targetMap (earlier.observe_natural source)
  representative_natural := by
    intro target
    calc
      later.sourceMap
          (earlier.sourceMap (first.readout.representative target)) =
        later.sourceMap
          (second.readout.representative (earlier.targetMap target)) :=
        congrArg later.sourceMap (earlier.representative_natural target)
      _ = third.readout.representative
          (later.targetMap (earlier.targetMap target)) :=
        later.representative_natural _

/-- Canonicalization is natural along every split-readout morphism. -/
theorem canonicalize_natural (morphism : Hom first second)
    (source : first.Source) :
    morphism.sourceMap (first.readout.canonicalize source) =
      second.readout.canonicalize (morphism.sourceMap source) := by
  unfold SplitReadout.canonicalize
  calc
    morphism.sourceMap
        (first.readout.representative (first.readout.observe source)) =
      second.readout.representative
        (morphism.targetMap (first.readout.observe source)) :=
      morphism.representative_natural _
    _ = second.readout.representative
        (second.readout.observe (morphism.sourceMap source)) :=
      congrArg second.readout.representative
        (morphism.observe_natural source).symm

/-- Faithfulness reflects from the target readout when the intensional map is
injective. -/
theorem source_faithful_of_target_faithful
    (morphism : Hom first second)
    (sourceInjective : Function.Injective morphism.sourceMap)
    (targetFaithful : second.readout.Faithful) :
    first.readout.Faithful := by
  intro left right sameObservation
  apply sourceInjective
  apply targetFaithful
  rw [morphism.observe_natural, morphism.observe_natural, sameObservation]

/-- Exactness reflects under the same injectivity hypothesis because every
split readout is already surjective. -/
theorem source_exact_of_target_exact
    (morphism : Hom first second)
    (sourceInjective : Function.Injective morphism.sourceMap)
    (targetExact : second.readout.Exact) :
    first.readout.Exact := by
  apply first.readout.exact_iff_faithful.mpr
  exact morphism.source_faithful_of_target_faithful sourceInjective
    (second.readout.exact_iff_faithful.mp targetExact)

/-- Faithfulness transports to the target when every target intensional value
comes from the source and the extensional map reflects equality. -/
theorem target_faithful_of_source_faithful
    (morphism : Hom first second)
    (sourceSurjective : Function.Surjective morphism.sourceMap)
    (targetInjective : Function.Injective morphism.targetMap)
    (sourceFaithful : first.readout.Faithful) :
    second.readout.Faithful := by
  intro left right sameObservation
  obtain ⟨leftPreimage, leftImage⟩ := sourceSurjective left
  obtain ⟨rightPreimage, rightImage⟩ := sourceSurjective right
  subst leftImage
  subst rightImage
  apply congrArg morphism.sourceMap
  apply sourceFaithful
  apply targetInjective
  rw [← morphism.observe_natural, ← morphism.observe_natural,
    sameObservation]

/-- Exactness transports forward under surjectivity of the intensional map and
injectivity of the extensional map. -/
theorem target_exact_of_source_exact
    (morphism : Hom first second)
    (sourceSurjective : Function.Surjective morphism.sourceMap)
    (targetInjective : Function.Injective morphism.targetMap)
    (sourceExact : first.readout.Exact) :
    second.readout.Exact := by
  apply second.readout.exact_iff_faithful.mpr
  exact morphism.target_faithful_of_source_faithful sourceSurjective
    targetInjective (first.readout.exact_iff_faithful.mp sourceExact)

end Hom

instance : Category Object where
  Hom := Hom
  id := Hom.identity
  comp := Hom.comp
  id_comp := by
    intro first second morphism
    ext <;> rfl
  comp_id := by
    intro first second morphism
    ext <;> rfl
  assoc := by
    intro first second third fourth firstMap secondMap thirdMap
    ext <;> rfl

end Object

#print axioms Object.Hom.canonicalize_natural
#print axioms Object.Hom.source_exact_of_target_exact
#print axioms Object.Hom.target_exact_of_source_exact

end Mettapedia.TypeTheory.SplitReadoutMorphism
