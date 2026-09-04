import Mettapedia.GSLT.Core.ObservedBisimulation
import Mettapedia.KR.ConceptOntology.FCA

/-!
# Formal concepts over observer-relative behavioral classes

An observer-relative bisimulation quotient supplies behavioral objects.  A
predicate on system states supplies an ontological attribute only when it is
invariant under that bisimulation.  This module places those two ingredients
inside formal concept analysis without identifying the operational states
with their behavioral classes.

The separation theorem gives the precise converse.  A family of saturated
attributes characterizes observed bisimilarity exactly when agreement on the
family implies bisimilarity.  Thus behavioral classes can be recovered from
distinction-bearing attributes when, and only when, the chosen attributes are
jointly separating.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ObservedGSLT

open Mettapedia.KR.ConceptOntology

universe uAtom

variable {system : GSLT} (observed : ObservedGSLT.{uAtom} system)

/-- An ontological attribute whose state predicate respects the selected
observer-relative behavioral equivalence. -/
structure BehavioralAttribute where
  holds : system.Term → Prop
  saturated : observed.Saturated holds

/-- Incidence of a behavioral class with a saturated attribute. -/
def behavioralIncidence
    (object : observed.Class)
    (property : observed.BehavioralAttribute) : Prop :=
  observed.classify property.holds property.saturated object

/-- The identity gate when evidence is already proposition-valued. -/
def propositionGate : EvidenceGate Prop where
  accept proposition := proposition
  mono := by
    intro left right implication leftProof
    exact implication leftProof

/-- Formal concepts formed from behavioral classes and saturated attributes. -/
abbrev BehavioralConcept :=
  CrispConcept propositionGate (observed.behavioralIncidence)

/-- The extent of a single saturated behavioral attribute. -/
def behavioralExtent
    (property : observed.BehavioralAttribute) : Set observed.Class :=
  crispExtent propositionGate observed.behavioralIncidence property

@[simp] theorem behavioralIncidence_toClass
    (term : system.Term) (property : observed.BehavioralAttribute) :
    observed.behavioralIncidence (observed.toClass term) property ↔
      property.holds term :=
  Iff.rfl

@[simp] theorem mem_behavioralExtent_toClass_iff
    (term : system.Term) (property : observed.BehavioralAttribute) :
    observed.toClass term ∈ observed.behavioralExtent property ↔
      property.holds term := by
  simp [behavioralExtent, behavioralIncidence, propositionGate]

/-- Disagreement on one saturated attribute refutes observed bisimilarity. -/
theorem not_bisimilar_of_attribute_disagreement
    (property : observed.BehavioralAttribute)
    {left right : system.Term}
    (leftHolds : property.holds left)
    (rightFails : ¬ property.holds right) :
    ¬ observed.Bisimilar left right := by
  intro bisimilar
  exact rightFails ((property.saturated bisimilar).mp leftHolds)

/-- The same disagreement separates the associated quotient objects. -/
theorem class_ne_of_attribute_disagreement
    (property : observed.BehavioralAttribute)
    {left right : system.Term}
    (leftHolds : property.holds left)
    (rightFails : ¬ property.holds right) :
    observed.toClass left ≠ observed.toClass right := by
  intro equalClasses
  exact observed.not_bisimilar_of_attribute_disagreement property
    leftHolds rightFails
    ((observed.class_eq_iff left right).mp equalClasses)

/-- A family of attributes is jointly separating when agreement on all of
them forces observed bisimilarity. -/
def JointlySeparating
    (attributes : Set observed.BehavioralAttribute) : Prop :=
  ∀ {left right},
    (∀ property ∈ attributes,
      (property.holds left ↔ property.holds right)) →
    observed.Bisimilar left right

/-- Saturation supplies one direction automatically; joint separation is
exactly the missing converse. -/
theorem bisimilar_iff_agrees_on_jointly_separating
    (attributes : Set observed.BehavioralAttribute)
    (separating : observed.JointlySeparating attributes)
    (left right : system.Term) :
    observed.Bisimilar left right ↔
      ∀ property ∈ attributes,
        (property.holds left ↔ property.holds right) := by
  constructor
  · intro bisimilar property _member
    exact property.saturated bisimilar
  · intro agreement
    exact separating agreement

/-! ## Axiom audit -/

#print axioms behavioralIncidence_toClass
#print axioms mem_behavioralExtent_toClass_iff
#print axioms not_bisimilar_of_attribute_disagreement
#print axioms class_ne_of_attribute_disagreement
#print axioms bisimilar_iff_agrees_on_jointly_separating

end Mettapedia.GSLT.ObservedGSLT
