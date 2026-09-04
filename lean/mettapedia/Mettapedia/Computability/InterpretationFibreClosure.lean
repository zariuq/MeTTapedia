import Mettapedia.Computability.FragmentwiseComputationalTrinity
import Mettapedia.Computability.FragmentwiseComputationalTrinityCanary

/-!
# Reflecting contextual constraints along interpretation fibres

An interpretation need not identify its source and target faces.  It induces
instead a closure operation on source constraints: saturate a constraint by
admitting every source element with the same interpreted image as an already
admitted element.

This module proves the universal property left implicit by the basic
construction.  Saturation is the least fibre-closed constraint containing the
original one.  Consequently, reasoning through an extensional interpretation
is a reflection into fibre-closed constraints, not a global claim that the
intensional source has ceased to carry additional distinctions.

The result applies equally to simple/dependent comparisons, code/behavior
observations, stream/bag/set projections, and operational/denotational maps.
Which distinctions are collapsed remains a property of the supplied
interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.InterpretationFibreClosure

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.Computability.FragmentwiseComputationalTrinity

universe u v w

variable {Context : Type u} [Category.{v} Context]
variable {sourceFace targetFace thirdFace : Face.{u, v, w} Context}

/-! ## The closure universal property -/

/-- Saturation is monotone in its source constraint. -/
theorem saturate_mono
    (interpretation : sourceFace ⟶ targetFace)
    {first second : Constraint sourceFace}
    (entails : first.Entails second) :
    (first.saturate interpretation).Entails
      (second.saturate interpretation) := by
  exact Constraint.pullback_mono interpretation
    (Constraint.pushforward_mono interpretation entails)

/-- Saturation is the least fibre-closed constraint containing the source
constraint. -/
theorem saturate_least_fibreClosed
    (interpretation : sourceFace ⟶ targetFace)
    (sourceConstraint targetConstraint : Constraint sourceFace)
    (contained : sourceConstraint.Entails targetConstraint)
    (closed : targetConstraint.FibreClosed interpretation) :
    (sourceConstraint.saturate interpretation).Entails targetConstraint := by
  intro context targetElement saturated
  rcases saturated with ⟨sourceElement, sourceAdmitted, sameImage⟩
  exact closed context sourceElement targetElement sameImage
    (contained context sourceElement sourceAdmitted)

/-- Mapping into a fibre-closed constraint may be checked before or after
extensional closure. -/
theorem entails_fibreClosed_iff_saturate_entails
    (interpretation : sourceFace ⟶ targetFace)
    (sourceConstraint targetConstraint : Constraint sourceFace)
    (closed : targetConstraint.FibreClosed interpretation) :
    sourceConstraint.Entails targetConstraint ↔
      (sourceConstraint.saturate interpretation).Entails targetConstraint := by
  constructor
  · intro contained
    exact saturate_least_fibreClosed interpretation sourceConstraint
      targetConstraint contained closed
  · intro saturatedContained
    exact (Constraint.entails_saturate interpretation sourceConstraint).trans
      saturatedContained

/-! ## Reflection through an intermediate semantic face -/

/-- Extensional closure along a composite interpretation agrees with first
sending the constraint to the intermediate face, closing it along the second
interpretation, and then pulling the result back to the source.

This is the constraint-level coherence law for a layered intensional,
logical, and extensional comparison.  It does not require either
interpretation to be faithful, full, or invertible. -/
theorem saturate_composite_equivalent_staged
    (first : sourceFace ⟶ targetFace)
    (second : targetFace ⟶ thirdFace)
    (sourceConstraint : Constraint sourceFace) :
    (sourceConstraint.saturate (first ≫ second)).Equivalent
      (((sourceConstraint.pushforward first).saturate second).pullback
        first) := by
  constructor
  · intro context sourceElement saturated
    rcases saturated with ⟨witness, admitted, sameCompositeImage⟩
    refine ⟨first.app context witness, ⟨witness, admitted, rfl⟩, ?_⟩
    exact sameCompositeImage
  · intro context sourceElement staged
    rcases staged with
      ⟨middleWitness, ⟨sourceWitness, admitted, sourceImage⟩,
        sameTargetImage⟩
    refine ⟨sourceWitness, admitted, ?_⟩
    change second.app context (first.app context sourceWitness) =
      second.app context (first.app context sourceElement)
    rw [sourceImage]
    exact sameTargetImage

/-- In a commuting three-face comparison, direct program-to-space reflection
is exactly the staged program-to-logic-to-space reflection. -/
theorem comparison_reflection_stages
    (comparison : Comparison.{u, v, w} Context)
    (programConstraint : Constraint comparison.program) :
    (programConstraint.saturate comparison.programToSpace).Equivalent
      (((programConstraint.pushforward comparison.programToLogic).saturate
        comparison.logicToSpace).pullback comparison.programToLogic) := by
  rw [← comparison.coherence]
  exact saturate_composite_equivalent_staged
    comparison.programToLogic comparison.logicToSpace programConstraint

/-! ## Fibre-closed constraints form the reflected fragment -/

/-- A contextual constraint together with evidence that it is insensitive to
every distinction erased by the selected interpretation. -/
structure FibreClosedConstraint
    (interpretation : sourceFace ⟶ targetFace) where
  constraint : Constraint sourceFace
  closed : constraint.FibreClosed interpretation

namespace FibreClosedConstraint

variable (interpretation : sourceFace ⟶ targetFace)

/-- Forget the closure witness. -/
def forget (constraint : FibreClosedConstraint interpretation) :
    Constraint sourceFace :=
  constraint.constraint

/-- Reflect any source constraint into the fibre-closed fragment. -/
def reflect (constraint : Constraint sourceFace) :
    FibreClosedConstraint interpretation where
  constraint := constraint.saturate interpretation
  closed := Constraint.saturate_fibreClosed interpretation constraint

/-- The reflection has the expected order-enriched universal property. -/
theorem reflect_entails_iff
    (sourceConstraint : Constraint sourceFace)
    (closedConstraint : FibreClosedConstraint interpretation) :
    (reflect interpretation sourceConstraint).constraint.Entails
        closedConstraint.constraint ↔
      sourceConstraint.Entails closedConstraint.constraint := by
  exact
    (entails_fibreClosed_iff_saturate_entails interpretation
      sourceConstraint closedConstraint.constraint closedConstraint.closed).symm

/-- Reflecting an already fibre-closed constraint changes it only up to the
extensional equality of constraints. -/
theorem reflect_include_equivalent
    (closedConstraint : FibreClosedConstraint interpretation) :
    closedConstraint.constraint.Equivalent
      (reflect interpretation closedConstraint.constraint).constraint := by
  exact
    (Constraint.equivalent_saturate_iff_fibreClosed interpretation
      closedConstraint.constraint).2 closedConstraint.closed

/-- Repeated reflection is idempotent up to constraint equivalence. -/
theorem reflect_idempotent (constraint : Constraint sourceFace) :
    (reflect interpretation
      (reflect interpretation constraint).constraint).constraint.Equivalent
        (reflect interpretation constraint).constraint := by
  exact Constraint.saturate_idempotent interpretation constraint

end FibreClosedConstraint

/-! ## Information preservation criteria -/

/-- A pointwise-injective interpretation has singleton fibres, so every
source constraint is already fibre-closed. -/
theorem fibreClosed_of_pointwise_injective
    (interpretation : sourceFace ⟶ targetFace)
    (injective : ∀ context, Function.Injective (interpretation.app context))
    (constraint : Constraint sourceFace) :
    constraint.FibreClosed interpretation := by
  intro context left right sameImage leftAdmitted
  have equalElements := injective context sameImage
  simpa [equalElements] using leftAdmitted

/-- Under a pointwise-injective interpretation, extensional closure retains
every contextual constraint exactly. -/
theorem saturation_exact_of_pointwise_injective
    (interpretation : sourceFace ⟶ targetFace)
    (injective : ∀ context, Function.Injective (interpretation.app context))
    (constraint : Constraint sourceFace) :
    constraint.Equivalent (constraint.saturate interpretation) := by
  exact
    (Constraint.equivalent_saturate_iff_fibreClosed interpretation
      constraint).2
      (fibreClosed_of_pointwise_injective interpretation injective constraint)

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.Computability.FragmentwiseComputationalTrinityCanary.FirstBit
open ComputationalTrinity.FirstBitObservation

private def here : ComputationalTrinity.FirstBitObservation.Context.{0}ᵒᵖ :=
  Opposite.op (Discrete.mk PUnit.unit)

/-- Positive control: a constraint on the visible first bit is fixed by the
reflection. -/
theorem visible_constraint_is_fixed :
    programFirstFalse.{0}.Equivalent
      (FibreClosedConstraint.reflect comparison.{0}.programToSpace
        programFirstFalse.{0}).constraint :=
  programFirstFalse_saturation_exact.{0}

/-- Negative control: the hidden-bit constraint is strictly enlarged by
reflection; the element with hidden `true` enters its saturation. -/
theorem hidden_constraint_is_strictly_enlarged :
    (programSecondFalse.{0}.saturate comparison.{0}.programToSpace).holds
        here (false, true) ∧
      ¬ programSecondFalse.{0}.holds
        here (false, true) := by
  constructor
  · exact ⟨(false, false), rfl, rfl⟩
  · change ¬(true = false)
    decide

/-- Therefore the reflector is not the identity for a genuinely lossy
interpretation. -/
theorem lossy_reflection_not_globally_exact :
    ¬ programSecondFalse.{0}.Equivalent
      (FibreClosedConstraint.reflect comparison.{0}.programToSpace
        programSecondFalse.{0}).constraint := by
  intro equivalent
  exact hidden_constraint_is_strictly_enlarged.2
    (equivalent.2 _ _ hidden_constraint_is_strictly_enlarged.1)

/-- The hidden-bit example also checks the layered coherence law: reflecting
directly to the spatial face agrees with reflecting through the logical face,
even though both routes necessarily forget the hidden bit. -/
theorem hidden_constraint_direct_and_staged_reflection_agree :
    (programSecondFalse.{0}.saturate comparison.{0}.programToSpace).Equivalent
      (((programSecondFalse.{0}.pushforward
        comparison.{0}.programToLogic).saturate
          comparison.{0}.logicToSpace).pullback
            comparison.{0}.programToLogic) :=
  comparison_reflection_stages comparison.{0} programSecondFalse.{0}

end Canary

#print axioms saturate_mono
#print axioms saturate_least_fibreClosed
#print axioms entails_fibreClosed_iff_saturate_entails
#print axioms saturate_composite_equivalent_staged
#print axioms comparison_reflection_stages
#print axioms FibreClosedConstraint.reflect_entails_iff
#print axioms FibreClosedConstraint.reflect_idempotent
#print axioms saturation_exact_of_pointwise_injective
#print axioms Canary.visible_constraint_is_fixed
#print axioms Canary.lossy_reflection_not_globally_exact
#print axioms Canary.hidden_constraint_direct_and_staged_reflection_agree

end Mettapedia.Computability.InterpretationFibreClosure
