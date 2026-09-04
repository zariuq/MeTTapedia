import Mettapedia.TypeTheory.FibrewiseFullyFaithfulCwfMorphism
import Mettapedia.TypeTheory.SetFamilyComprehensionMap
import Mettapedia.GSLT.Dynamics.DependentReflectiveProtocolEquipment

/-!
# Response-indexed result families

A response-indexed protocol supplies a concrete junction between contextual
typing and proof-relevant dynamics.  Its result type varies with the selected
successor state, so it is a type in the set-families CwF rather than an object
of the constant-family simply typed fragment.  A completed interaction pairs a
retained route occurrence with a value in the fibre over its exact target.

The resulting comprehension points are ordinary dependent pairs.  Forgetting
the occurrence retains a well-typed dependent result, while forgetting which
completed state was reached loses both the varying family and a
response-sensitive work/span valuation.

This module does not define a type theory or an operational language.  It
locates one inhabited protocol simultaneously in the fully faithful simple
fragment comparison, the dependent comprehension model, and the loose
operational equipment.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ResponseIndexedResultFamily

open CategoryTheory
open Mettapedia.Algebra
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol
open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol.VaryingCanary
open Mettapedia.GSLT.Dynamics.DependentReflectiveProtocolComparison
open Mettapedia.GSLT.Dynamics.DependentReflectiveProtocolEquipment.Comparison
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization

/-! ## The contextual family -/

/-- The successor-indexed result family as a displayed type over protocol
phases. -/
def resultDisplay : TypeOver (familiesCwf.{0}) Phase :=
  ⟨Result⟩

/-- The result family is not in the object image of constant-family simple
types.  Its two completed fibres have different cardinalities. -/
theorem resultDisplay_not_in_simple_image :
    ¬ ∃ simpleType : TypeOver (SimpleFamiliesCwf.{0}) Phase,
      simpleToDependentPseudoMorphism.mapTypeObject simpleType =
        resultDisplay := by
  rintro ⟨simpleType, imageEquality⟩
  have familyEquality : constantFamily simpleType.val = Result :=
    congrArg TypeOver.val imageEquality
  have unitEquality : simpleType.val = PUnit :=
    congrFun familyEquality Phase.unitDone
  have boolEquality : simpleType.val = Bool :=
    congrFun familyEquality Phase.boolDone
  have unitBoolEquality : PUnit = Bool :=
    unitEquality.symm.trans boolEquality
  exact Canary.unit_not_equiv_bool ⟨Equiv.cast unitBoolEquality⟩

/-- A completed result together with the exact enabled-event route occurrence
that selected its target. -/
abbrev InteractionOutcome :=
  Sigma fun target : Phase =>
    enabledEventRoute Phase.start target × Result target

/-- The false response supplies a point of dependent comprehension. -/
def unitInteractionOutcome : InteractionOutcome :=
  ⟨Phase.unitDone, unitRouteWitness, PUnit.unit⟩

/-- The true response supplies a differently typed point of the same
dependent comprehension. -/
def boolInteractionOutcome : InteractionOutcome :=
  ⟨Phase.boolDone, boolRouteWitness, false⟩

/-- Erase only the operational occurrence, retaining the target and its
correctly indexed result. -/
def forgetOccurrence : InteractionOutcome → Sigma Result
  | ⟨target, _route, result⟩ => ⟨target, result⟩

theorem forgotten_outcomes_are_comprehension_points :
    forgetOccurrence unitInteractionOutcome =
        (⟨Phase.unitDone, PUnit.unit⟩ : Sigma Result) /\
      forgetOccurrence boolInteractionOutcome =
        (⟨Phase.boolDone, false⟩ : Sigma Result) :=
  ⟨rfl, rfl⟩

/-! ## Observation and cost on the retained occurrence -/

/-- Coarse completion forgets which completed phase was selected. -/
def outcomeCompletion (outcome : InteractionOutcome) : Bool :=
  completion outcome.1

/-- Work/span remains a valuation of the retained event, not of its visible
completion bit or its dependent result type. -/
def outcomeWorkSpan (outcome : InteractionOutcome) : WorkSpan :=
  workSpan outcome.2.1.val

@[simp] theorem unitOutcome_completion :
    outcomeCompletion unitInteractionOutcome = true :=
  rfl

@[simp] theorem boolOutcome_completion :
    outcomeCompletion boolInteractionOutcome = true :=
  rfl

@[simp] theorem unitOutcome_workSpan :
    outcomeWorkSpan unitInteractionOutcome = ⟨1, 1⟩ :=
  rfl

@[simp] theorem boolOutcome_workSpan :
    outcomeWorkSpan boolInteractionOutcome = ⟨3, 2⟩ :=
  rfl

/-- Visible completion cannot reconstruct cost on dependent interaction
outcomes. -/
theorem outcomeWorkSpan_not_completion_determined :
    ¬ Factors outcomeCompletion outcomeWorkSpan := by
  let fibre : NonTrivialFiber outcomeCompletion outcomeWorkSpan :=
    { left := unitInteractionOutcome
      right := boolInteractionOutcome
      sameShadow := rfl
      differentValue := by decide }
  exact fibre.not_factors

/-! ## Connected boundary -/

/-- One inhabited boundary relates all three semantic strata without
collapsing them: constant-family STT embeds fully faithfully but omits this
result family; dependent comprehension retains both differently typed
outcomes; the generating interaction is genuinely loose; and cost does not
descend through the coarse completion observer. -/
theorem simple_dependent_operational_boundary :
    (¬ ∃ simpleType : TypeOver (SimpleFamiliesCwf.{0}) Phase,
      simpleToDependentPseudoMorphism.mapTypeObject simpleType =
        resultDisplay) /\
      Nonempty InteractionOutcome /\
      (forgetOccurrence unitInteractionOutcome).1 = Phase.unitDone /\
      (forgetOccurrence boolInteractionOutcome).1 = Phase.boolDone /\
      (¬ Nonempty
        (Mettapedia.GSLT.LooseRelationEquipment.Representation
          enabledEventRoute)) /\
      ¬ Factors outcomeCompletion outcomeWorkSpan :=
  ⟨resultDisplay_not_in_simple_image,
    ⟨unitInteractionOutcome⟩,
    rfl,
    rfl,
    enabledEventRoute_not_representable,
    outcomeWorkSpan_not_completion_determined⟩

#print axioms resultDisplay_not_in_simple_image
#print axioms forgotten_outcomes_are_comprehension_points
#print axioms outcomeWorkSpan_not_completion_determined
#print axioms simple_dependent_operational_boundary

end Mettapedia.TypeTheory.ResponseIndexedResultFamily

