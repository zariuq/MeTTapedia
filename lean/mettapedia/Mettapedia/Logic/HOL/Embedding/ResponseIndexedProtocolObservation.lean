import Mettapedia.Logic.HOL.Embedding.LiftedStandardModelTarskiInterpretation
import Mettapedia.GSLT.Dynamics.DependentReflectiveProtocolSemanticViews

/-!
# A simple higher-order observation of a response-indexed protocol

The response-indexed protocol has an extensional simple-type observation
language with one base type of protocol phases and one predicate constant
`completed : phase ⇒ prop`.  Its full standard Henkin model interprets that
predicate as fibre inhabitation of the separately defined dependent result
family.

This is a fragmentwise bridge, not a reduction of dependent typing to HOL.
The predicate detects whether a result fibre is inhabited, while the varying
family itself remains outside the essential image of constant-family simple
types.  Thus an extensional proposition and an intensional dependent family
can agree exactly on an observation without becoming interchangeable.

No choice, infinity, classical-axiom package, dependent proof calculus, or
product-language policy is selected by this example.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ResponseIndexedProtocolObservation

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol.VaryingCanary
open Mettapedia.GSLT.Dynamics.DependentReflectiveProtocolSemanticViews
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.LiftedStandardModelTarskiInterpretation
open Mettapedia.TypeTheory.ResponseIndexedResultFamily
open Mettapedia.TypeTheory.SetFamilyTypeOverEssentialImage

/-! ## Intrinsically typed observation syntax -/

/-- The only base type needed by this observation fragment. -/
inductive ObservationBase where
  | phase
deriving DecidableEq, Repr

/-- One typed predicate constant on protocol phases. -/
inductive ObservationConst : Ty ObservationBase → Type where
  | completed : ObservationConst (.base .phase ⇒ .prop)

/-- The small carrier assigned to the phase base type. -/
def smallCarrier : ObservationBase → Type
  | .phase => Phase

/-- The constant interpretation in the lifted standard model. -/
def constantDenotation : {type : Ty ObservationBase} →
    ObservationConst type →
      Ty.denote.{0, 0} (liftedCarrier smallCarrier) type
  | _, .completed => fun phase =>
      ⟨completion phase.down = true⟩

/-- A full standard Henkin model for the observation language. -/
abbrev observationModel :=
  liftedStandardModel smallCarrier constantDenotation

/-- There exists a completed phase. -/
def someCompleted : ClosedFormula ObservationConst :=
  .ex (.app (.const ObservationConst.completed) (.var .vz))

/-- Every phase is completed.  The initial phase refutes this formula. -/
def everyCompleted : ClosedFormula ObservationConst :=
  .all (.app (.const ObservationConst.completed) (.var .vz))

/-! ## The extensional/dependent bridge -/

/-- The object-language predicate denotes exactly inhabitation of the
dependent result fibre at the observed phase. -/
theorem completed_denotes_result_inhabited
    (phase : Ty.denote.{0, 0}
      (liftedCarrier smallCarrier) (.base .phase)) :
    (constantDenotation ObservationConst.completed phase).down ↔
      Nonempty (Result phase.down) := by
  change completion phase.down = true ↔ Nonempty (Result phase.down)
  exact (resultDisplay_inhabited_iff_completed phase.down).symm

/-- Positive control: the extensional language proves true in its model that
some dependent result fibre is inhabited. -/
theorem observationModel_models_someCompleted :
    observationModel.models someCompleted := by
  refine ⟨⟨Phase.unitDone⟩, ?_, ?_⟩
  · trivial
  · rfl

/-- Negative control: the initial phase is a countermodel to universal
completion. -/
theorem observationModel_not_models_everyCompleted :
    ¬ observationModel.models everyCompleted := by
  intro universal
  have atStart := universal (⟨Phase.start⟩ :
    Ty.denote.{0, 0}
      (liftedCarrier smallCarrier) (.base .phase)) (by trivial)
  exact Bool.false_ne_true atStart

/-- The extensional observation is exact about fibre inhabitation but does
not make the varying dependent family a simple type. -/
theorem extensional_observation_dependent_noncollapse :
    observationModel.models someCompleted ∧
      (¬ observationModel.models everyCompleted) ∧
      (∀ phase : Ty.denote.{0, 0}
          (liftedCarrier smallCarrier) (.base .phase),
        (constantDenotation ObservationConst.completed phase).down ↔
          Nonempty (Result phase.down)) ∧
      ¬ (simpleToDependentTypeFunctor Phase).essImage resultDisplay :=
  ⟨observationModel_models_someCompleted,
    observationModel_not_models_everyCompleted,
    completed_denotes_result_inhabited,
    resultDisplay_not_in_simple_essentialImage⟩

#print axioms completed_denotes_result_inhabited
#print axioms observationModel_models_someCompleted
#print axioms observationModel_not_models_everyCompleted
#print axioms extensional_observation_dependent_noncollapse

end Mettapedia.Logic.HOL.Embedding.ResponseIndexedProtocolObservation
