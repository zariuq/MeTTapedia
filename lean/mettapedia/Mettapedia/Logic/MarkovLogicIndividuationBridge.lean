import Mettapedia.Cybernetics.Individuation
import Mettapedia.Logic.MarkovLogicDynamicIndividuation

/-!
# MLN realization of processual individuation

The general cybernetic interface distinguishes static closure, a
proof-relevant process of becoming, and persistence of an already selected
boundary.  This module proves that the existing infinite-MLN development is
an instance of that interface:

* `InteractionClosed` supplies static closure;
* `DynamicIndividuationStep` supplies process steps;
* `SpecAgreesOnRegion` supplies boundary agreement;
* existing dynamic paths retain their exact sequence of steps; and
* the existing post-closure query theorem is recovered from persistence plus
  its explicit probabilistic premises.

The bridge is project-original.  The processual interpretation follows David
Weinbaum and Viktoras Veitas, while the MLN stability results remain the
existing Dobrushin-based theorems of the Markov-logic development.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.MarkovLogicIndividuationBridge

open Mettapedia.Cybernetics
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicOntologyGrowth
open Mettapedia.Logic.MarkovLogicIndividuation
open Mettapedia.Logic.MarkovLogicDynamicIndividuation
open MeasureTheory

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- The existing MLN notions instantiate the general processual-individuation
interface without changing their definitions. -/
def mlnTheory :
    Individuation.Theory
      (ClassicalInfiniteGroundMLNSpec Atom ClauseId) (Region Atom) where
  Step := DynamicIndividuationStep
  Closed := InteractionClosed
  Agrees := SpecAgreesOnRegion

/-- The informative abstract form of an MLN individuated subsystem includes
the non-emptiness condition that is specific to this MLN model. -/
abbrev NonemptyIndividuated
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) :=
  { state : Individuation.Individuated
      (mlnTheory (Atom := Atom) (ClauseId := ClauseId)) M //
    state.boundary.Nonempty }

/-- Encode the existing MLN structure as a general individuated state while
retaining its model-specific non-emptiness witness. -/
def encodeIndividuatedSubsystem
    {M : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (subsystem : IndividuatedSubsystem M) : NonemptyIndividuated M :=
  ⟨⟨subsystem.core, subsystem.interaction_closed⟩, subsystem.core_nonempty⟩

/-- Recover the existing MLN structure from its abstract informative form. -/
def decodeNonemptyIndividuated
    {M : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (state : NonemptyIndividuated M) : IndividuatedSubsystem M :=
  ⟨state.1.boundary, state.2, state.1.closed⟩

@[simp] theorem decode_encode_individuatedSubsystem
    {M : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (subsystem : IndividuatedSubsystem M) :
    decodeNonemptyIndividuated (encodeIndividuatedSubsystem subsystem) = subsystem := by
  cases subsystem
  rfl

@[simp] theorem encode_decode_nonemptyIndividuated
    {M : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (state : NonemptyIndividuated M) :
    encodeIndividuatedSubsystem (decodeNonemptyIndividuated state) = state := by
  rcases state with ⟨⟨boundary, closed⟩, nonempty⟩
  rfl

/-- The established MLN notion is equivalent to the general static notion
plus exactly its additional non-emptiness premise. -/
def individuatedSubsystemEquiv
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId) :
    IndividuatedSubsystem M ≃ NonemptyIndividuated M where
  toFun := encodeIndividuatedSubsystem
  invFun := decodeNonemptyIndividuated
  left_inv := decode_encode_individuatedSubsystem
  right_inv := encode_decode_nonemptyIndividuated

/-- Exact length of an existing MLN dynamic-individuation path. -/
def dynamicPathSteps :
    {first last : ClassicalInfiniteGroundMLNSpec Atom ClauseId} →
      DynamicIndividuationPath first last → Nat
  | _, _, .single _ => 1
  | _, _, .step path _ => dynamicPathSteps path + 1

/-- Every existing MLN path is a proof-relevant process in the general
interface.  No intermediate specification or step witness is erased. -/
def dynamicPathProcess :
    {first last : ClassicalInfiniteGroundMLNSpec Atom ClauseId} →
    (path : DynamicIndividuationPath first last) →
      Individuation.Process mlnTheory (dynamicPathSteps path) first last
  | _, _, .single firstStep => by
      simpa [dynamicPathSteps] using
        (Individuation.Process.snoc
          (Individuation.Process.refl _ : Individuation.Process mlnTheory 0 _ _)
          firstStep)
  | _, _, .step path next => by
      simpa [dynamicPathSteps] using
        (Individuation.Process.snoc (dynamicPathProcess path) next)

/-- A dynamic path whose endpoint has reached an interaction-closed shell is
a witnessed process of becoming individuated. -/
noncomputable def dynamicPathToBecomingIndividuated
    {first last : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (path : DynamicIndividuationPath first last)
    (closure : DynamicIndividuationClosure last) :
    Individuation.BecomingIndividuated mlnTheory first last where
  steps := dynamicPathSteps path
  process := dynamicPathProcess path
  result :=
    ⟨last.iterExpandRegion closure.proto.seed closure.closureDepth,
      closure.shell_closed⟩

/-- Existing static MLN individuation yields abstract persistence whenever a
second specification agrees on the selected core and keeps it closed. -/
def persistenceOfSubsystem
    {first last : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (subsystem : IndividuatedSubsystem first)
    (agreement : SpecAgreesOnRegion first last subsystem.core)
    (targetClosed : InteractionClosed last subsystem.core) :
    Individuation.Persistence mlnTheory first last subsystem.core where
  sourceClosed := subsystem.interaction_closed
  targetClosed := targetClosed
  agrees := agreement

/-- The general persistence package exposes exactly the structural premises
consumed by the established MLN ontology-growth theorem.  Budgets and DLR
witnesses remain explicit rather than being smuggled into individuation. -/
theorem persistence_queryProb_eq
    {first last : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    {boundary : Region Atom}
    (persistence : Individuation.Persistence mlnTheory first last boundary)
    (budgetFirst : first.PaperUniformSmallTotalInfluence)
    (budgetLast : last.PaperUniformSmallTotalInfluence)
    (μFirst : ProbabilityMeasure (InfiniteWorld Atom))
    (μLast : ProbabilityMeasure (InfiniteWorld Atom))
    (hμFirst : FixedRegionCylinderDLR
      first.toStrictlyPositiveInfiniteGroundMLNSpec
      (μFirst : Measure (InfiniteWorld Atom)))
    (hμLast : FixedRegionCylinderDLR
      last.toStrictlyPositiveInfiniteGroundMLNSpec
      (μLast : Measure (InfiniteWorld Atom)))
    (query : ConstraintQuery Atom)
    (supported : ∀ atom ∈ query,
      (atom : Sigma fun _ : Atom => Bool).1 ∈ boundary) :
    (infiniteMLNMassSemantics first μFirst hμFirst).queryProb query =
      (infiniteMLNMassSemantics last μLast hμLast).queryProb query :=
  queryProb_eq_of_specAgreesOnRegion persistence.agrees
    persistence.sourceClosed persistence.targetClosed budgetFirst budgetLast
    μFirst μLast hμFirst hμLast query supported

end Mettapedia.Logic.MarkovLogicIndividuationBridge

#print axioms Mettapedia.Logic.MarkovLogicIndividuationBridge.individuatedSubsystemEquiv
#print axioms Mettapedia.Logic.MarkovLogicIndividuationBridge.dynamicPathProcess
#print axioms Mettapedia.Logic.MarkovLogicIndividuationBridge.dynamicPathToBecomingIndividuated
#print axioms Mettapedia.Logic.MarkovLogicIndividuationBridge.persistence_queryProb_eq
