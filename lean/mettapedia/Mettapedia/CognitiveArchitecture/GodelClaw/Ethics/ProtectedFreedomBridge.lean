import Mettapedia.Enactive.ProtectedFreedom
import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.MetaStability

/-!
# Dynamic individuation as protected-family transport

The general protected-freedom theory retains evidence fibres over protected
indices.  This module connects that interface to the existing Gödel-machine
and world-model theorem: a proof-backed modification outside a dynamically
individuated core improves expected utility while preserving every selected
protected query value exactly.

The bridge does not identify expected utility with semantic freedom, and it
does not infer current executable authority from world-model agreement.
Those are separate obligations in `Enactive.ProtectedFreedom`.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.ProtectedFreedomBridge

open Mettapedia.Enactive.ProtectedFreedom
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteFixedRegionDLR
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness.ClassicalInfiniteGroundMLNSpec
open Mettapedia.Logic.MarkovLogicInfiniteWorldModel
open Mettapedia.Logic.MarkovLogicOntologyGrowth
open Mettapedia.Logic.MarkovLogicDynamicIndividuation
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.Logic.MarkovLogicAbstract
open Mettapedia.Logic.MarkovLogicAbstract.MassState
open Mettapedia.UniversalAI.GodelMachine
open Mettapedia.UniversalAI.GodelMachine.MetaGoalShellPreservation
open MeasureTheory

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- The protected-goal theorem, packaged as exact agreement over the whole
selected query family.  Improvement and observation preservation remain two
conjuncts rather than one scalar objective. -/
theorem validModification_yields_protectedObservationAgreement
    {oldSpec newSpec : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (oldMachine newMachine : GodelMachineState)
    (proofBacked : validModification oldMachine newMachine)
    (closure : DynamicIndividuationClosure oldSpec)
    (hagree : SpecAgreesOnRegion oldSpec newSpec
      (oldSpec.iterExpandRegion closure.proto.seed closure.closureDepth))
    (hclosedNew : InteractionClosed newSpec
      (oldSpec.iterExpandRegion closure.proto.seed closure.closureDepth))
    (oldBudget : oldSpec.PaperUniformSmallTotalInfluence)
    (newBudget : newSpec.PaperUniformSmallTotalInfluence)
    (protectedGoals : ProtectedCaringGoals (Atom := Atom) closure.proto.seed)
    (measures : CrossSpecDLR oldSpec newSpec) :
    expectedUtilityFromStart newMachine > expectedUtilityFromStart oldMachine ∧
      ProtectedObservationAgreement
        (↑protectedGoals.goals : Set (ConstraintQuery Atom))
        (fun query => BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics oldSpec measures.oldMeasure measures.oldDLR} :
            MassState (ConstraintQuery Atom)) query)
        (fun query => BinaryWorldModel.queryStrength
          ({infiniteMLNMassSemantics newSpec measures.newMeasure measures.newDLR} :
            MassState (ConstraintQuery Atom)) query) := by
  constructor
  · exact valid_modification_improves oldMachine newMachine proofBacked
  · intro query protectedQuery
    have queryMember : query ∈ protectedGoals.goals := by
      simpa using protectedQuery
    exact (validModification_preserves_protectedCaringGoal_of_dynamicIndividuationClosure
      (oldMachine := oldMachine) (newMachine := newMachine)
      (proofBacked := proofBacked)
      (closure := closure)
      (hagree := hagree)
      (hclosed₂ := hclosedNew)
      (hbudget₁ := oldBudget)
      (hbudget₂ := newBudget)
      (protectedCaringGoals := protectedGoals)
      (measures := measures)
      queryMember).2

/-- The same theorem transports the exact value fibres indexed by every
protected query.  This is the common structural shape shared with protected
completion transport; no cardinal readout intervenes. -/
noncomputable def validModification_protectedObservationFamilyMap
    {oldSpec newSpec : ClassicalInfiniteGroundMLNSpec Atom ClauseId}
    (oldMachine newMachine : GodelMachineState)
    (proofBacked : validModification oldMachine newMachine)
    (closure : DynamicIndividuationClosure oldSpec)
    (hagree : SpecAgreesOnRegion oldSpec newSpec
      (oldSpec.iterExpandRegion closure.proto.seed closure.closureDepth))
    (hclosedNew : InteractionClosed newSpec
      (oldSpec.iterExpandRegion closure.proto.seed closure.closureDepth))
    (oldBudget : oldSpec.PaperUniformSmallTotalInfluence)
    (newBudget : newSpec.PaperUniformSmallTotalInfluence)
    (protectedGoals : ProtectedCaringGoals (Atom := Atom) closure.proto.seed)
    (measures : CrossSpecDLR oldSpec newSpec) :
    ProtectedFamilyMap
      (↑protectedGoals.goals : Set (ConstraintQuery Atom))
      (ObservationFibre (fun query => BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics oldSpec measures.oldMeasure measures.oldDLR} :
          MassState (ConstraintQuery Atom)) query))
      (ObservationFibre (fun query => BinaryWorldModel.queryStrength
        ({infiniteMLNMassSemantics newSpec measures.newMeasure measures.newDLR} :
          MassState (ConstraintQuery Atom)) query)) :=
  protectedObservationFamilyMap
    (validModification_yields_protectedObservationAgreement
      oldMachine newMachine proofBacked closure hagree hclosedNew oldBudget
      newBudget protectedGoals measures).2

end Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.ProtectedFreedomBridge

#print axioms Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.ProtectedFreedomBridge.validModification_yields_protectedObservationAgreement
#print axioms Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.ProtectedFreedomBridge.validModification_protectedObservationFamilyMap
