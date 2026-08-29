import Mettapedia.GSLT.Core.ResourceAwareControl
import Mettapedia.Languages.MeTTa.Prime.NativeInteractionFamilyFibration

/-!
# Observation-controlled Cost waves

This module joins four previously independent boundaries for Prime's Cost-rho
event families:

* complete-bag versus bounded/streaming observation demand;
* permutation invariance of the exact candidate occurrences;
* operational serialization to one exact Cost target; and
* common-source decomposition of all consumed linear resources.

The resulting certificate may select bulk activation only for complete-bag
demand.  First-witness demand remains controlled, and a contested resource
cannot acquire a wave certificate merely because a desirable WorkSpan value
exists.  Exact receipts and WorkSpan remain observations of the already
licensed Cost schedule.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.NativeObservationControlledCostWaves

open Mettapedia.GSLT.Core.ObservationDemandControl
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFamilyFibration
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u

/-- The exact linear account consumed by one Cost event occurrence. -/
def eventDemand {Ground : Type u} (event : CostedEvent Ground) :
    CostConfig Ground :=
  event.consumed

/-- One independently declared unit of an auxiliary execution budget per
event occurrence.  This is deliberately not derived from `WorkSpan`: budgets
authorize execution, whereas `WorkSpan` observes a licensed schedule. -/
def eventUnitBudget {Ground : Type u} (_event : CostedEvent Ground) : Nat :=
  1

/-- Relational execution is the established chronological Cost trace, and
the result observer retains the complete target configuration. -/
def executionSemantics (Ground : Type u) :
    ExecutionSemantics (CostedEvent Ground) (CostConfig Ground)
      (CostConfig Ground) where
  run source events target := CostTrace source (costWaveTrace events) target
  observe := id

/-- A state that retains the chronological labels as well as the current
Cost configuration.  This is a stronger execution observer than final-state
observation; it is used only when chronology is explicitly requested. -/
abbrev ChronologicalState (Ground : Type u) :=
  CostConfig Ground × List (CostName Ground × CostSig Ground)

/-- The same Cost execution with an append-only chronological observation.
Changing only this observer can revoke a wave that was lawful at final-state
observation. -/
def chronologicalExecutionSemantics (Ground : Type u) :
    ExecutionSemantics (CostedEvent Ground) (ChronologicalState Ground)
      (ChronologicalState Ground) where
  run source events target :=
    CostTrace source.1 (costWaveTrace events) target.1 ∧
      target.2 = source.2 ++ costWaveTrace events
  observe := id

/-- Candidate occurrences are observed as an exact bag. -/
def completeBagContract (Ground : Type u) :
    Contract (CostedEvent Ground) Unit (Multiset (CostedEvent Ground)) where
  observer := { observe := fun events => (events : Multiset (CostedEvent Ground)) }
  demand := { completion := .completeBag }

/-- The same candidate observation under first-witness demand. -/
def firstContract (Ground : Type u) :
    Contract (CostedEvent Ground) Unit (Multiset (CostedEvent Ground)) where
  observer := { observe := fun events => (events : Multiset (CostedEvent Ground)) }
  demand := { completion := .first }

namespace CertifiedFamilyBridge

variable {Ground : Type u} {events : List (CostedEvent Ground)}
variable {source : CostConfig Ground}

/-- The Cost-rho common-source equation is exactly the generic additive
account decomposition. -/
def toBatchSeparation
    (separation : FamilySeparation Ground events source) :
    BatchSeparation (CostConfig Ground) eventDemand source events where
  frame := separation.frame
  source_eq := by
    change source =
      (events.map CostedEvent.consumed).sum + separation.frame
    exact separation.source_eq

/-- The positional event count supplies a second exact additive account.
It is independent of the linear Cost configuration. -/
def toUnitBudgetSeparation
    (events : List (CostedEvent Ground)) :
    BatchSeparation Nat eventUnitBudget events.length events where
  frame := 0
  source_eq := by
    induction events with
    | nil => rfl
    | cons event rest inductionHypothesis =>
        simp [batchDemand, eventUnitBudget, inductionHypothesis, Nat.add_comm]

/-- Linear Cost resources and an auxiliary execution budget compose
pointwise over the same exact event occurrences. -/
def toResourceBudgetSeparation
    (separation : FamilySeparation Ground events source) :
    BatchSeparation (CostConfig Ground × Nat)
      (fun event => (eventDemand event, eventUnitBudget event))
      (source, events.length) events :=
  BatchSeparation.pair (toBatchSeparation separation)
    (toUnitBudgetSeparation events)

/-- Every Cost-rho family serializes to its exact target under every
permutation of the same occurrence list. -/
theorem serializesToTarget
    (separation : FamilySeparation Ground events source) :
    (executionSemantics Ground).SerializesTo source events separation.target := by
  constructor
  · exact separation.permutation_reaches_common_target
      (List.Perm.refl events)
  · intro ordering permutation
    exact ⟨separation.target,
      separation.permutation_reaches_common_target permutation, rfl⟩

/-- A complete-bag Cost family inhabits the generic observation/resource
wave license without introducing a second scheduler. -/
def toCompleteCertified
    (separation : FamilySeparation Ground events source) :
    CertifiedBatch (completeBagContract Ground) (executionSemantics Ground)
      source separation.target (CostConfig Ground) eventDemand source events where
  nonempty := separation.nonempty
  candidateInvariant := by
    intro ordering permutation
    exact Quot.sound permutation
  executionSerializable := serializesToTarget separation
  resources := toBatchSeparation separation

/-- The complete-bag wave with both its native linear account and a distinct
unit execution budget.  Adding the second account changes no semantic or
observer proof. -/
def toCompleteResourceBudgetCertified
    (separation : FamilySeparation Ground events source) :
    CertifiedBatch (completeBagContract Ground) (executionSemantics Ground)
      source separation.target (CostConfig Ground × Nat)
      (fun event => (eventDemand event, eventUnitBudget event))
      (source, events.length) events where
  nonempty := separation.nonempty
  candidateInvariant := by
    intro ordering permutation
    exact Quot.sound permutation
  executionSerializable := serializesToTarget separation
  resources := toResourceBudgetSeparation separation

/-- The same semantic and resource evidence can be presented to a bounded
consumer without changing that consumer's demand. -/
def toFirstCertified
    (separation : FamilySeparation Ground events source) :
    CertifiedBatch (firstContract Ground) (executionSemantics Ground)
      source separation.target (CostConfig Ground) eventDemand source events where
  nonempty := separation.nonempty
  candidateInvariant := by
    intro ordering permutation
    exact Quot.sound permutation
  executionSerializable := serializesToTarget separation
  resources := toBatchSeparation separation

/-- Complete-bag observation uses the already licensed family as one bulk
wave. -/
theorem complete_plan_is_bulk
    (separation : FamilySeparation Ground events source) :
    ((toCompleteCertified separation).plan .general).activation = .bulk :=
  (toCompleteCertified separation).completeBag_dispatches_bulk rfl

/-- First-witness demand remains controlled for the identical event family. -/
theorem first_plan_is_controlled
    (separation : FamilySeparation Ground events source) :
    ((toFirstCertified separation).plan .general).activation = .controlled :=
  (toFirstCertified separation).first_remains_controlled rfl

/-- The generic structural readout agrees with the established Cost schedule
WorkSpan for one separated family. -/
theorem certified_workSpan_agrees
    (separation : FamilySeparation Ground events source) :
    (toCompleteCertified separation).unitWorkSpan = separation.schedule.workSpan := by
  rw [separation.schedule_workSpan]
  rfl

/-- The authored ordering is a genuine run of the chronology-retaining
semantics.  This does not claim that its permutations have the same
chronology. -/
theorem chronological_reference_run
    (separation : FamilySeparation Ground events source) :
    (chronologicalExecutionSemantics Ground).run (source, []) events
      (separation.target, costWaveTrace events) :=
  ⟨separation.permutation_reaches_common_target (List.Perm.refl events),
    by simp⟩

/-- Adding an independent funding axis does not alter the structural
WorkSpan readout of the licensed occurrence wave. -/
theorem resourceBudget_workSpan_agrees
    (separation : FamilySeparation Ground events source) :
    (toCompleteResourceBudgetCertified separation).unitWorkSpan =
      separation.schedule.workSpan := by
  rw [separation.schedule_workSpan]
  rfl

end CertifiedFamilyBridge

/-! ## Positive and negative controls -/

namespace Examples

open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFamilyFibration.Examples
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionFibration.Examples

/-- The existing same-channel, distinct-resource family receives a complete
bulk plan with its exact `(2, 1)` Cost schedule observation. -/
theorem separated_pair_is_bulk_with_exact_workSpan :
    ((CertifiedFamilyBridge.toCompleteCertified oneColourFamily).plan
        .general).activation = .bulk ∧
      (CertifiedFamilyBridge.toCompleteCertified oneColourFamily).unitWorkSpan =
        oneColourFamily.schedule.workSpan ∧
      oneColourFamily.schedule.workSpan = ⟨2, 1⟩ :=
  ⟨CertifiedFamilyBridge.complete_plan_is_bulk oneColourFamily,
    CertifiedFamilyBridge.certified_workSpan_agrees oneColourFamily,
    oneColourFamily.schedule_workSpan⟩

/-- The real pair is simultaneously funded by its Cost inventory and by two
independently declared execution units; neither account was inferred from the
other or from the schedule valuation. -/
theorem separated_pair_has_two_independent_accounts :
    ((CertifiedFamilyBridge.toCompleteResourceBudgetCertified
        oneColourFamily).plan .general).activation = .bulk ∧
      (CertifiedFamilyBridge.toCompleteResourceBudgetCertified
        oneColourFamily).resources.frame =
          (oneColourFamily.frame, 0) ∧
      (CertifiedFamilyBridge.toCompleteResourceBudgetCertified
        oneColourFamily).unitWorkSpan = ⟨2, 1⟩ := by
  constructor
  · exact (CertifiedFamilyBridge.toCompleteResourceBudgetCertified
      oneColourFamily).completeBag_dispatches_bulk rfl
  constructor
  · rfl
  · exact (CertifiedFamilyBridge.resourceBudget_workSpan_agrees
      oneColourFamily).trans oneColourFamily.schedule_workSpan

/-- The two event serializations have the same final Cost configuration but
different exact chronological labels. -/
theorem separated_pair_event_traces_differ :
    costWaveTrace [leftEvent, rightEvent] ≠
      costWaveTrace [rightEvent, leftEvent] := by
  decide

/-- A final-state complete-bag observer licenses the pair as one wave, but an
exact chronology observer refuses the same permutation quotient.  Resource
separation and good WorkSpan cannot override this stronger observation. -/
theorem separated_pair_not_serializable_at_exact_chronology :
    ¬ (chronologicalExecutionSemantics Ground).SerializesTo
      (source, []) [leftEvent, rightEvent]
      (oneColourFamily.target, costWaveTrace [leftEvent, rightEvent]) := by
  intro serializable
  obtain ⟨target, targetRun, sameObservation⟩ :=
    serializable.2 [rightEvent, leftEvent]
      (List.Perm.swap leftEvent rightEvent [])
  change target =
    (oneColourFamily.target, costWaveTrace [leftEvent, rightEvent])
      at sameObservation
  subst target
  apply separated_pair_event_traces_differ
  simpa using targetRun.2

/-- Merely changing the consumer to first-witness demand removes bulk
permission without changing Cost semantics or resource evidence. -/
theorem separated_pair_first_is_not_bulk :
    ((CertifiedFamilyBridge.toFirstCertified oneColourFamily).plan
      .general).activation =
      .controlled :=
  CertifiedFamilyBridge.first_plan_is_controlled oneColourFamily

/-- The contested single purse cannot inhabit the integrated wave license.
The obstruction is already present in its exact additive account field. -/
theorem contested_has_no_integrated_wave_license :
    ¬ Nonempty
      (Σ target : CostConfig Ground,
        CertifiedBatch (completeBagContract Ground)
          (executionSemantics Ground) contestedSource target
          (CostConfig Ground) eventDemand contestedSource
          [leftEvent, leftCompetitor]) := by
  rintro ⟨⟨target, certified⟩⟩
  apply contested_has_no_family_separation
  exact
    { frame := certified.resources.frame
      source_eq := by
        simpa [batchDemand, eventDemand, costWaveSource] using
          certified.resources.source_eq
      nonempty := certified.nonempty }

end Examples

/-! ## Axiom audit -/

#print axioms CertifiedFamilyBridge.serializesToTarget
#print axioms CertifiedFamilyBridge.complete_plan_is_bulk
#print axioms CertifiedFamilyBridge.first_plan_is_controlled
#print axioms CertifiedFamilyBridge.certified_workSpan_agrees
#print axioms CertifiedFamilyBridge.resourceBudget_workSpan_agrees
#print axioms CertifiedFamilyBridge.chronological_reference_run
#print axioms Examples.separated_pair_is_bulk_with_exact_workSpan
#print axioms Examples.separated_pair_has_two_independent_accounts
#print axioms Examples.separated_pair_not_serializable_at_exact_chronology
#print axioms Examples.separated_pair_first_is_not_bulk
#print axioms Examples.contested_has_no_integrated_wave_license

end Mettapedia.Languages.MeTTa.Prime.NativeObservationControlledCostWaves
