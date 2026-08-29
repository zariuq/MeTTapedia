import Mettapedia.CognitiveArchitecture.AttentionGuidedMindAgentWave
import Mettapedia.CognitiveArchitecture.RecurrentMindAgentPortfolio

/-!
# Recurrent generated work admitted as parallel mind-agent waves

A recurrent checked controller, an authored triggered-space realization, and a
parallel-wave certificate are independent structures.  This module gives their
smallest proof-relevant intersection: the exact generated work list of one
checked controller prefix is the batch admitted by the existing wave theory.

The positive discriminator uses the five-role cognitive portfolio and a
monotone occurrence-receipt store.  Every ordering has the same observation,
so one complete cycle earns bulk activation.  The negative discriminator keeps
the same checked, generated, selected, and funded work but changes execution to
last-writer-wins state.  Reversing two occurrences changes the observed result,
so no wave exists.  Recurrence and funding therefore cannot manufacture
parallel authority.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.RecurrentParallelMindAgentWave

noncomputable section

open Mettapedia.CognitiveArchitecture.AttentionEconomy
open Mettapedia.CognitiveArchitecture.AttentionEconomyResourceControl
open Mettapedia.CognitiveArchitecture.AttentionGuidedMindAgentWave
open Mettapedia.CognitiveArchitecture.MindAgentServiceScheduling
open Mettapedia.CognitiveArchitecture.RecurrentMindAgentPortfolio
open Mettapedia.CognitiveArchitecture.TriggeredMindAgentSpace
open Mettapedia.CognitiveArchitecture.TriggeredOccurrenceRouteRealization
open Mettapedia.GSLT
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.Dynamics.RecurrentOccurrenceRoute
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.CheckerCapabilities

universe uAuthority uCertificate uTrigger uResident
universe uGuard uCandidateView uState uStateView
universe uActor uCurrency uValue uPriority

/-! ## Generic intersection -/

/-- The exact triggered work batch obtained from one checked finite prefix. -/
def checkedGeneratedPrefix
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [DecidableEq theory.Term]
    (stepAuthority : StepAuthority.{uAuthority, uCertificate}
      AuthorityId theory)
    (accepting : theory.Term -> Bool)
    (claim : RecurrentTraceClaim theory stepAuthority.Certificate)
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    {Trigger : Type uTrigger} {Resident : Type uResident}
    {space : Space Trigger Resident} {trace : Space.TriggerTrace Trigger}
    {represents : TraceLink theory stepAuthority.Certificate ->
      Trigger -> Resident -> Prop}
    (codec : Codec stepAuthority claim space trace represents)
    (depth : Nat) : List (TriggeredOccurrence Trigger Resident) :=
  codec.realizeRoute accepting
    (finitePrefix stepAuthority accepting claim locallyValid execution depth)

/-- A recurrent generated wave retains recurrence of the source controller and
admits the exact generated prefix through the ordinary observation, execution,
and resource-certified wave interface.

This is an admission certificate, not an execution receipt. -/
structure RecurrentGeneratedWave
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [DecidableEq theory.Term]
    (stepAuthority : StepAuthority.{uAuthority, uCertificate}
      AuthorityId theory)
    (accepting : theory.Term -> Bool)
    (claim : RecurrentTraceClaim theory stepAuthority.Certificate)
    (locallyValid : claim.controller.LocallyValid
      (auditedLabeledSystem stepAuthority accepting) claim.root)
    (execution : ControlledExecution claim.controller claim.root)
    {Trigger : Type uTrigger} {Resident : Type uResident}
    (space : Space Trigger Resident) (trace : Space.TriggerTrace Trigger)
    (represents : TraceLink theory stepAuthority.Certificate ->
      Trigger -> Resident -> Prop)
    (codec : Codec stepAuthority claim space trace represents)
    (depth : Nat)
    {Guard : Type uGuard} {CandidateView : Type uCandidateView}
    {State : Type uState} {StateView : Type uStateView}
    {Actor : Type uActor} {Currency : Type uCurrency}
    [AddCommMonoid Currency]
    (contract : Contract (TriggeredOccurrence Trigger Resident)
      Guard CandidateView)
    (semantics : ExecutionSemantics
      (TriggeredOccurrence Trigger Resident) State StateView)
    (initial referenceTarget : State)
    (shortDemand : TriggeredOccurrence Trigger Resident ->
      Fund .shortTerm Actor Currency)
    (longDemand : TriggeredOccurrence Trigger Resident ->
      Fund .longTerm Actor Currency)
    (shortSource : Fund .shortTerm Actor Currency)
    (longSource : Fund .longTerm Actor Currency)
    (Value : Type uValue) (Priority : Type uPriority) where
  recurrence : claim.Meaning accepting
  admission : Wave contract semantics initial referenceTarget shortDemand
    longDemand shortSource longSource
    (checkedGeneratedPrefix stepAuthority accepting claim locallyValid
      execution codec depth) Value Priority

namespace RecurrentGeneratedWave

variable {AuthorityId : Type uAuthority} {theory : GSLT}
variable [DecidableEq theory.Term]
variable {stepAuthority : StepAuthority.{uAuthority, uCertificate}
  AuthorityId theory}
variable {accepting : theory.Term -> Bool}
variable {claim : RecurrentTraceClaim theory stepAuthority.Certificate}
variable {locallyValid : claim.controller.LocallyValid
  (auditedLabeledSystem stepAuthority accepting) claim.root}
variable {execution : ControlledExecution claim.controller claim.root}
variable {Trigger : Type uTrigger} {Resident : Type uResident}
variable {space : Space Trigger Resident} {trace : Space.TriggerTrace Trigger}
variable {represents : TraceLink theory stepAuthority.Certificate ->
  Trigger -> Resident -> Prop}
variable {codec : Codec stepAuthority claim space trace represents}
variable {depth : Nat}
variable {Guard : Type uGuard} {CandidateView : Type uCandidateView}
variable {State : Type uState} {StateView : Type uStateView}
variable {Actor : Type uActor} {Currency : Type uCurrency}
variable [AddCommMonoid Currency]
variable {contract : Contract (TriggeredOccurrence Trigger Resident)
  Guard CandidateView}
variable {semantics : ExecutionSemantics
  (TriggeredOccurrence Trigger Resident) State StateView}
variable {initial referenceTarget : State}
variable {shortDemand : TriggeredOccurrence Trigger Resident ->
  Fund .shortTerm Actor Currency}
variable {longDemand : TriggeredOccurrence Trigger Resident ->
  Fund .longTerm Actor Currency}
variable {shortSource : Fund .shortTerm Actor Currency}
variable {longSource : Fund .longTerm Actor Currency}
variable {Value : Type uValue} {Priority : Type uPriority}

/-- Every admitted batch member retains a checked source occurrence and the
authored action-to-resident relation. -/
theorem member_has_checked_source
    (_wave : RecurrentGeneratedWave stepAuthority accepting claim locallyValid
      execution space trace represents codec depth contract semantics initial
      referenceTarget shortDemand longDemand shortSource longSource
      Value Priority)
    {generated : TriggeredOccurrence Trigger Resident}
    (member : generated ∈ checkedGeneratedPrefix stepAuthority accepting claim
      locallyValid execution codec depth) :
    exists source,
      source ∈
        (finitePrefix stepAuthority accepting claim locallyValid execution
          depth).occurrences /\
      codec.realize source = generated /\
      represents source.action generated.trigger generated.resident :=
  codec.mem_realizeRoute_has_source accepting
    (finitePrefix stepAuthority accepting claim locallyValid execution depth)
    member

/-- Every admitted batch member was genuinely generated by the authored
triggered space. -/
theorem member_is_generated
    (_wave : RecurrentGeneratedWave stepAuthority accepting claim locallyValid
      execution space trace represents codec depth contract semantics initial
      referenceTarget shortDemand longDemand shortSource longSource
      Value Priority)
    {generated : TriggeredOccurrence Trigger Resident}
    (member : generated ∈ checkedGeneratedPrefix stepAuthority accepting claim
      locallyValid execution codec depth) :
    space.Generated trace generated.generatedAt generated :=
  codec.mem_realizeRoute_generated accepting
    (finitePrefix stepAuthority accepting claim locallyValid execution depth)
    member

/-- Complete-bag demand turns the already-certified generated prefix into a
bulk activation plan.  Recurrence is not an input to this projection. -/
theorem completeBag_dispatches_bulk
    (wave : RecurrentGeneratedWave stepAuthority accepting claim locallyValid
      execution space trace represents codec depth contract semantics initial
      referenceTarget shortDemand longDemand shortSource longSource
      Value Priority)
    (complete : contract.demand.completion = .completeBag) :
    (wave.admission.certified.plan .general).activation = .bulk :=
  wave.admission.completeBag_dispatches_bulk complete

end RecurrentGeneratedWave

/-! ## Five-role worked discriminator -/

namespace Canary

abbrev Item := Occurrence

def portfolioLocalValidity :
    portfolioClaim.controller.LocallyValid
      (auditedLabeledSystem portfolioStepAuthority foregroundAccepting)
      portfolioClaim.root :=
  ((ProgressMeasure.check_eq_true_iff
    (auditedLabeledSystem portfolioStepAuthority foregroundAccepting)
    portfolioController portfolioMeasure portfolioClaim.root).mp
      portfolio_checker_accepts).1

def cycleBatch : List Item :=
  checkedGeneratedPrefix portfolioStepAuthority foregroundAccepting
    portfolioClaim portfolioLocalValidity portfolioExecution portfolioCodec 5

theorem cycleBatch_is_portfolio_prefix :
    cycleBatch = generatedPrefix 5 :=
  rfl

def contract : Contract Item Unit (Multiset Item) where
  observer := { observe := fun items => (items : Multiset Item) }
  demand := { completion := .completeBag }

/-- A monotone receipt store accumulates exact generated occurrences. -/
def monotoneRun (source : Multiset Item) (items : List Item)
    (target : Multiset Item) : Prop :=
  target = source + (items : Multiset Item)

def monotoneSemantics : ExecutionSemantics Item (Multiset Item)
    (Multiset Item) where
  run := monotoneRun
  observe := id

def unitFund (horizon : ImportanceHorizon) (role : Role) :
    Fund horizon Role Nat where
  balances := Finsupp.single role 1

def shortDemand (item : Item) : Fund .shortTerm Role Nat :=
  unitFund .shortTerm item.resident

def longDemand (item : Item) : Fund .longTerm Role Nat :=
  unitFund .longTerm item.resident

def shortSourceFor (items : List Item) : Fund .shortTerm Role Nat :=
  batchDemand shortDemand items

def longSourceFor (items : List Item) : Fund .longTerm Role Nat :=
  batchDemand longDemand items

def shortSeparation (items : List Item) :
    BatchSeparation (Fund .shortTerm Role Nat)
      shortDemand (shortSourceFor items) items where
  frame := 0
  source_eq := by simp [shortSourceFor]

def longSeparation (items : List Item) :
    BatchSeparation (Fund .longTerm Role Nat)
      longDemand (longSourceFor items) items where
  frame := 0
  source_eq := by simp [longSourceFor]

def cycleCertified :
    CertifiedBatch contract monotoneSemantics 0 (cycleBatch : Multiset Item)
      (ImportanceAccount Role Nat)
      (fun item => (shortDemand item, longDemand item))
      (shortSourceFor cycleBatch, longSourceFor cycleBatch) cycleBatch where
  nonempty := by decide
  candidateInvariant := by
    intro ordering permutation
    exact Quot.sound permutation
  executionSerializable := by
    constructor
    · simp [monotoneSemantics, monotoneRun]
    · intro ordering permutation
      refine ⟨(ordering : Multiset Item), ?_, ?_⟩
      · simp [monotoneSemantics, monotoneRun]
      · exact Quot.sound permutation
  resources := pairFunding (shortSeparation cycleBatch)
    (longSeparation cycleBatch)

def workRole (occurrence : Fin cycleBatch.length) : WorkRole :=
  if (cycleBatch.get occurrence).resident = .foregroundChaining then
    .foreground
  else
    .background

def guidance :
    Mettapedia.GSLT.Dynamics.TypedValueGeometry.Guidance
      (Fin cycleBatch.length) Nat Nat where
  value occurrence := some occurrence.val
  priorityOf := id
  fallback _ := 0

def cycleWave : Wave contract monotoneSemantics 0
    (cycleBatch : Multiset Item) shortDemand longDemand
    (shortSourceFor cycleBatch) (longSourceFor cycleBatch)
    cycleBatch Nat Nat where
  certified := cycleCertified
  role := workRole
  guidance := guidance
  foregroundPresent := ⟨⟨4, by decide⟩, by decide⟩
  backgroundPresent := ⟨⟨0, by decide⟩, by decide⟩

def recurrentCycleWave :
    RecurrentGeneratedWave portfolioStepAuthority foregroundAccepting
      portfolioClaim portfolioLocalValidity portfolioExecution
      serviceSpace heartbeatTrace actionRepresents portfolioCodec 5
      contract monotoneSemantics 0 (cycleBatch : Multiset Item)
      shortDemand longDemand (shortSourceFor cycleBatch)
      (longSourceFor cycleBatch) Nat Nat where
  recurrence := portfolio_checked_consequences.2
  admission := cycleWave

/-- Positive control: the same exact checked cycle is recurrent, genuinely
generated, role-complete, independently funded, and eligible for bulk
activation in the monotone receipt semantics. -/
theorem checked_cycle_earns_parallel_wave :
    portfolioClaim.Meaning foregroundAccepting /\
      (cycleBatch.map fun item => item.resident) =
        [.ecan, .incrementalCompression, .pln, .premiseSelection,
          .foregroundChaining] /\
      (forall item, item ∈ cycleBatch ->
        serviceSpace.Generated heartbeatTrace item.generatedAt item) /\
      (forall item, item ∈ cycleBatch ->
        exists offset, offset < 1 /\
          selectedGenerated (item.generatedAt + offset) item) /\
      Nonempty (BatchSeparation (Fund .shortTerm Role Nat)
        shortDemand (shortSourceFor cycleBatch) cycleBatch) /\
      Nonempty (BatchSeparation (Fund .longTerm Role Nat)
        longDemand (longSourceFor cycleBatch) cycleBatch) /\
      (recurrentCycleWave.admission.certified.plan .general).activation =
        .bulk := by
  refine ⟨recurrentCycleWave.recurrence, ?_, ?_, ?_,
    ⟨shortSeparation cycleBatch⟩, ⟨longSeparation cycleBatch⟩, ?_⟩
  · simpa [cycleBatch_is_portfolio_prefix] using first_cycle_resident_order
  · intro item member
    exact recurrentCycleWave.member_is_generated member
  · intro item member
    exact portfolioCodec.mem_realizeRoute_selected foregroundAccepting
      (finitePrefix portfolioStepAuthority foregroundAccepting portfolioClaim
        portfolioLocalValidity portfolioExecution 5)
      generatedSelection member
  · exact recurrentCycleWave.completeBag_dispatches_bulk rfl

/-! ## Negative serializability control -/

def conflictingBatch : List Item :=
  checkedGeneratedPrefix portfolioStepAuthority foregroundAccepting
    portfolioClaim portfolioLocalValidity portfolioExecution portfolioCodec 2

theorem conflicting_resident_order :
    conflictingBatch.map (fun item => item.resident) =
      [.ecan, .incrementalCompression] := by
  decide

def overwriteStep (_state : Role) (item : Item) : Role := item.resident

def overwriteRun (source : Role) (items : List Item) (target : Role) : Prop :=
  target = items.foldl overwriteStep source

def overwriteSemantics : ExecutionSemantics Item Role Role where
  run := overwriteRun
  observe := id

theorem conflicting_reference_fold :
    conflictingBatch.foldl overwriteStep .foregroundChaining =
      .incrementalCompression := by
  decide

theorem conflicting_reverse_fold :
    conflictingBatch.reverse.foldl overwriteStep .foregroundChaining =
      .ecan := by
  decide

/-- Reversing the two genuinely generated actions changes last-writer-wins
state, so their execution is not serializable at the exact state observer. -/
theorem overwrite_not_serializable :
    ¬ overwriteSemantics.SerializesTo .foregroundChaining conflictingBatch
      .incrementalCompression := by
  intro serializable
  obtain ⟨target, targetRun, sameObservation⟩ :=
    serializable.2 conflictingBatch.reverse conflictingBatch.reverse_perm
  have targetIsEcan : target = .ecan :=
    targetRun.trans conflicting_reverse_fold
  have targetIsCompression : target = .incrementalCompression := by
    simpa [overwriteSemantics] using sameObservation
  rw [targetIsEcan] at targetIsCompression
  exact Role.noConfusion targetIsCompression

theorem no_overwrite_wave :
    ¬ Nonempty
      (Wave contract overwriteSemantics .foregroundChaining
        .incrementalCompression shortDemand longDemand
        (shortSourceFor conflictingBatch) (longSourceFor conflictingBatch)
        conflictingBatch Nat Nat) := by
  rintro ⟨wave⟩
  exact overwrite_not_serializable wave.certified.executionSerializable

/-- Negative control: checked recurrence, generation, bounded selection, and
exact STI/LTI funding together still do not imply parallel admission. -/
theorem recurrence_generation_selection_funding_do_not_imply_wave :
    portfolioClaim.Meaning foregroundAccepting /\
      (forall item, item ∈ conflictingBatch ->
        serviceSpace.Generated heartbeatTrace item.generatedAt item) /\
      (forall item, item ∈ conflictingBatch ->
        exists offset, offset < 1 /\
          selectedGenerated (item.generatedAt + offset) item) /\
      Nonempty (BatchSeparation (Fund .shortTerm Role Nat)
        shortDemand (shortSourceFor conflictingBatch) conflictingBatch) /\
      Nonempty (BatchSeparation (Fund .longTerm Role Nat)
        longDemand (longSourceFor conflictingBatch) conflictingBatch) /\
      ¬ Nonempty
        (Wave contract overwriteSemantics .foregroundChaining
          .incrementalCompression shortDemand longDemand
          (shortSourceFor conflictingBatch) (longSourceFor conflictingBatch)
          conflictingBatch Nat Nat) := by
  refine ⟨portfolio_checked_consequences.2, ?_, ?_,
    ⟨shortSeparation conflictingBatch⟩,
    ⟨longSeparation conflictingBatch⟩, no_overwrite_wave⟩
  · intro item member
    exact portfolioCodec.mem_realizeRoute_generated foregroundAccepting
      (finitePrefix portfolioStepAuthority foregroundAccepting portfolioClaim
        portfolioLocalValidity portfolioExecution 2) member
  · intro item member
    exact portfolioCodec.mem_realizeRoute_selected foregroundAccepting
      (finitePrefix portfolioStepAuthority foregroundAccepting portfolioClaim
        portfolioLocalValidity portfolioExecution 2)
      generatedSelection member

end Canary

#print axioms RecurrentGeneratedWave.member_has_checked_source
#print axioms RecurrentGeneratedWave.member_is_generated
#print axioms RecurrentGeneratedWave.completeBag_dispatches_bulk
#print axioms Canary.checked_cycle_earns_parallel_wave
#print axioms Canary.overwrite_not_serializable
#print axioms Canary.recurrence_generation_selection_funding_do_not_imply_wave

end
end Mettapedia.CognitiveArchitecture.RecurrentParallelMindAgentWave
