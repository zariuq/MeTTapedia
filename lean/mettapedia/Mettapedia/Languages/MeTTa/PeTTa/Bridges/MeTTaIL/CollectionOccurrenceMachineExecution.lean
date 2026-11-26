import Mettapedia.Languages.MeTTa.PeTTa.EquationEquality
import Mettapedia.OSLF.MeTTaIL.GeneralTypedSitesFocus
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceCollectorExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceInstallationExecution
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceMachine

/-!
# Native joint retained occurrence transitions

Each round advances source-job matcher lanes, appends only fresh allocation
frames, and advances the existing conditional batch. The comparison retains
the complete matcher state, continuation frames and chronological log. Source
job generation and selection of an emitted profile are separate interfaces.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceMachineExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionOccurrenceBatch CollectionOccurrenceMatcher CanonicalCompare
open SpaceSemantics Eval BridgeKit WireKit CollectionOccurrenceCollectorExecution
open CollectionOccurrenceRuntime
open scoped ProgramQuotation

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {sourcePattern : Pattern}

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_collection_occurrence_machine.metta"
    sha256 "bfbca7b35bfa678b4145030bf631bbe7bc4e6291cfb2e10561e152db0468f0df"

def library : Library :=
  CollectionOccurrenceSearchExecution.SelectedNativeSource.library

theorem checked : library.check = true := CollectionOccurrenceSearchExecution.SelectedNativeSource.checked

section ProofMetadata
private local instance machineEquationEq : DecidableEq SpaceSemantics.Equation :=
  SpaceSemantics.Equation.decideEq

private def machineProofBase : Program :=
  (((RuleExecutionProgram.callFragment ["gslt:occurrence-batch:begin", "gslt:occurrence-batch:run",
      "gslt:occurrence-batch:publication"]
      (RuleExecutionProgram.interpretedPremiseSupportSources[14]'(by decide +kernel)).program).append
    (RuleExecutionProgram.callFragment ["gslt:occurrence-install:append"]
      (RuleExecutionProgram.interpretedPremiseSupportSources[15]'(by decide +kernel)).program)).append
    (RuleExecutionProgram.callFragment ["gslt:occurrence-collector:advance-lanes"]
      (RuleExecutionProgram.interpretedPremiseSupportSources[17]'(by decide +kernel)).program))

def machineProofLibrary : Library := ⟨machineProofBase,
  source.program,
  ["gslt:occurrence-machine:"]⟩
def machineProofHeads (head : String) : Bool := !head.startsWith "gslt:" || machineProofLibrary.owns head ||
  ["gslt:occurrence-batch:begin", "gslt:occurrence-batch:run", "gslt:occurrence-batch:publication",
    "gslt:occurrence-install:append", "gslt:occurrence-collector:advance-lanes"].contains head

theorem machineProof_checked : machineProofLibrary.check = true := by decide +kernel

theorem machineProof_agreement : ProgramAgreementOn machineProofHeads machineProofLibrary.runtime
    CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

end ProofMetadata

def stateTerm (state : CollectionOccurrenceMachine.State plan bound expected sourcePattern) : Term :=
  .application "RecursiveOccurrenceState"
    [encodeList CollectionOccurrenceMatcherExecution.laneTerm state.matchers,
      CollectionOccurrenceBatchExecution.stateTerm state.batch]

/-- Encode the same retained state using the explicitly selected matching codec. -/
def stateTermWith {matcher : GeneralPremise.MatchingExecution}
    (codec : RetainedMatchingWire.MatchingCodec matcher)
    (state : CollectionOccurrenceMachine.State plan bound expected sourcePattern matcher) : Term :=
  .application "RecursiveOccurrenceState"
    [encodeList CollectionOccurrenceMatcherExecution.laneTerm state.matchers,
      CollectionOccurrenceBatchExecution.stateTermWith codec state.batch]

theorem stateTermWith_ordinary (state : CollectionOccurrenceMachine.State plan bound expected sourcePattern) :
    stateTermWith RetainedMatchingWire.ordinaryCodec state = stateTerm state := by
  simp only [stateTermWith, stateTerm, CollectionOccurrenceBatchExecution.stateTermWith_ordinary]

#print axioms stateTermWith_ordinary

syntax "occurrence_machine_eval" (" [" term,* "]")?
    (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| occurrence_machine_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call_in machineProof_checked using machineProof_agreement; metta_eval [$facts,*] with machineProof_checked in machineProof_agreement
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        stateTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany, $extra,*]))

structure Ready (names footprint : List String)
    (state : CollectionOccurrenceMachine.State plan bound expected sourcePattern) : Prop where
  matchers : ∀ lane ∈ state.matchers, LaneReady names footprint lane
  batch : CollectionOccurrenceBatchExecution.StateReady footprint state.batch

private theorem collected_job (job : CollectionOccurrenceHandoff.Job)
    (licensed : job.Valid plan bound expected sourcePattern) (work depth : Nat) :
    ∀ (answers : List RecursiveCollectionMachine.Answer)
      (published : ∀ answer ∈ answers, Published job work answer)
      {allocation : Allocation plan bound expected sourcePattern},
      allocation ∈ collect job licensed work depth answers published → allocation.job = job
  | [], _, _, member => by cases member
  | answer :: answers, published, allocation, member => by
    rcases List.mem_append.mp member with first | later
    · cases made : allocate? job licensed work answer
        (published answer List.mem_cons_self) depth with
      | none => simp only [made, Option.toList_none, List.not_mem_nil] at first
      | some selected =>
        have same : allocation = selected := by
          simpa only [made, Option.toList_some, List.mem_singleton] using first
        subst allocation
        exact (allocate_readout job licensed work depth answer
          (published answer List.mem_cons_self) made).1
    · exact collected_job job licensed work depth answers
        (fun next member => published next (List.mem_cons_of_mem _ member)) later

theorem lane_resume_ready (names footprint : List String)
    (lane : Lane plan bound expected sourcePattern) (work : Nat)
    (ready : LaneReady names footprint lane) : LaneReady names footprint (lane.resume work) := by
  exact ⟨RecursiveCollectionMachine.run_covered lane.job.request names work ready.state,
    ready.target, ready.free, ready.admitted, ready.sorted⟩

/-- Finite source-name coverage suffices for every newly created
continuation; no completed premise or publication account is assumed. -/
theorem fresh_frames_ready (names footprint : List String) (depth : Nat)
    (lanes : List (Lane plan bound expected sourcePattern))
    (ready : ∀ lane ∈ lanes, LaneReady names footprint lane)
    (allocation : Allocation plan bound expected sourcePattern)
    (member : allocation ∈ lanes.flatMap (Lane.allocations depth)) :
    CollectionOccurrenceBatchExecution.FrameReady footprint (Frame.initial allocation) := by
  obtain ⟨lane, inLanes, inLane⟩ := List.mem_flatMap.mp member
  have sameJob := collected_job lane.job lane.licensed (lane.spent + 1) depth lane.fresh
    (fun answer member => (lane.resume 1).published answer (List.mem_of_mem_drop member)) inLane
  apply RecursiveCollectionContinuation.start_free_within
  change ∀ name ∈ allocation.request.source.freeFvarNames, name ∈ footprint
  rw [allocation.request_fields.2.2.2.1, sameJob]
  exact (ready lane inLanes).free

theorem installed_ready (names footprint : List String) (depth : Nat)
    (state : CollectionOccurrenceMachine.State plan bound expected sourcePattern)
    (ready : Ready names footprint state) :
    CollectionOccurrenceBatchExecution.StateReady footprint
      (state.batch.install (state.matchers.flatMap (Lane.allocations depth))) := by
  intro frame member
  rcases List.mem_append.mp member with old | fresh
  · exact ready.batch frame old
  · obtain ⟨allocation, inAllocations, rfl⟩ := List.mem_map.mp fresh
    exact fresh_frames_ready names footprint depth state.matchers ready.matchers allocation inAllocations

theorem round_ready (names footprint : List String)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) (depth : Nat)
    (state : CollectionOccurrenceMachine.State plan bound expected sourcePattern)
    (ready : Ready names footprint state) :
    Ready names footprint (CollectionOccurrenceMachine.round depth state) := by
  constructor
  · intro lane member
    obtain ⟨old, inMatchers, rfl⟩ := List.mem_map.mp member
    exact lane_resume_ready names footprint old 1 (ready.matchers old inMatchers)
  · exact CollectionOccurrenceBatchExecution.round_ready footprint finite provider _
      (installed_ready names footprint depth state ready)

/-- Initialize from the actual source-generated lane list. This operation
does not claim to generate that list in the target language. -/
@[metta_head "gslt:occurrence-machine:from-lanes"]
theorem from_lanes_returns (host : Effects.State) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-machine:from-lanes"
        [encoded (encodeList CollectionOccurrenceMatcherExecution.laneTerm
          (lanes plan bound expected sourcePattern))])
      host (encoded (stateTerm (CollectionOccurrenceMachine.begin plan bound expected sourcePattern))) := by
  have native := CollectionOccurrenceBatchExecution.begin_returns host
    ([] : List (Allocation plan bound expected sourcePattern))
  have begun := native
  occurrence_machine_eval [begun] unfolding [CollectionOccurrenceMachine.begin, CollectionOccurrenceMachine.beginWith]

@[metta_head "gslt:occurrence-machine:round"]
theorem round_returns (host : Effects.State) (names : List String) (ordered : NameOrdered names)
    (footprint : List String)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) (depth : Nat)
    (state : CollectionOccurrenceMachine.State plan bound expected sourcePattern)
    (ready : Ready names footprint state) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-machine:round"
        [encoded (encodeList Term.string names),
          CompleteExecution.environmentValue (GeneralPlanEnvironment.environment plan)
            ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          number depth, encoded (stateTerm state)])
      host (encoded (stateTerm (CollectionOccurrenceMachine.round depth state))) := by
  have advanced := advance_lanes_returns host names ordered footprint depth state.matchers ready.matchers
  have installed := CollectionOccurrenceInstallationExecution.install_returns host
    (state.matchers.flatMap (Lane.allocations depth)) state.batch
  have worked := CollectionOccurrenceBatchExecution.run_returns host footprint finite provider 1
    (state.batch.install (state.matchers.flatMap (Lane.allocations depth)))
    (installed_ready names footprint depth state ready)
  have continued := worked
  have roundWire : stateTerm (CollectionOccurrenceMachine.round depth state) =
      .application "RecursiveOccurrenceState"
        [encodeList CollectionOccurrenceMatcherExecution.laneTerm (state.matchers.map (Lane.resume 1)),
          CollectionOccurrenceBatchExecution.stateTerm (CollectionOccurrenceBatch.State.run 1
            (state.batch.install (state.matchers.flatMap (Lane.allocations depth))))] := rfl
  rw [roundWire]
  occurrence_machine_eval [advanced, installed, continued] unfolding
    [advancedLanesTerm, CollectionOccurrenceMachine.round, CollectionOccurrenceMachine.roundWith, CollectionOccurrenceBatch.State.run]

@[metta_head "gslt:occurrence-machine:run"]
theorem run_returns (host : Effects.State) (names : List String) (ordered : NameOrdered names)
    (footprint : List String)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) (depth : Nat) :
    ∀ (work : Nat) (state : CollectionOccurrenceMachine.State plan bound expected sourcePattern),
      Ready names footprint state →
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-machine:run"
        [encoded (encodeList Term.string names),
          CompleteExecution.environmentValue (GeneralPlanEnvironment.environment plan)
            ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          number depth, number work, encoded (stateTerm state)])
      host (encoded (stateTerm (CollectionOccurrenceMachine.run depth work state)))
  | 0, state, _ => by occurrence_machine_eval unfolding [CollectionOccurrenceMachine.run, CollectionOccurrenceMachine.runWith]
  | work + 1, state, ready => by
    have next := round_returns host names ordered footprint finite provider depth state ready
    have later := run_returns host names ordered footprint finite provider depth work
      (CollectionOccurrenceMachine.round depth state)
      (round_ready names footprint finite provider depth state ready)
    occurrence_machine_eval [next, later] unfolding [CollectionOccurrenceMachine.run, CollectionOccurrenceMachine.runWith]

@[metta_head "gslt:occurrence-machine:publication"]
theorem publication_returns (host : Effects.State)
    (state : CollectionOccurrenceMachine.State plan bound expected sourcePattern) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-machine:publication" [encoded (stateTerm state)])
      host (encoded (encodeList CollectionOccurrenceBatchExecution.publicationTerm state.batch.log)) := by
  have native := CollectionOccurrenceBatchExecution.publication_returns host state.batch
  have read := native
  occurrence_machine_eval [read]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceMachineExecution


namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceMachineExecution.Canonical
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise CanonicalCompare CollectionOccurrenceBatch CollectionOccurrenceMatcher
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics Eval BridgeKit WireKit


variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr} {expected : TypeExpr} {sourcePattern : Pattern}
local notation "CBatch" => CollectionOccurrenceBatch.State plan bound expected (CanonicalBags.canon sourcePattern)
  RecursiveCollectionHandoff.canonicalMatchingExecution
local notation "CState" => CollectionOccurrenceMachine.State plan bound expected (CanonicalBags.canon sourcePattern)
  RecursiveCollectionHandoff.canonicalMatchingExecution
local notation "CLane" => Lane plan bound expected (CanonicalBags.canon sourcePattern)
local notation "Config" => CollectionOccurrenceBatchExecution.Canonical.Config plan

def stateTerm (state : CState) : Term := .application "RecursiveOccurrenceState"
  [encodeList CollectionOccurrenceMatcherExecution.laneTerm state.matchers,
    CollectionOccurrenceBatchExecution.Canonical.stateTerm state.batch]

theorem stateTermWith_canonical (state : CState) :
    CollectionOccurrenceMachineExecution.stateTermWith RetainedMatchingWire.canonicalCodec state = stateTerm state := by
  simp only [CollectionOccurrenceMachineExecution.stateTermWith, stateTerm,
    CollectionOccurrenceBatchExecution.stateTermWith_canonical]

#print axioms stateTermWith_canonical

structure Ready (config : Config) (state : CState) : Prop where
  source : ∀ name ∈ (CanonicalBags.canon sourcePattern).freeFvarNames, name ∈ config.footprint
  matchers : ∀ lane ∈ state.matchers,
    CollectionOccurrenceCollectorExecution.Selected.Canonical.LaneReady config.names config.footprint lane
  batch : CollectionOccurrenceBatchExecution.Canonical.StateReady config state.batch

theorem lane_resume_ready (config : Config) (lane : CLane) (work : Nat)
    (ready : CollectionOccurrenceCollectorExecution.Selected.Canonical.LaneReady config.names config.footprint lane) :
    CollectionOccurrenceCollectorExecution.Selected.Canonical.LaneReady config.names config.footprint (lane.resume work) :=
  ⟨RecursiveCollectionMachine.run_covered lane.job.request config.names work ready.state,
    ready.target, ready.free, ready.admitted, ready.sorted⟩

theorem installed_ready (config : Config) (depth : Nat) (state : CState) (ready : Ready config state) :
    CollectionOccurrenceBatchExecution.Canonical.StateReady config
      (state.batch.installWith (canonicalSeedProfile plan bound expected sourcePattern)
        (state.matchers.flatMap (Lane.allocations depth))) := by
  intro frame member
  rcases List.mem_append.mp member with old | fresh
  · exact ready.batch frame old
  · obtain ⟨allocation, inAllocations, rfl⟩ := List.mem_map.mp fresh
    rw [Frame.initialWith_canonical]
    apply CollectionOccurrenceBatchExecution.Canonical.initial_ready
    exact CollectionOccurrenceBatchExecution.Canonical.allocation_source_within allocation config.footprint ready.source

theorem round_ready (config : Config) (depth : Nat) (state : CState) (ready : Ready config state) :
    Ready config (CollectionOccurrenceMachine.roundWith (canonicalSeedProfile plan bound expected sourcePattern) depth state) := by
  constructor
  · exact ready.source
  · intro lane member
    obtain ⟨old, inMatchers, rfl⟩ := List.mem_map.mp member
    exact lane_resume_ready config old 1 (ready.matchers old inMatchers)
  · exact CollectionOccurrenceBatchExecution.Canonical.round_ready config _ (installed_ready config depth state ready)

syntax "canonical_machine_eval" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| canonical_machine_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call_in machineProof_checked using machineProof_agreement; metta_eval [$facts,*] with machineProof_checked in machineProof_agreement unfolding
      [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?, stateTerm,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, $extra,*]))

private theorem empty_batch_returns (host : Effects.State) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-batch:begin" [encoded (.symbol "LNil")]) host
      (encoded (CollectionOccurrenceBatchExecution.Canonical.stateTerm
        (⟨[], []⟩ : CBatch))) := by
  simpa only [CollectionOccurrenceBatchExecution.library,
    CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime_same,
    CollectionOccurrenceBatchExecution.frameTerm, CollectionOccurrenceBatchExecution.stateTerm,
    CollectionOccurrenceBatch.State.begin, CollectionOccurrenceBatchExecution.Canonical.stateTerm,
    encodeList, List.map_nil] using CollectionOccurrenceBatchExecution.begin_returns host
      ([] : List (Allocation plan bound expected (CanonicalBags.canon sourcePattern)))

/-- This initializer has no completed outcomes or supplied continuation states. -/
theorem from_lanes_returns (host : Effects.State) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-machine:from-lanes"
        [encoded (encodeList CollectionOccurrenceMatcherExecution.laneTerm
          (lanes plan bound expected (CanonicalBags.canon sourcePattern)))]) host
      (encoded (stateTerm (CollectionOccurrenceMachine.beginWith RecursiveCollectionHandoff.canonicalMatchingExecution
        plan bound expected (CanonicalBags.canon sourcePattern)))) := by
  have begun := empty_batch_returns (plan := plan) (bound := bound) (expected := expected) (sourcePattern := sourcePattern) host
  canonical_machine_eval [begun] unfolding [CollectionOccurrenceMachine.beginWith]

theorem round_returns (host : Effects.State) (config : Config) (depth : Nat) (state : CState) (ready : Ready config state) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-machine:round"
        [encoded (encodeList Term.string config.names), encoded (CollectionOccurrenceBatchExecution.Canonical.environmentTerm config),
          number depth, encoded (stateTerm state)]) host
      (encoded (stateTerm (CollectionOccurrenceMachine.roundWith
        (canonicalSeedProfile plan bound expected sourcePattern) depth state))) := by
  have advanced := CollectionOccurrenceCollectorExecution.Selected.Canonical.advance_lanes_returns host config.names
    config.ordered config.footprint depth state.matchers ready.matchers
  have installed := CollectionOccurrenceInstallationExecution.Canonical.install_returns host (state.matchers.flatMap (Lane.allocations depth)) state.batch
  have continued := CollectionOccurrenceBatchExecution.Canonical.run_returns host config 1
    (state.batch.installWith (canonicalSeedProfile plan bound expected sourcePattern)
      (state.matchers.flatMap (Lane.allocations depth))) (installed_ready config depth state ready)
  simp only [CollectionOccurrenceCollectorExecution.Selected.Canonical.environmentTerm,
    CollectionOccurrenceCollectorExecution.Selected.Canonical.advancedLanesTerm,
    CollectionOccurrenceCollectorExecution.Selected.Canonical.frameTerm, encodeList_map, Function.comp_def] at advanced
  simp only [CollectionOccurrenceBatchExecution.Canonical.frameTerm, encodeList_map, Function.comp_def] at installed
  simp only [CollectionOccurrenceBatchExecution.Canonical.environmentTerm] at continued
  canonical_machine_eval [advanced, installed, continued] unfolding
    [CollectionOccurrenceMachine.roundWith, CollectionOccurrenceCollectorExecution.Selected.Canonical.advancedLanesTerm,
      CollectionOccurrenceBatchExecution.Canonical.environmentTerm, CollectionOccurrenceBatch.State.run,
      Frame.initialWith_canonical, CollectionOccurrenceCollectorExecution.Selected.Canonical.frameTerm,
      CollectionOccurrenceBatchExecution.Canonical.frameTerm, encodeList_map, Function.comp_def]

theorem run_returns (host : Effects.State) (config : Config) (depth : Nat) :
    ∀ (work : Nat) (state : CState), Ready config state →
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-machine:run"
        [encoded (encodeList Term.string config.names), encoded (CollectionOccurrenceBatchExecution.Canonical.environmentTerm config),
          number depth, number work, encoded (stateTerm state)]) host
      (encoded (stateTerm (CollectionOccurrenceMachine.runWith
        (canonicalSeedProfile plan bound expected sourcePattern) depth work state)))
  | 0, state, _ => by canonical_machine_eval unfolding [CollectionOccurrenceMachine.runWith]
  | work + 1, state, ready => by
    have next := round_returns host config depth state ready
    have later := run_returns host config depth work
      (CollectionOccurrenceMachine.roundWith (canonicalSeedProfile plan bound expected sourcePattern) depth state)
      (round_ready config depth state ready)
    canonical_machine_eval [next, later] unfolding [CollectionOccurrenceMachine.runWith]

theorem run_ready (config : Config) (depth work : Nat) (state : CState) (ready : Ready config state) :
    Ready config (CollectionOccurrenceMachine.runWith (canonicalSeedProfile plan bound expected sourcePattern) depth work state) := by
  induction work generalizing state with
  | zero => exact ready
  | succ work ih => exact ih _ (round_ready config depth state ready)

theorem resumed_returns (host : Effects.State) (config : Config) (depth first extra : Nat)
    (state : CState) (ready : Ready config state) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-machine:run"
        [encoded (encodeList Term.string config.names), encoded (CollectionOccurrenceBatchExecution.Canonical.environmentTerm config),
          number depth, number extra, encoded (stateTerm (CollectionOccurrenceMachine.runWith
            (canonicalSeedProfile plan bound expected sourcePattern) depth first state))]) host
      (encoded (stateTerm (CollectionOccurrenceMachine.runWith
        (canonicalSeedProfile plan bound expected sourcePattern) depth (first + extra) state))) := by
  have native := run_returns host config depth extra
    (CollectionOccurrenceMachine.runWith (canonicalSeedProfile plan bound expected sourcePattern) depth first state)
    (run_ready config depth first state ready)
  rw [← CollectionOccurrenceMachine.runWith_add] at native
  exact native

theorem publication_returns (host : Effects.State) (state : CState) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-machine:publication" [encoded (stateTerm state)]) host
      (encoded (encodeList CollectionOccurrenceBatchExecution.Canonical.publicationTerm state.batch.log)) := by
  have native := CollectionOccurrenceBatchExecution.Canonical.publication_returns host state.batch
  canonical_machine_eval [native]

#print axioms machineProof_checked
#print axioms machineProof_agreement
#print axioms lane_resume_ready
#print axioms installed_ready
#print axioms round_ready
#print axioms CollectionOccurrenceInstallationExecution.Canonical.install_returns
#print axioms empty_batch_returns
#print axioms from_lanes_returns
#print axioms round_returns
#print axioms run_returns
#print axioms run_ready
#print axioms resumed_returns
#print axioms publication_returns
end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceMachineExecution.Canonical


namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceMachineExecution.Canonical
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise CanonicalCompare CollectionOccurrenceBatch CollectionOccurrenceMatcher
open SpaceSemantics Eval BridgeKit WireKit

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr} {expected : TypeExpr} {sourcePattern : Pattern}

/-- Every lane obligation follows from its genuine typed occurrence and the finite source alphabet. -/
theorem begin_ready (config : CollectionOccurrenceBatchExecution.Canonical.Config plan)
    (inside : ∀ name ∈ (CanonicalBags.canon sourcePattern).freeFvarNames, name ∈ config.footprint)
    (admitted : ∀ declaration ∈ plan.rules,
      RuleBinding.admittedFor declaration.rule declaration.binding.spec = true)
    (canonical : (CanonicalBags.canon sourcePattern).hasCanonicalBinderMetadata = true) :
    Ready config (CollectionOccurrenceMachine.beginWith RecursiveCollectionHandoff.canonicalMatchingExecution
      plan bound expected (CanonicalBags.canon sourcePattern)) := by
  constructor
  · exact inside
  · intro lane member
    obtain ⟨selected, _, rfl⟩ := List.mem_map.mp member
    let job := selected.val
    have valid : job.Valid plan bound expected (CanonicalBags.canon sourcePattern) :=
      (CollectionOccurrenceHandoff.jobs_exact _ _ _ _ _).mp selected.property
    have fields : job.variant.site.focus = job.origin.site.focus ∧
        job.variant.site.focusBound = job.origin.site.focusBound ∧
        job.variant.site.focusType = job.origin.site.focusType := by
      obtain ⟨context, _, same⟩ := List.mem_map.mp valid.2
      rw [← same]
      exact ⟨rfl,rfl,rfl⟩
    have sorted : WellSorted.OpenPatternWellSorted
        (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
        job.variant.site.focusBound job.variant.site.focusType job.variant.site.focus := by
      simpa only [fields.1, fields.2.1, fields.2.2] using valid.1.2.focus_sorted canonical
    have free : ∀ name ∈ job.variant.site.focus.freeFvarNames, name ∈ config.footprint := by
      rw [fields.1]
      intro name occurs
      apply inside name
      rw [← valid.1.2.source_eq]
      exact (GeneralEquationContexts.fill_contains_source job.origin.site.context job.origin.site.focus).2.1 name occurs
    have target : Covered config.names job.request.target :=
      TypedObjectAlphabet.wellSorted_covered sorted config.declarations
        (fun name member => config.included name (free name member))
    exact ⟨RecursiveCollectionMachine.start_covered config.names job.request target, target, free,
      admitted job.origin.declaration (List.fst_mem_of_mem_zipIdx valid.1.1), sorted⟩
  · intro frame member
    cases member

/-- Rule admission used here is read from the actual compiler result. -/
theorem compiled_rules_admitted (snapshot : GeneralExecutionAdmission.Snapshot)
    (permissions : GeneralExecutionAdmission.Permissions) :
    ∀ declaration ∈ (GeneralExecutionAdmission.compile snapshot permissions).rules,
      RuleBinding.admittedFor declaration.rule declaration.binding.spec = true := by
  intro declaration member
  obtain ⟨rule, index, authored, selected, made⟩ := GeneralExecutionAdmission.compiled_rule_origin member
  exact (GeneralExecutionAdmission.rulePlan_readout made).2.2.2.1

theorem seeded_ready
    (unregistered : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (admitted : ∀ declaration ∈ plan.rules,
      RuleBinding.admittedFor declaration.rule declaration.binding.spec = true)
    (canonical : (CanonicalBags.canon sourcePattern).hasCanonicalBinderMetadata = true) :
    Ready (CollectionOccurrenceBatchExecution.Canonical.Config.forSource plan (CanonicalBags.canon sourcePattern) unregistered)
      (CollectionOccurrenceMachine.beginWith RecursiveCollectionHandoff.canonicalMatchingExecution
        plan bound expected (CanonicalBags.canon sourcePattern)) :=
  begin_ready _ (fun _ member => List.mem_append_left _ member) admitted canonical

/-- Public-loop work begins from typed source discovery, with no supplied outcome or future readiness. -/
theorem seeded_run_returns (host : Effects.State)
    (unregistered : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (admitted : ∀ declaration ∈ plan.rules,
      RuleBinding.admittedFor declaration.rule declaration.binding.spec = true)
    (canonical : (CanonicalBags.canon sourcePattern).hasCanonicalBinderMetadata = true) (depth work : Nat) :
    let config := CollectionOccurrenceBatchExecution.Canonical.Config.forSource plan (CanonicalBags.canon sourcePattern) unregistered
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-machine:run" [encoded (encodeList Term.string config.names),
        encoded (CollectionOccurrenceBatchExecution.Canonical.environmentTerm config), number depth, number work,
        encoded (stateTerm (CollectionOccurrenceMachine.beginWith RecursiveCollectionHandoff.canonicalMatchingExecution
          plan bound expected (CanonicalBags.canon sourcePattern)))]) host
      (encoded (stateTerm (CollectionOccurrenceMachine.runWith (canonicalSeedProfile plan bound expected sourcePattern)
        depth work (CollectionOccurrenceMachine.beginWith RecursiveCollectionHandoff.canonicalMatchingExecution
          plan bound expected (CanonicalBags.canon sourcePattern))))) :=
  run_returns host _ depth work _ (seeded_ready unregistered admitted canonical)

/-- Compiler readout and the source-derived alphabet discharge readiness at the actual native loop. -/
theorem compiled_seeded_run_returns (host : Effects.State)
    (snapshot : GeneralExecutionAdmission.Snapshot) (permissions : GeneralExecutionAdmission.Permissions)
    (unregistered : (GeneralPlanEnvironment.environment
      (GeneralExecutionAdmission.compile snapshot permissions)).provider.dynamicRelations = [])
    (canonical : (CanonicalBags.canon sourcePattern).hasCanonicalBinderMetadata = true) (depth work : Nat) :
    let plan := GeneralExecutionAdmission.compile snapshot permissions
    let config := CollectionOccurrenceBatchExecution.Canonical.Config.forSource plan (CanonicalBags.canon sourcePattern) unregistered
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-machine:run" [encoded (encodeList Term.string config.names),
        encoded (CollectionOccurrenceBatchExecution.Canonical.environmentTerm config), number depth, number work,
        encoded (stateTerm (CollectionOccurrenceMachine.beginWith RecursiveCollectionHandoff.canonicalMatchingExecution
          plan bound expected (CanonicalBags.canon sourcePattern)))]) host
      (encoded (stateTerm (CollectionOccurrenceMachine.runWith (canonicalSeedProfile plan bound expected sourcePattern)
        depth work (CollectionOccurrenceMachine.beginWith RecursiveCollectionHandoff.canonicalMatchingExecution
          plan bound expected (CanonicalBags.canon sourcePattern))))) :=
  seeded_run_returns host unregistered (compiled_rules_admitted snapshot permissions) canonical depth work

/-- Interrupted compiled execution resumes the same lanes, frames, histories and full packet log. -/
theorem compiled_seeded_resume_returns (host : Effects.State)
    (snapshot : GeneralExecutionAdmission.Snapshot) (permissions : GeneralExecutionAdmission.Permissions)
    (unregistered : (GeneralPlanEnvironment.environment
      (GeneralExecutionAdmission.compile snapshot permissions)).provider.dynamicRelations = [])
    (canonical : (CanonicalBags.canon sourcePattern).hasCanonicalBinderMetadata = true) (depth first extra : Nat) :
    let plan := GeneralExecutionAdmission.compile snapshot permissions
    let config := CollectionOccurrenceBatchExecution.Canonical.Config.forSource plan (CanonicalBags.canon sourcePattern) unregistered
    let initial := CollectionOccurrenceMachine.beginWith RecursiveCollectionHandoff.canonicalMatchingExecution
      plan bound expected (CanonicalBags.canon sourcePattern)
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-machine:run" [encoded (encodeList Term.string config.names),
        encoded (CollectionOccurrenceBatchExecution.Canonical.environmentTerm config), number depth, number extra,
        encoded (stateTerm (CollectionOccurrenceMachine.runWith
          (canonicalSeedProfile plan bound expected sourcePattern) depth first initial))]) host
      (encoded (stateTerm (CollectionOccurrenceMachine.runWith
        (canonicalSeedProfile plan bound expected sourcePattern) depth (first + extra) initial))) :=
  resumed_returns host _ depth first extra _
    (seeded_ready unregistered (compiled_rules_admitted snapshot permissions) canonical)

#print axioms begin_ready
#print axioms compiled_rules_admitted
#print axioms seeded_ready
#print axioms seeded_run_returns
#print axioms compiled_seeded_run_returns
#print axioms compiled_seeded_resume_returns
end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceMachineExecution.Canonical
