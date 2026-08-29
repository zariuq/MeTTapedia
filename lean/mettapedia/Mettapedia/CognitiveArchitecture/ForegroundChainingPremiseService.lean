import Mettapedia.CognitiveArchitecture.TriggeredMindAgentSpace
import Mettapedia.CognitiveArchitecture.MindAgentStoreAdmission
import Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlChainer
import Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlExamples

/-!
# Foreground chaining assisted by a background premise service

This module exercises the mind-agent interfaces on a concrete cognitive
workload.  A foreground given-clause loop reaches a genuine saturated state.
An authored trigger activates a resident background premise selector, the
selector returns an exact algorithmic receipt, and a separate authorization
admits the selected occurrence to the foreground store.  The resumed loop then
derives and observes its goal.

Triggering, recommendation, authorization, store mutation, and proof success
are separate witnesses.  In particular, an unsupported recommendation cannot
enter the store, and a resident service without a trigger does no work.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.ForegroundChainingPremiseService

noncomputable section

open Mettapedia.CognitiveArchitecture.CognitiveSynergy
open Mettapedia.CognitiveArchitecture.MindAgentStoreAdmission
open Mettapedia.CognitiveArchitecture.TriggeredMindAgentSpace
open Mettapedia.GSLT.Core.GivenClauseLoop
open Mettapedia.GSLT.Core.WeightedOccurrenceControl
open Mettapedia.PLN.InferenceControl.PremiseSelection
open Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlChainer
open Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlExamples

/-! ## A triggered Chapter-13 premise selector -/

inductive ResidentService where
  | premiseSelector
deriving DecidableEq, Repr

def selectorSpace : Space Unit ResidentService where
  resident service := service = .premiseSelector
  enabled _trigger service := service = .premiseSelector
  enabled_resident _trigger _service enabled := enabled

def heartbeat (_cycle : Nat) : Option Unit := some ()

def selectorInvocation (cycle : Nat) :
    TriggeredOccurrence Unit ResidentService :=
  Space.occurrenceAt cycle () .premiseSelector

theorem selectorInvocation_generated (cycle : Nat) :
    selectorSpace.Generated heartbeat cycle (selectorInvocation cycle) :=
  selectorSpace.generated_occurrenceAt heartbeat cycle () .premiseSelector rfl rfl

/-- The actual finite Chapter-13 forward selector used by the service. -/
def selectedPremises : Finset Bool :=
  forwardSearch ch13_dependencyBool ch13_checklistBool.topK

/-- The executable Chapter-13 selector selects the unique required premise. -/
theorem requiredPremise_selected : true ∈ selectedPremises := by
  have coverage :
      dependencyCoverage ch13_dependencyBool selectedPremises = 1 := by
    simpa [selectedPremises, forwardSearch] using ch13_bool_coverage_exact_one
  by_contra missing
  have zeroCoverage :
      dependencyCoverage ch13_dependencyBool selectedPremises = 0 := by
    simp [dependencyCoverage, ch13_dependencyBool, missing]
  omega

/-- A recommendation is only data: which triggered call proposed which finite
premise. -/
structure Recommendation where
  invocation : TriggeredOccurrence Unit ResidentService
  selected : Bool

/-- An algorithmic receipt additionally proves that the selected premise came
from the declared Chapter-13 selector and that the service invocation existed. -/
structure SelectionReceipt where
  recommendation : Recommendation
  generated : selectorSpace.Generated heartbeat
    recommendation.invocation.generatedAt recommendation.invocation
  selectedByAlgorithm : recommendation.selected ∈ selectedPremises

def selectionReceiptAt (cycle : Nat) : SelectionReceipt where
  recommendation := ⟨selectorInvocation cycle, true⟩
  generated := selectorInvocation_generated cycle
  selectedByAlgorithm := requiredPremise_selected

/-- Store admission is a separate policy proof.  The current policy admits
only premises belonging to the authored dependency set. -/
structure Authorization (recommendation : Recommendation) where
  allowed : recommendation.selected ∈ ch13_dependencyBool

def selectionAuthorizationAt (cycle : Nat) :
    Authorization (selectionReceiptAt cycle).recommendation where
  allowed := by simp [selectionReceiptAt, ch13_dependencyBool]

/-- A recommendation outside the authored dependency policy cannot acquire an
admission witness merely by being present as advice. -/
def distractorAdvice : Recommendation :=
  ⟨selectorInvocation 0, false⟩

theorem distractorAdvice_not_authorized :
    IsEmpty (Authorization distractorAdvice) := by
  constructor
  intro authorization
  simpa [Authorization, distractorAdvice, ch13_dependencyBool] using
    authorization.allowed

/-! ## The foreground given-clause workload -/

inductive Clause where
  | seed
  | bridge
  | goal
  | distractor
deriving DecidableEq, Repr

/-- Structural clause equality does not identify proof-search occurrences. -/
structure ClauseOccurrence where
  occurrenceId : Nat
  clause : Clause
deriving DecidableEq, Repr

inductive ProofResult where
  | proved
deriving DecidableEq, Repr

def clauseOfPremise : Bool → Clause
  | true => .bridge
  | false => .distractor

/-- One selected and authorized premise becomes one fresh store occurrence.
Its identity is derived from the trigger epoch rather than from clause shape. -/
def admittedOccurrence
    (receipt : SelectionReceipt)
    (_authorization : Authorization receipt.recommendation) : ClauseOccurrence :=
  { occurrenceId := receipt.recommendation.invocation.generatedAt + 1
    clause := clauseOfPremise receipt.recommendation.selected }

structure AuthorizedSelection where
  receipt : SelectionReceipt
  authorization : Authorization receipt.recommendation

def authorizedSelectionAt (cycle : Nat) : AuthorizedSelection :=
  ⟨selectionReceiptAt cycle, selectionAuthorizationAt cycle⟩

def selectedOccurrenceAt (cycle : Nat) : ClauseOccurrence :=
  admittedOccurrence (authorizedSelectionAt cycle).receipt
    (authorizedSelectionAt cycle).authorization

/-- Equal selected premise values at distinct service epochs remain distinct
foreground occurrences. -/
theorem repeated_selection_keeps_occurrence_identity :
    (selectedOccurrenceAt 0).clause = (selectedOccurrenceAt 1).clause ∧
      selectedOccurrenceAt 0 ≠ selectedOccurrenceAt 1 := by
  constructor
  · rfl
  · intro equalOccurrences
    have equalIds := congrArg ClauseOccurrence.occurrenceId equalOccurrences
    simp [selectedOccurrenceAt, admittedOccurrence, authorizedSelectionAt,
      selectionReceiptAt, selectorInvocation, Space.occurrenceAt] at equalIds

def seedOccurrence : ClauseOccurrence := ⟨0, .seed⟩

def hasSeed (processed : List ClauseOccurrence) : Bool :=
  processed.any (fun occurrence => occurrence.clause == .seed)

def goalFrom (bridge : ClauseOccurrence) : ClauseOccurrence :=
  ⟨bridge.occurrenceId + 1, .goal⟩

/-- The bridge premise derives a goal only in a context where the seed has
already been activated. -/
def chainingSystem : System ClauseOccurrence ProofResult where
  observe occurrence _processed :=
    if occurrence.clause = .goal then some .proved else none
  generate occurrence processed :=
    if occurrence.clause = .bridge ∧ hasSeed processed then
      [goalFrom occurrence]
    else
      []

def initialSnapshot : Snapshot ClauseOccurrence ProofResult 1 :=
  Snapshot.initial Snapshot.breadthOnly [seedOccurrence] 0

/-- The foreground consumes its seed and then has no remaining work. -/
def stalledSnapshot : Snapshot ClauseOccurrence ProofResult 1 :=
  Snapshot.run chainingSystem Snapshot.breadthOnly 1 initialSnapshot

theorem foreground_really_stalls :
    stalledSnapshot.processed = [seedOccurrence] ∧
      stalledSnapshot.events = [] ∧
      stalledSnapshot.Saturated := by
  exact ⟨rfl, rfl, rfl⟩

/-- The domain authorization fixes the exact occurrence which the runtime may
append for this selected premise. -/
def StoreAllows (selection : AuthorizedSelection)
    (occurrence : ClauseOccurrence) : Prop :=
  occurrence = admittedOccurrence selection.receipt selection.authorization

def storeAdmission (selection : AuthorizedSelection) :
    AdmissionWitness StoreAllows selection
      (admittedOccurrence selection.receipt selection.authorization) where
  authorized := rfl

/-- Only an authorized selection crosses the recommendation/store boundary. -/
def admitAuthorized
    (snapshot : Snapshot ClauseOccurrence ProofResult 1)
    (selection : AuthorizedSelection) :
    Snapshot ClauseOccurrence ProofResult 1 :=
  applyAdmission Snapshot.breadthOnly snapshot (storeAdmission selection)

def admittedSnapshot : Snapshot ClauseOccurrence ProofResult 1 :=
  admitAuthorized stalledSnapshot (authorizedSelectionAt 0)

def solvedSnapshot : Snapshot ClauseOccurrence ProofResult 1 :=
  Snapshot.run chainingSystem Snapshot.breadthOnly 2 admittedSnapshot

/-- Positive control: the exact triggered, algorithmically selected, separately
authorized premise unblocks the foreground loop and yields its goal receipt. -/
theorem background_premise_service_unblocks_foreground :
    admittedSnapshot.processed = [seedOccurrence] ∧
      admittedSnapshot.passive.live = [selectedOccurrenceAt 0] ∧
      solvedSnapshot.processed =
        [seedOccurrence, selectedOccurrenceAt 0,
          goalFrom (selectedOccurrenceAt 0)] ∧
      solvedSnapshot.events =
        [⟨goalFrom (selectedOccurrenceAt 0), .proved⟩] ∧
      solvedSnapshot.Saturated := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Negative control: without an admitted service result, extra foreground
fuel cannot manufacture the missing premise or the goal. -/
theorem foreground_fuel_cannot_replace_service :
    Snapshot.run chainingSystem Snapshot.breadthOnly 2 stalledSnapshot =
        stalledSnapshot ∧
      (Snapshot.run chainingSystem Snapshot.breadthOnly 2 stalledSnapshot).events = [] := by
  exact ⟨rfl, rfl⟩

/-! ## The worked run inhabits the generic cognitive-synergy interface -/

inductive MindAgent where
  | premiseSelector
  | foregroundChainer
deriving DecidableEq, Repr

abbrev ForegroundState := Snapshot ClauseOccurrence ProofResult 1

def providerProcess : Process MindAgent ForegroundState AuthorizedSelection where
  id := .premiseSelector
  Autonomous := fun _source _target => Empty
  Produces := fun _source selection =>
    PLift (selection = authorizedSelectionAt 0)
  Consumes := fun _source _selection _target => Empty

/-- Autonomous foreground transitions require live work.  This makes
saturation genuine stuckness rather than an unproductive self-loop. -/
def foregroundProcess : Process MindAgent ForegroundState AuthorizedSelection where
  id := .foregroundChainer
  Autonomous := fun source target =>
    PLift (¬ source.Saturated ∧
      target = Snapshot.tick chainingSystem Snapshot.breadthOnly source)
  Produces := fun _source _selection => Empty
  Consumes := fun source selection target =>
    PLift (target = Snapshot.run chainingSystem Snapshot.breadthOnly 2
      (admitAuthorized source selection))

def workedSynergy : Witness providerProcess foregroundProcess
    stalledSnapshot stalledSnapshot where
  distinctProcesses := by decide
  occurrence := authorizedSelectionAt 0
  produced := ⟨rfl⟩
  target := solvedSnapshot
  consumerStuck := by
    constructor
    rintro ⟨target, autonomous⟩
    exact autonomous.down.1 foreground_really_stalls.2.2
  assisted := ⟨rfl⟩

/-- The concrete chaining example therefore supplies the generic theorem's
proof-relevant assisted successor, not merely a performance claim. -/
theorem worked_service_is_cognitive_synergy :
    Nonempty (Sigma fun selection : AuthorizedSelection =>
      Sigma fun target : ForegroundState =>
        foregroundProcess.Consumes stalledSnapshot selection target) :=
  workedSynergy.escapes_stuck_state

#print axioms requiredPremise_selected
#print axioms distractorAdvice_not_authorized
#print axioms repeated_selection_keeps_occurrence_identity
#print axioms foreground_really_stalls
#print axioms background_premise_service_unblocks_foreground
#print axioms foreground_fuel_cannot_replace_service
#print axioms worked_service_is_cognitive_synergy

end
end Mettapedia.CognitiveArchitecture.ForegroundChainingPremiseService
