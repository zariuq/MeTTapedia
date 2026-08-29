import Mettapedia.CognitiveArchitecture.AttentionEconomyResourceControl
import Mettapedia.GSLT.Dynamics.ContextualControlSurface

/-!
# Attention-guided foreground/background mind-agent waves

A cognitive workspace may keep one foreground task in focus while background
agents maintain attention, indexes, learned links, compression proposals, or
reasoning advice.  This module states the smallest common license for such a
finite wave without turning any advisory value into execution authority.

The wave is occurrence-indexed.  Foreground/background roles and optional
value guidance live on positions, so repeated equal task values are not
identified.  Execution still requires the generic observation-relative
serializability certificate and two independently funded ECAN accounts.
Changing guidance preserves the certified batch and its activation plan;
failure of either attention account prevents construction of the wave.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.AttentionGuidedMindAgentWave

noncomputable section

open Mettapedia.CognitiveArchitecture.AttentionEconomy
open Mettapedia.CognitiveArchitecture.AttentionEconomyResourceControl
open Mettapedia.GSLT.Core.ObservationControlContract
open Mettapedia.GSLT.Core.ObservationDemandControl
open Mettapedia.GSLT.Core.ResourceAwareControl
open Mettapedia.GSLT.Dynamics.ContextualControlSurface
open Mettapedia.GSLT.Dynamics.TypedValueGeometry

universe uItem uGuard uCandidateView uState uStateView
universe uActor uCurrency uValue uPriority

/-- The operational role of one occurrence in a cognitive wave. -/
inductive WorkRole where
  | foreground
  | background
deriving DecidableEq, Repr

/-- A finite cognitive wave with one foreground occurrence and one background
occurrence, exact STI/LTI funding, and candidate-local guidance.

Roles and guidance are indexed by `Fin batch.length`, rather than by `Item`,
so duplicate equal items remain distinct occurrences.  This structure is an
admission certificate, not an execution receipt. -/
structure Wave
    {Item : Type uItem} {Guard : Type uGuard}
    {CandidateView : Type uCandidateView}
    {State : Type uState} {StateView : Type uStateView}
    {Actor : Type uActor} {Currency : Type uCurrency}
    [AddCommMonoid Currency]
    (contract : Contract Item Guard CandidateView)
    (semantics : ExecutionSemantics Item State StateView)
    (initial referenceTarget : State)
    (shortDemand : Item → Fund .shortTerm Actor Currency)
    (longDemand : Item → Fund .longTerm Actor Currency)
    (shortSource : Fund .shortTerm Actor Currency)
    (longSource : Fund .longTerm Actor Currency)
    (batch : List Item)
    (Value : Type uValue) (Priority : Type uPriority) where
  certified : CertifiedBatch contract semantics initial referenceTarget
    (ImportanceAccount Actor Currency)
    (fun item => (shortDemand item, longDemand item))
    (shortSource, longSource) batch
  role : Fin batch.length → WorkRole
  guidance : Guidance (Fin batch.length) Value Priority
  foregroundPresent : ∃ occurrence, role occurrence = .foreground
  backgroundPresent : ∃ occurrence, role occurrence = .background

namespace Wave

variable {Item : Type uItem} {Guard : Type uGuard}
variable {CandidateView : Type uCandidateView}
variable {State : Type uState} {StateView : Type uStateView}
variable {Actor : Type uActor} {Currency : Type uCurrency}
variable [AddCommMonoid Currency]
variable {Value : Type uValue} {Priority : Type uPriority}
variable {contract : Contract Item Guard CandidateView}
variable {semantics : ExecutionSemantics Item State StateView}
variable {initial referenceTarget : State}
variable {shortDemand : Item → Fund .shortTerm Actor Currency}
variable {longDemand : Item → Fund .longTerm Actor Currency}
variable {shortSource : Fund .shortTerm Actor Currency}
variable {longSource : Fund .longTerm Actor Currency}
variable {batch : List Item}

/-- Every positional occurrence, in source order. -/
def positions
    (_wave : Wave contract semantics initial referenceTarget shortDemand
      longDemand shortSource longSource batch Value Priority) :
    List (Fin batch.length) :=
  List.finRange batch.length

/-- Optional values decorate positions without changing their occurrence
sequence. -/
def guidedPositions
    (wave : Wave contract semantics initial referenceTarget shortDemand
      longDemand shortSource longSource batch Value Priority) :
    List (GuidedOccurrence (Fin batch.length) Priority) :=
  advise wave.guidance wave.positions

@[simp] theorem erase_guidedPositions
    (wave : Wave contract semantics initial referenceTarget shortDemand
      longDemand shortSource longSource batch Value Priority) :
    wave.guidedPositions.map GuidedOccurrence.occurrence = wave.positions :=
  erase_advise wave.guidance wave.positions

/-- Project exact short-term funding from the paired attention account. -/
def shortTermResources
    (wave : Wave contract semantics initial referenceTarget shortDemand
      longDemand shortSource longSource batch Value Priority) :
    BatchSeparation (Fund .shortTerm Actor Currency)
      shortDemand shortSource batch :=
  projectShortTerm wave.certified.resources

/-- Project exact long-term funding independently. -/
def longTermResources
    (wave : Wave contract semantics initial referenceTarget shortDemand
      longDemand shortSource longSource batch Value Priority) :
    BatchSeparation (Fund .longTerm Actor Currency)
      longDemand longSource batch :=
  projectLongTerm wave.certified.resources

/-- Replace every advisory value while retaining the exact execution and
resource certificate. -/
def withGuidance
    (wave : Wave contract semantics initial referenceTarget shortDemand
      longDemand shortSource longSource batch Value Priority)
    (replacement : Guidance (Fin batch.length) Value Priority) :
    Wave contract semantics initial referenceTarget shortDemand longDemand
      shortSource longSource batch Value Priority where
  certified := wave.certified
  role := wave.role
  guidance := replacement
  foregroundPresent := wave.foregroundPresent
  backgroundPresent := wave.backgroundPresent

/-- Guidance replacement cannot alter observation-derived activation. -/
theorem plan_withGuidance
    (wave : Wave contract semantics initial referenceTarget shortDemand
      longDemand shortSource longSource batch Value Priority)
    (replacement : Guidance (Fin batch.length) Value Priority)
    (branchAuthority : BranchAuthority) :
    (wave.withGuidance replacement).certified.plan branchAuthority =
      wave.certified.plan branchAuthority :=
  rfl

/-- Complete-bag observation plus the retained certificates earns bulk
activation.  Guidance is not an input to this theorem. -/
theorem completeBag_dispatches_bulk
    (wave : Wave contract semantics initial referenceTarget shortDemand
      longDemand shortSource longSource batch Value Priority)
    (complete : contract.demand.completion = .completeBag) :
    (wave.certified.plan .general).activation = .bulk :=
  wave.certified.completeBag_dispatches_bulk complete

/-- The foreground occurrence remains present after advice is attached. -/
theorem foreground_retained
    (wave : Wave contract semantics initial referenceTarget shortDemand
      longDemand shortSource longSource batch Value Priority) :
    ∃ guided ∈ wave.guidedPositions,
      wave.role guided.occurrence = .foreground := by
  rcases wave.foregroundPresent with ⟨occurrence, foreground⟩
  refine ⟨⟨occurrence, wave.guidance.priority occurrence⟩, ?_, foreground⟩
  simp [guidedPositions, positions, advise]

/-- The background occurrence is retained by the same positional ledger. -/
theorem background_retained
    (wave : Wave contract semantics initial referenceTarget shortDemand
      longDemand shortSource longSource batch Value Priority) :
    ∃ guided ∈ wave.guidedPositions,
      wave.role guided.occurrence = .background := by
  rcases wave.backgroundPresent with ⟨occurrence, background⟩
  refine ⟨⟨occurrence, wave.guidance.priority occurrence⟩, ?_, background⟩
  simp [guidedPositions, positions, advise]

/-- Failure of the independent LTI account prevents construction of the
jointly funded wave, regardless of the guidance values or STI balance. -/
theorem no_wave_of_longTerm_refusal
    (refuses : ¬ Nonempty
      (BatchSeparation (Fund .longTerm Actor Currency)
        longDemand longSource batch)) :
    ¬ Nonempty
      (Wave contract semantics initial referenceTarget shortDemand longDemand
        shortSource longSource batch Value Priority) := by
  rintro ⟨wave⟩
  exact refuses ⟨wave.longTermResources⟩

end Wave

/-! ## A two-agent executable canary -/

namespace Canary

inductive Agent where
  | reasoner
  | organizer
deriving DecidableEq, Repr

structure Task where
  occurrenceId : Nat
  actor : Agent
deriving DecidableEq, Repr

def foregroundTask : Task := ⟨0, .reasoner⟩
def backgroundTask : Task := ⟨1, .organizer⟩
def batch : List Task := [foregroundTask, backgroundTask]

def contract : Contract Task Unit (Multiset Task) where
  observer := { observe := fun tasks => (tasks : Multiset Task) }
  demand := { completion := .completeBag }

/-- A monotone receipt store: running a task batch appends its occurrence bag.
Every ordering therefore reaches the same observed state. -/
def run (source : Multiset Task) (tasks : List Task)
    (target : Multiset Task) : Prop :=
  target = source + (tasks : Multiset Task)

def semantics : ExecutionSemantics Task (Multiset Task) (Multiset Task) where
  run := run
  observe := id

def unitFund (horizon : ImportanceHorizon) (agent : Agent) :
    Fund horizon Agent Nat where
  balances := Finsupp.single agent 1

def shortDemand (task : Task) : Fund .shortTerm Agent Nat :=
  unitFund .shortTerm task.actor

def longDemand (task : Task) : Fund .longTerm Agent Nat :=
  match task.actor with
  | .reasoner => 0
  | .organizer => unitFund .longTerm .organizer

def shortSource : Fund .shortTerm Agent Nat :=
  batchDemand shortDemand batch

def longSource : Fund .longTerm Agent Nat :=
  batchDemand longDemand batch

def shortSeparation :
    BatchSeparation (Fund .shortTerm Agent Nat)
      shortDemand shortSource batch where
  frame := 0
  source_eq := by simp [shortSource]

def longSeparation :
    BatchSeparation (Fund .longTerm Agent Nat)
      longDemand longSource batch where
  frame := 0
  source_eq := by simp [longSource]

def certified : CertifiedBatch contract semantics 0 (batch : Multiset Task)
    (ImportanceAccount Agent Nat)
    (fun task => (shortDemand task, longDemand task))
    (shortSource, longSource) batch where
  nonempty := by decide
  candidateInvariant := by
    intro ordering permutation
    exact Quot.sound permutation
  executionSerializable := by
    constructor
    · rfl
    · intro ordering permutation
      refine ⟨(ordering : Multiset Task), ?_, ?_⟩
      · rfl
      · exact Quot.sound permutation
  resources := pairFunding shortSeparation longSeparation

def role (occurrence : Fin batch.length) : WorkRole :=
  if occurrence.val = 0 then .foreground else .background

def guidance : Guidance (Fin batch.length) Nat Nat where
  value occurrence :=
    if occurrence.val = 0 then some 5 else some 8
  priorityOf := id
  fallback _ := 0

def wave : Wave contract semantics 0 (batch : Multiset Task)
    shortDemand longDemand shortSource longSource batch Nat Nat where
  certified := certified
  role := role
  guidance := guidance
  foregroundPresent := ⟨⟨0, by decide⟩, rfl⟩
  backgroundPresent := ⟨⟨1, by decide⟩, rfl⟩

/-- Positive control: the same certified wave retains both cognitive roles,
both resource projections, and bulk eligibility. -/
theorem foreground_and_background_run_together :
    (wave.certified.plan .general).activation = .bulk ∧
      Nonempty (BatchSeparation (Fund .shortTerm Agent Nat)
        shortDemand shortSource batch) ∧
      Nonempty (BatchSeparation (Fund .longTerm Agent Nat)
        longDemand longSource batch) ∧
      (∃ guided ∈ wave.guidedPositions,
        wave.role guided.occurrence = .foreground) ∧
      (∃ guided ∈ wave.guidedPositions,
        wave.role guided.occurrence = .background) :=
  ⟨wave.completeBag_dispatches_bulk rfl,
    ⟨wave.shortTermResources⟩, ⟨wave.longTermResources⟩,
    wave.foreground_retained, wave.background_retained⟩

def reversedGuidance : Guidance (Fin batch.length) Nat Nat where
  value occurrence :=
    if occurrence.val = 0 then some 100 else none
  priorityOf := id
  fallback _ := 0

/-- Negative authority control: even a radical priority change leaves the
certified plan exactly unchanged. -/
theorem reprioritization_does_not_mint_activation :
    ((wave.withGuidance reversedGuidance).certified.plan .general) =
      wave.certified.plan .general :=
  wave.plan_withGuidance reversedGuidance .general

/-- Zero LTI cannot fund the organizer occurrence. -/
theorem zeroLongTerm_refuses_separation :
    ¬ Nonempty
      (BatchSeparation (Fund .longTerm Agent Nat)
        longDemand 0 batch) := by
  rintro ⟨separation⟩
  have totals := congrArg Fund.total separation.source_eq
  rw [Fund.total_zero, Fund.total_add] at totals
  have demandTotal : Fund.total (batchDemand longDemand batch) = 1 := by
    simp [batchDemand, batch, longDemand, backgroundTask, foregroundTask,
      unitFund, Fund.total]
  rw [demandTotal] at totals
  omega

/-- Negative resource control: abundant STI or attractive guidance cannot
replace the independently missing LTI certificate. -/
theorem no_wave_without_longTerm_funding :
    ¬ Nonempty
      (Wave contract semantics 0 (batch : Multiset Task)
        shortDemand longDemand shortSource 0 batch Nat Nat) :=
  Wave.no_wave_of_longTerm_refusal zeroLongTerm_refuses_separation

end Canary

#print axioms Wave.erase_guidedPositions
#print axioms Wave.plan_withGuidance
#print axioms Wave.completeBag_dispatches_bulk
#print axioms Wave.foreground_retained
#print axioms Wave.background_retained
#print axioms Wave.no_wave_of_longTerm_refusal
#print axioms Canary.foreground_and_background_run_together
#print axioms Canary.reprioritization_does_not_mint_activation
#print axioms Canary.zeroLongTerm_refuses_separation
#print axioms Canary.no_wave_without_longTerm_funding

end
end Mettapedia.CognitiveArchitecture.AttentionGuidedMindAgentWave
