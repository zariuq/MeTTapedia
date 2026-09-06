import Mettapedia.Algebra.ConcurrentCostValuation
import Mettapedia.Computability.DependentEvidenceComparison
import Mettapedia.GSLT.Dynamics.IndexedEvidenceNeedPullback
import Mettapedia.GSLT.Dynamics.ProofRelevantNeedOwnershipValuation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ProtocolModuloEquationsBridge
import Mettapedia.TypeTheory.DependentFamilyObserverFactorization
import Mettapedia.TypeTheory.GuardedTimeModeTheory
import Mettapedia.TypeTheory.ExactCodeFamilyRepresentation

/-!
# Revisioned demand for typed rho communication

This module realizes one established typed rho communication occurrence as
exact evidence cached by the joint indexed-evidence/evaluator-ownership Need
protocol.  The raw cache key retains the source, target, and semantic
revision.  Its exact fibre contains precisely a strict-core typed COMM
occurrence for those endpoints.

The resulting square separates four compatible readings of one event:

* native source and target typing carried by the COMM receipt;
* proof-relevant operational reduction after erasing the typed refinement;
* a split extensional readout retaining only the reduction endpoints; and
* an independent WorkSpan valuation of outcome-observation events.

Endpoint-indexed evidence factors through the extensional readout.  Revision
identity does not.  The cache protocol also rejects a commit by the wrong
evaluator and cannot retag a live cache across a guarded revision tick.  Two
traces with identical cache endpoints but different observation histories
receive different observation-work grades.

This is a semantic integration theorem for one proved fragment.  It does not
select a product calculus, force demand into conversion, or assign a runtime
cost to rho communication itself.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.RevisionedTypedCommunicationDemand

open Mettapedia.Algebra
open Mettapedia.Algebra.ConcurrentCostValuation
open Mettapedia.Computability
open Mettapedia.Computability.DependentEvidenceComparison
open Mettapedia.GSLT.Dynamics
open Mettapedia.GSLT.Dynamics.IndexedEventValuation
open Mettapedia.GSLT.Dynamics.IndexedEvidenceNeedPullback
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ProtocolModuloEquationsBridge
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Soundness
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.TypedCommunicationProtocol
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.DisplayedEvidence
open Mettapedia.TypeTheory.ExtensionalReadout
open Mettapedia.TypeTheory.ExactCodeFamilyRepresentation
open Mettapedia.TypeTheory.ExactCodeModalityModel
open Mettapedia.TypeTheory.GuardedTimeModeTheory

/-! ## Revision-indexed exact communication evidence -/

/-- The visible extensional content of a direct communication claim. -/
abbrev CommunicationEndpoints := RhoProcess × RhoProcess

/-- A communication claim retains a semantic revision independently of its
visible source and target. -/
abbrev CommunicationClaim :=
  RevisionOrigin Nat CommunicationEndpoints

/-- Exact evidence at a claim is a typed strict-core COMM occurrence at its
declared endpoints.  Revision is retained in the raw index rather than hidden
inside the receipt. -/
def communicationEvidence : Family where
  Raw := CommunicationClaim
  Exact := fun claim =>
    StrictCoreCommOccurrence claim.origin.1 claim.origin.2

/-- Forget the revision while retaining both operational endpoints. -/
def endpointReadout :
    SplitReadout communicationEvidence.Raw CommunicationEndpoints where
  observe := RevisionOrigin.origin
  representative := fun endpoints =>
    { revision := 0, origin := endpoints }
  observe_representative := fun _ => rfl

/-- The exact COMM family is already indexed by the visible endpoint pair, so
it factors through endpoint observation without changing its fibres. -/
def communicationEvidenceFactorsThroughEndpoints :
    FamilyFactorization endpointReadout.observe communicationEvidence.Exact :=
  FamilyFactorization.pullback endpointReadout.observe
    (fun endpoints => StrictCoreCommOccurrence endpoints.1 endpoints.2)

/-- Every strict direct COMM occurrence is a genuine reduction: its source
contains the input/output pair in addition to the residual processes, while
its target contains one substituted residual in their place. -/
theorem closedComm_source_ne_target (data : ClosedCommData) :
    data.source ≠ data.target := by
  intro equalProcesses
  have equalPatterns := congrArg (fun process : RhoProcess => process.1)
    equalProcesses
  change
    (Pattern.collection .hashBag
      ([Pattern.apply "PInput" [data.channel, Pattern.lambda none data.body],
        Pattern.apply "POutput" [data.channel, data.payload]] ++ data.rest) none) =
      (Pattern.collection .hashBag
        (semanticCommSubst data.body data.payload :: data.rest) none) at equalPatterns
  injection equalPatterns with _ equalElements _
  have equalLengths := congrArg List.length equalElements
  simp at equalLengths

/-- Every retained typed COMM receipt separates its source and target. -/
theorem typedCommOccurrence_source_ne_target
    {source target : RhoProcess}
    (occurrence : StrictCoreCommOccurrence source target) : source ≠ target := by
  cases occurrence with
  | intro data => exact closedComm_source_ne_target data

/-- Hence the endpoint-indexed exact family is genuinely varying: the live
COMM endpoint is inhabited, whereas every self-loop fibre is empty. -/
theorem no_typed_communication_self_loop (process : RhoProcess) :
    IsEmpty (StrictCoreCommOccurrence process process) :=
  ⟨fun occurrence => typedCommOccurrence_source_ne_target occurrence rfl⟩

/-- The live closed communication claim at a selected revision. -/
def closedClaim (revision : Nat) : communicationEvidence.Raw :=
  { revision := revision
    origin := (closedNilCommData.source, closedNilCommData.target) }

/-- A claim whose source and target are literally the same process. -/
def selfClaim (revision : Nat) (process : RhoProcess) :
    communicationEvidence.Raw :=
  { revision := revision, origin := (process, process) }

/-- The exact communication family is not a constant-family spelling: it has
an inhabited live COMM fibre and an empty self-loop fibre. -/
theorem communicationEvidence_not_constant :
    Not (Exists fun Uniform : Type =>
      forall claim : communicationEvidence.Raw,
        Nonempty (communicationEvidence.Exact claim ≃ Uniform)) := by
  rintro ⟨Uniform, uniform⟩
  obtain ⟨liveEquiv⟩ := uniform (closedClaim 0)
  obtain ⟨selfEquiv⟩ := uniform (selfClaim 0 closedNilCommData.source)
  have uniformValue : Uniform := liveEquiv closedNilCommOccurrence
  have impossible :
      StrictCoreCommOccurrence closedNilCommData.source
        closedNilCommData.source := selfEquiv.symm uniformValue
  exact typedCommOccurrence_source_ne_target impossible rfl

/-- The closed typed receipt packed together with its exact raw index. -/
noncomputable def packedClosedOccurrence (revision : Nat) :
    Indexed.PackedEvidence communicationEvidence :=
  Sigma.mk (closedClaim revision) closedNilCommOccurrence

@[simp] theorem endpointReadout_closedClaim (revision : Nat) :
    endpointReadout.observe (closedClaim revision) =
      (closedNilCommData.source, closedNilCommData.target) :=
  rfl

/-- Revision is a real coordinate even when the visible reduction endpoints
are unchanged. -/
theorem closedClaims_distinct {left right : Nat} (different : left ≠ right) :
    closedClaim left ≠ closedClaim right := by
  intro equalClaim
  apply different
  exact congrArg RevisionOrigin.revision equalClaim

/-! ## An authentic computational-trinity comparison -/

/-- Total exact evidence retains both the revision-indexed claim and its
typed COMM receipt. -/
abbrev TotalCommunicationEvidence :=
  TotalEvidence communicationEvidence.Exact

/-- Typed operational evidence, its raw claim, and the visible endpoint pair
form the canonical dependent-evidence comparison triangle. -/
def communicationComparison :=
  DependentEvidenceComparison.comparison communicationEvidence.Exact
    endpointReadout.observe

/-- The same typed receipt can be retained at distinct semantic revisions. -/
noncomputable def evidencedClosedClaim (revision : Nat) :
    TotalCommunicationEvidence :=
  ⟨closedClaim revision, closedNilCommOccurrence⟩

theorem evidencedClosedClaims_distinct {left right : Nat}
    (different : left ≠ right) :
    evidencedClosedClaim left ≠ evidencedClosedClaim right := by
  intro equalEvidence
  exact closedClaims_distinct different (congrArg Sigma.fst equalEvidence)

/-- The comparison commutes, but its extensional endpoint face necessarily
forgets the revision coordinate of authentic typed evidence. -/
theorem communicationComparison_loses_program_information :
    communicationComparison.LosesProgramInformation :=
  comparison_loses_of_witness communicationEvidence.Exact
    endpointReadout.observe
    (left := evidencedClosedClaim 0) (right := evidencedClosedClaim 1)
    (evidencedClosedClaims_distinct (by decide)) rfl

/-! ## Exact code does not collapse the comparison -/

/-- One material exact-code layer around every typed COMM receipt. -/
abbrev CodedCommunicationEvidence :=
  codeFamily 1 communicationEvidence.Exact

/-- Each exact evidence fibre and its coded fibre are equivalent. -/
def communicationEvidenceCodeEquiv
    (claim : communicationEvidence.Raw) :
    communicationEvidence.Exact claim ≃ CodedCommunicationEvidence claim :=
  (iterEquiv 1 (communicationEvidence.Exact claim)).symm

/-- The exact-code version of the same computational-trinity triangle. -/
def codedCommunicationComparison :=
  DependentEvidenceComparison.comparison CodedCommunicationEvidence
    endpointReadout.observe

/-- Reversible quotation and splicing preserve the evidence exactly, but do
not restore the semantic revision erased by endpoint observation. -/
theorem exact_code_preserves_comparison_loss :
    codedCommunicationComparison.LosesProgramInformation := by
  exact
    (comparison_loses_congr_fibreEquiv endpointReadout.observe
      communicationEvidenceCodeEquiv).mp
        communicationComparison_loses_program_information

/-- Endpoint observation is complete but not faithful to revision identity. -/
theorem endpointReadout_not_faithful : Not endpointReadout.Faithful := by
  intro faithful
  have equalClaims : closedClaim 0 = closedClaim 1 := faithful rfl
  exact closedClaims_distinct (by decide) equalClaims

/-- Consequently semantic revision cannot be reconstructed from the endpoint
pair alone. -/
theorem revision_does_not_descend :
    Not (endpointReadout.FactorsObserver RevisionOrigin.revision) := by
  rw [endpointReadout.factorsObserver_iff_fibreInvariant]
  intro invariant
  have equalRevisions := invariant
    (left := closedClaim 0) (right := closedClaim 1) rfl
  exact Nat.zero_ne_one equalRevisions

/-! ## One authentic owned lazy realization -/

abbrev JointState (Owner : Type) :=
  State communicationEvidence Empty Owner

abbrev JointEvent (Cell Owner RetryableFault : Type) :=
  Event communicationEvidence Empty Cell Owner RetryableFault

abbrev JointStep (Cell Owner RetryableFault : Type) (cell : Cell) :=
  Step communicationEvidence Empty Cell Owner RetryableFault cell

abbrev JointTrace (Cell Owner RetryableFault : Type) (cell : Cell) :=
  Trace communicationEvidence Empty Cell Owner RetryableFault cell

/-- A fresh suspension for the closed typed communication claim. -/
def suspended (revision : Nat) : JointState Bool :=
  State.mk communicationEvidence Empty Bool
    (.suspended (closedClaim revision))
    (.suspended (closedClaim revision)) rfl

/-- An evaluator has claimed the communication suspension. -/
def evaluating (revision : Nat) (owner : Bool) : JointState Bool :=
  State.mk communicationEvidence Empty Bool
    (.evaluating (closedClaim revision))
    (.evaluating (closedClaim revision) owner) rfl

/-- The cache contains the exact typed COMM receipt at its original revision. -/
noncomputable def cached (revision : Nat) : JointState Bool :=
  State.mk communicationEvidence Empty Bool
    (.cachedEvidence (closedClaim revision) closedNilCommOccurrence)
    (.cachedValue (closedClaim revision) (packedClosedOccurrence revision)) rfl

def beginEvent (revision : Nat) (owner : Bool) :
    JointEvent Unit Bool Empty :=
  Event.mk communicationEvidence Empty Unit Bool Empty
    (.beginEvaluation () (closedClaim revision))
    (.beginEvaluation () (closedClaim revision) owner) rfl

noncomputable def commitEvent (revision : Nat) (owner : Bool) :
    JointEvent Unit Bool Empty :=
  Event.mk communicationEvidence Empty Unit Bool Empty
    (.commitEvidence () (closedClaim revision) closedNilCommOccurrence)
    (.commitValue () (closedClaim revision) owner
      (packedClosedOccurrence revision)) rfl

noncomputable def observeEvent (revision : Nat) :
    JointEvent Unit Bool Empty :=
  Event.mk communicationEvidence Empty Unit Bool Empty
    (.observeEvidence () (closedClaim revision) closedNilCommOccurrence)
    (.observeValue () (closedClaim revision)
      (packedClosedOccurrence revision)) rfl

def beginStep (revision : Nat) (owner : Bool) :
    JointStep Unit Bool Empty ()
      (suspended revision) (beginEvent revision owner)
      (evaluating revision owner) where
  indexed := .beginEvaluation (closedClaim revision)
  owned := .beginEvaluation (closedClaim revision) owner

noncomputable def commitStep (revision : Nat) (owner : Bool) :
    JointStep Unit Bool Empty ()
      (evaluating revision owner) (commitEvent revision owner)
      (cached revision) where
  indexed := .commitEvidence (closedClaim revision) closedNilCommOccurrence
  owned := by
    change ProofRelevantNeed.Ownership.Step Empty ()
      (.evaluating (closedClaim revision) owner)
      (.commitValue () (closedClaim revision) owner
        (packedClosedOccurrence revision))
      (.cachedValue (closedClaim revision) (packedClosedOccurrence revision))
    exact .commitValue (closedClaim revision) owner
      (packedClosedOccurrence revision)

noncomputable def observeStep (revision : Nat) :
    JointStep Unit Bool Empty ()
      (cached revision) (observeEvent revision) (cached revision) where
  indexed := .observeEvidence (closedClaim revision) closedNilCommOccurrence
  owned := by
    change ProofRelevantNeed.Ownership.Step Empty ()
      (.cachedValue (closedClaim revision)
        (packedClosedOccurrence revision))
      (.observeValue () (closedClaim revision)
        (packedClosedOccurrence revision))
      (.cachedValue (closedClaim revision)
        (packedClosedOccurrence revision))
    exact .observeValue (closedClaim revision)
      (packedClosedOccurrence revision)

/-- Evaluation claims ownership and then commits independently established
typed evidence. -/
noncomputable def demandTrace (revision : Nat) (owner : Bool) :
    JointTrace Unit Bool Empty () (suspended revision) (cached revision) :=
  .tail (beginEvent revision owner) (beginStep revision owner)
    (.tail (commitEvent revision owner) (commitStep revision owner)
      (.refl (cached revision)))

/-- An otherwise identical trace additionally observes the cached result. -/
noncomputable def observedTrace (revision : Nat) (owner : Bool) :
    JointTrace Unit Bool Empty () (suspended revision) (cached revision) :=
  .tail (beginEvent revision owner) (beginStep revision owner)
    (.tail (commitEvent revision owner) (commitStep revision owner)
      (.tail (observeEvent revision) (observeStep revision)
        (.refl (cached revision))))

/-- The receipt committed by the lazy protocol is the established typed rho
transition; demand supplies no typing premise of its own. -/
theorem committedReceipt_is_typed_rho_communication :
    typedCommSystem.Step closedNilCommData.source closedNilCommData.target /\
      HasType TypingContext.empty closedNilCommData.source.1 processTruth /\
      HasTypeUpToSubjectEquiv TypingContext.empty
        closedNilCommData.target.1 processTruth :=
  closedNilComm_protocol_control

/-- The same committed receipt enters both the generic modulo-equations
protocol and the established rho GSLT.  Static equations, operational
occurrences, and typing remain separate coordinates of this theorem. -/
theorem committedReceipt_enters_equation_saturated_protocol :
    saturatedRhoProtocolSystem.Step
        closedNilCommData.source closedNilCommData.target /\
      rhoLanguageDefGSLT.Step
        closedNilCommData.source closedNilCommData.target /\
      HasType TypingContext.empty closedNilCommData.source.1 processTruth /\
      HasTypeUpToSubjectEquiv TypingContext.empty
        closedNilCommData.target.1 processTruth :=
  typed_step_enters_saturated_protocol
    closedNilComm_protocol_control.1

/-- An evaluator other than the one which claimed the cell cannot commit the
same otherwise valid typed receipt. -/
theorem wrong_owner_commit_empty (revision : Nat) :
    IsEmpty
      (JointStep Unit Bool Empty ()
        (evaluating revision true) (commitEvent revision false)
        (cached revision)) :=
  ⟨by
    intro impossible
    cases impossible.owned⟩

/-! ## Guarded revision and observer boundaries -/

/-- A live cache cannot be retagged in place to the next semantic revision. -/
theorem revision_change_requires_fresh_cell (revision : Nat) :
    IsEmpty
      (JointTrace Unit Bool Empty ()
        (cached revision) (cached (revision + 1))) := by
  constructor
  intro trace
  have sameRevision : revision = revision + 1 :=
    trace_preserves_origin_coordinate
      (family := communicationEvidence) (Reason := Empty)
      (Cell := Unit) (Owner := Bool) (RetryableFault := Empty)
      RevisionOrigin.revision trace
      (sourceRaw := closedClaim revision)
      (targetRaw := closedClaim (revision + 1)) rfl rfl
  omega

/-- A guarded time tick has its selected temporal grade, but it does not
silently become permission to mutate a cache's immutable revision origin. -/
theorem guarded_tick_does_not_retag_cache (revision : Nat) :
    distanceGrading.gradeOf (guard revision) = 1 /\
      IsEmpty
        (JointTrace Unit Bool Empty ()
          (cached revision) (cached (revision + 1))) :=
  ⟨distance_guard revision, revision_change_requires_fresh_cell revision⟩

/-! ## Independent observation-work valuation -/

abbrev PackedCommunicationEvidence :=
  Indexed.PackedEvidence communicationEvidence

abbrev PackedCommunicationRefutation :=
  Indexed.PackedRefutation communicationEvidence Empty

abbrev BaseEvent :=
  ProofRelevantNeed.Event Unit communicationEvidence.Raw
    PackedCommunicationEvidence PackedCommunicationRefutation Empty

/-- WorkSpan here measures only cached-outcome observations.  It deliberately
does not claim to be the execution cost of COMM. -/
def outcomeObservationWorkSpan : Valuation BaseEvent where
  Grade := WorkSpan
  algebra := workSpanSequential
  grade := fun event =>
    let count := event.outcomeObservationCount
    some { work := count, span := count }

noncomputable def erasedDemandTrace (revision : Nat) (owner : Bool) :=
  (demandTrace revision owner).forgetIndexing.erase

noncomputable def erasedObservedTrace (revision : Nat) (owner : Bool) :=
  (observedTrace revision owner).forgetIndexing.erase

/-- Equal cache endpoints do not determine observation work: reading the
cached evidence is an authentic extra event. -/
theorem equal_endpoints_distinct_observation_work
    (revision : Nat) (owner : Bool) :
    (erasedDemandTrace revision owner).grade outcomeObservationWorkSpan =
        some (0 : WorkSpan) /\
      (erasedObservedTrace revision owner).grade
        outcomeObservationWorkSpan = some { work := 1, span := 1 } := by
  constructor <;> rfl

/-- The whole live discriminator: endpoint-indexed exact evidence descends,
while revision, owner mismatch, in-place revision change, and event cost stay
outside that extensional quotient. -/
theorem typed_communication_demand_boundary :
    Nonempty
        (FamilyFactorization endpointReadout.observe
          communicationEvidence.Exact) /\
      Not (Exists fun Uniform : Type =>
        forall claim : communicationEvidence.Raw,
          Nonempty (communicationEvidence.Exact claim ≃ Uniform)) /\
      communicationComparison.LosesProgramInformation /\
      codedCommunicationComparison.LosesProgramInformation /\
      Not endpointReadout.Faithful /\
      Not (endpointReadout.FactorsObserver RevisionOrigin.revision) /\
      IsEmpty
        (JointStep Unit Bool Empty ()
          (evaluating 0 true) (commitEvent 0 false) (cached 0)) /\
      IsEmpty
        (JointTrace Unit Bool Empty () (cached 0) (cached 1)) /\
      (erasedDemandTrace 0 true).grade outcomeObservationWorkSpan =
        some (0 : WorkSpan) /\
      (erasedObservedTrace 0 true).grade outcomeObservationWorkSpan =
        some { work := 1, span := 1 } := by
  exact
    ⟨⟨communicationEvidenceFactorsThroughEndpoints⟩,
      communicationEvidence_not_constant,
      communicationComparison_loses_program_information,
      exact_code_preserves_comparison_loss,
      endpointReadout_not_faithful,
      revision_does_not_descend,
      wrong_owner_commit_empty 0,
      by simpa using revision_change_requires_fresh_cell 0,
      (equal_endpoints_distinct_observation_work 0 true).1,
      (equal_endpoints_distinct_observation_work 0 true).2⟩

/-! ## Axiom audit -/

#print axioms communicationEvidenceFactorsThroughEndpoints
#print axioms communicationEvidence_not_constant
#print axioms communicationComparison_loses_program_information
#print axioms exact_code_preserves_comparison_loss
#print axioms endpointReadout_not_faithful
#print axioms revision_does_not_descend
#print axioms committedReceipt_is_typed_rho_communication
#print axioms committedReceipt_enters_equation_saturated_protocol
#print axioms wrong_owner_commit_empty
#print axioms revision_change_requires_fresh_cell
#print axioms guarded_tick_does_not_retag_cache
#print axioms equal_endpoints_distinct_observation_work
#print axioms typed_communication_demand_boundary

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.RevisionedTypedCommunicationDemand
