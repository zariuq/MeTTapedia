import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SemanticShaping.FairSafety
import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SemanticShaping.RepairEvidence
import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.VerifierFlow
import Mathlib.Tactic

/-!
# A common waist for verifier-guided learning and search

Supervised prefixes, partial-match repair, provenance-aware evidence,
zeroth-order optimization, and terminal-flow learning all alter proposal
priority or mass.  They do not own acceptance.  This module places those
signals in one finite search model whose accepted ledger is filtered by an
external checker.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.VerifierGuidance

open SemanticShaping

universe uP uA uT uL

/-- The shared finite interface.  Each learned channel is graded; `checker`
is the only factive field. -/
structure SearchModel (Program : Type uP) (Action : Type uA) where
  checker : Program → Bool
  partialPriority : Program → ℚ
  actionTrace : Program → List Action
  evidencePriority : Program → ℚ
  terminalReward : Program → ℚ
  baselineQueue : List Program
  guidedQueue : List Program
  semanticSlots : ℕ

section CheckerBoundary

variable {Program : Type uP} {Action : Type uA}
variable [Fintype Program] [DecidableEq Program]

/-- The finite set owned by the external checker. -/
def checkerSet (model : SearchModel Program Action) : Finset Program :=
  Finset.univ.filter fun program ↦ model.checker program = true

/-- Exact terminal reward is the checker indicator, not a learned score. -/
def exactReward (model : SearchModel Program Action) (program : Program) : ℚ :=
  if model.checker program then 1 else 0

/-- Positive support of any graded score. -/
def positiveSupport (score : Program → ℚ) : Finset Program :=
  Finset.univ.filter fun program ↦ 0 < score program

theorem mem_checkerSet_iff (model : SearchModel Program Action) (program : Program) :
    program ∈ checkerSet model ↔ model.checker program = true := by
  simp [checkerSet]

omit [Fintype Program] [DecidableEq Program] in
theorem exactReward_pos_iff (model : SearchModel Program Action) (program : Program) :
    0 < exactReward model program ↔ model.checker program = true := by
  cases hchecked : model.checker program <;>
    simp [exactReward, hchecked]

omit [DecidableEq Program] in
theorem positiveSupport_exactReward (model : SearchModel Program Action) :
    positiveSupport (exactReward model) = checkerSet model := by
  classical
  ext program
  simp [positiveSupport, checkerSet, exactReward_pos_iff]

/-- The transform has positive output at the factive Boolean reward exactly
at input one. -/
def PreservesBooleanPositiveSupport (transform : ℚ → ℚ) : Prop :=
  ¬ 0 < transform 0 ∧ 0 < transform 1

/-- Both sides of the acceptance boundary are present, so support
preservation is observable rather than vacuous. -/
def HasAcceptanceBoundary (model : SearchModel Program Action) : Prop :=
  (∃ accepted, model.checker accepted = true) ∧
    (∃ rejected, model.checker rejected = false)

/-- On a nontrivial checker, preserving the positive support of exact reward
is equivalent to the two Boolean endpoint conditions. -/
theorem transformedExactSupport_eq_iff
    (model : SearchModel Program Action) (transform : ℚ → ℚ)
    (hboundary : HasAcceptanceBoundary model) :
    positiveSupport (fun program ↦ transform (exactReward model program)) =
        checkerSet model ↔
      PreservesBooleanPositiveSupport transform := by
  classical
  constructor
  · intro hequality
    rcases hboundary with ⟨⟨accepted, haccepted⟩, ⟨rejected, hrejected⟩⟩
    constructor
    · intro hpositive
      have hmember : rejected ∈
          positiveSupport (fun program ↦ transform (exactReward model program)) := by
        simp [positiveSupport, exactReward, hrejected, hpositive]
      rw [hequality] at hmember
      have htrue := (mem_checkerSet_iff model rejected).1 hmember
      rw [hrejected] at htrue
      contradiction
    · have hmember : accepted ∈ checkerSet model :=
        (mem_checkerSet_iff model accepted).2 haccepted
      rw [← hequality] at hmember
      simpa [positiveSupport, exactReward, haccepted] using hmember
  · intro hpreserves
    ext program
    cases hchecked : model.checker program
    · simp [positiveSupport, checkerSet, exactReward, hchecked, hpreserves.1]
    · simp [positiveSupport, checkerSet, exactReward, hchecked, hpreserves.2]

theorem square_preservesBooleanPositiveSupport :
    PreservesBooleanPositiveSupport fun reward : ℚ ↦ reward ^ 2 := by
  norm_num [PreservesBooleanPositiveSupport]

/-- Priority-only shaping may have wider support, but checker filtration does
not. -/
def checkerFilteredSupport
    (model : SearchModel Program Action) (priority : Program → ℚ) : Finset Program :=
  positiveSupport priority ∩ checkerSet model

theorem checkerFilteredSupport_subset_checker
    (model : SearchModel Program Action) (priority : Program → ℚ) :
    checkerFilteredSupport model priority ⊆ checkerSet model := by
  intro program hmember
  exact (Finset.mem_inter.1 hmember).2

/-! ## Fair finite scheduling -/

def SubmittedWithin
    (model : SearchModel Program Action) (horizon : ℕ) (program : Program) : Prop :=
  ∃ time, time < horizon ∧
    twoQueueCandidate model.baselineQueue model.guidedQueue
      model.semanticSlots time = some program

/-- Only submitted and checker-accepted programs enter the ledger. -/
noncomputable def acceptedLedger
    (model : SearchModel Program Action) (horizon : ℕ) : Finset Program := by
  classical
  exact Finset.univ.filter fun program ↦
    model.checker program = true ∧ SubmittedWithin model horizon program

theorem mem_acceptedLedger_iff
    (model : SearchModel Program Action) (horizon : ℕ) (program : Program) :
    program ∈ acceptedLedger model horizon ↔
      model.checker program = true ∧ SubmittedWithin model horizon program := by
  classical
  simp [acceptedLedger]

theorem acceptedLedger_subset_checkerSet
    (model : SearchModel Program Action) (horizon : ℕ) :
    acceptedLedger model horizon ⊆ checkerSet model := by
  intro program hmember
  exact (mem_checkerSet_iff model program).2
    ((mem_acceptedLedger_iff model horizon program).1 hmember).1

/-- Every accepted program occurs at a baseline rank whose reserved slot lies
inside the horizon. -/
def CheckerCompleteWithin
    (model : SearchModel Program Action) (horizon : ℕ) : Prop :=
  ∀ program, model.checker program = true →
    ∃ rank,
      model.baselineQueue[rank]? = some program ∧
        queuePeriod model.semanticSlots * rank < horizon

omit [Fintype Program] [DecidableEq Program] in
theorem baselineRank_submittedWithin
    (model : SearchModel Program Action) (horizon rank : ℕ) (program : Program)
    (hlookup : model.baselineQueue[rank]? = some program)
    (htime : queuePeriod model.semanticSlots * rank < horizon) :
    SubmittedWithin model horizon program := by
  refine ⟨queuePeriod model.semanticSlots * rank, htime, ?_⟩
  rw [twoQueueCandidate_mul_queuePeriod]
  exact hlookup

-- Reserving `semanticSlots` guided positions stretches each baseline rank by
-- the explicit period and never removes its next reserved slot.
omit [Fintype Program] [DecidableEq Program] in
theorem modelBaselineRank_slowdownBound
    (model : SearchModel Program Action) (rank : ℕ) :
    queuePeriod model.semanticSlots * rank <
      queuePeriod model.semanticSlots * (rank + 1) :=
  baseline_rank_time_slowdown_bound model.semanticSlots rank

/-- Fair baseline reachability makes the finite accepted ledger exactly the
checker set. -/
theorem acceptedLedger_eq_checkerSet_of_complete
    (model : SearchModel Program Action) (horizon : ℕ)
    (hcomplete : CheckerCompleteWithin model horizon) :
    acceptedLedger model horizon = checkerSet model := by
  apply Finset.Subset.antisymm (acceptedLedger_subset_checkerSet model horizon)
  intro program hchecked
  have hchecker := (mem_checkerSet_iff model program).1 hchecked
  rcases hcomplete program hchecker with ⟨rank, hlookup, htime⟩
  exact (mem_acceptedLedger_iff model horizon program).2
    ⟨hchecker, baselineRank_submittedWithin model horizon rank program hlookup htime⟩

end CheckerBoundary

/-! ## Prefix and repair signals are graded -/

section GradedSignals

variable {Program : Type uP} {Action : Type uA}

/-- Accepted traces induce supervised first-action counts, but these local
targets remain subordinate to complete-program checking. -/
def acceptedFirstActionCount
    [Fintype Program] [DecidableEq Program] [DecidableEq Action]
    (model : SearchModel Program Action) (action : Action) : ℕ :=
  (checkerSet model |>.filter fun program ↦
    (model.actionTrace program).head? = some action).card

def acceptedFirstActionProbability
    [Fintype Program] [DecidableEq Program] [DecidableEq Action]
    (model : SearchModel Program Action) (action : Action) : ℚ :=
  acceptedFirstActionCount model action / (checkerSet model).card

def PrefixCertifiesAcceptance (model : SearchModel Program Action) : Prop :=
  ∀ accepted rejected,
    (model.actionTrace accepted).head? = (model.actionTrace rejected).head? →
    model.checker accepted = true → model.checker rejected = true

theorem sharedPrefix_rejected_counterexample
    (model : SearchModel Program Action)
    (accepted rejected : Program)
    (hprefix : (model.actionTrace accepted).head? =
      (model.actionTrace rejected).head?)
    (haccepted : model.checker accepted = true)
    (hrejected : model.checker rejected = false) :
    ¬ PrefixCertifiesAcceptance model := by
  intro hcertifies
  have := hcertifies accepted rejected hprefix haccepted
  rw [hrejected] at this
  contradiction

def RepairImproves
    (model : SearchModel Program Action) (before after : Program) : Prop :=
  model.partialPriority before < model.partialPriority after

def RepairProgressCertifiesAcceptance (model : SearchModel Program Action) : Prop :=
  ∀ before after, RepairImproves model before after → model.checker after = true

theorem improving_rejected_counterexample
    (model : SearchModel Program Action)
    (before after : Program)
    (himproves : RepairImproves model before after)
    (hrejected : model.checker after = false) :
    ¬ RepairProgressCertifiesAcceptance model := by
  intro hcertifies
  have := hcertifies before after himproves
  rw [hrejected] at this
  contradiction

end GradedSignals

/-! ## Provenance-aware scheduling evidence -/

/-- A reliability weight annotates the existing source packet.  It is a
scheduling projection, not a second evidence carrier. -/
structure ReliabilityPacket
    (Program : Type uP) (Target : Type uT) (Lineage : Type uL) where
  provenance : SourcePacket Program Target Lineage
  reliability : ℚ
  positive : Bool

namespace ReliabilityPacket

variable {Program : Type uP} {Target : Type uT} {Lineage : Type uL}

def naiveWeight
    [DecidableEq Program]
    (packets : List (ReliabilityPacket Program Target Lineage))
    (program : Program) (positive : Bool) : ℚ :=
  ((packets.filter fun packet ↦
    packet.provenance.program = program ∧ packet.positive = positive).map
      (fun packet ↦ packet.reliability)).sum

/-- Repeated packets from one exact source contribute their maximum declared
reliability once.  Ancestor dependence remains governed by `SourceDisjoint`;
this operation does not certify distinct sources independent. -/
def sourceWeight
    [DecidableEq Program] [DecidableEq Lineage]
    (packets : List (ReliabilityPacket Program Target Lineage))
    (program : Program) (source : Lineage) (positive : Bool) : ℚ :=
  ((packets.filter fun packet ↦
    packet.provenance.program = program ∧
      packet.provenance.source = source ∧ packet.positive = positive).map
        (fun packet ↦ packet.reliability)).foldl max 0

def correctedWeight
    [Fintype Lineage] [DecidableEq Program] [DecidableEq Lineage]
    (packets : List (ReliabilityPacket Program Target Lineage))
    (program : Program) (positive : Bool) : ℚ :=
  ∑ source : Lineage, sourceWeight packets program source positive

def naiveEvidence
    [DecidableEq Program]
    (packets : List (ReliabilityPacket Program Target Lineage))
    (program : Program) : ℚ × ℚ :=
  (naiveWeight packets program true, naiveWeight packets program false)

def correctedEvidence
    [Fintype Lineage] [DecidableEq Program] [DecidableEq Lineage]
    (packets : List (ReliabilityPacket Program Target Lineage))
    (program : Program) : ℚ × ℚ :=
  (correctedWeight packets program true, correctedWeight packets program false)

theorem sameSource_not_sourceDisjoint
    [DecidableEq Lineage]
    (left right : ReliabilityPacket Program Target Lineage)
    (hsame : left.provenance.source = right.provenance.source) :
    ¬ left.provenance.SourceDisjoint right.provenance := by
  intro hdisjoint
  exact hdisjoint.1 hsame

end ReliabilityPacket

/-- Counts-primal evidence is mapped to a rational priority only after
provenance correction.  This is a scheduler statistic, not a factive truth
value. -/
def evidencePriority (evidence : ℚ × ℚ) : ℚ :=
  (evidence.1 + 1) / (evidence.1 + evidence.2 + 2)

/-- The existing repair layer collapses a duplicated completed outcome before
the graded priority layer sees it. -/
theorem duplicateRepair_uses_existingOverlapCorrection :
    overlapCorrectedRepairRevision ⟨0, 0⟩ ⟨1, 0⟩ ⟨1, 0⟩ ⟨1, 0⟩ =
      ⟨1, 0⟩ :=
  duplicatedRepairOutcome_contributes_once

/-! ## Whole-program zeroth-order reward -/

section ZerothOrder

variable {Program : Type uP} [Fintype Program]

def expectedCheckerReward
    (checker : Program → Bool) (proposal : ℚ → Program → ℚ) (parameter : ℚ) : ℚ :=
  ∑ program : Program,
    proposal parameter program * (if checker program then 1 else 0)

def symmetricTwoPoint
    (checker : Program → Bool) (proposal : ℚ → Program → ℚ) (step : ℚ) : ℚ :=
  (expectedCheckerReward checker proposal step -
    expectedCheckerReward checker proposal (-step)) / (2 * step)

/-- A symmetric two-point estimator is exact for an affine expected checker
reward. -/
theorem symmetricTwoPoint_of_affine
    (checker : Program → Bool) (proposal : ℚ → Program → ℚ)
    (intercept slope step : ℚ) (hstep : step ≠ 0)
    (haffine : ∀ parameter,
      expectedCheckerReward checker proposal parameter =
        intercept + slope * parameter) :
    symmetricTwoPoint checker proposal step = slope := by
  rw [symmetricTwoPoint, haffine step, haffine (-step)]
  field_simp
  ring

end ZerothOrder

/-! ## Terminal-flow reward remains checker subordinate -/

def RewardSupportSafe {Program : Type uP}
    (checker : Program → Bool) (reward : Program → ℚ) : Prop :=
  ∀ program, 0 < reward program → checker program = true

def proportionalTerminalMass {Program : Type uP}
    (reward : Program → ℚ) (totalReward : ℚ) (program : Program) : ℚ :=
  reward program / totalReward

theorem proportionalTerminalMass_checkerSafe
    {Program : Type uP} (checker : Program → Bool) (reward : Program → ℚ)
    (totalReward : ℚ) (htotal : 0 < totalReward)
    (hsafe : RewardSupportSafe checker reward) (program : Program)
    (hmass : 0 < proportionalTerminalMass reward totalReward program) :
    checker program = true := by
  apply hsafe program
  rw [proportionalTerminalMass] at hmass
  rcases (div_pos_iff.mp hmass) with ⟨hreward, _⟩ | ⟨_, htotalNegative⟩
  · exact hreward
  · exact False.elim ((not_lt_of_ge (le_of_lt htotal)) htotalNegative)

/-- The pre-existing finite-flow fixture is an instance of the same support
boundary. -/
theorem existingVerifierFlow_support_is_checkerSafe
    (node : Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.FlowNode)
    (hterminal : node = .x ∨ node = .y ∨ node = .rejected) :
    0 < Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.terminalReward node ↔
      Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.checkerAccepts node :=
  Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.verified_reward_support_matches_checker
    node hterminal

#print axioms transformedExactSupport_eq_iff
#print axioms checkerFilteredSupport_subset_checker
#print axioms acceptedLedger_subset_checkerSet
#print axioms acceptedLedger_eq_checkerSet_of_complete
#print axioms modelBaselineRank_slowdownBound
#print axioms sharedPrefix_rejected_counterexample
#print axioms improving_rejected_counterexample
#print axioms ReliabilityPacket.sameSource_not_sourceDisjoint
#print axioms duplicateRepair_uses_existingOverlapCorrection
#print axioms symmetricTwoPoint_of_affine
#print axioms proportionalTerminalMass_checkerSafe
#print axioms existingVerifierFlow_support_is_checkerSafe

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.VerifierGuidance
