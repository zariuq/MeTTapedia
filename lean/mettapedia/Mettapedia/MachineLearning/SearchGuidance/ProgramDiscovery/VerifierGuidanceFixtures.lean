import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.VerifierGuidance

/-!
# Exact six-program verifier-guidance fixture

This fixture mirrors the frozen rational conformance oracle.  Two of six
programs pass the checker.  The other channels alter priorities, proposal
mass, or submission order without receiving authority over the accepted
ledger.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.VerifierGuidance
namespace OracleFixture

inductive Program where
  | p0 | p1 | p2 | p3 | p4 | p5
  deriving DecidableEq, Fintype, Repr

inductive Action where
  | a0 | a1
  deriving DecidableEq, Fintype, Repr

inductive Lineage where
  | source0 | source1 | shared2 | independent4a | independent4b
  deriving DecidableEq, Fintype, Repr

open Program Action Lineage
open SemanticShaping

def allPrograms : Finset Program := {.p0, .p1, .p2, .p3, .p4, .p5}

theorem allPrograms_eq_univ : allPrograms = Finset.univ := by
  ext program
  fin_cases program <;> simp [allPrograms]

@[simp] theorem sum_programs (function : Program → ℚ) :
    (∑ program : Program, function program) =
      function .p0 + function .p1 + function .p2 +
        function .p3 + function .p4 + function .p5 := by
  rw [← allPrograms_eq_univ]
  simp [allPrograms]
  ring

def allLineages : Finset Lineage :=
  {.source0, .source1, .shared2, .independent4a, .independent4b}

theorem allLineages_eq_univ : allLineages = Finset.univ := by
  ext lineage
  fin_cases lineage <;> simp [allLineages]

@[simp] theorem sum_lineages (function : Lineage → ℚ) :
    (∑ lineage : Lineage, function lineage) =
      function .source0 + function .source1 + function .shared2 +
        function .independent4a + function .independent4b := by
  rw [← allLineages_eq_univ]
  simp [allLineages]
  ring

def checker : Program → Bool
  | .p1 | .p4 => true
  | _ => false

def partialPriority : Program → ℚ
  | .p0 => 1 / 5
  | .p1 => 1
  | .p2 => 3 / 5
  | .p3 => 2 / 5
  | .p4 => 1
  | .p5 => 0

def actionTrace : Program → List Action
  | .p0 => [.a0, .a0]
  | .p1 => [.a0, .a1]
  | .p2 => [.a0, .a1]
  | .p3 => [.a1, .a0]
  | .p4 => [.a1, .a1]
  | .p5 => [.a0, .a0]

def sourcePacket (program : Program) (source : Lineage) :
    SourcePacket Program Unit Lineage where
  program := program
  target := ()
  source := source
  ancestors := ∅

def reliabilityPacket
    (program : Program) (source : Lineage) (reliability : ℚ) (positive : Bool) :
    ReliabilityPacket Program Unit Lineage where
  provenance := sourcePacket program source
  reliability := reliability
  positive := positive

def evidencePackets : List (ReliabilityPacket Program Unit Lineage) :=
  [ reliabilityPacket .p0 .source0 1 false,
    reliabilityPacket .p1 .source1 (1 / 2) true,
    reliabilityPacket .p2 .shared2 (9 / 10) true,
    reliabilityPacket .p2 .shared2 (9 / 10) true,
    reliabilityPacket .p2 .shared2 (9 / 10) true,
    reliabilityPacket .p4 .independent4a (3 / 5) true,
    reliabilityPacket .p4 .independent4b (3 / 5) true ]

def naivePriority (program : Program) : ℚ :=
  evidencePriority (ReliabilityPacket.naiveEvidence evidencePackets program)

def correctedPriority (program : Program) : ℚ :=
  evidencePriority (ReliabilityPacket.correctedEvidence evidencePackets program)

def gflowReward : Program → ℚ
  | .p1 => 1
  | .p4 => 2
  | _ => 0

def gflowMass (program : Program) : ℚ :=
  proportionalTerminalMass gflowReward 3 program

def baselineQueue : List Program := [.p0, .p1, .p2, .p3, .p4, .p5]
def guidedQueue : List Program := [.p4, .p1, .p2, .p3, .p0, .p5]

def model : SearchModel Program Action where
  checker := checker
  partialPriority := partialPriority
  actionTrace := actionTrace
  evidencePriority := correctedPriority
  terminalReward := gflowReward
  baselineQueue := baselineQueue
  guidedQueue := guidedQueue
  semanticSlots := 2

theorem checker_boundary_nontrivial : HasAcceptanceBoundary model := by
  exact ⟨⟨.p1, rfl⟩, ⟨.p0, rfl⟩⟩

theorem checker_set_exact : checkerSet model = {.p1, .p4} := by
  ext program
  fin_cases program <;> simp [checkerSet, model, checker]

theorem exact_reward_support :
    positiveSupport (exactReward model) = {.p1, .p4} := by
  rw [positiveSupport_exactReward]
  exact checker_set_exact

theorem squared_reward_support :
    positiveSupport (fun program ↦ (exactReward model program) ^ 2) =
      {.p1, .p4} := by
  have hsupport := (transformedExactSupport_eq_iff model
    (fun reward : ℚ ↦ reward ^ 2) checker_boundary_nontrivial).2
      square_preservesBooleanPositiveSupport
  rw [hsupport]
  ext program
  fin_cases program <;> simp [checkerSet, model, checker]

noncomputable def additivePartialReward (program : Program) : ℚ :=
  exactReward model program + partialPriority program

theorem additive_partial_support :
    positiveSupport additivePartialReward = {.p0, .p1, .p2, .p3, .p4} := by
  ext program
  fin_cases program
  <;> norm_num [positiveSupport, additivePartialReward, exactReward, model,
      checker, partialPriority]
  all_goals decide

theorem additive_partial_creates_rejected_support :
    ({.p0, .p2, .p3} : Finset Program) ⊆
        positiveSupport additivePartialReward ∧
      ({.p0, .p2, .p3} : Finset Program) ∩ checkerSet model = ∅ := by
  constructor
  · rw [additive_partial_support]
    decide
  · ext program
    fin_cases program <;> simp [checkerSet, model, checker]

theorem checker_filter_after_partial_is_exact :
    checkerFilteredSupport model additivePartialReward = {.p1, .p4} := by
  ext program
  fin_cases program <;>
    norm_num [checkerFilteredSupport, positiveSupport, checkerSet,
      additivePartialReward, exactReward, model, checker, partialPriority] <;>
    decide

theorem accepted_root_action_counts :
    acceptedFirstActionCount model .a0 = 1 ∧
      acceptedFirstActionCount model .a1 = 1 := by
  rw [acceptedFirstActionCount, acceptedFirstActionCount, checker_set_exact]
  decide

theorem accepted_root_action_distribution :
    acceptedFirstActionProbability model .a0 = 1 / 2 ∧
      acceptedFirstActionProbability model .a1 = 1 / 2 := by
  have hcard : ({.p1, .p4} : Finset Program).card = 2 := by decide
  rw [acceptedFirstActionProbability, acceptedFirstActionProbability,
    accepted_root_action_counts.1, accepted_root_action_counts.2,
    checker_set_exact, hcard]
  norm_num

theorem rejected_program_shares_supervised_prefix :
    ¬ PrefixCertifiesAcceptance model := by
  apply sharedPrefix_rejected_counterexample model .p1 .p2
  · rfl
  · trivial
  · rfl

theorem repair_depth_improves_but_is_not_acceptance :
    RepairImproves model .p0 .p2 ∧ model.checker .p2 = false ∧
      ¬ RepairProgressCertifiesAcceptance model := by
  have himproves : RepairImproves model .p0 .p2 := by
    norm_num [RepairImproves, model, partialPriority]
  have hrejected : model.checker .p2 = false := rfl
  exact ⟨himproves, hrejected,
    improving_rejected_counterexample model .p0 .p2 himproves hrejected⟩

theorem naive_evidence_positive_values :
    (ReliabilityPacket.naiveEvidence evidencePackets .p0).1 = 0 ∧
      (ReliabilityPacket.naiveEvidence evidencePackets .p1).1 = 1 / 2 ∧
      (ReliabilityPacket.naiveEvidence evidencePackets .p2).1 = 27 / 10 ∧
      (ReliabilityPacket.naiveEvidence evidencePackets .p4).1 = 6 / 5 := by
  simp [ReliabilityPacket.naiveEvidence, ReliabilityPacket.naiveWeight,
    evidencePackets, reliabilityPacket, sourcePacket]
  norm_num

theorem corrected_evidence_positive_values :
    (ReliabilityPacket.correctedEvidence evidencePackets .p0).1 = 0 ∧
      (ReliabilityPacket.correctedEvidence evidencePackets .p1).1 = 1 / 2 ∧
      (ReliabilityPacket.correctedEvidence evidencePackets .p2).1 = 9 / 10 ∧
      (ReliabilityPacket.correctedEvidence evidencePackets .p4).1 = 6 / 5 := by
  simp [ReliabilityPacket.correctedEvidence,
    ReliabilityPacket.correctedWeight, ReliabilityPacket.sourceWeight,
    evidencePackets, reliabilityPacket, sourcePacket, max_def]
  norm_num

theorem dependence_correction_reverses_priority :
    naivePriority .p4 < naivePriority .p2 ∧
      correctedPriority .p2 < correctedPriority .p4 := by
  simp [naivePriority, correctedPriority, evidencePriority,
    ReliabilityPacket.naiveEvidence, ReliabilityPacket.correctedEvidence,
    ReliabilityPacket.naiveWeight, ReliabilityPacket.correctedWeight,
    ReliabilityPacket.sourceWeight, evidencePackets, reliabilityPacket,
    sourcePacket, max_def]
  norm_num

theorem repeated_p2_packets_are_not_sourceDisjoint :
    let repeated := reliabilityPacket .p2 .shared2 (9 / 10) true
    ¬ repeated.provenance.SourceDisjoint repeated.provenance := by
  dsimp
  exact ReliabilityPacket.sameSource_not_sourceDisjoint _ _ rfl

/-! ## Exact zeroth-order checker reward -/

def proposal (parameter : ℚ) (program : Program) : ℚ :=
  if checker program then (1 + parameter) / 6 else (1 - parameter / 2) / 6

theorem proposal_mass_one (parameter : ℚ) :
    (∑ program : Program, proposal parameter program) = 1 := by
  rw [sum_programs]
  simp [proposal, checker]
  ring

theorem expected_checker_reward_affine (parameter : ℚ) :
    expectedCheckerReward checker proposal parameter =
      1 / 3 + (1 / 3) * parameter := by
  rw [expectedCheckerReward, sum_programs]
  simp [proposal, checker]
  ring

theorem zeroth_order_expected_and_estimator :
    expectedCheckerReward checker proposal 0 = 1 / 3 ∧
      symmetricTwoPoint checker proposal (1 / 2) = 1 / 3 := by
  constructor
  · rw [expected_checker_reward_affine]
    norm_num
  · exact symmetricTwoPoint_of_affine checker proposal (1 / 3) (1 / 3)
      (1 / 2) (by norm_num) expected_checker_reward_affine

/-! ## Reward-proportional terminal mass -/

theorem gflow_reward_support_safe : RewardSupportSafe checker gflowReward := by
  intro program hpositive
  fin_cases program <;> simp_all [gflowReward, checker]

theorem gflow_terminal_distribution :
    gflowMass .p1 = 1 / 3 ∧ gflowMass .p4 = 2 / 3 ∧
      gflowMass .p0 = 0 ∧ gflowMass .p2 = 0 ∧
      gflowMass .p3 = 0 ∧ gflowMass .p5 = 0 := by
  norm_num [gflowMass, proportionalTerminalMass, gflowReward]

theorem gflow_positive_mass_is_checker_safe (program : Program)
    (hmass : 0 < gflowMass program) : checker program = true :=
  proportionalTerminalMass_checkerSafe checker gflowReward 3 (by norm_num)
    gflow_reward_support_safe program hmass

theorem additive_partial_is_not_terminal_support_safe :
    ¬ RewardSupportSafe checker additivePartialReward := by
  intro hsafe
  have hpositive : 0 < additivePartialReward .p0 := by
    norm_num [additivePartialReward, exactReward, model, checker, partialPriority]
  have hfalse := hsafe .p0 hpositive
  simp [checker] at hfalse

/-! ## Exact fair schedule and accepted ledger -/

def fairSchedule : List Program :=
  (List.range 16).filterMap fun time ↦
    twoQueueCandidate baselineQueue guidedQueue 2 time

theorem fair_schedule_exact :
    fairSchedule =
      [.p0, .p4, .p1, .p1, .p2, .p3, .p2, .p0,
        .p5, .p3, .p4, .p5] := by
  decide

def concreteAcceptedLedger : Finset Program :=
  (fairSchedule.filter checker).toFinset

theorem concrete_accepted_ledger_exact :
    concreteAcceptedLedger = {.p1, .p4} := by
  decide

theorem checker_complete_within_sixteen : CheckerCompleteWithin model 16 := by
  intro program hchecked
  fin_cases program <;> simp [model, checker, baselineQueue] at hchecked ⊢
  · exact ⟨1, by norm_num [queuePeriod]⟩
  · exact ⟨4, by norm_num [queuePeriod]⟩

theorem abstract_accepted_ledger_exact :
    acceptedLedger model 16 = checkerSet model :=
  acceptedLedger_eq_checkerSet_of_complete model 16 checker_complete_within_sixteen

theorem baseline_submission_times :
    (List.range 6).map (fun rank ↦ queuePeriod 2 * rank) =
      [0, 3, 6, 9, 12, 15] := by
  decide

theorem semantic_only_budget_one_omits_accepted :
    .p1 ∈ checkerSet model ∧ .p1 ∉ guidedQueue.take 1 := by
  constructor
  · simp [checkerSet, model, checker]
  · decide

#print axioms exact_reward_support
#print axioms squared_reward_support
#print axioms checker_filter_after_partial_is_exact
#print axioms accepted_root_action_distribution
#print axioms rejected_program_shares_supervised_prefix
#print axioms repair_depth_improves_but_is_not_acceptance
#print axioms dependence_correction_reverses_priority
#print axioms zeroth_order_expected_and_estimator
#print axioms gflow_positive_mass_is_checker_safe
#print axioms additive_partial_is_not_terminal_support_safe
#print axioms fair_schedule_exact
#print axioms concrete_accepted_ledger_exact
#print axioms abstract_accepted_ledger_exact
#print axioms semantic_only_budget_one_omits_accepted

end OracleFixture
end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.VerifierGuidance
