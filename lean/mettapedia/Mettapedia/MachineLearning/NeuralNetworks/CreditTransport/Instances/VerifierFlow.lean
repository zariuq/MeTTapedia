import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances.SplittingOptimizer
import Mathlib.Tactic

/-!
# Verifier-facing flow and fair guided search

Search-level flow credit is not a neural reverse derivative.  It receives
terminal reward from an external verifier and allocates sampling mass over a
construction DAG.  This module proves a finite conserved-flow fixture, records
the exact boundary between reward support and checker acceptance, and gives a
general fair-mixture lower bound preserving every baseline-reachable terminal.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances

/-! ## General finite-flow accounting -/

namespace FiniteFlow

variable {Node : Type*} [Fintype Node]

noncomputable def incoming (flow : Node → Node → ℝ) (node : Node) : ℝ :=
  ∑ parent : Node, flow parent node

noncomputable def outgoing (flow : Node → Node → ℝ) (node : Node) : ℝ :=
  ∑ child : Node, flow node child

noncomputable def balance (flow : Node → Node → ℝ) (node : Node) : ℝ :=
  outgoing flow node - incoming flow node

/-- Every finite edge-flow table has zero total divergence.  This is the
telescoping identity used by the terminal-distribution theorem; it does not
assume acyclicity or nonnegativity. -/
theorem total_balance_zero (flow : Node → Node → ℝ) :
    ∑ node : Node, balance flow node = 0 := by
  classical
  simp only [balance, Finset.sum_sub_distrib, outgoing, incoming]
  rw [Finset.sum_comm]
  exact sub_self _

/-- Conservation at every non-source, nonterminal node transfers all source
outflow to terminal inflow. -/
theorem source_outflow_eq_terminal_inflow
    [DecidableEq Node]
    (flow : Node → Node → ℝ) (source : Node) (terminals : Finset Node)
    (sourceNotTerminal : source ∉ terminals)
    (noIncomingSource : incoming flow source = 0)
    (noOutgoingTerminal : ∀ terminal ∈ terminals, outgoing flow terminal = 0)
    (internalConservation : ∀ node, node ≠ source → node ∉ terminals →
      incoming flow node = outgoing flow node) :
    outgoing flow source = ∑ terminal ∈ terminals, incoming flow terminal := by
  classical
  have terminalSubset : terminals ⊆ Finset.univ.erase source := by
    intro terminal terminalMem
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact fun equality => sourceNotTerminal (equality ▸ terminalMem)
  have zeroOffTerminal :
      ∀ node ∈ Finset.univ.erase source, node ∉ terminals → balance flow node = 0 := by
    intro node nodeMem nodeNotTerminal
    have nodeNeSource : node ≠ source := by
      simpa only [Finset.mem_erase, Finset.mem_univ, and_true] using nodeMem
    simp [balance, internalConservation node nodeNeSource nodeNotTerminal]
  have terminalSumEqualsErase :
      (∑ terminal ∈ terminals, balance flow terminal) =
        ∑ node ∈ Finset.univ.erase source, balance flow node :=
    Finset.sum_subset terminalSubset zeroOffTerminal
  have splitAtSource :=
    Finset.sum_erase_add Finset.univ (balance flow) (Finset.mem_univ source)
  have totalZero := total_balance_zero flow
  have sourceBalance : balance flow source = outgoing flow source := by
    simp [balance, noIncomingSource]
  have terminalBalance :
      (∑ terminal ∈ terminals, balance flow terminal) =
        -(∑ terminal ∈ terminals, incoming flow terminal) := by
    calc
      (∑ terminal ∈ terminals, balance flow terminal) =
          ∑ terminal ∈ terminals, -incoming flow terminal := by
            apply Finset.sum_congr rfl
            intro terminal terminalMem
            simp [balance, noOutgoingTerminal terminal terminalMem]
      _ = -(∑ terminal ∈ terminals, incoming flow terminal) := by
            rw [Finset.sum_neg_distrib]
  rw [← terminalSumEqualsErase] at splitAtSource
  rw [totalZero, terminalBalance, sourceBalance] at splitAtSource
  linarith

end FiniteFlow

/-! ## A finite construction DAG with shared terminal -/

inductive FlowNode where
  | root | left | right | x | y | rejected
  deriving DecidableEq, Fintype, Repr

open FlowNode

def allFlowNodes : Finset FlowNode :=
  {.root, .left, .right, .x, .y, .rejected}

theorem allFlowNodes_eq_univ : allFlowNodes = Finset.univ := by
  ext node
  fin_cases node <;> simp [allFlowNodes]

@[simp] theorem sum_flow_nodes (function : FlowNode → ℝ) :
    (∑ node : FlowNode, function node) =
      function .root + function .left + function .right +
        function .x + function .y + function .rejected := by
  rw [← allFlowNodes_eq_univ]
  simp [allFlowNodes]
  ring

noncomputable def verifiedFlow : FlowNode → FlowNode → ℝ
  | .root, .left => 1 / 2
  | .root, .right => 7 / 2
  | .root, .rejected => 0
  | .left, .x => 1 / 2
  | .right, .x => 1 / 2
  | .right, .y => 3
  | .right, .rejected => 0
  | _, _ => 0

noncomputable def alteredFlow : FlowNode → FlowNode → ℝ
  | .root, .left => 1 / 2
  | .root, .right => 7 / 2
  | .root, .rejected => 0
  | .left, .x => 1 / 2
  | .right, .x => 1
  | .right, .y => 3
  | .right, .rejected => 0
  | _, _ => 0

noncomputable def incoming (flow : FlowNode → FlowNode → ℝ) (node : FlowNode) : ℝ :=
  ∑ parent : FlowNode, flow parent node

noncomputable def outgoing (flow : FlowNode → FlowNode → ℝ) (node : FlowNode) : ℝ :=
  ∑ child : FlowNode, flow node child

def terminalReward : FlowNode → ℝ
  | .x => 1
  | .y => 3
  | .rejected => 0
  | _ => 0

def checkerAccepts : FlowNode → Prop
  | .x | .y => True
  | _ => False

theorem verifiedFlow_nonnegative (parent child : FlowNode) :
    0 ≤ verifiedFlow parent child := by
  fin_cases parent <;> fin_cases child <;> norm_num [verifiedFlow]

theorem verifiedFlow_internal_conservation :
    incoming verifiedFlow .left = outgoing verifiedFlow .left ∧
      incoming verifiedFlow .right = outgoing verifiedFlow .right := by
  norm_num [incoming, outgoing, verifiedFlow]

theorem verifiedFlow_terminal_reward_match :
    incoming verifiedFlow .x = terminalReward .x ∧
      incoming verifiedFlow .y = terminalReward .y ∧
      incoming verifiedFlow .rejected = terminalReward .rejected := by
  norm_num [incoming, verifiedFlow, terminalReward]

theorem verifiedFlow_total : outgoing verifiedFlow .root = 4 := by
  norm_num [outgoing, verifiedFlow]

noncomputable def terminalProbability
    (flow : FlowNode → FlowNode → ℝ) (node : FlowNode) : ℝ :=
  incoming flow node / outgoing flow .root

/-- Terminal reward matching plus the total-flow identity gives the
reward-proportional terminal distribution. -/
theorem terminalProbability_eq_reward_ratio
    (flow : FlowNode → FlowNode → ℝ) (node : FlowNode) (totalReward : ℝ)
    (terminal_match : incoming flow node = terminalReward node)
    (source_total : outgoing flow .root = totalReward) :
    terminalProbability flow node = terminalReward node / totalReward := by
  simp [terminalProbability, terminal_match, source_total]

theorem verifiedFlow_reward_proportional :
    terminalProbability verifiedFlow .x = 1 / 4 ∧
      terminalProbability verifiedFlow .y = 3 / 4 ∧
      terminalProbability verifiedFlow .rejected = 0 := by
  norm_num [terminalProbability, incoming, outgoing, verifiedFlow,
    terminalReward]

/-- A single edge perturbation breaks both an internal conservation equation
and terminal reward matching. -/
theorem alteredFlow_breaks_conservation_and_reward :
    incoming alteredFlow .right ≠ outgoing alteredFlow .right ∧
      incoming alteredFlow .x ≠ terminalReward .x := by
  norm_num [incoming, outgoing, alteredFlow, terminalReward]

/-! ## Reward support and checker ownership -/

theorem squared_reward_preserves_support
    (reward : ℝ) (nonnegative : 0 ≤ reward) :
    0 < reward ^ 2 ↔ 0 < reward := by
  constructor
  · intro squarePositive
    by_contra notPositive
    have rewardZero : reward = 0 := le_antisymm (le_of_not_gt notPositive) nonnegative
    simp [rewardZero] at squarePositive
  · intro positive
    exact sq_pos_of_pos positive

theorem verified_reward_support_matches_checker (node : FlowNode)
    (terminal : node = .x ∨ node = .y ∨ node = .rejected) :
    0 < terminalReward node ↔ checkerAccepts node := by
  rcases terminal with rfl | rfl | rfl <;> simp [terminalReward, checkerAccepts]

/-- Positive additive shaping creates sampling support on a rejected terminal;
the external checker itself remains unchanged. -/
theorem additive_shaping_creates_rejected_support :
    ¬ checkerAccepts .rejected ∧
      terminalReward .rejected = 0 ∧
      0 < terminalReward .rejected + 1 := by
  norm_num [checkerAccepts, terminalReward]

/-! ## Fair mixture with a baseline policy -/

noncomputable def mixPolicy {Terminal : Type*}
    (epsilon : ℝ) (baseline shaped : Terminal → ℝ) (terminal : Terminal) : ℝ :=
  epsilon * baseline terminal + (1 - epsilon) * shaped terminal

/-- Every baseline-reachable terminal retains at least its epsilon-weighted
baseline probability. -/
theorem mixPolicy_baseline_lower_bound {Terminal : Type*}
    (epsilon : ℝ) (baseline shaped : Terminal → ℝ) (terminal : Terminal)
    (epsilon_at_most_one : epsilon ≤ 1)
    (shaped_nonnegative : 0 ≤ shaped terminal) :
    epsilon * baseline terminal ≤ mixPolicy epsilon baseline shaped terminal := by
  unfold mixPolicy
  have residual_nonnegative : 0 ≤ 1 - epsilon := by linarith
  nlinarith [mul_nonneg residual_nonnegative shaped_nonnegative]

theorem mixPolicy_strict_baseline_reachability {Terminal : Type*}
    (epsilon : ℝ) (baseline shaped : Terminal → ℝ) (terminal : Terminal)
    (epsilon_positive : 0 < epsilon) (epsilon_at_most_one : epsilon ≤ 1)
    (baseline_positive : 0 < baseline terminal)
    (shaped_nonnegative : 0 ≤ shaped terminal) :
    0 < mixPolicy epsilon baseline shaped terminal := by
  have lower := mixPolicy_baseline_lower_bound epsilon baseline shaped terminal
      epsilon_at_most_one shaped_nonnegative
  nlinarith [mul_pos epsilon_positive baseline_positive]

/-- Broader support alone does not dominate the probability of a particular
novel verified terminal under a finite budget. -/
theorem broader_support_does_not_dominate_target_probability :
    let broadX : ℝ := 1 / 2
    let broadY : ℝ := 1 / 2
    let narrowX : ℝ := 0
    let narrowY : ℝ := 1
    0 < broadX ∧ 0 < broadY ∧ narrowX = 0 ∧
      broadY < narrowY := by
  norm_num

def terminalVerifierOracle : OracleAudit where
  accesses := [.terminalVerifierReward]

def verifierGlobalLocality (Event : Type*) : LocalityAudit Event where
  scope := .checkerTerminalGlobal
  dependsOn := fun _ _ => True

#print axioms verifiedFlow_internal_conservation
#print axioms FiniteFlow.total_balance_zero
#print axioms FiniteFlow.source_outflow_eq_terminal_inflow
#print axioms verifiedFlow_terminal_reward_match
#print axioms terminalProbability_eq_reward_ratio
#print axioms verifiedFlow_reward_proportional
#print axioms alteredFlow_breaks_conservation_and_reward
#print axioms squared_reward_preserves_support
#print axioms additive_shaping_creates_rejected_support
#print axioms mixPolicy_baseline_lower_bound
#print axioms mixPolicy_strict_baseline_reachability
#print axioms broader_support_does_not_dominate_target_probability

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.Instances
