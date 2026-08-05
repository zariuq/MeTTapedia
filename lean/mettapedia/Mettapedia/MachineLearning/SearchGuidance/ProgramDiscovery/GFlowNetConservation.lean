import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.VerifierGuidance
import Mathlib.Tactic

/-!
# Finite flow matching and reward-proportional verifier search

This file formalizes a finite layered specialization of the flow-matching
construction in:

* Bengio et al., *Flow Network based Generative Models for Non-Iterative
  Diverse Candidate Generation* (2021), arXiv:2106.04399;
* Bengio et al., *GFlowNet Foundations* (2023), especially Definitions
  11--13, Proposition 14, and Proposition 19, arXiv:2111.09266.

Local incoming/outgoing flow matching and edge factorization imply that the
forward policy's exact finite reach mass is state flow divided by root flow.
At the terminal layer this is reward divided by total reward.  The theorem
allows several parents to merge into one state, so it does not silently replace
the construction DAG by a trajectory tree.

Primary source artifact SHA-256:
`b27eab696862ec01c2661905129afce0834c2c54a4aa9d35f323777f7d9db257`.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.VerifierGuidance

universe uN

/-- A finite, topologically layered rational flow network.  A node may occur
with zero flow in any layer; this avoids padding the theorem with separate
layer-dependent node types while retaining merging and splitting. -/
structure LayeredGFlowNet (depth : ℕ) (Node : Type uN)
    [Fintype Node] [DecidableEq Node] where
  source : Node
  stateFlow : Fin (depth + 1) → Node → ℚ
  edgeFlow : Fin depth → Node → Node → ℚ
  forward : Fin depth → Node → Node → ℚ
  reward : Node → ℚ
  totalFlow : ℚ
  totalFlow_pos : 0 < totalFlow
  stateFlow_nonnegative : ∀ layer node, 0 ≤ stateFlow layer node
  edgeFlow_nonnegative : ∀ layer parent child, 0 ≤ edgeFlow layer parent child
  forward_nonnegative : ∀ layer parent child, 0 ≤ forward layer parent child
  initial_match :
    ∀ node, stateFlow 0 node = if node = source then totalFlow else 0
  outgoing_match :
    ∀ layer parent,
      (∑ child : Node, edgeFlow layer parent child) =
        stateFlow layer.castSucc parent
  incoming_match :
    ∀ layer child,
      (∑ parent : Node, edgeFlow layer parent child) =
        stateFlow layer.succ child
  edge_factorization :
    ∀ layer parent child,
      edgeFlow layer parent child =
        stateFlow layer.castSucc parent * forward layer parent child
  terminal_match :
    ∀ node, stateFlow (Fin.last depth) node = reward node

namespace LayeredGFlowNet

variable {depth : ℕ} {Node : Type uN}
variable [Fintype Node] [DecidableEq Node]

/-- The probability mass obtained by actually executing the forward policy.
The branch beyond `depth` is defined as zero only to keep the recursion total;
all correspondence theorems require `step ≤ depth`. -/
def sampledMass (network : LayeredGFlowNet depth Node) :
    ℕ → Node → ℚ
  | 0, node => if node = network.source then 1 else 0
  | step + 1, node =>
      if hstep : step < depth then
        ∑ parent : Node,
          sampledMass network step parent *
            network.forward ⟨step, hstep⟩ parent node
      else 0

/-- At a positive-flow state, factorization plus outgoing flow matching makes
the forward row sum to one.  Zero-flow states are deliberately unconstrained:
they are unreachable and their policy row is observationally irrelevant. -/
theorem sum_forward_eq_one_of_stateFlow_pos
    (network : LayeredGFlowNet depth Node)
    (layer : Fin depth) (parent : Node)
    (hpositive : 0 < network.stateFlow layer.castSucc parent) :
    (∑ child : Node, network.forward layer parent child) = 1 := by
  have hfactor :
      network.stateFlow layer.castSucc parent *
          (∑ child : Node, network.forward layer parent child) =
        ∑ child : Node, network.edgeFlow layer parent child := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro child _hchild
    rw [network.edge_factorization]
  have hout := network.outgoing_match layer parent
  have hne : network.stateFlow layer.castSucc parent ≠ 0 :=
    ne_of_gt hpositive
  apply (mul_left_cancel₀ hne)
  simpa using hfactor.trans hout

/-- One local flow-matching layer preserves total state flow. -/
theorem sum_stateFlow_succ_eq
    (network : LayeredGFlowNet depth Node) (layer : Fin depth) :
    (∑ child : Node, network.stateFlow layer.succ child) =
      ∑ parent : Node, network.stateFlow layer.castSucc parent := by
  calc
    (∑ child : Node, network.stateFlow layer.succ child)
        = ∑ child : Node,
            ∑ parent : Node, network.edgeFlow layer parent child := by
          apply Finset.sum_congr rfl
          intro child _hchild
          rw [network.incoming_match]
    _ = ∑ parent : Node,
          ∑ child : Node, network.edgeFlow layer parent child := by
        rw [Finset.sum_comm]
    _ = ∑ parent : Node, network.stateFlow layer.castSucc parent := by
      apply Finset.sum_congr rfl
      intro parent _hparent
      rw [network.outgoing_match]

/-- Every represented layer carries exactly the root flow. -/
theorem sum_stateFlow_eq_totalFlow
    (network : LayeredGFlowNet depth Node)
    (step : ℕ) (hstep : step ≤ depth) :
    (∑ node : Node,
      network.stateFlow ⟨step, Nat.lt_succ_of_le hstep⟩ node) =
        network.totalFlow := by
  induction step with
  | zero =>
      simp [network.initial_match]
  | succ step ih =>
      have hlt : step < depth := Nat.lt_of_succ_le hstep
      let layer : Fin depth := ⟨step, hlt⟩
      have hpreserve := sum_stateFlow_succ_eq network layer
      have hprevious := ih (Nat.le_of_lt hlt)
      simpa [layer] using hpreserve.trans hprevious

/-- Local edge factorization and flow matching recover the source's normalized
state flow from the actual forward-policy recurrence. -/
theorem sampledMass_eq_stateFlow_div
    (network : LayeredGFlowNet depth Node)
    (step : ℕ) (hstep : step ≤ depth) (node : Node) :
    sampledMass network step node =
      network.stateFlow ⟨step, Nat.lt_succ_of_le hstep⟩ node /
        network.totalFlow := by
  induction step generalizing node with
  | zero =>
      by_cases hsource : node = network.source
      · subst node
        simp [sampledMass, network.initial_match,
          ne_of_gt network.totalFlow_pos]
      · simp [sampledMass, network.initial_match, hsource]
  | succ step ih =>
      have hlt : step < depth := Nat.lt_of_succ_le hstep
      have hprevious : step ≤ depth := (Nat.le_of_lt hlt).trans
        (Nat.le_refl depth)
      let layer : Fin depth := ⟨step, hlt⟩
      rw [sampledMass]
      simp only [dif_pos hlt]
      simp_rw [ih hprevious]
      change
        (∑ parent : Node,
          network.stateFlow layer.castSucc parent / network.totalFlow *
            network.forward layer parent node) =
          network.stateFlow layer.succ node / network.totalFlow
      rw [← network.incoming_match layer node, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro parent _hparent
      rw [network.edge_factorization]
      ring

/-- The executable forward sampler reaches each terminal with mass exactly
proportional to its declared reward. -/
theorem terminalSample_eq_reward_div_totalFlow
    (network : LayeredGFlowNet depth Node) (node : Node) :
    sampledMass network depth node =
      network.reward node / network.totalFlow := by
  have hsample :=
    sampledMass_eq_stateFlow_div network depth (Nat.le_refl depth) node
  simpa using hsample.trans
    (congrArg (fun value : ℚ ↦ value / network.totalFlow)
      (network.terminal_match node))

theorem reward_sum_eq_totalFlow
    (network : LayeredGFlowNet depth Node) :
    (∑ node : Node, network.reward node) = network.totalFlow := by
  have htotal :=
    sum_stateFlow_eq_totalFlow network depth (Nat.le_refl depth)
  have hlast :
      (⟨depth, Nat.lt_succ_of_le (Nat.le_refl depth)⟩ :
        Fin (depth + 1)) = Fin.last depth := by
    apply Fin.ext
    rfl
  calc
    (∑ node : Node, network.reward node) =
        ∑ node : Node, network.stateFlow (Fin.last depth) node := by
      apply Finset.sum_congr rfl
      intro node _hnode
      rw [network.terminal_match]
    _ = network.totalFlow := by
      rw [← hlast]
      exact htotal

/-- Proposition 14 in the finite rational specialization: the terminal
sampler is normalized. -/
theorem sum_terminalSample_eq_one
    (network : LayeredGFlowNet depth Node) :
    (∑ node : Node, sampledMass network depth node) = 1 := by
  simp_rw [terminalSample_eq_reward_div_totalFlow]
  rw [← Finset.sum_div, reward_sum_eq_totalFlow]
  exact div_self (ne_of_gt network.totalFlow_pos)

theorem terminalSample_nonnegative
    (network : LayeredGFlowNet depth Node) (node : Node) :
    0 ≤ sampledMass network depth node := by
  rw [terminalSample_eq_reward_div_totalFlow]
  exact div_nonneg
    (network.terminal_match node ▸
      network.stateFlow_nonnegative (Fin.last depth) node)
    network.totalFlow_pos.le

/-- Reward support remains subordinate to the external checker after the
whole flow-matching construction, not merely after direct normalization. -/
theorem terminalSample_checkerSafe
    (network : LayeredGFlowNet depth Node) (checker : Node → Bool)
    (hsafe : RewardSupportSafe checker network.reward)
    (node : Node) (hpositive : 0 < sampledMass network depth node) :
    checker node = true := by
  apply hsafe node
  rw [terminalSample_eq_reward_div_totalFlow] at hpositive
  rcases div_pos_iff.mp hpositive with
    ⟨hreward, _htotal⟩ | ⟨_hreward, htotalNegative⟩
  · exact hreward
  · exact False.elim
      ((not_lt_of_ge network.totalFlow_pos.le) htotalNegative)

end LayeredGFlowNet

/-! ## Shared-terminal fixture and broken-conservation boundary -/

namespace GFlowFixture

inductive Node
  | left
  | right
  | merge
  deriving DecidableEq, Fintype

namespace Node

theorem univ_eq :
    (Finset.univ : Finset Node) = {left, right, merge} := by
  ext node
  cases node <;> simp

theorem sum_eq (f : Node → ℚ) :
    (∑ node : Node, f node) = f left + f right + f merge := by
  rw [univ_eq]
  simp [add_assoc]

end Node

def stateFlow (layer : Fin 3) (node : Node) : ℚ :=
  if layer = 0 then
    if node = .left then 4 else 0
  else if layer = 1 then
    if node = .left then 1 / 2 else if node = .right then 1 / 2 else 3
  else
    if node = .left then 1 else if node = .right then 3 else 0

def edgeFlow (layer : Fin 2) (parent child : Node) : ℚ :=
  if layer = 0 then
    if parent = .left then
      if child = .left then 1 / 2 else if child = .right then 1 / 2 else 3
    else 0
  else
    if parent = .left ∧ child = .left then 1 / 2
    else if parent = .right ∧ child = .left then 1 / 2
    else if parent = .merge ∧ child = .right then 3
    else 0

def forward (layer : Fin 2) (parent child : Node) : ℚ :=
  if layer = 0 then
    if parent = .left then
      if child = .left then 1 / 8 else if child = .right then 1 / 8 else 3 / 4
    else 0
  else
    if parent = .left ∧ child = .left then 1
    else if parent = .right ∧ child = .left then 1
    else if parent = .merge ∧ child = .right then 1
    else 0

def reward : Node → ℚ
  | .left => 1
  | .right => 3
  | .merge => 0

def checker : Node → Bool
  | .left => true
  | .right => true
  | .merge => false

noncomputable def network : LayeredGFlowNet 2 Node where
  source := .left
  stateFlow := stateFlow
  edgeFlow := edgeFlow
  forward := forward
  reward := reward
  totalFlow := 4
  totalFlow_pos := by norm_num
  stateFlow_nonnegative := by
    intro layer node
    fin_cases layer <;> cases node <;>
      simp [stateFlow]
  edgeFlow_nonnegative := by
    intro layer parent child
    fin_cases layer <;> cases parent <;> cases child <;>
      simp [edgeFlow]
  forward_nonnegative := by
    intro layer parent child
    fin_cases layer <;> cases parent <;> cases child <;>
      simp [forward]; try norm_num
  initial_match := by
    intro node
    cases node <;> simp [stateFlow]
  outgoing_match := by
    intro layer parent
    fin_cases layer <;> cases parent <;>
      simp [Node.sum_eq, edgeFlow, stateFlow]; try norm_num
  incoming_match := by
    intro layer child
    fin_cases layer <;> cases child <;>
      simp [Node.sum_eq, edgeFlow, stateFlow]; try norm_num
  edge_factorization := by
    intro layer parent child
    fin_cases layer <;> cases parent <;> cases child <;>
      simp [edgeFlow, stateFlow, forward] <;> norm_num
  terminal_match := by
    intro node
    cases node <;> simp [stateFlow, reward, Fin.last]

theorem reward_support_safe : RewardSupportSafe checker reward := by
  intro node hpositive
  cases node <;> simp [reward, checker] at hpositive ⊢

/-- Two distinct layer-one parents merge into terminal `0`; their incoming
flows add to its unit reward. -/
theorem shared_terminal_has_two_positive_parents :
    0 < edgeFlow 1 .left .left ∧ 0 < edgeFlow 1 .right .left ∧
      edgeFlow 1 .left .left + edgeFlow 1 .right .left = reward .left := by
  norm_num [edgeFlow, reward]

theorem terminal_distribution :
    LayeredGFlowNet.sampledMass network 2 .left = 1 / 4 ∧
      LayeredGFlowNet.sampledMass network 2 .right = 3 / 4 ∧
      LayeredGFlowNet.sampledMass network 2 .merge = 0 := by
  constructor
  · rw [LayeredGFlowNet.terminalSample_eq_reward_div_totalFlow]
    change reward .left / 4 = 1 / 4
    norm_num [reward]
  constructor
  · rw [LayeredGFlowNet.terminalSample_eq_reward_div_totalFlow]
    change reward .right / 4 = 3 / 4
    norm_num [reward]
  · rw [LayeredGFlowNet.terminalSample_eq_reward_div_totalFlow]
    change reward .merge / 4 = 0
    norm_num [reward]

theorem positive_terminal_sample_is_checker_safe
    (node : Node)
    (hpositive : 0 < LayeredGFlowNet.sampledMass network 2 node) :
    checker node = true :=
  LayeredGFlowNet.terminalSample_checkerSafe
    network checker reward_support_safe node hpositive

/-- Perturbing one of the two merging edges breaks the local equation while
leaving the declared terminal reward unchanged. -/
def alteredEdgeFlow (layer : Fin 2) (parent child : Node) : ℚ :=
  if layer = 1 ∧ parent = .right ∧ child = .left then 1 else
    edgeFlow layer parent child

theorem altered_merge_breaks_incoming_match :
    (∑ parent : Node, alteredEdgeFlow 1 parent .left) ≠
      stateFlow 2 .left := by
  rw [Node.sum_eq]
  simp [alteredEdgeFlow, edgeFlow, stateFlow]

end GFlowFixture

#print axioms LayeredGFlowNet.sampledMass_eq_stateFlow_div
#print axioms LayeredGFlowNet.terminalSample_eq_reward_div_totalFlow
#print axioms LayeredGFlowNet.sum_terminalSample_eq_one
#print axioms LayeredGFlowNet.terminalSample_checkerSafe
#print axioms GFlowFixture.shared_terminal_has_two_positive_parents
#print axioms GFlowFixture.terminal_distribution
#print axioms GFlowFixture.altered_merge_breaks_incoming_match

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.VerifierGuidance
