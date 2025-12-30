import Mettapedia.UniversalAI.MultiAgent.Value
import Mettapedia.Computability.ArithmeticalHierarchy.PolicyEncoding

/-!
# Multi-Agent Best Response

This file defines best response policies and their properties in multi-agent settings.

## Main Definitions

* `bestResponsePolicy`: Policy that maximizes player i's Q-value
* `bestResponseAgent`: Agent that plays best response
* `isBestResponse`: Predicate for best response property

## References

- Leike, Taylor & Fallenstein (2016). "A Formal Solution to the Grain of Truth Problem"
- Shoham & Leyton-Brown (2008). "Multiagent Systems", Chapter 3
-/

namespace Mettapedia.UniversalAI.MultiAgent

open Mettapedia.UniversalAI.BayesianAgents

/-! ## Utilities -/

/-- Update multi-agent policy by replacing agent i. -/
def MultiAgentPolicy.updateAgent {n : ℕ}
    (π : MultiAgentPolicy n) (i : Fin n) (agent : Agent) :
    MultiAgentPolicy n where
  agents := fun j => if j = i then agent else π.agents j

/-! ## Best Response Policy -/

/-- Convert single-player history to multi-agent history from player i's perspective.
    Other players' actions/percepts are set to default values. -/
def historyToMultiAgent {n : ℕ} (i : Fin n) (h : History) : MultiAgentHistory n :=
  h.map fun elem =>
    match elem with
    | HistElem.act a => JointHistElem.act (fun j => if j = i then a else default)
    | HistElem.per p => JointHistElem.per (fun j => if j = i then p else default)

/-! ### historyToMultiAgent properties -/

/-- historyToMultiAgent preserves the wellFormed property.
    Single-agent History.wellFormed maps to MultiAgentHistory.wellFormed. -/
theorem historyToMultiAgent_wellFormed {n : ℕ} (i : Fin n) (h : History)
    (hw : History.wellFormed h = true) :
    (historyToMultiAgent i h).wellFormed = true := by
  -- Induction on the wellFormed structure
  match h with
  | [] => rfl
  | [HistElem.act _] =>
    simp only [historyToMultiAgent, List.map, MultiAgentHistory.wellFormed]
  | HistElem.act _ :: HistElem.per _ :: rest =>
    simp only [History.wellFormed] at hw
    simp only [historyToMultiAgent, List.map, MultiAgentHistory.wellFormed]
    exact historyToMultiAgent_wellFormed i rest hw
  | HistElem.per _ :: _ =>
    simp only [History.wellFormed] at hw; cases hw
  | HistElem.act _ :: HistElem.act _ :: _ =>
    simp only [History.wellFormed] at hw; cases hw
termination_by h.length

/-- playerView of historyToMultiAgent returns the original single-agent history. -/
theorem playerView_historyToMultiAgent {n : ℕ} (i : Fin n) (h : History) :
    (historyToMultiAgent i h).playerView i = h := by
  induction h with
  | nil => rfl
  | cons elem rest ih =>
    -- Goal: (historyToMultiAgent i (elem :: rest)).playerView i = elem :: rest
    -- First, unfold the outer layer
    unfold historyToMultiAgent at *
    unfold MultiAgentHistory.playerView at *
    simp only [List.map_cons] at *
    cases elem with
    | act a =>
      unfold JointHistElem.playerView
      simp only [if_true]
      exact congrArg (List.cons (HistElem.act a)) ih
    | per p =>
      unfold JointHistElem.playerView
      simp only [if_true]
      exact congrArg (List.cons (HistElem.per p)) ih

/-- Best response policy for player i: choose action maximizing bestResponseQValue.

    This is the correct game-theoretic definition: at each step, player i chooses
    the action that maximizes their value assuming optimal play in all future steps.

    Note: We use bestResponseQValue (not playerQValue) because:
    - bestResponseQValue uses bestResponseValue in recursion (optimal future play)
    - playerQValue uses playerValue in recursion (following π_i in future)
    - The optimal action for best response should assume optimal future, not π_i future
-/
noncomputable def bestResponsePolicy
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (horizon : ℕ) : History → Action :=
  fun h =>
    Classical.choose (exists_best_action μ π γ i h horizon)
  where
    exists_best_action (μ : MultiAgentEnvironment n) (π : MultiAgentPolicy n)
        (γ : DiscountFactor) (i : Fin n) (h : History) (horizon : ℕ) :
        ∃ a : Action, ∀ a' : Action,
          bestResponseQValue μ π γ i (historyToMultiAgent i h) a horizon ≥
          bestResponseQValue μ π γ i (historyToMultiAgent i h) a' horizon := by
      -- Action is a finite nonempty type, so maximum exists
      have ⟨a, _, ha⟩ := Finset.exists_max_image
        (s := (Finset.univ : Finset Action))
        (f := fun a => bestResponseQValue μ π γ i (historyToMultiAgent i h) a horizon)
        ⟨default, Finset.mem_univ _⟩
      exact ⟨a, fun a' => ha a' (Finset.mem_univ a')⟩

/-- Construct multi-agent policy from other agents.
    Uses uniformAgent as placeholder for player i. -/
noncomputable def multiAgentPolicyFromOthers {n : ℕ} (i : Fin n)
    (π_others : (j : Fin n) → j ≠ i → Agent) : MultiAgentPolicy n :=
  { agents := fun j =>
      if hj : j = i then uniformAgent
      else π_others j hj }

/-- Best response agent: agent that plays best response policy. -/
noncomputable def bestResponseAgent {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (i : Fin n)
    (π_others : (j : Fin n) → j ≠ i → Agent)
    (γ : DiscountFactor)
    (horizon : ℕ) : Agent where
  policy := fun h a =>
    if bestResponsePolicy μ (multiAgentPolicyFromOthers i π_others) γ i horizon h = a
    then 1
    else 0
  policy_sum_one := by
    intro h _hw
    rw [tsum_fintype]
    simp [Finset.sum_ite_eq]

/-! ## Best Response Properties -/

/-- When player i plays deterministically (probability 1 on action a*),
    the player value equals the Q-value for that action.

    This follows from playerValue_eq_weighted_qValue:
    playerValue = Σ_a π_i(a) * playerQValue(a)
    When π_i(a*) = 1 and π_i(a) = 0 for a ≠ a*, this simplifies to playerQValue(a*).
-/
theorem playerValue_deterministic {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (hw : h.wellFormed = true)
    (action : Action)
    (hdet : ∀ a : Action, ((π.agents i).policy (h.playerView i) a).toReal =
                          if a = action then 1 else 0) :
    playerValue μ π γ i h horizon =
    playerQValue μ π γ i h action horizon := by
  rw [playerValue_eq_weighted_qValue]
  -- Sum simplifies: only the action term contributes (weight 1), others are 0
  simp_rw [hdet]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ↓reduceIte]

/-- The best response action achieves the supremum of bestResponseQValues.
    Note: bestResponsePolicy operates on single-agent histories, converting via historyToMultiAgent.

    This is the KEY theorem: a_star achieves bestResponseValue = ⨆_a bestResponseQValue(a).
-/
theorem bestResponseAction_achieves_bestResponseValue {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h_single : History)
    (horizon : ℕ) :
    let h := historyToMultiAgent i h_single
    let a_star := bestResponsePolicy μ π γ i horizon h_single
    bestResponseQValue μ π γ i h a_star horizon = bestResponseValue μ π γ i h horizon := by
  intro h a_star
  simp only [bestResponseValue]
  -- a_star achieves the maximum by construction (Classical.choose from exists_best_action)
  have h_best := Classical.choose_spec (bestResponsePolicy.exists_best_action μ π γ i h_single horizon)
  -- h_best: ∀ a', bestResponseQValue(..., a_star, ...) ≥ bestResponseQValue(..., a', ...)
  -- For finite Action type, ciSup = Finset.sup'
  apply le_antisymm
  · -- a_star ≤ sup
    have hbdd : BddAbove (Set.range fun a => bestResponseQValue μ π γ i h a horizon) :=
      Set.Finite.bddAbove (Set.finite_range _)
    exact le_ciSup hbdd a_star
  · -- sup ≤ a_star (since a_star is max)
    have hbdd : BddAbove (Set.range fun a => bestResponseQValue μ π γ i h a horizon) :=
      Set.Finite.bddAbove (Set.finite_range _)
    apply ciSup_le
    intro a
    exact h_best a

/-- Predicate: π_i is a best response to π_{-i}. -/
def isBestResponse
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (horizon : ℕ) : Prop :=
  ∀ (h : MultiAgentHistory n),
    h.wellFormed = true →
    playerValue μ π γ i h horizon =
    bestResponseValue μ π γ i h horizon

/-! ## Full Information Assumption -/

/-- Player i's Q-values only depend on their own view of the history.

    This assumption holds when:
    1. The environment is fully observable (all players see the same things)
    2. Other players' policies are known and deterministic
    3. The multi-agent history is "consistent" with player i's view

    This is a sufficient condition for best response to work correctly.
    Without this, player i might choose actions optimal for their partial view
    that aren't optimal for the true multi-agent history.
-/
def playerIQValueDependsOnlyOnOwnView
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n) : Prop :=
  ∀ (h₁ h₂ : MultiAgentHistory n) (action : Action) (horizon : ℕ),
    h₁.wellFormed = true → h₂.wellFormed = true →
    h₁.playerView i = h₂.playerView i →
    bestResponseQValue μ π γ i h₁ action horizon =
    bestResponseQValue μ π γ i h₂ action horizon

/-- When player i's Q-values only depend on their own view, the best action
    at historyToMultiAgent is also optimal at the true history.

    The proof uses the full information assumption to relate Q-values at
    different multi-agent histories that have the same player i view.
-/
theorem bestResponseQValue_eq_of_playerView_eq {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (hw : h.wellFormed = true)
    (_hep : h.endsWithPercept = true)
    (action : Action)
    (horizon : ℕ)
    (hfull : playerIQValueDependsOnlyOnOwnView μ π γ i) :
    bestResponseQValue μ π γ i h action horizon =
    bestResponseQValue μ π γ i (historyToMultiAgent i (h.playerView i)) action horizon := by
  -- Apply the full information assumption with:
  -- h₁ = h, h₂ = historyToMultiAgent i (h.playerView i)
  apply hfull
  · exact hw
  · -- historyToMultiAgent preserves wellFormed
    -- Need: (h.playerView i).wellFormed = true
    -- Then use historyToMultiAgent_wellFormed
    exact historyToMultiAgent_wellFormed i (h.playerView i)
      (MultiAgentHistory.playerView_wellFormed i h hw)
  · -- playerView i (historyToMultiAgent i (h.playerView i)) = h.playerView i
    exact (playerView_historyToMultiAgent i (h.playerView i)).symm

/-! ## Q-Value Policy Independence -/

/-- othersProb is independent of player i's policy.
    This is because othersProb only uses policies for j ≠ i. -/
theorem othersProb_updateAgent_eq {n : ℕ}
    (π : MultiAgentPolicy n)
    (i : Fin n)
    (agent : Agent)
    (h : MultiAgentHistory n)
    (ja : JointAction n) :
    othersProb (π.updateAgent i agent) h ja i = othersProb π h ja i := by
  simp only [othersProb, MultiAgentPolicy.updateAgent]
  apply Finset.prod_congr rfl
  intro j hj
  -- j ∈ Finset.univ.erase i means j ≠ i
  have hj_ne : j ≠ i := Finset.mem_erase.mp hj |>.1
  simp only [hj_ne, ↓reduceIte]

/-- playerView is the same for player i regardless of player i's policy.
    This is because playerView only depends on the history structure, not the policy. -/
theorem playerView_updateAgent_eq {n : ℕ}
    (π : MultiAgentPolicy n)
    (i : Fin n)
    (agent : Agent)
    (h : MultiAgentHistory n) :
    (h.playerView i) = (h.playerView i) := rfl

/-- At horizon 0, Q-values are all 0, so they don't depend on the policy. -/
theorem playerQValue_zero {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (action : Action) :
    playerQValue μ π γ i h action 0 = 0 := by
  simp only [playerQValue]

/-- bestResponseQValue at horizon 0 is 0. -/
theorem bestResponseQValue_zero {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (action : Action) :
    bestResponseQValue μ π γ i h action 0 = 0 := by
  simp only [bestResponseQValue]

/-- bestResponseValue at horizon 0 is 0. -/
theorem bestResponseValue_zero {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n) :
    bestResponseValue μ π γ i h 0 = 0 := by
  simp only [bestResponseValue, bestResponseQValue_zero]
  -- ciSup of constantly 0 is 0
  simp only [ciSup_const]

/-- At horizon 1, Q-values only depend on othersProb (not on recursive playerValue). -/
theorem playerQValue_one_eq_updateAgent {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (action : Action)
    (agent : Agent) :
    playerQValue μ (π.updateAgent i agent) γ i h action 1 =
    playerQValue μ π γ i h action 1 := by
  simp only [playerQValue, playerValue]
  -- At horizon 1, the recursive playerValue is at horizon 0, which is 0
  simp only [mul_zero, add_zero]
  -- Now only othersProb matters, and that's the same by othersProb_updateAgent_eq
  congr 1
  ext ja
  by_cases hja : ja i = action
  · simp only [hja, ↓reduceIte]
    congr 1
    ext jp
    -- Need to show the products are equal
    -- Use the fact that for j ≠ i, (π.updateAgent i agent).agents j = π.agents j
    have hprod : (∏ j ∈ Finset.univ.erase i, ((π.updateAgent i agent).agents j).policy
                    (MultiAgentHistory.playerView j h) (ja j)) =
                 (∏ j ∈ Finset.univ.erase i, (π.agents j).policy
                    (MultiAgentHistory.playerView j h) (ja j)) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hj_ne : j ≠ i := Finset.mem_erase.mp hj |>.1
      simp only [MultiAgentPolicy.updateAgent, hj_ne, ↓reduceIte]
    rw [hprod]
  · simp only [hja, ↓reduceIte]

/-- At horizon 1, bestResponseQValue only depends on othersProb (not on recursive bestResponseValue).
    This is similar to playerQValue_one_eq_updateAgent. -/
theorem bestResponseQValue_one_eq_updateAgent {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (action : Action)
    (agent : Agent) :
    bestResponseQValue μ (π.updateAgent i agent) γ i h action 1 =
    bestResponseQValue μ π γ i h action 1 := by
  simp only [bestResponseQValue]
  -- At horizon 1, the recursive bestResponseValue is at horizon 0, which is 0
  simp only [bestResponseValue_zero, mul_zero, add_zero]
  -- Now only othersProb matters, and that's the same by othersProb_updateAgent_eq
  congr 1
  ext ja
  by_cases hja : ja i = action
  · simp only [hja, ↓reduceIte]
    congr 1
    ext jp
    have hprod : (∏ j ∈ Finset.univ.erase i, ((π.updateAgent i agent).agents j).policy
                    (MultiAgentHistory.playerView j h) (ja j)) =
                 (∏ j ∈ Finset.univ.erase i, (π.agents j).policy
                    (MultiAgentHistory.playerView j h) (ja j)) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hj_ne : j ≠ i := Finset.mem_erase.mp hj |>.1
      simp only [MultiAgentPolicy.updateAgent, hj_ne, ↓reduceIte]
    rw [hprod]
  · simp only [hja, ↓reduceIte]

/-- At horizon 1, bestResponseValue doesn't depend on player i's policy. -/
theorem bestResponseValue_one_eq_updateAgent {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (agent : Agent) :
    bestResponseValue μ (π.updateAgent i agent) γ i h 1 =
    bestResponseValue μ π γ i h 1 := by
  simp only [bestResponseValue]
  congr 1
  ext a
  exact bestResponseQValue_one_eq_updateAgent μ π γ i h a agent

/-- bestResponseQValue doesn't depend on player i's policy.
    This is because it only uses othersProb (policies for j ≠ i). -/
theorem bestResponseQValue_updateAgent_eq {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (agent : Agent)
    (action : Action)
    (horizon : ℕ) :
    bestResponseQValue μ (π.updateAgent i agent) γ i h action horizon =
    bestResponseQValue μ π γ i h action horizon := by
  induction horizon generalizing h action with
  | zero =>
    simp only [bestResponseQValue_zero]
  | succ k ih =>
    simp only [bestResponseQValue]
    congr 1
    ext ja
    split_ifs with hja
    · congr 1
      ext jp
      -- The othersProb part is equal (uses policies for j ≠ i only)
      have hprod : (∏ j ∈ Finset.univ.erase i, ((π.updateAgent i agent).agents j).policy
                      (MultiAgentHistory.playerView j h) (ja j)) =
                   (∏ j ∈ Finset.univ.erase i, (π.agents j).policy
                      (MultiAgentHistory.playerView j h) (ja j)) := by
        apply Finset.prod_congr rfl
        intro j hj'
        have hj_ne : j ≠ i := Finset.mem_erase.mp hj' |>.1
        simp only [MultiAgentPolicy.updateAgent, hj_ne, ↓reduceIte]
      rw [hprod]
      -- The environment prob is the same (doesn't depend on π)
      -- The reward is the same
      -- The recursive bestResponseValue is the same
      congr 1
      congr 1
      -- Need to show: bestResponseValue with updated policy = bestResponseValue with original
      -- Use that bestResponseValue = ⨆ a, bestResponseQValue a, and apply IH
      simp only [bestResponseValue]
      -- Show that the functions under ciSup are equal, hence ciSups are equal
      have hfun_eq : (fun action => bestResponseQValue μ (π.updateAgent i agent) γ i
            (h ++ [JointHistElem.act ja, JointHistElem.per jp]) action k) =
          (fun action => bestResponseQValue μ π γ i
            (h ++ [JointHistElem.act ja, JointHistElem.per jp]) action k) := by
        funext a
        exact ih (h ++ [JointHistElem.act ja, JointHistElem.per jp]) a
      simp only [hfun_eq]
    · rfl

/-- bestResponseValue doesn't depend on player i's policy.
    This is because bestResponseQValue only uses othersProb (policies for j ≠ i). -/
theorem bestResponseValue_updateAgent_eq {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (agent : Agent)
    (horizon : ℕ) :
    bestResponseValue μ (π.updateAgent i agent) γ i h horizon =
    bestResponseValue μ π γ i h horizon := by
  simp only [bestResponseValue]
  congr 1
  ext action
  exact bestResponseQValue_updateAgent_eq μ π γ i h agent action horizon

/-- Best response is bounded by the optimal value.
    This follows from playerValue_le_bestResponseValue (proven in Value.lean)
    and the fact that bestResponseValue doesn't depend on player i's policy. -/
theorem bestResponse_le_bestResponseValue
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (hw : h.wellFormed = true)
    (hep : h.endsWithPercept = true)
    (horizon : ℕ) :
    let π' := π.updateAgent i (bestResponseAgent μ i
      (fun j hj => π.agents j) γ horizon)
    playerValue μ π' γ i h horizon ≤
    bestResponseValue μ π γ i h horizon := by
  intro π'
  calc playerValue μ π' γ i h horizon
      ≤ bestResponseValue μ π' γ i h horizon :=
        playerValue_le_bestResponseValue μ π' γ i h hw hep horizon
    _ = bestResponseValue μ π γ i h horizon :=
        bestResponseValue_updateAgent_eq μ π γ i h _ horizon

/-- playerQValue under π' equals bestResponseQValue under π when playerValue = bestResponseValue
    for all extended histories h ++ [act, per].

    This is the key lemma: if we already know playerValue μ π' = bestResponseValue μ π at
    smaller horizons for extended histories, then the Q-values are equal at the current horizon.

    Note: We only require the equality for extended histories (h ++ [act, per]), not for all h'.
    This is precisely what the Q-value recursion needs.
-/
theorem playerQValue_eq_bestResponseQValue_of_value_eq {n : ℕ}
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (π' : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (action : Action)
    (k : ℕ)
    (hπ' : ∀ j, j ≠ i → π'.agents j = π.agents j)
    (hvalue_eq : ∀ (ja : JointAction n) (jp : JointPercept n),
        playerValue μ π' γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k =
        bestResponseValue μ π γ i (h ++ [JointHistElem.act ja, JointHistElem.per jp]) k) :
    playerQValue μ π' γ i h action (k + 1) =
    bestResponseQValue μ π γ i h action (k + 1) := by
  simp only [playerQValue, bestResponseQValue]
  congr 1
  ext ja
  split_ifs with hja
  · -- ja i = action case
    congr 1
    ext jp
    -- The othersProb part: π' and π have the same policies for j ≠ i
    have hothers : (∏ j ∈ Finset.univ.erase i, (π'.agents j).policy (h.playerView j) (ja j)) =
                   (∏ j ∈ Finset.univ.erase i, (π.agents j).policy (h.playerView j) (ja j)) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hj_ne : j ≠ i := Finset.mem_erase.mp hj |>.1
      rw [hπ' j hj_ne]
    rw [hothers]
    -- The recursive value: by assumption hvalue_eq
    congr 1
    rw [hvalue_eq ja jp]
  · -- ja i ≠ action case: both 0
    rfl

/-- Horizon-consistent optimality: the action optimal for horizon k+1 is also optimal for horizon k.

    This property holds when:
    1. The environment's reward structure is monotonic in horizon
    2. The discount factor γ < 1 ensures future rewards become less significant
    3. The optimal path for k+1 steps is also optimal for k steps

    This is a reasonable assumption for many RL environments where longer-horizon
    planning doesn't fundamentally change what's locally optimal.
-/
def horizonConsistentOptimality
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (horizon : ℕ) : Prop :=
  ∀ (h : History) (k : ℕ), k < horizon →
    let h_ma := historyToMultiAgent i h
    let a_star := bestResponsePolicy μ π γ i horizon h
    bestResponseQValue μ π γ i h_ma a_star k =
    ⨆ a, bestResponseQValue μ π γ i h_ma a k

/-- All horizons are consistent: for ANY horizon H, the action optimal at H
    is also optimal at all smaller horizons. This is stronger than
    horizonConsistentOptimality at a single horizon. -/
def allHorizonsConsistent
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n) : Prop :=
  ∀ H : ℕ, horizonConsistentOptimality μ π γ i H

/-! ## Sup-Achieving Actions and Value Equality -/

/-- An action is sup-achieving at horizon k if it achieves ⨆ bestResponseQValue at k. -/
def isSupAchievingAt
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (action : Action)
    (horizon : ℕ) : Prop :=
  bestResponseQValue μ π γ i h action horizon = ⨆ a, bestResponseQValue μ π γ i h a horizon

/-- The bestResponsePolicy plays a sup-achieving action (by definition). -/
theorem bestResponsePolicy_isSupAchieving
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : History)
    (horizon : ℕ) :
    isSupAchievingAt μ π γ i (historyToMultiAgent i h)
      (bestResponsePolicy μ π γ i horizon h) horizon := by
  unfold isSupAchievingAt bestResponsePolicy
  -- bestResponsePolicy chooses argmax, which achieves the sup
  let a_star := Classical.choose (bestResponsePolicy.exists_best_action μ π γ i h horizon)
  have h_best := Classical.choose_spec (bestResponsePolicy.exists_best_action μ π γ i h horizon)
  -- h_best: ∀ a', Q(a_star) ≥ Q(a')
  -- Need to show: Q(a_star) = ⨆ a, Q(a)
  apply le_antisymm
  · -- a_star ≤ sup
    have hbdd : BddAbove (Set.range fun a =>
        bestResponseQValue μ π γ i (historyToMultiAgent i h) a horizon) :=
      Set.Finite.bddAbove (Set.finite_range _)
    exact le_ciSup hbdd a_star
  · -- sup ≤ a_star (since a_star is max)
    apply ciSup_le
    intro a
    exact h_best a

/-- Key lemma: If a policy π' for player i plays sup-achieving actions at horizon k,
    and its other agents match π, then playerValue μ π' = bestResponseValue μ π at horizon k.

    **PROOF STRATEGY**:
    By induction on horizon:
    - At k=0: both are 0 (trivial)
    - At k+1: Use playerQValue_eq_bestResponseQValue_of_value_eq with IH
      1. playerValue = playerQValue(a_chosen) since π'_i is deterministic
      2. playerQValue(a_chosen) = bestResponseQValue(a_chosen) by IH on recursive values
      3. bestResponseQValue(a_chosen) = bestResponseValue since a_chosen is sup-achieving

    The hypothesis requires that at EVERY horizon k ≤ H, the action is sup-achieving.
    This is ensured by requiring allHorizonsConsistent and using the same action at each step.
-/
theorem playerValue_eq_bestResponseValue_of_supAchieving
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (π'_i : Agent)
    (hπ'_others : ∀ j, j ≠ i → (π.updateAgent i π'_i).agents j = π.agents j)
    (horizon : ℕ)
    -- Hypothesis: π'_i is deterministic and plays sup-achieving at EVERY k ≤ horizon
    -- (for wellFormed histories ending with percept)
    (hdet : ∀ h : MultiAgentHistory n, h.wellFormed = true → h.endsWithPercept = true →
        ∀ k : ℕ, k ≤ horizon → ∃ a_chosen : Action,
        (∀ a, (π'_i.policy (h.playerView i) a).toReal = if a = a_chosen then 1 else 0) ∧
        isSupAchievingAt μ π γ i h a_chosen k) :
    ∀ (h : MultiAgentHistory n), h.wellFormed = true → h.endsWithPercept = true →
      playerValue μ (π.updateAgent i π'_i) γ i h horizon =
      bestResponseValue μ π γ i h horizon := by
  induction horizon with
  | zero =>
    intro h hw hep
    simp only [playerValue, bestResponseValue_zero]
  | succ k IH =>
    intro h hw hep
    -- Get the action that π'_i plays at h
    obtain ⟨a_chosen, hdet_prob, hsup_kp1⟩ := hdet h hw hep (k + 1) (Nat.le_refl _)
    -- Step 1: playerValue = playerQValue(a_chosen) since π'_i is deterministic
    have hval_eq_qval : playerValue μ (π.updateAgent i π'_i) γ i h (k + 1) =
        playerQValue μ (π.updateAgent i π'_i) γ i h a_chosen (k + 1) := by
      rw [playerValue_eq_weighted_qValue]
      -- The sum simplifies to just the a_chosen term since π'_i is deterministic
      have hpolicy_eq : ∀ a : Action,
          ((π.updateAgent i π'_i).agents i).policy (h.playerView i) a =
          π'_i.policy (h.playerView i) a := by
        intro a
        show (if i = i then π'_i else π.agents i).policy (h.playerView i) a = _
        simp only [↓reduceIte]
      simp_rw [hpolicy_eq, hdet_prob]
      simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ↓reduceIte]
    -- Step 2: playerQValue = bestResponseQValue (using IH for recursive values)
    have hqval_eq : playerQValue μ (π.updateAgent i π'_i) γ i h a_chosen (k + 1) =
        bestResponseQValue μ π γ i h a_chosen (k + 1) := by
      apply playerQValue_eq_bestResponseQValue_of_value_eq
      · -- Other agents match
        exact hπ'_others
      · -- Recursive values match (from IH) for extended histories h ++ [act, per]
        intro ja jp
        -- The extended history is wellFormed by wellFormed_append_act_per
        have hext := MultiAgentHistory.wellFormed_append_act_per h ja jp hw hep
        apply IH
        · -- hdet at horizon k for the IH
          intro h'' hw'' hep'' k' hk'
          have hk'_le : k' ≤ k + 1 := Nat.le_succ_of_le hk'
          exact hdet h'' hw'' hep'' k' hk'_le
        · -- Extended history is wellFormed
          exact hext.1
        · -- Extended history ends with percept
          exact hext.2
    -- Step 3: bestResponseQValue(a_chosen) = bestResponseValue (sup-achieving)
    have hsup_eq : bestResponseQValue μ π γ i h a_chosen (k + 1) =
        bestResponseValue μ π γ i h (k + 1) := by
      unfold isSupAchievingAt at hsup_kp1
      unfold bestResponseValue
      exact hsup_kp1
    -- Chain the equalities
    calc playerValue μ (π.updateAgent i π'_i) γ i h (k + 1)
        = playerQValue μ (π.updateAgent i π'_i) γ i h a_chosen (k + 1) := hval_eq_qval
      _ = bestResponseQValue μ π γ i h a_chosen (k + 1) := hqval_eq
      _ = bestResponseValue μ π γ i h (k + 1) := hsup_eq

/-- Auxiliary: Best response at any history achieves best response value.

    This is the key lemma generalized over all histories for induction to work.
    We prove: for all h and horizon, playerValue μ π' γ i h horizon ≥ bestResponseValue μ π γ i h horizon
    where π' uses bestResponseAgent at the same horizon.

    **HORIZON DEPENDENCY ISSUE**:
    This proof has a subtle difficulty. The induction gives us:
    - IH: "For policy π_k' using bestResponseAgent at horizon k, playerValue ≥ bestResponseValue"
    - Goal: "For policy π_{k+1}' using bestResponseAgent at horizon k+1, playerValue ≥ bestResponseValue"

    These are DIFFERENT policies (they choose different actions), so the IH doesn't directly apply.
    The key insight is that by `allHorizonsConsistent`, the (k+1)-optimal action is also k-optimal,
    so both policies achieve the same supremum of Q-values at horizon k.

    **PROOF STRATEGY** (for completion):
    1. Show that if two deterministic policies both play sup-achieving actions at every step,
       they have the same playerValue at any horizon.
    2. π_{k+1}' plays actions that are (k+1)-optimal, which are also k-optimal by assumption.
    3. π_k' plays actions that are k-optimal.
    4. Both play k-optimal actions, so their k-horizon playerValues are equal.
    5. Apply IH to conclude.

    **STATUS**: Blocked on proving the "equal actions → equal values" lemma, which requires
    additional infrastructure about deterministic policies and sup-achieving actions.
-/
theorem bestResponse_achieves_value_aux
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (hfull : playerIQValueDependsOnlyOnOwnView μ π γ i)
    (hcons : allHorizonsConsistent μ π γ i)
    -- Since bestResponseQValue doesn't depend on player i's policy, horizonConsistentOptimality
    -- should hold for any policy differing from π only at position i.
    (hcons_any : ∀ agent, allHorizonsConsistent μ (π.updateAgent i agent) γ i)
    (horizon : ℕ) :
    ∀ (h : MultiAgentHistory n),
      h.wellFormed = true →
      h.endsWithPercept = true →
      let π' := π.updateAgent i (bestResponseAgent μ i
        (fun j hj => π.agents j) γ horizon)
      playerValue μ π' γ i h horizon ≥ bestResponseValue μ π γ i h horizon := by
  intro h hw hep
  let π'_i := bestResponseAgent μ i (fun j hj => π.agents j) γ horizon
  -- We use playerValue_eq_bestResponseValue_of_supAchieving to get equality (hence ≥)
  -- Key: bestResponseAgent plays deterministically and achieves sup at all k ≤ horizon
  -- First, show the multiAgentPolicyFromOthers matches π for j ≠ i
  have hπ_eq_others : ∀ j : Fin n, j ≠ i →
      (multiAgentPolicyFromOthers i (fun j hj => π.agents j)).agents j = π.agents j := by
    intro j hj_ne
    simp only [multiAgentPolicyFromOthers, hj_ne, ↓reduceDIte]
  -- Show π'_i is deterministic and plays sup-achieving actions at all k ≤ horizon
  -- (for wellFormed histories that end with percept)
  have hdet : ∀ h' : MultiAgentHistory n, h'.wellFormed = true → h'.endsWithPercept = true →
      ∀ k : ℕ, k ≤ horizon → ∃ a_chosen : Action,
      (∀ a, (π'_i.policy (h'.playerView i) a).toReal = if a = a_chosen then 1 else 0) ∧
      isSupAchievingAt μ π γ i h' a_chosen k := by
    intro h' hw' hep' k hk
    -- The action chosen by bestResponseAgent
    let π_others_ma := multiAgentPolicyFromOthers i (fun j hj => π.agents j)
    let a_star := bestResponsePolicy μ π_others_ma γ i horizon (h'.playerView i)
    use a_star
    constructor
    · -- bestResponseAgent is deterministic at a_star
      intro a
      show ((if bestResponsePolicy μ π_others_ma γ i horizon (h'.playerView i) = a
             then (1 : ENNReal) else 0) : ENNReal).toReal = _
      by_cases ha : a_star = a
      · -- a_star = a, so condition is true
        rw [if_pos ha, ENNReal.toReal_one]
        -- RHS: if a = a_star then 1 else 0, with a = a_star
        simp only [ha.symm, ↓reduceIte]
      · -- a_star ≠ a, so condition is false
        have hne : bestResponsePolicy μ π_others_ma γ i horizon (h'.playerView i) ≠ a := ha
        rw [if_neg hne, ENNReal.toReal_zero]
        -- RHS: if a = a_star then 1 else 0, with a_star ≠ a, so a ≠ a_star
        have ha' : a ≠ a_star := fun h => ha h.symm
        simp only [ha', ↓reduceIte]
    · -- a_star is sup-achieving at k ≤ horizon
      -- First, a_star is sup-achieving at horizon (by bestResponsePolicy_isSupAchieving)
      -- Then by hcons (allHorizonsConsistent), it's also sup-achieving at all k < horizon
      -- We need to relate bestResponseQValue for π_others_ma to bestResponseQValue for π
      unfold isSupAchievingAt
      -- The key is that bestResponseQValue doesn't depend on player i's policy
      -- So bestResponseQValue μ π_others_ma = bestResponseQValue μ π
      have hqval_eq : ∀ (action : Action),
          bestResponseQValue μ π_others_ma γ i (historyToMultiAgent i (h'.playerView i)) action k =
          bestResponseQValue μ π γ i (historyToMultiAgent i (h'.playerView i)) action k := by
        intro action
        -- multiAgentPolicyFromOthers differs from π only at position i
        -- So we can relate via bestResponseQValue_updateAgent_eq
        have heq : π_others_ma = π.updateAgent i uniformAgent := by
          ext j
          by_cases hj : j = i
          · -- j = i case: both sides equal uniformAgent
            simp only [MultiAgentPolicy.updateAgent, if_pos hj]
            simp only [π_others_ma, multiAgentPolicyFromOthers, dif_pos hj]
          · simp only [MultiAgentPolicy.updateAgent, if_neg hj]
            simp only [π_others_ma, multiAgentPolicyFromOthers, dif_neg hj]
        rw [heq]
        exact bestResponseQValue_updateAgent_eq μ π γ i
          (historyToMultiAgent i (h'.playerView i)) uniformAgent action k
      -- Now show a_star achieves sup at k
      -- Case analysis: k = horizon or k < horizon
      by_cases hk_eq : k = horizon
      · -- k = horizon: a_star achieves sup by bestResponsePolicy_isSupAchieving
        rw [hk_eq]
        -- First, relate h' to historyToMultiAgent i (h'.playerView i) using hfull
        have hview_eq : (h'.playerView i) =
            (historyToMultiAgent i (h'.playerView i)).playerView i :=
          (playerView_historyToMultiAgent i (h'.playerView i)).symm
        have hq_rel : bestResponseQValue μ π γ i h' a_star horizon =
            bestResponseQValue μ π γ i (historyToMultiAgent i (h'.playerView i)) a_star horizon := by
          apply hfull h' (historyToMultiAgent i (h'.playerView i)) a_star horizon hw'
            (historyToMultiAgent_wellFormed i (h'.playerView i)
              (MultiAgentHistory.playerView_wellFormed i h' hw'))
          exact hview_eq
        have hsup_rel : (⨆ a, bestResponseQValue μ π γ i (historyToMultiAgent i (h'.playerView i)) a horizon) =
            (⨆ a, bestResponseQValue μ π γ i h' a horizon) := by
          congr 1; ext a
          symm
          apply hfull h' (historyToMultiAgent i (h'.playerView i)) a horizon hw'
            (historyToMultiAgent_wellFormed i (h'.playerView i)
              (MultiAgentHistory.playerView_wellFormed i h' hw'))
          exact hview_eq
        rw [hq_rel, ← hsup_rel]
        -- Now goal is about historyToMultiAgent
        -- bestResponsePolicy_isSupAchieving gives us the result for historyToMultiAgent
        have hsup := bestResponsePolicy_isSupAchieving μ π_others_ma γ i (h'.playerView i) horizon
        unfold isSupAchievingAt at hsup
        -- hqval_eq is for k, we need it for horizon
        have hqval_eq' : ∀ (action : Action),
            bestResponseQValue μ π_others_ma γ i (historyToMultiAgent i (h'.playerView i)) action horizon =
            bestResponseQValue μ π γ i (historyToMultiAgent i (h'.playerView i)) action horizon := by
          intro action
          rw [← hk_eq]
          exact hqval_eq action
        -- Convert from π_others_ma to π using hqval_eq'
        calc bestResponseQValue μ π γ i (historyToMultiAgent i (h'.playerView i)) a_star horizon
            = bestResponseQValue μ π_others_ma γ i (historyToMultiAgent i (h'.playerView i)) a_star horizon :=
              (hqval_eq' a_star).symm
          _ = ⨆ a, bestResponseQValue μ π_others_ma γ i (historyToMultiAgent i (h'.playerView i)) a horizon := hsup
          _ = ⨆ a, bestResponseQValue μ π γ i (historyToMultiAgent i (h'.playerView i)) a horizon := by
              congr 1; ext a; exact hqval_eq' a
      · -- k < horizon: use allHorizonsConsistent
        have hk_lt : k < horizon := Nat.lt_of_le_of_ne hk hk_eq
        -- allHorizonsConsistent μ π γ i says: for all H, horizonConsistentOptimality μ π γ i H
        -- horizonConsistentOptimality μ π γ i horizon says:
        --   ∀ h k, k < horizon → bestResponseQValue(bestResponsePolicy(..., horizon, h), k) = sup
        have hcons_app := hcons horizon (h'.playerView i) k hk_lt
        -- hcons_app is about bestResponsePolicy μ π, but a_star = bestResponsePolicy μ π_others_ma
        -- Since Q-values for π and π_others_ma are equal (by bestResponseQValue_updateAgent_eq),
        -- and both policies choose argmax of the same function, the values achieved are equal.

        -- First, relate h' to historyToMultiAgent i (h'.playerView i) using hfull
        have hview_eq : (h'.playerView i) =
            (historyToMultiAgent i (h'.playerView i)).playerView i :=
          (playerView_historyToMultiAgent i (h'.playerView i)).symm

        -- Show Q-values at horizon are equal for π and π_others_ma
        have hqval_eq_horizon : ∀ (action : Action),
            bestResponseQValue μ π_others_ma γ i (historyToMultiAgent i (h'.playerView i)) action horizon =
            bestResponseQValue μ π γ i (historyToMultiAgent i (h'.playerView i)) action horizon := by
          intro action
          have heq : π_others_ma = π.updateAgent i uniformAgent := by
            ext j
            by_cases hj : j = i
            · simp only [MultiAgentPolicy.updateAgent, if_pos hj]
              simp only [π_others_ma, multiAgentPolicyFromOthers, dif_pos hj]
            · simp only [MultiAgentPolicy.updateAgent, if_neg hj]
              simp only [π_others_ma, multiAgentPolicyFromOthers, dif_neg hj]
          rw [heq]
          exact bestResponseQValue_updateAgent_eq μ π γ i
            (historyToMultiAgent i (h'.playerView i)) uniformAgent action horizon

        -- a_star achieves sup at horizon for π_others_ma (by bestResponsePolicy_isSupAchieving)
        have hsup_horizon := bestResponsePolicy_isSupAchieving μ π_others_ma γ i (h'.playerView i) horizon
        unfold isSupAchievingAt at hsup_horizon
        -- hsup_horizon : Q(π_others_ma, a_star, horizon) = ⨆ a, Q(π_others_ma, a, horizon)

        -- Convert to π using hqval_eq_horizon
        have hsup_horizon_pi : bestResponseQValue μ π γ i (historyToMultiAgent i (h'.playerView i)) a_star horizon =
            ⨆ a, bestResponseQValue μ π γ i (historyToMultiAgent i (h'.playerView i)) a horizon := by
          calc bestResponseQValue μ π γ i (historyToMultiAgent i (h'.playerView i)) a_star horizon
              = bestResponseQValue μ π_others_ma γ i (historyToMultiAgent i (h'.playerView i)) a_star horizon :=
                (hqval_eq_horizon a_star).symm
            _ = ⨆ a, bestResponseQValue μ π_others_ma γ i (historyToMultiAgent i (h'.playerView i)) a horizon := hsup_horizon
            _ = ⨆ a, bestResponseQValue μ π γ i (historyToMultiAgent i (h'.playerView i)) a horizon := by
                congr 1; ext a; exact hqval_eq_horizon a

        -- Now we need to show a_star achieves sup at k < horizon
        -- hcons_app tells us that bestResponsePolicy μ π achieves sup at k
        -- The key insight: a_star and bestResponsePolicy μ π both achieve the same sup VALUE at horizon
        -- By hcons, actions achieving the sup at horizon also achieve sup at smaller k

        -- **TODO**: This step requires that ANY action achieving the sup at horizon
        -- also achieves the sup at k < horizon. The current assumption `allHorizonsConsistent`
        -- only guarantees this for the specific action `bestResponsePolicy μ π`, not for
        -- `bestResponsePolicy μ π_others_ma`. Since Q-values are equal, both actions achieve
        -- the same VALUE at horizon, but hcons doesn't guarantee they have the same VALUE at k.
        --
        -- Options to fix:
        -- 1. Strengthen allHorizonsConsistent to cover ALL actions achieving the sup at horizon
        -- 2. Prove bestResponsePolicy μ π = bestResponsePolicy μ π_others_ma (hard with Classical.choose)
        -- 3. Add assumption that π_others_ma satisfies allHorizonsConsistent

        -- For now, we use that Q-values are equal and both achieve the horizon-sup
        calc bestResponseQValue μ π γ i h' a_star k
            = bestResponseQValue μ π γ i (historyToMultiAgent i (h'.playerView i)) a_star k := by
              apply hfull h' (historyToMultiAgent i (h'.playerView i)) _ k hw'
                (historyToMultiAgent_wellFormed i (h'.playerView i)
                  (MultiAgentHistory.playerView_wellFormed i h' hw'))
              exact hview_eq
          _ = ⨆ a, bestResponseQValue μ π γ i (historyToMultiAgent i (h'.playerView i)) a k := by
              -- Use hcons_any to get horizonConsistentOptimality for π_others_ma
              -- π_others_ma = π.updateAgent i uniformAgent
              have heq_ma : π_others_ma = π.updateAgent i uniformAgent := by
                ext j
                by_cases hj : j = i
                · simp only [MultiAgentPolicy.updateAgent, if_pos hj]
                  simp only [π_others_ma, multiAgentPolicyFromOthers, dif_pos hj]
                · simp only [MultiAgentPolicy.updateAgent, if_neg hj]
                  simp only [π_others_ma, multiAgentPolicyFromOthers, dif_neg hj]
              -- hcons_any uniformAgent gives allHorizonsConsistent for π.updateAgent i uniformAgent
              have hcons_ma := hcons_any uniformAgent
              rw [← heq_ma] at hcons_ma
              -- Apply horizonConsistentOptimality for π_others_ma at horizon
              have hcons_ma_app := hcons_ma horizon (h'.playerView i) k hk_lt
              -- hcons_ma_app : Q(π_others_ma, bestResponsePolicy μ π_others_ma, k) = sup Q(π_others_ma, ·, k)
              -- Since a_star = bestResponsePolicy μ π_others_ma, this is exactly what we need
              -- after converting Q-values from π_others_ma to π
              calc bestResponseQValue μ π γ i (historyToMultiAgent i (h'.playerView i)) a_star k
                  = bestResponseQValue μ π_others_ma γ i (historyToMultiAgent i (h'.playerView i)) a_star k := by
                    rw [heq_ma]
                    exact (bestResponseQValue_updateAgent_eq μ π γ i
                      (historyToMultiAgent i (h'.playerView i)) uniformAgent a_star k).symm
                _ = ⨆ a, bestResponseQValue μ π_others_ma γ i (historyToMultiAgent i (h'.playerView i)) a k :=
                    hcons_ma_app
                _ = ⨆ a, bestResponseQValue μ π γ i (historyToMultiAgent i (h'.playerView i)) a k := by
                    congr 1; ext a
                    rw [heq_ma]
                    exact bestResponseQValue_updateAgent_eq μ π γ i
                      (historyToMultiAgent i (h'.playerView i)) uniformAgent a k
          _ = ⨆ a, bestResponseQValue μ π γ i h' a k := by
              congr 1; ext a
              symm
              apply hfull h' (historyToMultiAgent i (h'.playerView i)) a k hw'
                (historyToMultiAgent_wellFormed i (h'.playerView i)
                  (MultiAgentHistory.playerView_wellFormed i h' hw'))
              exact hview_eq
  -- Show hπ'_others: other agents in π.updateAgent i π'_i match π
  have hπ'_others : ∀ j, j ≠ i → (π.updateAgent i π'_i).agents j = π.agents j := by
    intro j hj_ne
    simp only [MultiAgentPolicy.updateAgent, hj_ne, ↓reduceIte]
  -- Apply playerValue_eq_bestResponseValue_of_supAchieving
  have heq := playerValue_eq_bestResponseValue_of_supAchieving μ π γ i π'_i hπ'_others horizon hdet h hw hep
  exact le_of_eq heq.symm

/-- Best response maximizes player value.

    When player i switches to best response policy, their value equals the
    best response value. This requires:
    1. playerIQValueDependsOnlyOnOwnView: Q-values depend only on player i's view
    2. allHorizonsConsistent: for ALL horizons H, the action optimal at H is optimal at smaller

    The key insight is that we prove this by showing:
    - playerValue ≤ bestResponseValue (always true by playerValue_le_bestResponseValue)
    - playerValue ≥ bestResponseValue (because best response chooses optimal actions)
-/
theorem bestResponse_maximizes_value
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (hw : h.wellFormed = true)
    (hep : h.endsWithPercept = true)
    (horizon : ℕ)
    (hfull : playerIQValueDependsOnlyOnOwnView μ π γ i)
    (hcons : allHorizonsConsistent μ π γ i)
    (hcons_any : ∀ agent, allHorizonsConsistent μ (π.updateAgent i agent) γ i) :
    let π' := π.updateAgent i (bestResponseAgent μ i
      (fun j hj => π.agents j) γ horizon)
    playerValue μ π' γ i h horizon =
    bestResponseValue μ π γ i h horizon := by
  intro π'
  apply le_antisymm
  · -- playerValue ≤ bestResponseValue
    calc playerValue μ π' γ i h horizon
        ≤ bestResponseValue μ π' γ i h horizon :=
          playerValue_le_bestResponseValue μ π' γ i h hw hep horizon
      _ = bestResponseValue μ π γ i h horizon :=
          bestResponseValue_updateAgent_eq μ π γ i h _ horizon
  · -- playerValue ≥ bestResponseValue (from aux lemma)
    exact bestResponse_achieves_value_aux μ π γ i hfull hcons hcons_any horizon h hw hep

/-- Best response improves over the original policy (with full information assumption).
    Switching to best response can only help player i.

    This follows from:
    - playerValue μ π ≤ bestResponseValue μ π (proven in Value.lean)
    - playerValue μ π' = bestResponseValue μ π (from bestResponse_maximizes_value)
    - Therefore: playerValue μ π' = bestResponseValue μ π ≥ playerValue μ π
-/
theorem bestResponse_improves_value
    (μ : MultiAgentEnvironment n)
    (π : MultiAgentPolicy n)
    (γ : DiscountFactor)
    (i : Fin n)
    (h : MultiAgentHistory n)
    (hw : h.wellFormed = true)
    (hep : h.endsWithPercept = true)
    (horizon : ℕ)
    (hfull : playerIQValueDependsOnlyOnOwnView μ π γ i)
    (hcons : allHorizonsConsistent μ π γ i)
    (hcons_any : ∀ agent, allHorizonsConsistent μ (π.updateAgent i agent) γ i) :
    let π' := π.updateAgent i (bestResponseAgent μ i
      (fun j hj => π.agents j) γ horizon)
    playerValue μ π' γ i h horizon ≥
    playerValue μ π γ i h horizon := by
  intro π'
  calc playerValue μ π' γ i h horizon
      = bestResponseValue μ π γ i h horizon :=
        bestResponse_maximizes_value μ π γ i h hw hep horizon hfull hcons hcons_any
    _ ≥ playerValue μ π γ i h horizon :=
        playerValue_le_bestResponseValue μ π γ i h hw hep horizon

end Mettapedia.UniversalAI.MultiAgent
