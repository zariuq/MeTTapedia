import Mettapedia.UniversalAI.SelfModification.Basic

/-!
# Value Functions for Self-Modifying Agents

This module defines the three types of value functions from Everitt et al. (2016):

1. **Hedonistic** (Definition 10): Uses future utility u_{t+1}
2. **Ignorant** (Definition 11): Uses current utility u_t with ignorant measure ρ_ig
3. **Realistic** (Definition 12): Uses current utility u_t with realistic measure ρ_re

The key insight is that these differ in:
- Which utility function is used to evaluate future states
- Which measure (realistic vs ignorant) predicts future action distributions

## Key Results (to prove)

* Theorem 14: Hedonistic agents will self-modify to u(·)=1
* Theorem 15: Ignorant agents are indifferent to self-modification
* Theorem 16: Realistic agents make only safe (value-preserving) modifications

## References

- Everitt et al., "Self-Modification of Policy and Utility Function in Rational Agents" (2016)
-/

namespace Mettapedia.UniversalAI.SelfModification

open BayesianAgents

/-! ## Iterative Value Function Forms (Lemma 13)

The paper's Lemma 13 shows that the three Q-value functions can be written as:

* Q^{he,π}(æ<t, a_t) = E_{ρ^π_ig}[Σ_{k≥t} γ^{k-t} u_{k+1}(æ̌_{1:k}) | æ̌<t, ǎ_t]
* Q^{ig,π}_t(æ<t, a_t) = E_{ρ^π_ig}[Σ_{k≥t} γ^{k-t} u_t(æ̌_{1:k}) | æ̌<t, ǎ_t]
* Q^{re,π}_t(æ<t, a_t) = E_{ρ^π_re}[Σ_{k≥t} γ^{k-t} u_t(æ̌_{1:k}) | æ̌<t, ǎ_t]

The differences are:
- Hedonistic uses u_{k+1} (future utility) vs current u_t
- Ignorant uses ρ_ig vs realistic uses ρ_re
-/

/-! ## Hedonistic Value Functions (Definition 10)

A hedonistic agent optimizes the hedonistic value functions:

  V^{he,π}(æ<t) = Q^{he,π}(æ<t, π(æ<t))
  Q^{he,π}(æ<t, a_t) = E_{e_t}[u_{t+1}(æ̌_{1:t}) + γV^{he,π}(æ_{1:t}) | æ̌<t, ǎ_t]

Key characteristic: Evaluates by FUTURE utility u_{t+1}, not current u_t.
This means the agent cares about its future self's satisfaction.
-/

/-- Data for computing hedonistic value: environment, policy interpreter, discount -/
structure HedonisticValueData where
  /-- Environment probability -/
  envProb : History → Percept → ENNReal
  /-- Initial policy -/
  initialPolicy : SelfModPolicy
  /-- Discount factor -/
  γ : DiscountFactor

/-- Hedonistic Q-value (Definition 10, Equation 4).

    Uses u_{t+1} (the utility selected by action a_t) for evaluation.
    This is what makes hedonistic agents vulnerable to self-modification:
    they optimize for their future self's satisfaction, not current goals. -/
noncomputable def qValueHedonistic (data : HedonisticValueData)
    (h : History) (a : PolicyModAction) (nextUtility : Utility) (horizon : ℕ) : ℝ :=
  match horizon with
  | 0 => 0
  | n + 1 =>
    if ¬h.wellFormed then 0
    else
      let ha := h ++ [HistElem.act a.worldAction]
      -- Sum over possible percepts
      let percepts : List Percept := [⟨false, false⟩, ⟨false, true⟩, ⟨true, false⟩, ⟨true, true⟩]
      percepts.foldl (fun sum x =>
        let prob_x := (data.envProb ha x).toReal
        let hax := ha ++ [HistElem.per x]
        -- Key: use nextUtility (u_{t+1}) not some fixed u_t
        let immediate := nextUtility hax
        let next_action := data.initialPolicy hax
        let future := qValueHedonistic data hax next_action nextUtility n
        sum + prob_x * (immediate + data.γ.val * future)
      ) 0

/-- Hedonistic V-value (Definition 10, Equation 3). -/
noncomputable def vValueHedonistic (data : HedonisticValueData)
    (h : History) (nextUtility : Utility) (horizon : ℕ) : ℝ :=
  let a := data.initialPolicy h
  qValueHedonistic data h a nextUtility horizon

/-! ## Ignorant Value Functions (Definition 11)

An ignorant agent optimizes the ignorant value functions:

  V^{ig,π}_t(æ<k) = Q^{ig,π}_t(æ<k, π(æ<k))
  Q^{ig,π}_t(æ<k, a_k) = E_{e_t}[u_t(æ̌_{1:k}) + γV^{ig,π}_t(æ_{1:k}) | æ̌<k, ǎ_k]

Key characteristics:
- Uses CURRENT utility u_t for evaluation (good!)
- But uses π (initial policy) for all future predictions (bad!)
- Ignores that self-modifications change future behavior

This is called "ignorant" because the agent doesn't anticipate that its
self-modifications will affect its future actions.
-/

/-- Data for computing ignorant value: environment, fixed policy, current utility -/
structure IgnorantValueData where
  /-- Environment probability -/
  envProb : History → Percept → ENNReal
  /-- Fixed policy used for ALL predictions (ignores self-modification) -/
  fixedPolicy : SelfModPolicy
  /-- Current utility function u_t (fixed throughout) -/
  currentUtility : Utility
  /-- Discount factor -/
  γ : DiscountFactor

/-- Ignorant Q-value (Definition 11, Equation 6).

    Uses u_t (current utility) for evaluation, but predicts future actions
    using the fixed policy π (ignoring self-modifications). -/
noncomputable def qValueIgnorant (data : IgnorantValueData)
    (h : History) (a : PolicyModAction) (horizon : ℕ) : ℝ :=
  match horizon with
  | 0 => 0
  | n + 1 =>
    if ¬h.wellFormed then 0
    else
      let ha := h ++ [HistElem.act a.worldAction]
      let percepts : List Percept := [⟨false, false⟩, ⟨false, true⟩, ⟨true, false⟩, ⟨true, true⟩]
      percepts.foldl (fun sum x =>
        let prob_x := (data.envProb ha x).toReal
        let hax := ha ++ [HistElem.per x]
        -- Key: use currentUtility (u_t), not future utility
        let immediate := data.currentUtility hax
        -- Key: predict next action using fixedPolicy, ignoring self-modification
        let next_action := data.fixedPolicy hax
        let future := qValueIgnorant data hax next_action n
        sum + prob_x * (immediate + data.γ.val * future)
      ) 0

/-- Ignorant V-value (Definition 11, Equation 5). -/
noncomputable def vValueIgnorant (data : IgnorantValueData)
    (h : History) (horizon : ℕ) : ℝ :=
  let a := data.fixedPolicy h
  qValueIgnorant data h a horizon

/-! ## Realistic Value Functions (Definition 12)

A realistic agent optimizes the realistic value functions:

  V^{re,π}_t(æ<k) = Q^{re}_t(æ<k, π(æ<k))
  Q^{re}_t(æ<k, a_k) = E_{e_k}[u_t(æ̌_{1:k}) + γV^{re,π_{k+1}}_t(æ_{1:k}) | æ̌<k, ǎ_k]

Key characteristics:
- Uses CURRENT utility u_t for evaluation (good!)
- Uses π_{k+1} from the action for future predictions (good!)
- Correctly anticipates that self-modifications affect future behavior

This is the "safe" value function: agents optimizing it make only
modifications that don't harm their original goals.
-/

/-- Data for computing realistic value: environment, policy interpreter, current utility -/
structure RealisticValueData where
  /-- Environment probability -/
  envProb : History → Percept → ENNReal
  /-- Policy interpreter (maps names to policies) -/
  policyInterp : PolicyInterpreter
  /-- Current utility function u_t (fixed, evaluates the original goal) -/
  currentUtility : Utility
  /-- Discount factor -/
  γ : DiscountFactor

/-- Realistic Q-value (Definition 12, Equation 8).

    Uses u_t (current utility) for evaluation AND correctly uses π_{k+1}
    (the policy selected by action a_k) for future predictions. -/
noncomputable def qValueRealistic (data : RealisticValueData)
    (h : History) (a : PolicyModAction) (horizon : ℕ) : ℝ :=
  match horizon with
  | 0 => 0
  | n + 1 =>
    if ¬h.wellFormed then 0
    else
      let ha := h ++ [HistElem.act a.worldAction]
      let percepts : List Percept := [⟨false, false⟩, ⟨false, true⟩, ⟨true, false⟩, ⟨true, true⟩]
      percepts.foldl (fun sum x =>
        let prob_x := (data.envProb ha x).toReal
        let hax := ha ++ [HistElem.per x]
        -- Key: use currentUtility (u_t), not future utility
        let immediate := data.currentUtility hax
        -- Key: use the policy π_{k+1} selected by action a
        let nextPolicy := data.policyInterp a.nextPolicyName
        let next_action := nextPolicy hax
        let future := qValueRealistic data hax next_action n
        sum + prob_x * (immediate + data.γ.val * future)
      ) 0

/-- Realistic V-value (Definition 12, Equation 7).

    Note: The policy argument π to V^re is superfluous since the action
    determines the next policy π_{k+1}. -/
noncomputable def vValueRealistic (data : RealisticValueData)
    (initialPolicy : SelfModPolicy) (h : History) (horizon : ℕ) : ℝ :=
  let a := initialPolicy h
  qValueRealistic data h a horizon

/-! ## Optimal Value Functions

The optimal Q and V values are defined as suprema over all policies.
-/

/-- Optimal hedonistic Q-value: sup_π Q^{he,π} -/
noncomputable def optimalQValueHedonistic (data : HedonisticValueData)
    (h : History) (a : PolicyModAction) (nextUtility : Utility) (horizon : ℕ) : ℝ :=
  -- For now, just use the value for the given policy
  -- Full optimization would require sup over all policies
  qValueHedonistic data h a nextUtility horizon

/-- Optimal ignorant Q-value: sup_π Q^{ig,π} -/
noncomputable def optimalQValueIgnorant (data : IgnorantValueData)
    (h : History) (a : PolicyModAction) (horizon : ℕ) : ℝ :=
  qValueIgnorant data h a horizon

/-- Optimal realistic Q-value: sup_π Q^{re,π} -/
noncomputable def optimalQValueRealistic (data : RealisticValueData)
    (h : History) (a : PolicyModAction) (horizon : ℕ) : ℝ :=
  qValueRealistic data h a horizon

/-! ## Key Comparison Table (Table 1 from paper)

| Value | Utility | Policy | Self-mod | Primary risk |
|-------|---------|--------|----------|--------------|
| Q^he  | Future  | Either | Promotes | Survival agent |
| Q^ig  | Current | Current| Indifferent | Self-damage |
| Q^re  | Current | Future | Demotes  | Resists modification |

The differences are:
- Q^he uses u_{k+1} (future utility) → promotes self-modification
- Q^ig uses u_t but predicts via π (current) → indifferent to self-mod
- Q^re uses u_t and predicts via π_{k+1} (future) → resists harmful mods
-/

/-! ## The Maximum Utility Function

This is the "bad" utility function that hedonistic agents will self-modify to.
-/

/-- The constant-1 utility function (maximum possible utility for all histories). -/
def maxUtility : Utility := fun _ => 1

/-- Maximum utility gives value 1 for any history.
    The discounted sum ∑γⁿ converges to 1/(1-γ) when γ < 1. -/
theorem maxUtility_value (γ : DiscountFactor) (_hγ : γ.val < 1) :
    ∀ h : History, maxUtility h = 1 := by
  intro h
  rfl

end Mettapedia.UniversalAI.SelfModification
