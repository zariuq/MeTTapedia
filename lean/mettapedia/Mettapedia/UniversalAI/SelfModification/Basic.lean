import Mettapedia.UniversalAI.BayesianAgents

/-!
# Self-Modification in Rational Agents

This module formalizes the self-modification framework from:

  Everitt, Filan, Daswani, Hutter (2016). "Self-Modification of Policy and
  Utility Function in Rational Agents" (AGI-16, arXiv:1605.03142)

## Main Definitions

* `PolicyModAction` - Extended action: world action + next policy selection
* `UtilityModAction` - Extended action: world action + next utility selection
* `ModificationIndependent` - Property that function doesn't depend on past mods
* `History.worldPart` - History with modification records stripped (æ̌)

## Key Concepts

The paper defines two self-modification models:

1. **Policy Modification (Def 3)**: Actions select next policy
   a_t = (ǎ_t, π_{t+1}) where ǎ_t is world action, π_{t+1} is next policy

2. **Utility Modification (Def 5)**: Actions select next utility function
   a_t = (ǎ_t, u_{t+1}) where ǎ_t is world action, u_{t+1} is next utility

3. **Modification-Independence (Def 7)**: f(æ<t) = f(æ'<t) when æ̌<t = æ̌'<t
   This is the key technical assumption that enables Theorems 14-16.

## References

- Everitt et al., "Self-Modification of Policy and Utility Function in Rational Agents"
- Hutter (2005), "Universal Artificial Intelligence"
-/

namespace Mettapedia.UniversalAI.SelfModification

open BayesianAgents

/-! ## Policy Modification Model (Definition 3)

In the policy self-modification model, actions can modify the agent's future policy.
The action a_t = (ǎ_t, p_{t+1}) selects both:
- A world action ǎ_t ∈ Ǎ that affects the environment
- A policy name p_{t+1} ∈ P that determines the next policy π_{t+1} = ι(p_{t+1})
-/

/-- Policy names are natural numbers (representing program codes).
    In the paper, P is a set of names, and ι : P → Π maps names to policies.
    Using ℕ as the type of names (programs as Gödel numbers). -/
abbrev PolicyName := ℕ

/-- Extended action for policy self-modification (Definition 3).
    a_t = (ǎ_t, p_{t+1}) selects world action AND next policy name. -/
structure PolicyModAction where
  /-- World action ǎ_t that affects the environment -/
  worldAction : Action
  /-- Policy name p_{t+1} that determines next policy -/
  nextPolicyName : PolicyName
  deriving DecidableEq, Repr

/-- A policy interpreter maps policy names to actual policies.
    This is ι : P → Π in the paper. -/
abbrev PolicyInterpreter := PolicyName → (History → PolicyModAction)

/-- A self-modifying policy takes history and returns extended action. -/
abbrev SelfModPolicy := History → PolicyModAction

/-! ## Utility Modification Model (Definition 5)

In the utility self-modification model, actions can modify the agent's future
utility function. This indirectly changes the policy as well.
-/

/-- Utility function type: maps histories to real values in [0,1]. -/
abbrev Utility := History → ℝ

/-- Extended action for utility self-modification (Definition 5).
    a_t = (ǎ_t, u_{t+1}) selects world action AND next utility function. -/
structure UtilityModAction where
  /-- World action ǎ_t that affects the environment -/
  worldAction : Action
  /-- Next utility function u_{t+1} -/
  nextUtility : Utility

/-! ## Extended Histories

With self-modification, histories contain both world interactions and
modification records. We need to distinguish the full history from the
"world part" that strips modification records.
-/

/-- Extended history element: action (with modification) or percept -/
inductive ExtHistElem where
  | policyAct : PolicyModAction → ExtHistElem
  | utilityAct : UtilityModAction → ExtHistElem
  | per : Percept → ExtHistElem

/-- Extended history with modification records -/
abbrev ExtHistory := List ExtHistElem

/-- Convert extended history to standard history (strip modifications) -/
def ExtHistory.toHistory : ExtHistory → History
  | [] => []
  | ExtHistElem.policyAct a :: rest =>
      HistElem.act a.worldAction :: ExtHistory.toHistory rest
  | ExtHistElem.utilityAct a :: rest =>
      HistElem.act a.worldAction :: ExtHistory.toHistory rest
  | ExtHistElem.per x :: rest =>
      HistElem.per x :: ExtHistory.toHistory rest

/-- Extract just the world part (æ̌) from extended history -/
def ExtHistory.worldPart (h : ExtHistory) : History :=
  h.toHistory

/-- Check if extended history is well-formed -/
def ExtHistory.wellFormed (h : ExtHistory) : Bool :=
  h.toHistory.wellFormed

/-- Extract percepts from extended history -/
def ExtHistory.percepts : ExtHistory → List Percept
  | [] => []
  | ExtHistElem.policyAct _ :: rest => ExtHistory.percepts rest
  | ExtHistElem.utilityAct _ :: rest => ExtHistory.percepts rest
  | ExtHistElem.per x :: rest => x :: ExtHistory.percepts rest

/-- Extract world actions from extended history -/
def ExtHistory.worldActions : ExtHistory → List Action
  | [] => []
  | ExtHistElem.policyAct a :: rest => a.worldAction :: ExtHistory.worldActions rest
  | ExtHistElem.utilityAct a :: rest => a.worldAction :: ExtHistory.worldActions rest
  | ExtHistElem.per _ :: rest => ExtHistory.worldActions rest

/-- The number of interaction cycles -/
def ExtHistory.cycles (h : ExtHistory) : ℕ :=
  h.percepts.length

/-! ## Modification-Independence (Definition 7)

A function is modification-independent if its output depends only on the
world part of the history (æ̌), not on the modification records.

This is Assumption 8 in the paper: both ρ and u are modification-independent.
-/

/-- A function on extended histories is modification-independent if it only
    depends on the world part (Definition 7).

    f is modification-independent iff:
    æ̌<t = æ̌'<t implies f(æ<t) = f(æ'<t)

    In other words, the function "doesn't see" the modification components. -/
def ModificationIndependent {α : Type*} (f : ExtHistory → α) : Prop :=
  ∀ h h' : ExtHistory, h.worldPart = h'.worldPart → f h = f h'

/-- Helper: lift a standard history to extended history (all policy actions with name 0) -/
def toExtHistory : History → ExtHistory
  | [] => []
  | HistElem.act a :: rest => ExtHistElem.policyAct ⟨a, 0⟩ :: toExtHistory rest
  | HistElem.per x :: rest => ExtHistElem.per x :: toExtHistory rest

/-- Lifting and projecting gives identity on world part -/
theorem toExtHistory_worldPart (h : History) :
    (toExtHistory h).worldPart = h := by
  induction h with
  | nil => rfl
  | cons e rest ih =>
    cases e with
    | act a =>
      simp only [toExtHistory, ExtHistory.worldPart, ExtHistory.toHistory]
      simp only [ExtHistory.worldPart] at ih
      exact congrArg _ ih
    | per x =>
      simp only [toExtHistory, ExtHistory.worldPart, ExtHistory.toHistory]
      simp only [ExtHistory.worldPart] at ih
      exact congrArg _ ih

/-- A modification-independent function factors through worldPart -/
theorem mod_independent_factors {α : Type*} (f : ExtHistory → α)
    (hf : ModificationIndependent f) :
    ∃ g : History → α, ∀ h, f h = g h.worldPart := by
  use fun wh => f (toExtHistory wh)
  intro h
  apply hf
  rw [toExtHistory_worldPart]

/-- Modification-independence is preserved under function composition -/
theorem mod_independent_comp {α β : Type*} (f : ExtHistory → α) (g : α → β)
    (hf : ModificationIndependent f) : ModificationIndependent (g ∘ f) := by
  intro h h' heq
  simp [Function.comp]
  congr 1
  exact hf h h' heq

/-! ## Non-Modifying Policies

A policy is non-modifying if it always selects itself as the next policy.
These are the "safe" policies that don't change their own behavior.
-/

/-- A self-modifying policy is non-modifying if it always picks the same
    policy name (itself) for the next step. -/
def SelfModPolicy.isNonModifying (π : SelfModPolicy) (selfName : PolicyName) : Prop :=
  ∀ h : ExtHistory, (π h.toHistory).nextPolicyName = selfName

/-- A modification-independent policy only depends on world history -/
def SelfModPolicy.isModificationIndependent (π : SelfModPolicy) : Prop :=
  ∀ h h' : ExtHistory, h.worldPart = h'.worldPart →
    π h.toHistory = π h'.toHistory

/-- Non-modifying policies compose nicely: if π₁ always selects itself,
    the agent follows π₁ forever. -/
theorem nonmod_policy_stable (π : SelfModPolicy) (p : PolicyName)
    (ι : PolicyInterpreter) (hι : ι p = π)
    (hnonmod : π.isNonModifying p) :
    ∀ h : ExtHistory, ι ((π h.toHistory).nextPolicyName) = π := by
  intro h
  simp [hnonmod h, hι]

/-! ## Realistic vs Ignorant Measures

The paper defines two probability measures on histories:

1. **Realistic measure ρ_re**: Correctly models that self-modifications
   affect future actions. At time t, action is chosen by π_t (the policy
   that was selected at time t-1).

2. **Ignorant measure ρ_ig**: Ignores self-modification effects. At time t,
   action is (incorrectly) predicted to be chosen by initial policy π₁.

The key theorems depend on which measure the agent uses for planning.
-/

/-- The realistic measure correctly tracks which policy is active at each step.
    Under ρ_re, action a_t is chosen by π_t (from the previous action).

    This is implicit in the paper's Definition 3 and the value function
    definitions (Def 12). We capture it via the sequence of policies. -/
structure RealisticMeasureData where
  /-- Initial policy name -/
  initialPolicy : PolicyName
  /-- Policy interpreter -/
  interpret : PolicyInterpreter
  /-- Environment's conditional probability of percepts -/
  envProb : History → Percept → ENNReal

/-- The ignorant measure ignores self-modification effects.
    Under ρ_ig, ALL actions are predicted to be chosen by π₁.

    This corresponds to Definition 11's value function, which uses
    the initial policy π throughout the recursive expansion. -/
structure IgnorantMeasureData where
  /-- The (fixed) policy used for all predictions -/
  fixedPolicy : SelfModPolicy
  /-- Environment's conditional probability of percepts -/
  envProb : History → Percept → ENNReal

/-! ## Agent Performance (Definition 9)

The performance of an agent is measured by its ρ_re-expected u₁-utility.
That is, we evaluate using the realistic measure (correctly accounting for
self-modification effects) and the original utility function u₁.
-/

/-- Agent performance is ρ_re-expected u₁-utility (Definition 9).
    This is the "ground truth" evaluation of how well an agent does.

    Note: The agent might use a different measure (ρ_ig) or different
    utility function (u_{t+1}) internally for planning, but performance
    is always judged by this definition. -/
noncomputable def agentPerformance (_rmd : RealisticMeasureData) (_u₁ : Utility)
    (_γ : DiscountFactor) (_horizon : ℕ) : ℝ :=
  -- This would be the expected discounted u₁-utility under ρ_re
  -- For now, we defer the full measure-theoretic definition
  0  -- placeholder

/-! ## Key Assumption (Assumption 8)

The belief ρ and all utility functions u ∈ U are modification independent.

This is a technical assumption that enables the main theorems. It says that
the environment's behavior and the utility function only depend on world
actions and percepts, not on which policies/utilities were selected.
-/

/-- Assumption 8: Environment probability is modification-independent -/
def Environment.isModificationIndependent (envProb : History → Percept → ENNReal) : Prop :=
  ∀ x : Percept, ModificationIndependent (fun h => envProb h.worldPart x)

/-- Assumption 8: Utility function is modification-independent -/
def Utility.isModificationIndependent (u : Utility) : Prop :=
  ModificationIndependent (fun h => u h.worldPart)

end Mettapedia.UniversalAI.SelfModification
