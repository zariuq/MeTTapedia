import Mettapedia.UniversalAI.BayesianAgents
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Basic

/-!
# Joint Actions and Percepts for Multi-Agent RL

This file defines the basic structures for multi-agent reinforcement learning:
joint actions, joint percepts, and multi-agent histories.

## Main Definitions

* `JointAction n`: A tuple of n actions (one per agent)
* `JointPercept n`: A tuple of n percepts (one per agent)
* `MultiAgentHistory n`: Interleaved sequence of joint actions and joint percepts
* `playerView i`: Extract agent i's single-agent history from multi-agent history

## Key Design Decision

We use `Fin n → Action` rather than `Vector Action n` because:
1. Simpler reasoning (function application vs vector indexing)
2. Better compatibility with Mathlib's Fintype machinery
3. Easier to prove properties about "for all agents"

## References

- Leike, Taylor & Fallenstein (2016). "A Formal Solution to the Grain of Truth Problem"
- Shoham & Leyton-Brown (2008). "Multiagent Systems"

-/

namespace Mettapedia.UniversalAI.MultiAgent

open Mettapedia.UniversalAI.BayesianAgents

/-! ## Joint Actions -/

/-- A joint action is a function assigning an action to each of n agents.

    For n=2 agents, a joint action might be:
    - Agent 0 chooses Action.left
    - Agent 1 chooses Action.right

    We represent this as a function `Fin 2 → Action` rather than a tuple
    for easier reasoning about properties that hold "for all agents".
-/
def JointAction (n : ℕ) : Type := Fin n → Action

/-- Extract agent i's action from a joint action. -/
def JointAction.get {n : ℕ} (ja : JointAction n) (i : Fin n) : Action := ja i

/-- Construct a joint action from individual actions.

    This is just the identity function, but we define it for clarity. -/
def JointAction.mk {n : ℕ} (f : Fin n → Action) : JointAction n := f

/-- Two joint actions are equal if all agents choose the same actions. -/
@[ext]
theorem JointAction.ext {n : ℕ} (ja₁ ja₂ : JointAction n) :
    (∀ i : Fin n, ja₁ i = ja₂ i) → ja₁ = ja₂ := by
  intro h
  funext i
  exact h i

/-- Joint actions are finite when Action is finite. -/
instance {n : ℕ} : Fintype (JointAction n) := Pi.instFintype

/-- The number of possible joint actions is |Action|^n. -/
theorem JointAction.card {n : ℕ} :
    Fintype.card (JointAction n) = (Fintype.card Action) ^ n := by
  simp [JointAction, Fintype.card_fun]

/-! ## Joint Percepts -/

/-- A joint percept is a function assigning a percept to each of n agents.

    In multi-agent settings, each agent may observe different information.
    For example, in a card game:
    - Agent 0 sees their own cards + public cards
    - Agent 1 sees their own cards + public cards (different from Agent 0)
-/
def JointPercept (n : ℕ) : Type := Fin n → Percept

/-- Extract agent i's percept from a joint percept. -/
def JointPercept.get {n : ℕ} (jp : JointPercept n) (i : Fin n) : Percept := jp i

/-- Construct a joint percept from individual percepts. -/
def JointPercept.mk {n : ℕ} (f : Fin n → Percept) : JointPercept n := f

/-- Two joint percepts are equal if all agents receive the same percepts. -/
@[ext]
theorem JointPercept.ext {n : ℕ} (jp₁ jp₂ : JointPercept n) :
    (∀ i : Fin n, jp₁ i = jp₂ i) → jp₁ = jp₂ := by
  intro h
  funext i
  exact h i

/-- Joint percepts are finite when Percept is finite. -/
instance {n : ℕ} : Fintype (JointPercept n) := Pi.instFintype

/-- The number of possible joint percepts is |Percept|^n. -/
theorem JointPercept.card {n : ℕ} :
    Fintype.card (JointPercept n) = (Fintype.card Percept) ^ n := by
  simp [JointPercept, Fintype.card_fun]

/-! ## Joint History Elements -/

/-- A joint history element is either a joint action or a joint percept.

    Multi-agent histories are sequences of joint actions and joint percepts:
    ⟨ja₀, jp₀, ja₁, jp₁, ja₂, jp₂, ...⟩

    This is analogous to single-agent HistElem but for multiple agents. -/
inductive JointHistElem (n : ℕ) : Type
  | act : JointAction n → JointHistElem n
  | per : JointPercept n → JointHistElem n

/-- Extract agent i's view of a joint history element. -/
def JointHistElem.playerView {n : ℕ} (jhe : JointHistElem n) (i : Fin n) : HistElem :=
  match jhe with
  | JointHistElem.act ja => HistElem.act (ja i)
  | JointHistElem.per jp => HistElem.per (jp i)

/-! ## Multi-Agent History -/

/-- A multi-agent history is a list of joint history elements.

    Like single-agent History, but each element contains actions/percepts
    for ALL agents simultaneously.

    Example for 2 agents, 3 timesteps:
    [act ⟨a₀₀, a₁₀⟩, per ⟨p₀₀, p₁₀⟩,
     act ⟨a₀₁, a₁₁⟩, per ⟨p₀₁, p₁₁⟩,
     act ⟨a₀₂, a₁₂⟩, per ⟨p₀₂, p₁₂⟩]
-/
abbrev MultiAgentHistory (n : ℕ) := List (JointHistElem n)

namespace MultiAgentHistory

/-- The empty multi-agent history. -/
def empty {n : ℕ} : MultiAgentHistory n := []

/-- Check if a multi-agent history is well-formed.

    A history is well-formed if actions and percepts alternate properly.
    Valid histories: [], [act], [act, per], [act, per, act], [act, per, act, per], ...

    This mirrors the single-agent definition which allows ending with an action
    (needed for environment probability queries after an action is taken). -/
def wellFormed {n : ℕ} (h : MultiAgentHistory n) : Bool :=
  match h with
  | [] => true
  | [JointHistElem.act _] => true  -- Can end with action (like single-agent)
  | JointHistElem.act _ :: JointHistElem.per _ :: rest => wellFormed rest
  | _ => false

/-- The number of complete action-percept cycles in the history. -/
def cycles {n : ℕ} (h : MultiAgentHistory n) : ℕ :=
  h.length / 2

/-- Extract the list of joint actions from a history. -/
def jointActions {n : ℕ} : MultiAgentHistory n → List (JointAction n)
  | [] => []
  | JointHistElem.act ja :: rest => ja :: jointActions rest
  | JointHistElem.per _ :: rest => jointActions rest

/-- Extract the list of joint percepts from a history. -/
def jointPercepts {n : ℕ} : MultiAgentHistory n → List (JointPercept n)
  | [] => []
  | JointHistElem.act _ :: rest => jointPercepts rest
  | JointHistElem.per jp :: rest => jp :: jointPercepts rest

/-! NOTE: Well-formed histories have equal numbers of actions and percepts

This property (`wellFormed h → jointActions h.length = jointPercepts h.length`)
is straightforward to prove by induction on the `wellFormed` structure.

Proof sketch: Observe that each valid step in a well-formed history adds
exactly one action and one percept, maintaining the balance.

Will be proven when needed (estimated ~10 lines).
-/

/-- Extract agent i's single-agent history from a multi-agent history.

    This is the KEY function connecting multi-agent and single-agent frameworks.
    Agent i "sees" only their own actions and percepts, not others'. -/
def playerView {n : ℕ} (i : Fin n) (h : MultiAgentHistory n) : History :=
  h.map (fun jhe => jhe.playerView i)

/-- Player view of a well-formed multi-agent history is well-formed.

    The `map` function preserves the alternating action/percept structure
    because `jhe.playerView i` maps actions to actions and percepts to percepts.

    Multi-agent wellFormed accepts: [], [act], [act,per], [act,per,act], ...
    Single-agent wellFormed accepts: [], [act], [act,per], [act,per,act], ...
    These are identical, so the implication is direct.
-/
theorem playerView_wellFormed {n : ℕ} (i : Fin n) (h : MultiAgentHistory n)
    (hw : h.wellFormed = true) : (h.playerView i).wellFormed = true := by
  -- Use recursion on the structure, with termination by list length
  match h with
  | [] => rfl
  | [JointHistElem.act _] =>
    -- Single action → [HistElem.act _] is well-formed
    simp only [playerView, List.map_cons, List.map_nil, JointHistElem.playerView,
               History.wellFormed]
  | JointHistElem.act ja :: JointHistElem.per jp :: rest =>
    -- [act, per, ...rest] → wellFormed rest must be true
    simp only [wellFormed] at hw
    simp only [playerView, List.map_cons, JointHistElem.playerView, History.wellFormed]
    exact playerView_wellFormed i rest hw
  | JointHistElem.per _ :: _ =>
    -- Multi-agent wellFormed returns false for histories starting with per
    simp only [wellFormed] at hw; cases hw
  | JointHistElem.act _ :: JointHistElem.act _ :: _ =>
    -- Two actions in a row is not well-formed
    simp only [wellFormed] at hw; cases hw
termination_by h.length

/-- Check if a well-formed history ends with a percept (or is empty).
    These are the histories where we can extend with an action. -/
def endsWithPercept {n : ℕ} : MultiAgentHistory n → Bool
  | [] => true
  | [JointHistElem.act _] => false
  | JointHistElem.act _ :: JointHistElem.per _ :: rest => endsWithPercept rest
  | _ => false  -- ill-formed cases

/-- Extending a history that ends with percept (or is empty) with an action
    preserves well-formedness. -/
theorem wellFormed_append_act {n : ℕ} (h : MultiAgentHistory n) (ja : JointAction n)
    (hw : h.wellFormed = true) (hep : h.endsWithPercept = true) :
    (h ++ [JointHistElem.act ja]).wellFormed = true := by
  match h with
  | [] => rfl
  | [JointHistElem.act _] =>
    -- [act] has endsWithPercept = false, contradicts hep
    simp only [endsWithPercept] at hep; cases hep
  | JointHistElem.act _ :: JointHistElem.per _ :: rest =>
    simp only [wellFormed] at hw
    simp only [endsWithPercept] at hep
    simp only [List.cons_append, List.nil_append, wellFormed]
    exact wellFormed_append_act rest ja hw hep
  | JointHistElem.per _ :: _ =>
    simp only [wellFormed] at hw; cases hw
  | JointHistElem.act _ :: JointHistElem.act _ :: _ =>
    simp only [wellFormed] at hw; cases hw
termination_by h.length

/-- Extending a history that ends with percept (or is empty) with action then percept
    preserves well-formedness and the history still ends with percept. -/
theorem wellFormed_append_act_per {n : ℕ} (h : MultiAgentHistory n)
    (ja : JointAction n) (jp : JointPercept n)
    (hw : h.wellFormed = true) (hep : h.endsWithPercept = true) :
    (h ++ [JointHistElem.act ja, JointHistElem.per jp]).wellFormed = true ∧
    (h ++ [JointHistElem.act ja, JointHistElem.per jp]).endsWithPercept = true := by
  match h with
  | [] => simp [wellFormed, endsWithPercept]
  | [JointHistElem.act _] =>
    simp only [endsWithPercept] at hep; cases hep
  | JointHistElem.act _ :: JointHistElem.per _ :: rest =>
    simp only [wellFormed] at hw
    simp only [endsWithPercept] at hep
    simp only [List.cons_append, List.nil_append, wellFormed, endsWithPercept]
    exact wellFormed_append_act_per rest ja jp hw hep
  | JointHistElem.per _ :: _ =>
    simp only [wellFormed] at hw; cases hw
  | JointHistElem.act _ :: JointHistElem.act _ :: _ =>
    simp only [wellFormed] at hw; cases hw
termination_by h.length

/-- The empty history ends with percept (trivially). -/
@[simp]
theorem empty_endsWithPercept {n : ℕ} : (empty : MultiAgentHistory n).endsWithPercept = true := rfl

end MultiAgentHistory

/-! ## Examples and Properties -/

/-- Example: 2-player joint action where both choose 'left'. -/
example : JointAction 2 := fun i =>
  match i with
  | ⟨0, _⟩ => Action.left
  | ⟨1, _⟩ => Action.left
  | ⟨n+2, h⟩ => by omega

/-- Example: 2-player joint percept where both observe true with reward 1. -/
example : JointPercept 2 := fun i =>
  match i with
  | ⟨0, _⟩ => Percept.mk true true
  | ⟨1, _⟩ => Percept.mk true true
  | ⟨n+2, h⟩ => by omega

/-- The empty history is well-formed. -/
theorem empty_wellFormed {n : ℕ} : (MultiAgentHistory.empty : MultiAgentHistory n).wellFormed = true := by
  rfl

/-- The empty history has zero cycles. -/
theorem empty_cycles {n : ℕ} : (MultiAgentHistory.empty : MultiAgentHistory n).cycles = 0 := by
  simp [MultiAgentHistory.cycles, MultiAgentHistory.empty]

end Mettapedia.UniversalAI.MultiAgent
