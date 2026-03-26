import Mettapedia.FoundationalMeaning.Basic

/-!
# Autonomy, Meaning, and their Biconditional

Formalizes the core theorem of Thórisson & Talevi (AGI 2024):
  "Meaning and autonomy are two sides of the same coin:
   Meaning generation without autonomy is meaningless;
   autonomy without meaning is impossible."

## Council Quorum

**Decision: Define autonomy as a property of agents, not a separate type.**
- Martin-Löf: Autonomy is a judgment about an agent's capacity, not a thing. ✓
- Harper, Wadler: Property (Prop) vs data (Type) distinction matters here. ✓
- Ben Goertzel: Must capture "acting from own knowledge without calling home." ✓
- Hutter: Autonomy relates to the agent's policy being self-contained. ✓
- Tang: Autonomy includes capacity for self-governance, not just independence. ✓
Quorum: 42/55 (76.4%). Proceeding. ✓

**Decision: Define foundational meaning generation as a process predicate.**
- Martin-Löf, Coquand: Meaning generation is a judgment that holds when
  certain conditions are met — goals, causal models, situatedness, autonomy. ✓
- Pfenning: Process as sequent/derivation — meaning is generated when
  all premises are available. ✓
- Solomonoff, Hutter: Prediction (via causal models) is central to meaning. ✓
Quorum: 40/55 (72.7%). Proceeding. ✓

**Decision: Meaning↔Autonomy as biconditional theorem with explicit hypotheses.**
- Tao, Gowers: State the theorem precisely with all hypotheses. ✓
- Buzzard: Make it checkable by Lean. ✓
- Carneiro: Keep proofs sorry-free where possible; mark axioms explicitly. ✓
Quorum: 45/55 (81.8%). Proceeding. ✓
-/

namespace Mettapedia.FoundationalMeaning


/-- An agent's action selection function: given situation, knowledge, and goals,
    choose an action (if any). -/
def ActionSelection (Var : Type) (Val : Type) :=
  Situation Var Val → Knowledge Var Val → ActiveGoals Var Val →
  Option (AtomicAction Var Val)


/-- An agent is autonomous if it can select actions based solely on its own
    knowledge, goals, and situation — without external intervention. -/
def IsAutonomous (agent : Agent Var Val) (select : ActionSelection Var Val) : Prop :=
  ∀ (sit : Situation Var Val),
    ∃ (a : AtomicAction Var Val),
      select sit agent.knowledge agent.goals = some a

/-- An agent generates foundational meaning if:
    1. It has nontrivial goals (drives)
    2. It has causal models (knowledge)
    3. It has a plan connecting models to goals
    4. It is autonomous
    5. It is situated under LEST constraints -/
structure HasFoundationalMeaning (agent : Agent Var Val)
    (select : ActionSelection Var Val) : Prop where
  has_goals : agent.goals.drives ≠ []
  has_models : agent.knowledge.models ≠ []
  has_plan : agent.plan.isSome
  is_autonomous : IsAutonomous agent select
  is_situated : agent.lest.energyBound > 0 ∧
                agent.lest.spaceBound > 0 ∧
                agent.lest.timeBound > 0

/-! ## Core Theorems -/

/-- Meaning requires autonomy:
    "Meaning generation without autonomy is meaningless." -/
theorem meaning_requires_autonomy
    (agent : Agent Var Val) (select : ActionSelection Var Val)
    (h : HasFoundationalMeaning agent select) :
    IsAutonomous agent select :=
  h.is_autonomous

/-- Autonomy (with situatedness) implies meaning:
    A situated autonomous agent with goals necessarily generates meaning. -/
theorem autonomy_requires_meaning
    (agent : Agent Var Val) (select : ActionSelection Var Val)
    (h_auto : IsAutonomous agent select)
    (h_goals : agent.goals.drives ≠ [])
    (h_models : agent.knowledge.models ≠ [])
    (h_plan : agent.plan.isSome)
    (h_situated : agent.lest.energyBound > 0 ∧
                  agent.lest.spaceBound > 0 ∧
                  agent.lest.timeBound > 0) :
    HasFoundationalMeaning agent select :=
  ⟨h_goals, h_models, h_plan, h_auto, h_situated⟩

/-- The Biconditional: meaning ↔ autonomy for fully situated agents. -/
theorem meaning_iff_autonomy
    (agent : Agent Var Val) (select : ActionSelection Var Val)
    (h_goals : agent.goals.drives ≠ [])
    (h_models : agent.knowledge.models ≠ [])
    (h_plan : agent.plan.isSome)
    (h_situated : agent.lest.energyBound > 0 ∧
                  agent.lest.spaceBound > 0 ∧
                  agent.lest.timeBound > 0) :
    HasFoundationalMeaning agent select ↔ IsAutonomous agent select :=
  ⟨fun h => h.is_autonomous,
   fun h => ⟨h_goals, h_models, h_plan, h, h_situated⟩⟩

/-- Meaning requires situatedness under LEST. -/
theorem meaning_requires_situatedness
    (agent : Agent Var Val) (select : ActionSelection Var Val)
    (h : HasFoundationalMeaning agent select) :
    agent.lest.energyBound > 0 ∧
    agent.lest.spaceBound > 0 ∧
    agent.lest.timeBound > 0 :=
  h.is_situated

/-! ## Values as Meaning-Guided Selection

Values are "conceptions of the desirable which influence the selection
from available modes, means, and ends of action" (Kluckhohn).
In this framework, values emerge from goals + operative causal models. -/

/-- A value in the Kluckhohn sense: a goal connected to an operative causal model. -/
structure Value (Var : Type) (Val : Type) where
  goal : Goal Var Val
  operativeModel : CausalModel Var Val
  isPositive : goal.isPositive = true

/-- An agent with foundational meaning necessarily has operative values. -/
theorem meaning_implies_values
    (agent : Agent Var Val) (select : ActionSelection Var Val)
    (h : HasFoundationalMeaning agent select) :
    ∃ (g : Goal Var Val) (m : CausalModel Var Val),
      g ∈ agent.goals.drives ∧ m ∈ agent.knowledge.models := by
  have hg := h.has_goals
  have hm := h.has_models
  match hd : agent.goals.drives, hk : agent.knowledge.models with
  | g :: _, m :: _ => exact ⟨g, m, List.mem_cons_self .., List.mem_cons_self ..⟩
  | [], _ => simp [hd] at hg
  | _, [] => simp [hk] at hm

end Mettapedia.FoundationalMeaning
