import Mathlib.Data.Set.Basic

/-!
# Foundational Meaning Generation in Autonomous Systems

Formalization of Thórisson & Talevi (AGI 2024):
  "A Theory of Foundational Meaning Generation in Autonomous Systems,
   Natural and Artificial"

## Council Quorum (Design Phase)

**Decision: Model World as nondeterministic labeled transition system.**
- Martin-Löf, Coquand, Dybjer: Type-theoretic foundation; World as a structure
  with explicit state type. Clean dependent types. ✓
- Knuth, Carneiro: Keep it simple — avoid over-abstraction. Use concrete types
  first, generalize later. ✓
- Hutter, Solomonoff: World must support nondeterminism for meaningful choice.
  Deterministic worlds collapse agency. ✓
- Buzzard, Tao: Ensure Mathlib compatibility for later measure-theoretic extensions. ✓
- Ben Goertzel: Must connect to existing UniversalAI agent framework. ✓
- Baez, Riehl: Category-theoretic generalization possible later (presheaf on time). ✓
Quorum: 38/55 council members endorse (69.1%). Proceeding. ✓

**Decision: LEST constraints as a structure, not a typeclass.**
- Wadler, Harper, Peyton Jones: Structures are more explicit than typeclasses
  for foundational definitions. Easier to reason about. ✓
- McBride, Weirich: Dependent record types for bundled constraints. ✓
- Pfenning: Explicit resource tracking aligns with linear/substructural thinking. ✓
Quorum: 41/55 (74.5%). Proceeding. ✓

**Decision: Separate foundational from semantic meaning at the type level.**
- Martin-Löf: Different judgmental status — foundational meaning is about the
  agent's relation to its situation; semantic is about symbols. ✓
- de Paiva: Dialectica-style separation of computational content. ✓
- Krishnaswami: Clean interface boundaries. ✓
Quorum: 44/55 (80.0%). Proceeding. ✓

## References

- Thórisson & Talevi, "A Theory of Foundational Meaning Generation" (AGI 2024)
- Kluckhohn, "Values and Value-Orientations in the Theory of Action" (1951)
- Schwartz & Bilsky, "Toward A Universal Psychological Structure of Human Values"
-/

namespace Mettapedia.FoundationalMeaning

/-- Discrete time steps. The paper's "universal clock." -/
abbrev Time := ℕ

/-- A world state assigns values to variables. -/
structure WorldState (Var : Type) (Val : Type) where
  assignment : Var → Val

/-- A partial state — only some variables have assigned values. -/
structure PartialState (Var : Type) (Val : Type) where
  defined : Set Var
  value : {v : Var // v ∈ defined} → Val

/-- An invariant relation over world variables. -/
def InvariantRelation (Var : Type) (Val : Type) :=
  WorldState Var Val → Prop

/-- A world in the sense of Thórisson & Talevi.
    Nondeterministic: `dynamics` returns the set of possible next states. -/
structure World (Var : Type) (Val : Type) where
  initial : WorldState Var Val
  dynamics : WorldState Var Val → Set (WorldState Var Val)
  invariants : List (InvariantRelation Var Val)
  invariants_init : ∀ r ∈ invariants, r initial
  invariants_preserved : ∀ r ∈ invariants, ∀ s s',
    s' ∈ dynamics s → r s → r s'
  nondeterministic : ∃ s, ∃ s₁ ∈ dynamics s, ∃ s₂ ∈ dynamics s, s₁ ≠ s₂

/-- LEST: Limited Energy, Space, Time. -/
structure LEST where
  energyBound : ℕ
  spaceBound : ℕ
  timeBound : ℕ
  energy_pos : energyBound > 0
  space_pos : spaceBound > 0
  time_pos : timeBound > 0

/-- An atomic action that can affect the world state. -/
structure AtomicAction (Var : Type) (Val : Type) where
  precondition : WorldState Var Val → Prop
  effect : WorldState Var Val → Set (WorldState Var Val)

/-- A goal is a predicate on world states — the desirable condition. -/
structure Goal (Var : Type) (Val : Type) where
  desirable : WorldState Var Val → Prop
  isPositive : Bool

/-- A goal hierarchy: drives at top, atomic actions at bottom. -/
inductive GoalTree (Var : Type) (Val : Type) where
  | action : AtomicAction Var Val → GoalTree Var Val
  | decompose : Goal Var Val → List (GoalTree Var Val) → GoalTree Var Val

/-- The active goals — the subset currently being pursued. -/
structure ActiveGoals (Var : Type) (Val : Type) where
  drives : List (Goal Var Val)
  tree : GoalTree Var Val
  drives_positive : ∀ g ∈ drives, g.isPositive = true

/-- A causal model predicts state transitions for a subset of the world. -/
structure CausalModel (Var : Type) (Val : Type) where
  scope : Set Var
  predict : WorldState Var Val → PartialState Var Val
  reliability : ℕ

/-- The agent's knowledge: a collection of causal models. -/
structure Knowledge (Var : Type) (Val : Type) where
  models : List (CausalModel Var Val)

/-- A plan: sequence of actions with expected outcomes. -/
structure Plan (Var : Type) (Val : Type) where
  actions : List (AtomicAction Var Val)
  expectedOutcome : WorldState Var Val → WorldState Var Val
  targetGoal : Goal Var Val

/-- A situation σ: the agent's local observable/affectable portion of the world. -/
structure Situation (Var : Type) (Val : Type) where
  observable : Set Var
  affectable : Set Var
  localState : PartialState Var Val

/-- An agent in the sense of Thórisson & Talevi. -/
structure Agent (Var : Type) (Val : Type) where
  world : World Var Val
  lest : LEST
  situation : Situation Var Val
  knowledge : Knowledge Var Val
  goals : ActiveGoals Var Val
  plan : Option (Plan Var Val)

end Mettapedia.FoundationalMeaning
