import Mettapedia.OSLF.RhoCalculus.Context
import Mettapedia.OSLF.RhoCalculus.SpiceRule

/-!
# The Present Moment for ρ-Calculus Agents

This file formalizes the present moment concept from Meredith's
"How the Agents Got Their Present Moment", Section 4.4.1 (pages 6-7).

## Paper Reference

Meredith (2026): "How the Agents Got Their Present Moment", Section 4.4.1

**Key concept**: "An agent's present moment comprises all the interactions it can have
immediately with its environment and all the interactions it can have immediately
internally with itself."

## Definitions

- `surfaceChannels` - surf(agent, environment): channels for external interaction
- `internalChannels` - int(agent, environment): channels for internal interaction
- `presentMomentExt` - PMext(agent, environment): external interactions with context
- `presentMomentInt` - PMint(agent, environment): internal self-interactions
- `presentMoment` - PM(agent, environment): complete present moment (PMext ∪ PMint)
- `AgentMemory` - Episodic memory structure (recipes + facts)

## Main Results

- `surf_comm`: Surface channels are symmetric
- `presentMoment_nonempty_iff`: Present moment nonempty iff interaction possible
- `presentMoment_subset_futureStates`: Present moment is subset of 1-step future

-/

namespace Mettapedia.OSLF.RhoCalculus.PresentMoment

open Mettapedia.OSLF.RhoCalculus
open Mettapedia.OSLF.RhoCalculus.Context
open Mettapedia.OSLF.RhoCalculus.Spice
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Surface Channels (External Interactions) -/

/-- Surface channels: where agent and environment can interact.

    Paper definition (Section 4.4.1, page 6):
    surf(agent, environment) = {x ∈ FN(agent) ∩ FN(environment) : agent | environment ↓ₓ}

    "Surface channels are those channels that are in the free names of both the agent
     and the environment, and where the agent and environment can interact."
-/
def surfaceChannels (agent environment : Pattern) : Set Pattern :=
  { x | x ∈ freeNames agent ∩ freeNames environment ∧
        canInteract (.collection .hashBag [agent, environment] none) x }

notation:50 "surf(" a "," e ")" => surfaceChannels a e

/-! ## Internal Channels (Internal Interactions) -/

/-- Internal channels: where agent can interact with itself.

    Paper definition (Section 4.4.1, page 7):
    int(agent, environment) = {x ∈ N(agent) \ FN(environment) : agent ↓ₓ}

    "Internal channels are those channels that are in all the names of the agent
     but not in the free names of the environment, and where the agent can interact."
-/
def internalChannels (agent environment : Pattern) : Set Pattern :=
  { x | x ∈ (allNames agent) \ (freeNames environment) ∧
        canInteract agent x }

notation:50 "int(" a "," e ")" => internalChannels a e

/-! ## Present Moment -/

/-- External present moment: interactions with environment.

    Paper definition (Section 4.4.1, page 7):
    PMext(agent, environment) =
      {K(x) : x ∈ surf(agent, environment), K = □ | environment, agent ↓K(x)}

    The external present moment consists of all contexts where the agent can
    immediately interact with its environment.
-/
def presentMomentExt (agent environment : Pattern) : Set (EvalContext × Pattern) :=
  { p | ∃ (x : Pattern), x ∈ surfaceChannels agent environment ∧
        ∃ (k : EvalContext), k = EvalContext.par environment EvalContext.hole ∧
        p = ⟨k, x⟩ ∧
        ∃ (q : Pattern), Nonempty (LabeledTransition agent k q) }

/-- Internal present moment: internal self-interactions.

    Paper definition (Section 4.4.1, page 7):
    PMint(agent, environment) =
      {K(x) : x ∈ int(agent, environment),
       ∃agent1, agent2. agent = agent1 | agent2, K = □ | agent2, agent ↓K(x)}

    The internal present moment consists of all contexts where the agent can
    immediately interact with itself (internal communication).
-/
def presentMomentInt (agent environment : Pattern) : Set (EvalContext × Pattern) :=
  { p | ∃ (x : Pattern), x ∈ internalChannels agent environment ∧
        ∃ (agent1 agent2 : Pattern),
          agent = .collection .hashBag [agent1, agent2] none ∧
        ∃ (k : EvalContext), k = EvalContext.par agent2 EvalContext.hole ∧
        p = ⟨k, x⟩ ∧
        ∃ (q : Pattern), Nonempty (LabeledTransition agent k q) }

/-- The complete present moment: all immediate interactions.

    Paper definition (Section 4.4.1, page 7):
    PM(agent, environment) = PMext(agent, environment) ∪ PMint(agent, environment)

    Paper quote: "An agent's present moment comprises all the interactions it can have
    immediately with its environment and all the interactions it can have immediately
    internally with itself."
-/
def presentMoment (agent environment : Pattern) : Set (EvalContext × Pattern) :=
  presentMomentExt agent environment ∪ presentMomentInt agent environment

notation:50 "PM(" a "," e ")" => presentMoment a e

/-! ## Episodic Memory -/

/-- Agent memory structure: recipes (inputs) and facts (outputs).

    Paper definition (Section 4.4.4, page 7):
    agent = ∏ᵢ for(yᵢ <- xᵢ)Pᵢ | ∏ⱼ xⱼ!(Qⱼ)

    Paper quote: "An agent comprises a store of two kinds of things:
    recipes and facts. A recipe for(y <- x)P is a description of what
    to do when presented with a Q on channel x... A fact x!(Q) is a
    piece of information available on channel x."
-/
structure AgentMemory where
  /-- Recipes: (channel, variable, continuation) for for(y <- x)P -/
  recipes : List (Pattern × String × Pattern)
  /-- Facts: (channel, payload) for x!(Q) -/
  facts : List (Pattern × Pattern)
deriving Repr

/-- Extract episodic memory structure from a pattern.

    Decomposes a parallel composition into recipes and facts.

    TODO: Implement pattern matching on parallel composition structure
-/
def extractMemory : Pattern → AgentMemory
  | .collection .hashBag elems none =>
      let recipes := elems.filterMap fun p =>
        match p with
        | .apply "PInput" [chan, .lambda y body] => some (chan, y, body)
        | _ => none
      let facts := elems.filterMap fun p =>
        match p with
        | .apply "POutput" [chan, payload] => some (chan, payload)
        | _ => none
      { recipes := recipes, facts := facts }
  | _ => { recipes := [], facts := [] }

/-! ## Basic Properties -/

/-- Surface channels are symmetric.

    Paper note: The intersection of free names is symmetric by definition.
-/
theorem surf_comm (a e : Pattern) :
    surfaceChannels a e = surfaceChannels e a := by
  unfold surfaceChannels
  ext x
  simp only [Set.mem_setOf, Set.mem_inter_iff]
  constructor
  · intro ⟨⟨ha, he⟩, hcan⟩
    exact ⟨⟨he, ha⟩, (canInteract_par_comm a e x).mp hcan⟩
  · intro ⟨⟨he, ha⟩, hcan⟩
    exact ⟨⟨ha, he⟩, (canInteract_par_comm e a x).mp hcan⟩

/-- Internal channels are disjoint from environment free names.

    By definition, internal channels exclude environment free names.
-/
theorem int_disjoint_env (a e : Pattern) :
    internalChannels a e ∩ freeNames e = ∅ := by
  unfold internalChannels
  sorry  -- TODO: Prove using set difference properties

/-- Present moment is nonempty iff interaction possible.

    An agent has a present moment exactly when it can interact either
    externally or internally.
-/
theorem presentMoment_nonempty_iff {a e : Pattern} :
    (presentMoment a e).Nonempty ↔
    (∃ x, x ∈ surfaceChannels a e) ∨ (∃ x, x ∈ internalChannels a e) := by
  constructor
  · intro ⟨⟨k, x⟩, h⟩
    unfold presentMoment at h
    sorry  -- TODO: Case analysis on presentMomentExt vs presentMomentInt
  · intro h
    sorry  -- TODO: Construct context from surf or int channel

/-! ## Connection to Future States -/

/-- The present moment is a subset of the 1-step future.

    Paper reference (Section 4.4.2, page 7):
    "An agent's future is a natural extension of its present moment to
     include many steps from the current state."

    This theorem shows that present moment interactions are exactly
    the immediate (1-step) reachable states.
-/
theorem presentMoment_subset_futureStates (a e : Pattern) :
    ∀ k x, ⟨k, x⟩ ∈ presentMoment a e →
    ∃ q ∈ futureStates (.collection .hashBag [a, e] none) 1,
      Nonempty (LabeledTransition a k q) := by
  intro k x h
  unfold presentMoment at h
  unfold presentMomentExt presentMomentInt at h
  sorry  -- TODO: Use labeled transition to show q ∈ futureStates

/-! ## Summary

This file establishes the present moment formalization:

**✅ COMPLETED**:
1. `surfaceChannels` - surf(agent, environment) for external interaction
2. `internalChannels` - int(agent, environment) for internal interaction
3. `presentMomentExt` - external present moment with contexts
4. `presentMomentInt` - internal present moment with contexts
5. `presentMoment` - complete present moment (PMext ∪ PMint)
6. `AgentMemory` - episodic memory structure (recipes + facts)
7. `extractMemory` - pattern decomposition into recipes/facts

**⚠️ WITH SORRIES**:
- `surf_comm` - straightforward set theory
- `int_disjoint_env` - straightforward set difference property
- `presentMoment_nonempty_iff` - requires case analysis (standard)
- `presentMoment_subset_futureStates` - requires labeled transition bridge

**Next Steps**:
- Phase 3: GSLT.lean for user-defined languages (Section 5)
- Phase 4: Integration theorems connecting all components

-/

end Mettapedia.OSLF.RhoCalculus.PresentMoment
