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
open Mettapedia.OSLF.RhoCalculus.Reduction
open Mettapedia.OSLF.RhoCalculus.Spice
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

/-! ## Surface Channels (External Interactions) -/

/-- Surface channels: where agent and environment can interact.

    Paper definition (Section 4.4.1, page 6):
    surf(agent, environment) = {x ∈ FN(agent) ∩ FN(environment) : agent | environment ↓ₓ}

    "Surface channels are those channels that are in the free names of both the agent
     and the environment, and where the agent and environment can interact."

    Uses `parComponents` to flatten nested bags, matching the paper's convention
    that processes are considered up to structural congruence (which includes
    associativity: `(P|Q)|R ≡ P|Q|R`).
-/
def surfaceChannels (agent environment : Pattern) : Set Pattern :=
  { x | x ∈ freeNames agent ∩ freeNames environment ∧
        canInteract (.collection .hashBag
          (parComponents agent ++ parComponents environment) none) x }

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
          StructuralCongruence agent (.collection .hashBag [agent1, agent2] none) ∧
        ∃ (k : EvalContext), k = EvalContext.par agent2 EvalContext.hole ∧
        p = ⟨k, x⟩ ∧
        ∃ (q : Pattern), Nonempty (LabeledTransition agent1 k q) }

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
  /-- Recipes: (channel, body) for for(<-x){body} — body has BVar 0 for bound var -/
  recipes : List (Pattern × Pattern)
  /-- Facts: (channel, payload) for x!(Q) -/
  facts : List (Pattern × Pattern)
deriving Repr

/-- Extract episodic memory structure from a pattern.

    Decomposes a parallel composition into recipes and facts.

    Decomposes parallel composition into input patterns (recipes) and other terms (facts).
-/
def extractMemory : Pattern → AgentMemory
  | .collection .hashBag elems none =>
      let recipes := elems.filterMap fun p =>
        match p with
        | .apply "PInput" [chan, .lambda body] => some (chan, body)
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
    exact ⟨⟨he, ha⟩, (canInteract_perm List.perm_append_comm x).mp hcan⟩
  · intro ⟨⟨he, ha⟩, hcan⟩
    exact ⟨⟨ha, he⟩, (canInteract_perm List.perm_append_comm x).mp hcan⟩

/-- Internal channels are disjoint from environment free names.

    By definition, internal channels exclude environment free names.
-/
theorem int_disjoint_env (a e : Pattern) :
    internalChannels a e ∩ freeNames e = ∅ := by
  unfold internalChannels
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf, Set.mem_diff, Set.mem_empty_iff_false]
  tauto


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
    -- h : ⟨k, x⟩ ∈ PMext ∪ PMint
    cases h with
    | inl h_ext =>
        -- h_ext : ⟨k, x⟩ ∈ presentMomentExt
        unfold presentMomentExt at h_ext
        obtain ⟨x_chan, hx_surf, _⟩ := h_ext
        left
        exact ⟨x_chan, hx_surf⟩
    | inr h_int =>
        -- h_int : ⟨k, x⟩ ∈ presentMomentInt
        unfold presentMomentInt at h_int
        obtain ⟨x_chan, hx_int, _⟩ := h_int
        right
        exact ⟨x_chan, hx_int⟩
  · intro h
    -- Construct pair from channel
    -- With corrected canInteract (requiring both input and output), we know COMM can apply
    -- However, LabeledTransition constructors only work for simple patterns (agent is input/output)
    -- For complex agents, we need to show the agent has the right structure
    cases h with
    | inl h_surf =>
        -- External case: x ∈ surfaceChannels a e
        obtain ⟨x, hx_surf⟩ := h_surf
        unfold surfaceChannels at hx_surf
        simp only [Set.mem_setOf] at hx_surf
        obtain ⟨hx_free, hx_interact⟩ := hx_surf
        -- hx_interact: canInteract on flat bag (parComponents a ++ parComponents e)
        -- Use reduces_of_canInteract to get COMM reduction on the flat bag
        obtain ⟨q_flat, ⟨red_flat⟩⟩ := reduces_of_canInteract hx_interact
        -- Bridge: [a, e] ≡ parComponents a ++ parComponents e via par_sc_flatten
        have h_sc := par_sc_flatten a e
        -- Lift reduction to [a, e] via structural congruence
        have h_reduces : Reduces (.collection .hashBag [a, e] none) q_flat :=
          Reduces.equiv h_sc red_flat (StructuralCongruence.refl _)
        -- fillEvalContext (par e hole) a = [e, a], need [e, a] ⇝ q_flat
        have h_ea_reduces : Reduces (.collection .hashBag [e, a] none) q_flat :=
          Reduces.equiv (StructuralCongruence.par_comm e a) h_reduces
            (StructuralCongruence.refl _)
        -- Construct labeled transition
        have h_ltrans : Nonempty (LabeledTransition a
            (EvalContext.par e EvalContext.hole) q_flat) :=
          ⟨LabeledTransition.from_reduction ⟨by
            simp only [fillEvalContext]; exact h_ea_reduces⟩⟩
        -- Construct the presentMomentExt witness
        refine ⟨⟨EvalContext.par e EvalContext.hole, x⟩, ?_⟩
        left
        unfold presentMomentExt
        simp only [Set.mem_setOf]
        have hx_surf_mem : x ∈ surfaceChannels a e := by
          unfold surfaceChannels; simp only [Set.mem_setOf]
          exact ⟨hx_free, hx_interact⟩
        exact ⟨x, hx_surf_mem, EvalContext.par e EvalContext.hole, rfl, rfl,
               q_flat, h_ltrans⟩
    | inr h_int =>
        -- Internal case: x ∈ internalChannels a e
        obtain ⟨x, hx_int⟩ := h_int
        unfold internalChannels at hx_int
        simp only [Set.mem_setOf] at hx_int
        obtain ⟨hx_names, hx_interact⟩ := hx_int
        -- canInteract only returns non-False for .collection .hashBag elems none
        match ha : a with
        | .collection .hashBag elems none =>
            simp only [canInteract] at hx_interact
            obtain ⟨⟨p_body, h_input⟩, ⟨q_payload, h_output⟩⟩ := hx_interact
            let input_proc := Pattern.apply "PInput" [x, .lambda p_body]
            let output_proc := Pattern.apply "POutput" [x, q_payload]
            -- input_proc ≠ output_proc since "PInput" ≠ "POutput"
            have h_ne : output_proc ≠ input_proc := by
              intro h; injection h with h_name _; exact absurd h_name (by decide)
            -- Decompose elems at input_proc
            obtain ⟨before, after, h_split⟩ := List.mem_iff_append.mp h_input
            let rest := before ++ after
            -- output_proc ∈ rest (since it's in elems and ≠ input_proc)
            have h_output_rest : output_proc ∈ rest := by
              rw [h_split] at h_output
              simp only [List.mem_append, List.mem_cons] at h_output
              rcases h_output with h_b | h_eq | h_a
              · exact List.mem_append_left after h_b
              · exact absurd h_eq h_ne
              · exact List.mem_append_right before h_a
            -- Decompose rest at output_proc
            obtain ⟨before₂, after₂, h_split₂⟩ := List.mem_iff_append.mp h_output_rest
            let other_rest := before₂ ++ after₂
            -- agent2 = .hashBag rest none (the "other part" of the agent)
            let agent2 := Pattern.collection .hashBag rest none
            -- Structural congruence: .hashBag elems ≡ .hashBag [input_proc, agent2]
            -- Via: par_perm (move input_proc to front) + symm(par_flatten) (nest the rest)
            have h_perm_elems : elems.Perm (input_proc :: rest) := by
              rw [h_split]; exact List.perm_middle
            have h_struct_cong :
                StructuralCongruence
                  (.collection .hashBag elems none)
                  (.collection .hashBag [input_proc, agent2] none) :=
              StructuralCongruence.trans _ _ _
                (StructuralCongruence.par_perm elems (input_proc :: rest) h_perm_elems)
                (StructuralCongruence.symm _ _
                  (StructuralCongruence.par_flatten [input_proc] rest))
            -- LabeledTransition for input_proc in context (par agent2 hole)
            -- fillEvalContext (par agent2 hole) input_proc = .hashBag [agent2, input_proc]
            -- Chain: [agent2, input_proc] ≡ [output_proc, input_proc, other_rest...] via COMM
            have h_perm_inner :
                (input_proc :: rest).Perm (output_proc :: input_proc :: other_rest) := by
              rw [h_split₂]
              exact ((List.Perm.cons input_proc List.perm_middle).trans
                     (List.Perm.swap output_proc input_proc (before₂ ++ after₂)))
            have h_src_cong :
                StructuralCongruence
                  (.collection .hashBag [agent2, input_proc] none)
                  (.collection .hashBag (output_proc :: input_proc :: other_rest) none) :=
              StructuralCongruence.trans _ _ _
                (StructuralCongruence.trans _ _ _
                  (StructuralCongruence.par_comm agent2 input_proc)
                  (StructuralCongruence.par_flatten [input_proc] rest))
                (StructuralCongruence.par_perm (input_proc :: rest)
                  (output_proc :: input_proc :: other_rest) h_perm_inner)
            -- COMM reduction on the reordered list
            have h_comm_step :
                Reduces
                  (.collection .hashBag (output_proc :: input_proc :: other_rest) none)
                  (.collection .hashBag (commSubst p_body q_payload :: other_rest) none) :=
              @Reduces.comm x q_payload p_body other_rest
            -- Combined reduction via structural equivalence
            let result := Pattern.collection .hashBag
              (commSubst p_body q_payload :: other_rest) none
            have h_reduces :
                Reduces (.collection .hashBag [agent2, input_proc] none) result :=
              Reduces.equiv h_src_cong h_comm_step (StructuralCongruence.refl _)
            have h_ltrans :
                Nonempty (LabeledTransition input_proc
                  (EvalContext.par agent2 EvalContext.hole) result) :=
              ⟨LabeledTransition.from_reduction ⟨h_reduces⟩⟩
            -- Assemble the presentMomentInt witness
            have hx_int_mem :
                x ∈ internalChannels (.collection .hashBag elems none) e := by
              unfold internalChannels; simp only [Set.mem_setOf]
              exact ⟨hx_names, ⟨⟨p_body, h_input⟩, ⟨q_payload, h_output⟩⟩⟩
            refine ⟨⟨EvalContext.par agent2 EvalContext.hole, x⟩, ?_⟩
            right
            unfold presentMomentInt
            simp only [Set.mem_setOf]
            exact ⟨x, hx_int_mem, input_proc, agent2, h_struct_cong,
                   EvalContext.par agent2 EvalContext.hole, rfl, rfl,
                   result, h_ltrans⟩
        | .collection .hashBag _ (some _) =>
            simp only [canInteract] at hx_interact
        | .collection .vec _ _ | .collection .hashSet _ _ =>
            simp only [canInteract] at hx_interact
        | .bvar _ | .fvar _ | .apply _ _ | .lambda _ | .subst _ _ | .multiLambda _ _ =>
            simp only [canInteract] at hx_interact

/-! ## Connection to Future States -/

/-- The present moment is a subset of the 1-step future.

    Paper reference (Section 4.4.2, page 7):
    "An agent's future is a natural extension of its present moment to
     include many steps from the current state."

    This theorem shows that present moment interactions produce
    1-step reachable states. For external interactions, the labeled
    transition directly corresponds to the future state. For internal
    interactions, the agent's self-reduction propagates to (agent | env).
-/
theorem presentMoment_subset_futureStates (a e : Pattern) :
    ∀ k x, ⟨k, x⟩ ∈ presentMoment a e →
    (futureStates (.collection .hashBag [a, e] none) 1).Nonempty := by
  intro k_ctx x_chan h
  unfold presentMoment at h
  cases h with
  | inl h_ext =>
      -- External present moment case
      unfold presentMomentExt at h_ext
      obtain ⟨x_surf, _hx_surf, k_par, hk_eq, hpair_eq, q_res, h_trans⟩ := h_ext
      have hk_ctx : k_ctx = k_par := congrArg Prod.fst hpair_eq
      have hx_chan : x_chan = x_surf := congrArg Prod.snd hpair_eq
      subst hk_ctx hx_chan hk_eq
      obtain ⟨h_reduces⟩ := labeled_implies_reduces h_trans
      simp only [fillEvalContext] at h_reduces
      have h_comm : Reduces (.collection .hashBag [a, e] none) q_res :=
        Reduces.equiv (StructuralCongruence.par_comm a e) h_reduces (StructuralCongruence.refl _)
      refine ⟨q_res, ?_⟩
      unfold futureStates
      simp only [Set.mem_setOf_eq]
      exact ⟨ReducesN.succ h_comm (ReducesN.zero q_res)⟩
  | inr h_int =>
      -- Internal present moment case
      -- With corrected presentMomentInt:
      --   ha_cong : StructuralCongruence a (.hashBag [a1, a2])
      --   h_trans : LabeledTransition a1 (par a2 hole) q
      unfold presentMomentInt at h_int
      obtain ⟨x, _hx_int, a1, a2, ha_cong, k, hk_eq, hpair_eq, q, h_trans⟩ := h_int
      have hk_ctx : k_ctx = k := congrArg Prod.fst hpair_eq
      have hx_chan : x_chan = x := congrArg Prod.snd hpair_eq
      subst hk_ctx hx_chan hk_eq
      -- Get the reduction from labeled transition of a1
      obtain ⟨h_reduces⟩ := labeled_implies_reduces h_trans
      simp only [fillEvalContext] at h_reduces
      -- h_reduces : .hashBag [a2, a1] ⇝ q
      -- Strategy: connect .hashBag [a, e] to .hashBag [.hashBag [a2, a1], e]
      -- via structural congruence, then use Reduces.par.
      --
      -- Chain: [a, e] ≡ [[a2, a1], e] via par_cong
      --   where a ≡ [a1, a2] (ha_cong) ≡ [a2, a1] (par_comm)
      have h_cong_ae :
          StructuralCongruence
            (.collection .hashBag [a, e] none)
            (.collection .hashBag [.collection .hashBag [a2, a1] none, e] none) :=
        StructuralCongruence.par_cong [a, e] [.collection .hashBag [a2, a1] none, e]
          (by simp)
          (fun i h₁ h₂ => by
            match i with
            | 0 => exact StructuralCongruence.trans _ _ _ ha_cong
                     (StructuralCongruence.par_comm a1 a2)
            | 1 => exact StructuralCongruence.refl _)
      -- Use Reduces.par: .hashBag [a2, a1] ⇝ q implies .hashBag [[a2, a1], e] ⇝ .hashBag [q, e]
      have h_par_red :
          Reduces
            (.collection .hashBag [.collection .hashBag [a2, a1] none, e] none)
            (.collection .hashBag [q, e] none) :=
        Reduces.par h_reduces
      -- Combine: .hashBag [a, e] ⇝ .hashBag [q, e]
      have h_final :
          Reduces
            (.collection .hashBag [a, e] none)
            (.collection .hashBag [q, e] none) :=
        Reduces.equiv h_cong_ae h_par_red (StructuralCongruence.refl _)
      exact ⟨.collection .hashBag [q, e] none, by
        unfold futureStates; simp only [Set.mem_setOf_eq]
        exact ⟨ReducesN.succ h_final (ReducesN.zero _)⟩⟩

/-! ## Race Conditions

Paper reference: Meredith (2026), Section 4.3.1 - "Races and compression"

A race condition occurs when multiple inputs compete for the same output
on a channel (or vice versa). The spice calculus explores all branches
of such races via its lookahead mechanism.
-/

/-- A race condition on channel x: two or more inputs AND an output on x.

    A race means there are at least two distinct input guards listening
    on the same channel where an output is also available. The COMM rule
    can synchronize with either input, leading to non-deterministic choice.

    Paper reference: Meredith (2026), Section 4.3.1
    "When there are races, the branching factor increases, i.e. there
     are potentially more reachable states to consider."
-/
def hasRace (elems : List Pattern) (x : Pattern) : Prop :=
  -- At least one output on x
  (∃ q, .apply "POutput" [x, q] ∈ elems) ∧
  -- At least two distinct inputs on x
  (∃ body₁ body₂,
    .apply "PInput" [x, .lambda body₁] ∈ elems ∧
    .apply "PInput" [x, .lambda body₂] ∈ elems ∧
    (.lambda body₁ : Pattern) ≠ .lambda body₂)

/-- Dual race: two or more outputs AND an input on x.

    The dual case: multiple outputs compete to send on a channel
    where an input is listening.
-/
def hasDualRace (elems : List Pattern) (x : Pattern) : Prop :=
  -- At least one input on x
  (∃ body, .apply "PInput" [x, .lambda body] ∈ elems) ∧
  -- At least two distinct outputs on x
  (∃ q₁ q₂,
    .apply "POutput" [x, q₁] ∈ elems ∧
    .apply "POutput" [x, q₂] ∈ elems ∧
    q₁ ≠ q₂)

/-- A race implies the process can interact on x.

    If there's a race on x, then certainly canInteract holds on x
    (there's at least one input and one output).
-/
theorem hasRace_implies_canInteract {elems : List Pattern} {x : Pattern}
    (h : hasRace elems x) :
    canInteract (.collection .hashBag elems none) x := by
  obtain ⟨⟨q, hq⟩, ⟨body₁, _, h₁, _, _⟩⟩ := h
  exact ⟨⟨body₁, h₁⟩, ⟨q, hq⟩⟩

/-- A dual race also implies the process can interact on x. -/
theorem hasDualRace_implies_canInteract {elems : List Pattern} {x : Pattern}
    (h : hasDualRace elems x) :
    canInteract (.collection .hashBag elems none) x := by
  obtain ⟨⟨body, hy⟩, ⟨q₁, _, hq₁, _, _⟩⟩ := h
  exact ⟨⟨body, hy⟩, ⟨q₁, hq₁⟩⟩

/-- A race implies the process can step (is not a value).

    A racing process is definitely not stuck: there's at least one
    synchronizable pair on channel x.
-/
theorem hasRace_implies_canStep {elems : List Pattern} {x : Pattern}
    (h : hasRace elems x) :
    CanStep (.collection .hashBag elems none) := by
  have hci := hasRace_implies_canInteract h
  obtain ⟨q, hq⟩ := reduces_of_canInteract hci
  exact ⟨q, hq⟩

/-- A dual race also implies the process can step. -/
theorem hasDualRace_implies_canStep {elems : List Pattern} {x : Pattern}
    (h : hasDualRace elems x) :
    CanStep (.collection .hashBag elems none) := by
  have hci := hasDualRace_implies_canInteract h
  obtain ⟨q, hq⟩ := reduces_of_canInteract hci
  exact ⟨q, hq⟩

/-- No race can occur in a value (contrapositive of hasRace_implies_canStep). -/
theorem value_no_race {elems : List Pattern}
    (hv : Value (.collection .hashBag elems none)) (x : Pattern) :
    ¬ hasRace elems x :=
  fun h => hv (hasRace_implies_canStep h)

/-- **Race non-determinism**: A race on channel x implies at least two
    distinct reductions, witnessing genuine non-determinism.

    Given a race (output `x!(q)` and two distinct inputs `for(y₁←x){body₁}`,
    `for(y₂←x){body₂}`), COMM can fire with either input, producing different
    results. Under `Nodup` (processes are resources, not duplicated), the two
    results are provably distinct because the "leftover" siblings differ:
    each result retains the other input that wasn't consumed.

    Paper reference: Meredith (2026), Section 4.3.1 - "Races and compression"
    "When there are races, the branching factor increases, i.e. there
     are potentially more reachable states to consider."
-/
theorem race_nondeterminism {elems : List Pattern} {x : Pattern}
    (h_race : hasRace elems x) (h_nodup : elems.Nodup) :
    ∃ r₁ r₂, Nonempty (Reduces (.collection .hashBag elems none) r₁) ∧
              Nonempty (Reduces (.collection .hashBag elems none) r₂) ∧
              r₁ ≠ r₂ := by
  obtain ⟨⟨q, hq_mem⟩, ⟨body₁, body₂, h₁_mem, h₂_mem, h_ne_lam⟩⟩ := h_race
  -- Abbreviate the three key processes
  let out := Pattern.apply "POutput" [x, q]
  let inp₁ := Pattern.apply "PInput" [x, .lambda body₁]
  let inp₂ := Pattern.apply "PInput" [x, .lambda body₂]
  -- All three are distinct
  have h_out_ne₁ : out ≠ inp₁ := by
    intro h; injection h with h_name; exact absurd h_name (by decide)
  have h_out_ne₂ : out ≠ inp₂ := by
    intro h; injection h with h_name; exact absurd h_name (by decide)
  have h_inp_ne : inp₁ ≠ inp₂ := by
    intro h
    have : (.lambda body₁ : Pattern) = .lambda body₂ := by
      injection h with _ h_args
      simp only [List.cons.injEq] at h_args
      exact h_args.2.1
    exact h_ne_lam this
  -- Split elems at out, get rest with Nodup
  obtain ⟨befO, aftO, h_splitO⟩ := List.mem_iff_append.mp hq_mem
  have h_permO : elems.Perm (out :: (befO ++ aftO)) := by
    rw [h_splitO]; exact List.perm_middle
  have h_nodup_cons : (out :: (befO ++ aftO)).Nodup :=
    h_permO.nodup_iff.mp h_nodup
  have h_rest_nodup : (befO ++ aftO).Nodup :=
    (List.nodup_cons.mp h_nodup_cons).2
  -- Both inputs are in rest (since they're in elems and ≠ out)
  have h₁_rest : inp₁ ∈ befO ++ aftO := by
    rw [h_splitO] at h₁_mem
    simp only [List.mem_append, List.mem_cons] at h₁_mem
    rcases h₁_mem with h | h | h
    · exact List.mem_append_left _ h
    · exact absurd h h_out_ne₁.symm
    · exact List.mem_append_right _ h
  have h₂_rest : inp₂ ∈ befO ++ aftO := by
    rw [h_splitO] at h₂_mem
    simp only [List.mem_append, List.mem_cons] at h₂_mem
    rcases h₂_mem with h | h | h
    · exact List.mem_append_left _ h
    · exact absurd h h_out_ne₂.symm
    · exact List.mem_append_right _ h
  -- Split rest at inp₁
  obtain ⟨b₁, a₁, h_split₁⟩ := List.mem_iff_append.mp h₁_rest
  -- Split rest at inp₂
  obtain ⟨b₂, a₂, h_split₂⟩ := List.mem_iff_append.mp h₂_rest
  -- inp₂ ∈ b₁ ++ a₁ (since inp₂ ∈ rest, inp₂ ≠ inp₁)
  have h₂_in_other₁ : inp₂ ∈ b₁ ++ a₁ := by
    rw [h_split₁] at h₂_rest
    simp only [List.mem_append, List.mem_cons] at h₂_rest
    rcases h₂_rest with h | h | h
    · exact List.mem_append_left _ h
    · exact absurd h h_inp_ne.symm
    · exact List.mem_append_right _ h
  -- inp₂ ∉ b₂ ++ a₂ (since rest.Nodup and rest = b₂ ++ [inp₂] ++ a₂)
  have h₂_notin_other₂ : inp₂ ∉ b₂ ++ a₂ := by
    have h_perm_rest : (befO ++ aftO).Perm (inp₂ :: (b₂ ++ a₂)) := by
      rw [h_split₂]; exact List.perm_middle
    exact (List.nodup_cons.mp (h_perm_rest.nodup_iff.mp h_rest_nodup)).1
  -- Therefore the "other" lists differ
  have h_others_ne : b₁ ++ a₁ ≠ b₂ ++ a₂ := by
    intro h_eq; rw [h_eq] at h₂_in_other₁; exact h₂_notin_other₂ h₂_in_other₁
  -- Construct COMM₁: elems ⇝ {commSubst body₁ q, b₁ ++ a₁}
  have h_perm₁ : elems.Perm (out :: inp₁ :: (b₁ ++ a₁)) :=
    h_permO.trans (List.Perm.cons out (by rw [h_split₁]; exact List.perm_middle))
  have h_red₁ : Nonempty (Reduces (.collection .hashBag elems none)
      (.collection .hashBag (commSubst body₁ q :: (b₁ ++ a₁)) none)) :=
    ⟨Reduces.equiv
      (StructuralCongruence.par_perm _ _ h_perm₁)
      (@Reduces.comm x q body₁ (b₁ ++ a₁))
      (StructuralCongruence.refl _)⟩
  -- Construct COMM₂: elems ⇝ {commSubst body₂ q, b₂ ++ a₂}
  have h_perm₂ : elems.Perm (out :: inp₂ :: (b₂ ++ a₂)) :=
    h_permO.trans (List.Perm.cons out (by rw [h_split₂]; exact List.perm_middle))
  have h_red₂ : Nonempty (Reduces (.collection .hashBag elems none)
      (.collection .hashBag (commSubst body₂ q :: (b₂ ++ a₂)) none)) :=
    ⟨Reduces.equiv
      (StructuralCongruence.par_perm _ _ h_perm₂)
      (@Reduces.comm x q body₂ (b₂ ++ a₂))
      (StructuralCongruence.refl _)⟩
  -- Results differ: different tails imply different lists imply different patterns
  refine ⟨_, _, h_red₁, h_red₂, ?_⟩
  intro h_eq
  have : commSubst body₁ q :: (b₁ ++ a₁) =
      commSubst body₂ q :: (b₂ ++ a₂) := by
    have h := h_eq
    simp only [Pattern.collection.injEq] at h
    exact h.2.1
  exact h_others_ne (List.tail_eq_of_cons_eq this)

/-! ## Episodic Memory Correctness

We prove that `extractMemory` correctly decomposes a parallel composition
into its recipes (input guards) and facts (output guards).

Paper reference: Meredith (2026), Section 4.4.4
-/

/-- Helper: a term is a recipe (input guard) -/
def isRecipe (p : Pattern) : Prop :=
  ∃ chan body, p = .apply "PInput" [chan, .lambda body]

/-- Helper: a term is a fact (output guard) -/
def isFact (p : Pattern) : Prop :=
  ∃ chan payload, p = .apply "POutput" [chan, payload]

/-- Helper: recipe extraction function -/
private def recipeExtract : Pattern → Option (Pattern × Pattern)
  | .apply "PInput" [chan, .lambda body] => some (chan, body)
  | _ => none

/-- Helper: fact extraction function -/
private def factExtract : Pattern → Option (Pattern × Pattern)
  | .apply "POutput" [chan, payload] => some (chan, payload)
  | _ => none

/-- If recipeExtract returns some, the pattern is a PInput -/
private theorem recipeExtract_some {p : Pattern} {chan : Pattern} {body : Pattern}
    (h : recipeExtract p = some (chan, body)) :
    p = .apply "PInput" [chan, .lambda body] := by
  cases p with
  | apply name args =>
    simp only [recipeExtract] at h
    split at h <;> simp_all
  | _ => simp [recipeExtract] at h

/-- If factExtract returns some, the pattern is a POutput -/
private theorem factExtract_some {p : Pattern} {chan payload : Pattern}
    (h : factExtract p = some (chan, payload)) :
    p = .apply "POutput" [chan, payload] := by
  cases p with
  | apply name args =>
    simp only [factExtract] at h
    split at h <;> simp_all
  | _ => simp [factExtract] at h

/-- extractMemory recipes = filterMap recipeExtract -/
private theorem extractMemory_recipes_eq {elems : List Pattern} :
    (extractMemory (.collection .hashBag elems none)).recipes =
    elems.filterMap recipeExtract := by
  unfold extractMemory recipeExtract
  rfl

/-- extractMemory facts = filterMap factExtract -/
private theorem extractMemory_facts_eq {elems : List Pattern} :
    (extractMemory (.collection .hashBag elems none)).facts =
    elems.filterMap factExtract := by
  unfold extractMemory factExtract
  rfl

/-- Every extracted recipe corresponds to a PInput in the original bag.

    If (chan, y, body) is in extractMemory(agent).recipes, then
    PInput [chan, λ y. body] is a member of the agent's parallel bag.
-/
theorem extractMemory_recipes_sound {elems : List Pattern}
    {chan : Pattern} {body : Pattern}
    (h : (chan, body) ∈ (extractMemory (.collection .hashBag elems none)).recipes) :
    .apply "PInput" [chan, .lambda body] ∈ elems := by
  rw [extractMemory_recipes_eq] at h
  obtain ⟨p, hp_mem, hp_eq⟩ := List.mem_filterMap.mp h
  rw [← recipeExtract_some hp_eq]
  exact hp_mem

/-- Every extracted fact corresponds to a POutput in the original bag. -/
theorem extractMemory_facts_sound {elems : List Pattern}
    {chan payload : Pattern}
    (h : (chan, payload) ∈ (extractMemory (.collection .hashBag elems none)).facts) :
    .apply "POutput" [chan, payload] ∈ elems := by
  rw [extractMemory_facts_eq] at h
  obtain ⟨p, hp_mem, hp_eq⟩ := List.mem_filterMap.mp h
  rw [← factExtract_some hp_eq]
  exact hp_mem

/-- If an agent has both a recipe and a fact on channel x, it can self-interact.

    Paper reference: Meredith (2026), Section 4.4.4
    "A recipe for(y <- x)P is a description of what to do when presented
     with a Q on channel x... A fact x!(Q) is a piece of information
     available on channel x."

    When both exist on the same channel, COMM can fire internally.
-/
theorem memory_self_interaction {elems : List Pattern}
    {chan : Pattern} {body payload : Pattern}
    (h_recipe : (chan, body) ∈
      (extractMemory (.collection .hashBag elems none)).recipes)
    (h_fact : (chan, payload) ∈
      (extractMemory (.collection .hashBag elems none)).facts) :
    canInteract (.collection .hashBag elems none) chan := by
  simp only [canInteract]
  exact ⟨⟨body, extractMemory_recipes_sound h_recipe⟩,
         ⟨payload, extractMemory_facts_sound h_fact⟩⟩

/-- An agent with matching recipes and facts on a channel can step.

    Corollary of `memory_self_interaction` + `reduces_of_canInteract`.
-/
theorem memory_self_interaction_canStep {elems : List Pattern}
    {chan : Pattern} {body payload : Pattern}
    (h_recipe : (chan, body) ∈
      (extractMemory (.collection .hashBag elems none)).recipes)
    (h_fact : (chan, payload) ∈
      (extractMemory (.collection .hashBag elems none)).facts) :
    CanStep (.collection .hashBag elems none) := by
  have hci := memory_self_interaction h_recipe h_fact
  obtain ⟨q, hq⟩ := reduces_of_canInteract hci
  exact ⟨q, hq⟩

/-! ## Episodic Memory Completeness

Completeness: every top-level PInput/POutput in a flat bag appears in extractMemory.
-/

/-- Completeness for recipes: every PInput in the bag is extracted. -/
theorem extractMemory_recipes_complete {elems : List Pattern}
    {chan : Pattern} {body : Pattern}
    (h : .apply "PInput" [chan, .lambda body] ∈ elems) :
    (chan, body) ∈ (extractMemory (.collection .hashBag elems none)).recipes := by
  rw [extractMemory_recipes_eq]
  exact List.mem_filterMap.mpr ⟨.apply "PInput" [chan, .lambda body], h, by
    simp [recipeExtract]⟩

/-- Completeness for facts: every POutput in the bag is extracted. -/
theorem extractMemory_facts_complete {elems : List Pattern}
    {chan payload : Pattern}
    (h : .apply "POutput" [chan, payload] ∈ elems) :
    (chan, payload) ∈ (extractMemory (.collection .hashBag elems none)).facts := by
  rw [extractMemory_facts_eq]
  exact List.mem_filterMap.mpr ⟨.apply "POutput" [chan, payload], h, by
    simp [factExtract]⟩

/-! ## Logged COMM: Reversible Reduction

Paper reference: Meredith (2026), Section 4.4.3 - "The Past"

"The past only comes into being if there is some record or trace…
 continuation-saturated form… developed… for reversibility."

We formalize a "logged COMM" that records exactly what was consumed,
enabling reconstruction of the pre-state from the record + post-state.
This is the core of the reversibility story: each COMM step is undoable.
-/

/-- A COMM record: what happened during a COMM reduction step.

    Records the channel, the consumed input (recipe), the consumed output (fact),
    and the remaining parallel siblings. This is exactly the information
    needed to reconstruct the pre-state.
-/
structure CommRecord where
  /-- The channel on which synchronization occurred -/
  channel : Pattern
  /-- The consumed input body: for(<-channel){body} — body has BVar 0 -/
  inputBody : Pattern
  /-- The consumed output payload: channel!(payload) -/
  outputPayload : Pattern
  /-- The other processes in the parallel bag (untouched by COMM) -/
  rest : List Pattern
deriving Repr

/-- The pre-state reconstructed from a COMM record.

    This is the parallel bag BEFORE the COMM fired:
    { output, input, rest... }
-/
def CommRecord.preState (r : CommRecord) : Pattern :=
  .collection .hashBag
    ([.apply "POutput" [r.channel, r.outputPayload],
      .apply "PInput" [r.channel, .lambda r.inputBody]]
      ++ r.rest) none

/-- The post-state resulting from a COMM record.

    This is the parallel bag AFTER the COMM fired:
    { body[@payload/y], rest... }
-/
def CommRecord.postState (r : CommRecord) : Pattern :=
  .collection .hashBag
    ([commSubst r.inputBody r.outputPayload] ++ r.rest) none

/-- **Forward**: a COMM record witnesses a reduction from pre to post.

    The logged COMM step is a genuine reduction: preState ⇝ postState.
-/
theorem CommRecord.forward (r : CommRecord) :
    Nonempty (Reduces r.preState r.postState) := by
  simp only [preState, postState]
  exact ⟨Reduces.comm⟩

/-- **Backward**: from a COMM record, we can reconstruct the pre-state.

    Given the post-state and the record, we recover the pre-state exactly.
    This is the reversibility property: COMM steps can be undone.
-/
theorem CommRecord.reconstruct (r : CommRecord) :
    r.preState =
    .collection .hashBag
      ([.apply "POutput" [r.channel, r.outputPayload],
        .apply "PInput" [r.channel, .lambda r.inputBody]]
        ++ r.rest) none := by
  rfl

/-- **Linearity**: after COMM, the consumed recipe is absent from the result.

    Paper reference: Meredith (2026), Section 4.4.4
    "visitation is interaction and interaction is linear and destructive"

    After COMM fires, the consumed PInput is no longer in the post-state's
    top-level parallel bag (it was replaced by the substituted body).

    Hypotheses: the consumed input wasn't duplicated in rest, and the
    substituted body doesn't happen to equal the consumed input.
-/
theorem CommRecord.recipe_consumed (r : CommRecord)
    (h_not_in_rest : .apply "PInput" [r.channel, .lambda r.inputBody] ∉ r.rest)
    (h_not_result : commSubst r.inputBody r.outputPayload ≠
      .apply "PInput" [r.channel, .lambda r.inputBody]) :
    .apply "PInput" [r.channel, .lambda r.inputBody] ∉
      ([commSubst r.inputBody r.outputPayload] ++ r.rest) := by
  intro hmem
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  cases hmem with
  | inl h => exact h_not_result h.symm
  | inr h => exact h_not_in_rest h

/-- **Linearity**: after COMM, the consumed fact is absent from the result. -/
theorem CommRecord.fact_consumed (r : CommRecord)
    (h_not_in_rest : .apply "POutput" [r.channel, r.outputPayload] ∉ r.rest)
    (h_not_result : commSubst r.inputBody r.outputPayload ≠
      .apply "POutput" [r.channel, r.outputPayload]) :
    .apply "POutput" [r.channel, r.outputPayload] ∉
      ([commSubst r.inputBody r.outputPayload] ++ r.rest) := by
  intro hmem
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  cases hmem with
  | inl h => exact h_not_result h.symm
  | inr h => exact h_not_in_rest h

/-- **Round-trip**: log a COMM, undo it, get back where you started.

    Given a COMM record r, we have:
    1. r.preState ⇝ r.postState  (forward, by CommRecord.forward)
    2. From r + r.postState, we recover r.preState  (backward, by CommRecord.reconstruct)

    This combined fact is the "reversibility POC": COMM steps are undoable
    when the record is available.
-/
theorem CommRecord.round_trip (r : CommRecord) :
    Nonempty (Reduces r.preState r.postState) ∧
    r.preState = .collection .hashBag
      ([.apply "POutput" [r.channel, r.outputPayload],
        .apply "PInput" [r.channel, .lambda r.inputBody]]
        ++ r.rest) none :=
  ⟨r.forward, rfl⟩

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

**All theorems PROVEN (0 sorries)**:
- `surf_comm` - surface channels are symmetric
- `int_disjoint_env` - internal channels disjoint from env free names
- `presentMoment_nonempty_iff` - both external AND internal cases
- `presentMoment_subset_futureStates` - both external AND internal cases

**Key techniques used**:
- `StructuralCongruence.par_flatten` + `par_perm` for list decomposition
- `StructuralCongruence.par_cong` + `par_comm` for the SC chain in internal case
- `Reduces.equiv` + `Reduces.par` for lifting reductions through parallel composition
- `LabeledTransition.from_reduction` for constructing labeled transitions

-/

end Mettapedia.OSLF.RhoCalculus.PresentMoment
