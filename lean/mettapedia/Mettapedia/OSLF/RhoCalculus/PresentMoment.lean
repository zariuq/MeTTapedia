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
  /-- Recipes: (channel, variable, continuation) for for(y <- x)P -/
  recipes : List (Pattern × String × Pattern)
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
            obtain ⟨⟨y, p_body, h_input⟩, ⟨q_payload, h_output⟩⟩ := hx_interact
            let input_proc := Pattern.apply "PInput" [x, .lambda y p_body]
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
                  (.collection .hashBag (commSubst p_body y q_payload :: other_rest) none) :=
              @Reduces.comm x q_payload p_body y other_rest
            -- Combined reduction via structural equivalence
            let result := Pattern.collection .hashBag
              (commSubst p_body y q_payload :: other_rest) none
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
              exact ⟨hx_names, ⟨⟨y, p_body, h_input⟩, ⟨q_payload, h_output⟩⟩⟩
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
        | .var _ | .apply _ _ | .lambda _ _ | .subst _ _ _ | .multiLambda _ _ =>
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
