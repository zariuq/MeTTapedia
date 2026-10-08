import Mettapedia.GSLT.Causality.DoCalculus.RungBridge
import Mettapedia.GSLT.Causality.DoCalculus.Rule1Collider

/-!
# An intervention as an admissible context

On the two-gate chain, `do(x = true)` is an admissible binding. Reading a
passive formula under that binding agrees with reading it after surgery
assigns the same value.

The collider `Z → X ← Y` has no edge between `Z` and `Y`. Conditioning on `X`
in the graph that still has the arrows into `X` leaves the trail `Z — X — Y`
active. That is a path through a conditioned collider. It is not, by itself, a
count of top-level inputs and outputs on ρ-calculus names.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.Causality.Hierarchy
open Mettapedia.GSLT.Causality.StructuralModels
open Mettapedia.GSLT.Causality.ContextBindings
open OverrideAction
open Mettapedia.ProbabilityTheory.BayesianNetworks
open DirectedGraph
open DSeparation

/-- On the chain, the admissible context `do(x = true)` and surgery at `x`
agree on every passive formula. -/
theorem chain_context_agrees_with_surgery
    (obs : ContextualRules.Observations (modelGSLT Gate Bool))
    (formula : Formula (passive obs).Atom (passive obs).Label)
    (store : Gate → Bool) :
    let action := surgeryAction (Key := Gate) (Value := Bool)
    let admissible := action.regionDerived Set.univ
    let context : {bindings : Bindings Gate Bool // admissible.Admissible bindings} :=
      ⟨doBinding .x true, chain_do_admissible⟩
    (admissible.saturated obs).sat
        (underIntervention admissible obs context formula) ⟨chain, store⟩ ↔
      (passive obs).sat formula (action.assign (single .x true) ⟨chain, store⟩) :=
  chain_do_is_rung2 obs formula store

/-- `Z` and `Y` have no edge in either direction. -/
theorem collider_no_direct_channel :
    ¬ colliderGraph.edges Collider.z Collider.y ∧
      ¬ colliderGraph.edges Collider.y Collider.z := by
  constructor
  · intro h
    rcases h with ⟨_, hb⟩ | ⟨ha, _⟩
    · cases hb
    · cases ha
  · intro h
    rcases h with ⟨ha, _⟩ | ⟨_, hb⟩
    · cases ha
    · cases hb

/-- Conditioning on `X` opens `Z — X — Y` while the arrows into `X` remain,
and `Z` is not joined to `Y` by an edge. -/
theorem collider_conditioned_trail_without_direct_edge :
    ¬ colliderGraph.edges Collider.z Collider.y ∧
      ActiveTrail (deleteOutgoing colliderGraph ({Collider.x} : Finset Collider))
        ({Collider.x} : Set Collider) [Collider.z, Collider.x, Collider.y] :=
  ⟨collider_no_direct_channel.1, collider_outgoing_trail⟩

end Mettapedia.GSLT.Causality.DoCalculus
