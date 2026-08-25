import Mettapedia.CognitiveArchitecture.Agent.WorldState
import Mettapedia.Logic.WorldModel.Basic

/-!
# Codex-Style Operational State as a World Model

Source provenance: adapted from GödelClaw commit
`a3a94210bd4d951dd5f9a541db819ac107ef5182`; the semantic module name now
describes its chronological construction independently of one agent product.

The minimal `WorldModel` calculus is not probabilistic and does not require
commutative revision.  This file instantiates it with a chronological sequence
of full snapshots and patches, matching the abstract shape of a coding agent's
model-visible operational state.

The whole operational model is monoidal under chronological append.  A
separate projection of the larger typed agent state may still instantiate
`AdditiveWorldModel` for WM-PLN evidence.  These are nested world-model views,
not competing definitions.
-/

namespace Mettapedia.CognitiveArchitecture.Agent.ChronologicalWorldModel

/-- An update either establishes a full baseline or applies a patch to the
current baseline. -/
inductive Update (Snapshot Patch : Type*) where
  | full (snapshot : Snapshot)
  | patch (patch : Patch)

/-- Semantics of exact operational snapshots, patches, and queries. -/
structure PatchSemantics (Snapshot Patch Query Value : Type*) where
  emptySnapshot : Snapshot
  applyPatch : Snapshot → Patch → Snapshot
  query : Snapshot → Query → Value

def applyUpdate {Snapshot Patch Query Value : Type*}
    (semantics : PatchSemantics Snapshot Patch Query Value)
    (snapshot : Snapshot) : Update Snapshot Patch → Snapshot
  | .full replacement => replacement
  | .patch patch => semantics.applyPatch snapshot patch

/-- Replay is chronological and therefore may be noncommutative. -/
def replay {Snapshot Patch Query Value : Type*}
    (semantics : PatchSemantics Snapshot Patch Query Value)
    (updates : List (Update Snapshot Patch)) : Snapshot :=
  updates.foldl (applyUpdate semantics) semantics.emptySnapshot

/-- Chronological update histories form a minimal world model. -/
@[reducible]
def chronologicalWorldModel {Snapshot Patch Query Value : Type*}
    (semantics : PatchSemantics Snapshot Patch Query Value) :
    WorldModel (List (Update Snapshot Patch)) Query Value where
  revise := List.append
  empty := []
  extract updates query := semantics.query (replay semantics updates) query

/-- Chronological composition is associative and has the empty history as its
identity, so the operational world model is monoidal without being
commutative. -/
@[reducible]
def chronologicalMonoidalWorldModel
    {Snapshot Patch Query Value : Type*}
    (semantics : PatchSemantics Snapshot Patch Query Value) :
    MonoidalWorldModel (List (Update Snapshot Patch)) Query Value where
  revise := List.append
  empty := []
  extract updates query := semantics.query (replay semantics updates) query
  revise_assoc := List.append_assoc
  revise_empty_left := List.nil_append
  revise_empty_right := List.append_nil

theorem full_snapshot_replaces_prior_state
    {Snapshot Patch Query Value : Type*}
    (semantics : PatchSemantics Snapshot Patch Query Value)
    (before : List (Update Snapshot Patch)) (replacement : Snapshot) :
    replay semantics (before ++ [.full replacement]) = replacement := by
  simp [replay, List.foldl_append, applyUpdate]

/-! ## An observable noncommutative instance -/

inductive NatPatch where
  | increment
  | double
deriving Repr, DecidableEq

def natSemantics : PatchSemantics Nat NatPatch Unit Nat where
  emptySnapshot := 1
  applyPatch state
    | .increment => state + 1
    | .double => state * 2
  query state _ := state

def incrementUpdate : Update Nat NatPatch := .patch .increment
def doubleUpdate : Update Nat NatPatch := .patch .double

/-- Ordered patch histories can answer the same query differently. -/
theorem operational_revision_is_not_commutative :
    let wm := chronologicalWorldModel natSemantics
    wm.extract (wm.revise [incrementUpdate] [doubleUpdate]) () ≠
      wm.extract (wm.revise [doubleUpdate] [incrementUpdate]) () := by
  decide

/-- A full baseline makes earlier operational patches observationally
irrelevant to later queries, matching compaction baseline replacement. -/
theorem full_baseline_cuts_off_earlier_patches :
    replay natSemantics
        [incrementUpdate, doubleUpdate, .full 7, incrementUpdate] = 8 := by
  decide

end Mettapedia.CognitiveArchitecture.Agent.ChronologicalWorldModel

#print axioms Mettapedia.CognitiveArchitecture.Agent.ChronologicalWorldModel.full_snapshot_replaces_prior_state
#print axioms Mettapedia.CognitiveArchitecture.Agent.ChronologicalWorldModel.operational_revision_is_not_commutative
#print axioms Mettapedia.CognitiveArchitecture.Agent.ChronologicalWorldModel.full_baseline_cuts_off_earlier_patches
