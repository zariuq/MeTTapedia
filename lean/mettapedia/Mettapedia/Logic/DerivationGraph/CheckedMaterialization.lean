import Mettapedia.Logic.DerivationGraph

/-!
# Materializing the cache of an already checked derivation graph

Successful replay appends exactly the declared conclusion of each node.
This equality permits certified producers to construct that cache directly
when they already possess replay evidence. It grants no authority to an
unchecked node or a failed replay.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.DerivationGraph

universe u v w
variable {J : Type u} {W : Type v} {Origin : Type w}

def materialize (cache : Array J) (nodes : List (Node J W Origin)) : Array J :=
  nodes.foldl (fun result node => result.push node.conclusion) cache

theorem replayFrom_eq_materialize {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) {cache result : Array J}
    {nodes : List (Node J interface.W Origin)}
    (accepted : replayFrom interface cache nodes = some result) :
    result = materialize cache nodes := by
  induction nodes generalizing cache with
  | nil => exact (Option.some.inj accepted).symm
  | cons node rest ih =>
      cases first : node.replay interface cache with
      | none => simp [replayFrom, first] at accepted
      | some next =>
          have remaining : replayFrom interface next rest = some result := by
            simpa [replayFrom, first] using accepted
          have same := Node.replay_eq_push interface first
          simpa only [materialize, List.foldl_cons, ← same] using ih remaining

theorem replayFrom_materialized {rules : List J → J → Prop}
    (interface : RuleWitness.{u, v} rules) {cache : Array J}
    {nodes : List (Node J interface.W Origin)}
    (accepted : ∃ result, replayFrom interface cache nodes = some result) :
    replayFrom interface cache nodes = some (materialize cache nodes) := by
  obtain ⟨result, replayed⟩ := accepted
  exact replayed.trans (congrArg some (replayFrom_eq_materialize interface replayed))

#print axioms replayFrom_eq_materialize
#print axioms replayFrom_materialized

end Mettapedia.Logic.DerivationGraph
