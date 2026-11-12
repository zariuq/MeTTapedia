import Mettapedia.Languages.MeTTa.PeTTa.StreamingRegionPreservation

/-!
# Entry and paid prefixes retain the right region owners

Every actual request earns marker ordering and complete continuation links.
The logical-variable allocation counter is not used as a marker identity.
An arbitrary suspended prefix retains the same invariant on resumption.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Streaming.Regions

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

theorem enter_wellFormed (world : World) (expression : Atom) : WellFormed (enter world expression) :=
  ⟨True.intro,True.intro,True.intro⟩

theorem every_request_prefix_wellFormed (registry : SpaceSemantics.Program) (fuel : Nat)
    (world : World) (expression : Atom) : WellFormed (advance registry fuel (enter world expression)) :=
  advance_wellFormed registry fuel _ (enter_wellFormed world expression)

theorem every_reachable_request_wellFormed {registry : SpaceSemantics.Program} {world : World}
    {expression : Atom} {state : State}
    (path : Relation.ReflTransGen (Transition registry) (enter world expression) state) : WellFormed state :=
  path_wellFormed path (enter_wellFormed world expression)

theorem paid_resumption_wellFormed (registry : SpaceSemantics.Program) (first second : Nat)
    (world : World) (expression : Atom) :
    WellFormed (advance registry second (advance registry first (enter world expression))) :=
  advance_wellFormed registry second _ (every_request_prefix_wellFormed registry first world expression)

theorem marker_keys_unique (state : State) (good : WellFormed state) :
    ((markers state.agenda).map Boundary.key).Nodup := ordered_keys_nodup good.1

theorem marker_key_allocated (state : State) (good : WellFormed state) :
    ∀ scope ∈ markers state.agenda, scope.key < state.nextBoundary := ordered_key_lt good.1

theorem next_marker_fresh (state : State) (good : WellFormed state) :
    ∀ scope ∈ markers state.agenda, scope.key ≠ state.nextBoundary := by
  intro scope present
  exact Nat.ne_of_lt (marker_key_allocated state good scope present)

theorem job_links_at {state : State} {before older : List Job} {job : Job}
    (good : WellFormed state) (agenda : state.agenda = before ++ job :: older) :
    jobFits (markers older) job := by
  have all := good.2
  rw [agenda] at all
  exact (linked_suffix before (job :: older) all).1

theorem task_links_at {state : State} {before older : List Job} {task : Task}
    (good : WellFormed state) (agenda : state.agenda = before ++ .execute task :: older) :
    framesFit (markers older) task.frames := job_links_at good agenda

/-- These wrappers retain proofs of the actual state, not a second controller. -/
def enterLinked (world : World) (expression : Atom) : {state : State // WellFormed state} :=
  ⟨enter world expression,enter_wellFormed world expression⟩

def advanceLinked (registry : SpaceSemantics.Program) (fuel : Nat)
    (source : {state : State // WellFormed state}) : {state : State // WellFormed state} :=
  ⟨advance registry fuel source.val,advance_wellFormed registry fuel source.val source.property⟩

end Mettapedia.Languages.MeTTa.PeTTa.Streaming.Regions
