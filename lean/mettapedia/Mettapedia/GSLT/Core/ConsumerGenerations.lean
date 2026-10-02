import Mettapedia.GSLT.Core.AdvisoryWork

/-!
# Revoking a pure consumer generation

Source production and pure consumer work have separate authority. Each
consumer job and response names its generation; its descendants keep that
generation and cannot create source work. Revocation returns an exact list
of removed occurrences while retaining source work and other generations.

The new observation forgets obsolete consumers. Its remaining source and
current-consumer computations agree with independently defined transitions.
This boundary applies to detached pure consumers, not effectful work or jobs
on which source production depends. A new goal must admit its own consumer
work over retained witnesses; revocation does not manufacture that work.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ConsumerGenerations

open BranchingTemporal

variable {Node Job Answer Response : Type*}

inductive Task (Node Job : Type*) where
  | source (node : Node)
  | consumer (generation : Nat) (job : Job)
  deriving Repr, DecidableEq

def belongs (generation : Nat) : Task Node Job → Bool
  | .source _ => false
  | .consumer owner _ => owner == generation

def revoke (generation : Nat) (tasks : List (Task Node Job)) : List (Task Node Job) :=
  tasks.filter fun task => !belongs generation task

def receipt (generation : Nat) (tasks : List (Task Node Job)) : List (Task Node Job) :=
  tasks.filter (belongs generation)

/-- Revocation partitions occurrences; equal payloads are not deduplicated. -/
theorem revocation_partition (generation : Nat) (tasks : List (Task Node Job)) :
    (receipt generation tasks ++ revoke generation tasks).Perm tasks :=
  List.filter_append_perm (belongs generation) tasks

theorem removed_owned (generation : Nat) (tasks : List (Task Node Job))
    (task : Task Node Job) (removed : task ∈ receipt generation tasks) :
    ∃ job, task = .consumer generation job := by
  obtain ⟨_, owned⟩ := List.mem_filter.mp removed
  cases task with
  | source node => simp [belongs] at owned
  | consumer owner job =>
      have same : owner = generation := by simpa [belongs] using owned
      subst owner
      exact ⟨job, rfl⟩

def source? : Task Node Job → Option Node
  | .source node => some node
  | .consumer _ _ => none

def current? (generation : Nat) : Task Node Job → Option (Node ⊕ Job)
  | .source node => some (.inl node)
  | .consumer owner job => if owner = generation then some (.inr job) else none

theorem source_preserved (generation : Nat) (tasks : List (Task Node Job)) :
    (revoke generation tasks).filterMap source? = tasks.filterMap source? := by
  induction tasks with
  | nil => rfl
  | cons task tasks ih =>
      cases task with
      | source node => simpa [revoke, source?, belongs] using congrArg (node :: ·) ih
      | consumer owner job =>
          by_cases owned : owner = generation
          · simp_all [revoke, List.filterMap_cons, source?, belongs]
          · simp_all [revoke, List.filterMap_cons, source?, belongs]

/-- Cancellation of an obsolete generation leaves the new observation's
owned work unchanged, including its occurrence multiplicity and order. -/
theorem current_preserved (old current : Nat) (different : old ≠ current)
    (tasks : List (Task Node Job)) :
    (revoke old tasks).filterMap (current? current) = tasks.filterMap (current? current) := by
  induction tasks with
  | nil => rfl
  | cons task tasks ih =>
      cases task with
      | source node =>
          simpa [revoke, belongs, current?] using congrArg (Sum.inl node :: ·) ih
      | consumer owner job =>
          by_cases obsolete : owner = old
          · subst owner
            simpa [revoke, belongs, current?, different] using ih
          · by_cases active : owner = current
            · simp_all [revoke, belongs, current?]
            · simpa [revoke, belongs, current?, obsolete, active] using ih

def system (source : BranchingSystem Node Answer)
    (consumers : Nat → BranchingSystem Job Response) :
    BranchingSystem (Task Node Job) (Answer ⊕ (Nat × Response)) where
  emit
    | .source node => (source.emit node).map Sum.inl
    | .consumer generation job => (consumers generation |>.emit job).map
        (fun response => .inr (generation, response))
  successors
    | .source node => (source.successors node).map Task.source
    | .consumer generation job => (consumers generation |>.successors job).map
        (Task.consumer generation)

def currentSystem (source : BranchingSystem Node Answer)
    (consumer : BranchingSystem Job Response) :
    BranchingSystem (Node ⊕ Job) (Answer ⊕ Response) where
  emit
    | .inl node => (source.emit node).map Sum.inl
    | .inr job => (consumer.emit job).map Sum.inr
  successors
    | .inl node => (source.successors node).map Sum.inl
    | .inr job => (consumer.successors job).map Sum.inr

def embed (generation : Nat) : Node ⊕ Job → Task Node Job
  | .inl node => .source node
  | .inr job => .consumer generation job

@[simp] theorem current_embed (generation : Nat) (node : Node ⊕ Job) :
    current? generation (embed generation node) = some node := by
  cases node <;> simp [current?, embed]

theorem generated_lifts (source : BranchingSystem Node Answer)
    (consumers : Nat → BranchingSystem Job Response) (current : Nat)
    (roots : List (Task Node Job)) {node : Node ⊕ Job}
    (generated : Generated (currentSystem source (consumers current))
      (roots.filterMap (current? current)) node) :
    Generated (system source consumers) roots (embed current node) := by
  induction generated with
  | @root node member =>
      obtain ⟨task, present, projected⟩ := List.mem_filterMap.mp member
      cases task with
      | source original =>
          have same : Sum.inl original = node := Option.some.inj projected
          subst node
          exact .root present
      | consumer generation job =>
          by_cases active : generation = current
          · subst generation
            have same : Sum.inr job = node := Option.some.inj (by
              simpa [current?] using projected)
            subst node
            exact .root present
          · simp [current?, active] at projected
  | @successor parent child previous member ih =>
      apply Generated.successor ih
      cases parent with
      | inl original =>
          obtain ⟨next, adjacent, same⟩ := List.mem_map.mp member
          subst child
          exact List.mem_map.mpr ⟨next, adjacent, rfl⟩
      | inr job =>
          obtain ⟨next, adjacent, same⟩ := List.mem_map.mp member
          subst child
          exact List.mem_map.mpr ⟨next, adjacent, rfl⟩

theorem generated_erases (source : BranchingSystem Node Answer)
    (consumers : Nat → BranchingSystem Job Response) (current : Nat)
    (roots : List (Task Node Job)) {task : Task Node Job}
    (generated : Generated (system source consumers) roots task) :
    ∀ node, current? current task = some node →
      Generated (currentSystem source (consumers current))
        (roots.filterMap (current? current)) node := by
  induction generated with
  | @root task member =>
      intro node projected
      exact .root (List.mem_filterMap.mpr ⟨task, member, projected⟩)
  | @successor parent child previous member ih =>
      intro node projected
      cases parent with
      | source original =>
          obtain ⟨next, adjacent, same⟩ := List.mem_map.mp member
          subst child
          have sameNode : Sum.inl next = node := Option.some.inj projected
          subst node
          exact .successor (ih (.inl original) rfl)
            (List.mem_map.mpr ⟨next, adjacent, rfl⟩)
      | consumer generation job =>
          obtain ⟨next, adjacent, same⟩ := List.mem_map.mp member
          subst child
          by_cases active : generation = current
          · subst generation
            have sameNode : Sum.inr next = node := Option.some.inj (by
              simpa [current?] using projected)
            subst node
            exact .successor (ih (.inr job) (by simp [current?]))
              (List.mem_map.mpr ⟨next, adjacent, rfl⟩)
          · simp [current?, active] at projected

/-- No obsolete consumer descendant can create a new source or current
consumer computation. Conversely every projected computation remains live
after removing obsolete roots. -/
theorem generated_after_revocation (source : BranchingSystem Node Answer)
    (consumers : Nat → BranchingSystem Job Response) (old current : Nat)
    (different : old ≠ current) (roots : List (Task Node Job)) (node : Node ⊕ Job) :
    Generated (system source consumers) (revoke old roots) (embed current node) ↔
      Generated (currentSystem source (consumers current))
        (roots.filterMap (current? current)) node := by
  constructor
  · intro reached
    have erased := generated_erases source consumers current (revoke old roots)
      reached node (current_embed current node)
    simpa only [current_preserved old current different roots] using erased
  · intro reached
    apply generated_lifts source consumers current (revoke old roots)
    simpa only [current_preserved old current different roots] using reached

def embedAnswer (generation : Nat) : Answer ⊕ Response → Answer ⊕ (Nat × Response)
  | .inl answer => .inl answer
  | .inr response => .inr (generation, response)

def response? (generation : Nat) : Answer ⊕ (Nat × Response) → Option (Answer ⊕ Response)
  | .inl answer => some (.inl answer)
  | .inr (owner, response) => if owner = generation then some (.inr response) else none

@[simp] theorem response_embed (generation : Nat) (answer : Answer ⊕ Response) :
    response? generation (embedAnswer generation answer) = some answer := by
  cases answer <;> simp [response?, embedAnswer]

theorem emit_embed (source : BranchingSystem Node Answer)
    (consumers : Nat → BranchingSystem Job Response) (current : Nat) (node : Node ⊕ Job) :
    (system source consumers).emit (embed current node) =
      ((currentSystem source (consumers current)).emit node).map (embedAnswer current) := by
  cases node <;> simp [system, currentSystem, embed, embedAnswer, Option.map_map,
    Function.comp_def]

def projectEvent (current : Nat)
    (event : Emission (Task Node Job) (Answer ⊕ (Nat × Response))) :
    Option (Emission (Node ⊕ Job) (Answer ⊕ Response)) :=
  match current? current event.origin, response? current event.value with
  | some origin, some value => some ⟨origin, value⟩
  | _, _ => none

def observe (current : Nat)
    (state : BranchingTemporal.Snapshot (Task Node Job) (Answer ⊕ (Nat × Response))) :
    BranchingTemporal.Snapshot (Node ⊕ Job) (Answer ⊕ Response) :=
  ⟨state.events.filterMap (projectEvent current), state.frontier.filterMap (current? current)⟩

/-- A source/current observation retains coverage of independently permitted
answers. An obsolete consumer response cannot satisfy the new observation. -/
theorem coverage_projects (source : BranchingSystem Node Answer)
    (consumers : Nat → BranchingSystem Job Response) (current : Nat)
    (roots : List (Task Node Job))
    (state : BranchingTemporal.Snapshot (Task Node Job) (Answer ⊕ (Nat × Response)))
    (covered : BoundedPublication.Covers (system source consumers) roots state) :
    BoundedPublication.Covers (currentSystem source (consumers current))
      (roots.filterMap (current? current)) (observe current state) := by
  intro node answer generated emitted
  have lifted := generated_lifts source consumers current roots generated
  have emittedLift : (system source consumers).emit (embed current node) =
      some (embedAnswer current answer) := by
    rw [emit_embed, emitted]
    rfl
  rcases covered (embed current node) (embedAnswer current answer) lifted emittedLift with
    seen | pending
  · left
    apply List.mem_filterMap.mpr
    refine ⟨⟨embed current node, embedAnswer current answer⟩, seen, ?_⟩
    simp [projectEvent]
  · right
    exact generated_erases source consumers current state.frontier pending node
      (current_embed current node)

theorem revoke_observation (old current : Nat) (different : old ≠ current)
    (state : BranchingTemporal.Snapshot (Task Node Job) (Answer ⊕ (Nat × Response))) :
    observe current ⟨state.events, revoke old state.frontier⟩ = observe current state := by
  simp only [observe, current_preserved old current different state.frontier]

theorem coverage_after_revocation (source : BranchingSystem Node Answer)
    (consumers : Nat → BranchingSystem Job Response) (old current : Nat)
    (different : old ≠ current) (roots : List (Task Node Job))
    (state : BranchingTemporal.Snapshot (Task Node Job) (Answer ⊕ (Nat × Response)))
    (covered : BoundedPublication.Covers (system source consumers) roots state) :
    BoundedPublication.Covers (currentSystem source (consumers current))
      (roots.filterMap (current? current))
      (observe current ⟨state.events, revoke old state.frontier⟩) := by
  rw [revoke_observation old current different state]
  exact coverage_projects source consumers current roots state covered

namespace Controls

def pending : List (Task Nat Nat) :=
  [.source 7, .consumer 1 10, .consumer 1 10, .consumer 2 20]

example : revoke 1 pending = [.source 7, .consumer 2 20] := by decide
example : receipt 1 pending = [.consumer 1 10, .consumer 1 10] := by decide
example : (revoke 1 pending).filterMap (current? 2) = [.inl 7, .inr 20] := by decide

example : response? (Answer := Nat) (Response := Bool) 2 (.inr (1, true)) = none := by decide
example : response? (Answer := Nat) (Response := Bool) 2 (.inr (2, false)) =
    some (.inr false) := by decide

/-- A consumer-to-source edge violates the declared authority contract. -/
example : Task.source 7 ∉
    (system (Node := Nat) (Job := Nat) (Answer := Nat) (Response := Nat)
      ⟨fun _ => none, fun _ => []⟩ (fun _ => ⟨fun _ => none, fun job => [job]⟩)).successors
        (.consumer 1 0) := by decide

end Controls

end Mettapedia.GSLT.Core.ConsumerGenerations
