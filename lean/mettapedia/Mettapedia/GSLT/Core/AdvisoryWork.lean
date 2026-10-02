import Mettapedia.GSLT.Core.BoundedPublication

/-!
# Pure advisory work and semantic observation

Authorized bodies and resumable scoring jobs are admitted separately. A score
may inform a lawful controller's memory, but the scoring system has no answer
emission and cannot create body work. The body is already live while scoring
is unfinished.

The semantic frontier is an observation of the whole frontier. Its closure
can certify that all source answers have been observed even when a pure
advisory computation is still running. Whole-work closure remains a different
judgment. Effectful computations cannot use this erasure contract.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.AdvisoryWork

open BranchingTemporal
open InferenceControl (Controller)

variable {Node Score Answer Memory : Type*}

inductive Task (Node Score : Type*) where
  | body (node : Node)
  | scoring (state : Score)
  deriving Repr, DecidableEq

def body? : Task Node Score → Option Node
  | .body node => some node
  | .scoring _ => none

def bodies (tasks : List (Task Node Score)) : List Node := tasks.filterMap body?

def system (source : BranchingSystem Node Answer) (scoring : Score → List Score) :
    BranchingSystem (Task Node Score) Answer where
  emit
    | .body node => source.emit node
    | .scoring _ => none
  successors
    | .body node => (source.successors node).map Task.body
    | .scoring state => (scoring state).map Task.scoring

def admit (roots : List Node) (scores : List Score) : List (Task Node Score) :=
  roots.map Task.body ++ scores.map Task.scoring

@[simp] theorem bodies_admit (roots : List Node) (scores : List Score) :
    bodies (admit roots scores) = roots := by
  simp [bodies, admit, List.filterMap_map, body?, Function.comp_def]

/-- Scoring is not a gate preceding body admission. -/
theorem body_admitted (roots : List Node) (scores : List Score) {node : Node}
    (member : node ∈ roots) : Task.body node ∈ admit roots scores := by
  exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨node, member, rfl⟩))

theorem generated_body_lifts (source : BranchingSystem Node Answer)
    (scoring : Score → List Score) (roots : List (Task Node Score)) {node : Node}
    (generated : Generated source (bodies roots) node) :
    Generated (system source scoring) roots (.body node) := by
  induction generated with
  | @root node member =>
      obtain ⟨task, present, erased⟩ := List.mem_filterMap.mp member
      cases task with
      | body original =>
          have same : original = node := Option.some.inj erased
          subst original
          exact .root present
      | scoring state => simp [body?] at erased
  | @successor parent child prior member ih =>
      exact .successor ih (List.mem_map.mpr ⟨child, member, rfl⟩)

/-- Every reached body arose from an independently authorized source step.
A scoring descendant cannot cross into body authority. -/
theorem generated_body_erases (source : BranchingSystem Node Answer)
    (scoring : Score → List Score) (roots : List (Task Node Score))
    {task : Task Node Score} (generated : Generated (system source scoring) roots task) :
    ∀ node, body? task = some node → Generated source (bodies roots) node := by
  induction generated with
  | @root task member =>
      intro node erased
      exact .root (List.mem_filterMap.mpr ⟨task, member, erased⟩)
  | @successor parent child prior member ih =>
      intro node erased
      cases parent with
      | body original =>
          obtain ⟨next, edge, same⟩ := List.mem_map.mp member
          subst child
          have equal : next = node := Option.some.inj erased
          subst next
          exact .successor (ih original rfl) edge
      | scoring state =>
          obtain ⟨next, _, same⟩ := List.mem_map.mp member
          subst child
          simp [body?] at erased

theorem generated_body_iff (source : BranchingSystem Node Answer)
    (scoring : Score → List Score) (roots : List (Task Node Score)) (node : Node) :
    Generated (system source scoring) roots (.body node) ↔
      Generated source (bodies roots) node :=
  ⟨fun generated => generated_body_erases source scoring roots generated node rfl,
    generated_body_lifts source scoring roots⟩

def projectEvent (event : Emission (Task Node Score) Answer) : Option (Emission Node Answer) :=
  (body? event.origin).map (fun node => ⟨node, event.value⟩)

def observe (state : BranchingTemporal.Snapshot (Task Node Score) Answer) :
    BranchingTemporal.Snapshot Node Answer :=
  ⟨state.events.filterMap projectEvent, bodies state.frontier⟩

/-- Coverage transports through the actual source/body embedding. Pure advice
is erased only after proving it cannot hide an unobserved source answer. -/
theorem coverage_erases (source : BranchingSystem Node Answer)
    (scoring : Score → List Score) (roots : List (Task Node Score))
    (state : BranchingTemporal.Snapshot (Task Node Score) Answer)
    (covered : BoundedPublication.Covers (system source scoring) roots state) :
    BoundedPublication.Covers source (bodies roots) (observe state) := by
  intro node answer generated emits
  have lifted := generated_body_lifts source scoring roots generated
  rcases covered (.body node) answer lifted emits with seen | remaining
  · left
    exact List.mem_filterMap.mpr ⟨⟨.body node, answer⟩, seen, rfl⟩
  · right
    exact generated_body_erases source scoring state.frontier remaining node rfl

theorem controlled_coverage (source : BranchingSystem Node Answer)
    (scoring : Score → List Score)
    (controller : Controller (Task Node Score) Answer Memory)
    (roots : List Node) (scores : List Score) (fuel : Nat) :
    BoundedPublication.Covers source roots
      (observe (InferenceControl.Snapshot.run (system source scoring) controller fuel
        (InferenceControl.Snapshot.initial controller (admit roots scores))).search) := by
  have covered := coverage_erases source scoring (admit roots scores) _
    (BoundedPublication.covers_controlled_run (system source scoring) controller
      (admit roots scores) fuel)
  simpa only [bodies_admit] using covered

/-- Closure of the body observation accounts for every source answer, even
if pure advisory work remains. It does not establish whole-work closure. -/
theorem semantic_closure_complete (source : BranchingSystem Node Answer)
    (scoring : Score → List Score)
    (controller : Controller (Task Node Score) Answer Memory)
    (roots : List Node) (scores : List Score) (fuel : Nat)
    (closed : (observe (InferenceControl.Snapshot.run (system source scoring) controller fuel
      (InferenceControl.Snapshot.initial controller (admit roots scores))).search).frontier = [])
    (node : Node) (answer : Answer) (generated : Generated source roots node)
    (emits : source.emit node = some answer) :
    (⟨node, answer⟩ : Emission Node Answer) ∈
      (observe (InferenceControl.Snapshot.run (system source scoring) controller fuel
        (InferenceControl.Snapshot.initial controller (admit roots scores))).search).events := by
  rcases controlled_coverage source scoring controller roots scores fuel
      node answer generated emits with seen | pending
  · exact seen
  · rw [closed] at pending
    have impossible : ∀ target : Node, ¬ Generated source [] target := by
      intro target path
      induction path with
      | root member => simp at member
      | successor _ _ ih => exact ih
    exact False.elim (impossible node pending)

namespace Controls

def oneAnswer : BranchingSystem Unit Nat := ⟨fun _ => some 7, fun _ => []⟩
def divergent : Unit → List Unit := fun _ => [()]
def fifo : Controller (Task Unit Unit) Nat Unit := .fixed Scheduler.breadthFirst

def afterBody :=
  InferenceControl.Snapshot.run (system oneAnswer divergent) fifo 1
    (InferenceControl.Snapshot.initial fifo (admit [()] [()]))

example : (observe afterBody.search).events.map Emission.value = [7] := by decide
example : (observe afterBody.search).frontier = [] := by decide
example : afterBody.search.frontier ≠ [] := by decide

/-- Turning a scoring result into an answer changes the authority boundary. -/
example : (system oneAnswer divergent).emit (.scoring ()) = none := rfl

end Controls

end Mettapedia.GSLT.Core.AdvisoryWork
