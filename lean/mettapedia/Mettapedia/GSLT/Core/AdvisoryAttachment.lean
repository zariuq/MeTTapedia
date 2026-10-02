import Mettapedia.GSLT.Core.AdvisoryWork

/-!
# Attaching pure advice during source expansion

Newly admitted source successors may create scoring jobs. These jobs may
continue after source closure, but cannot create source work, publish source
answers, or suppress a successor. The carrier, observations and initial
admission reuse `AdvisoryWork`; the only new operation is attachment at a
source edge.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.AdvisoryAttachment

open BranchingTemporal AdvisoryWork
open InferenceControl (Controller)

variable {Node Score Answer Memory : Type*}

def system (source : BranchingSystem Node Answer) (scoring : Score → List Score)
    (attach : Node → Node → List Score) : BranchingSystem (Task Node Score) Answer where
  emit
    | .body node => source.emit node
    | .scoring _ => none
  successors
    | .body node =>
        (source.successors node).map Task.body ++
          ((source.successors node).flatMap (attach node)).map Task.scoring
    | .scoring score => (scoring score).map Task.scoring

/-- Attachment is multiplicity preserving on the complete source successor
list, rather than merely preserving its set support. -/
theorem successor_projection (source : BranchingSystem Node Answer)
    (scoring : Score → List Score) (attach : Node → Node → List Score) (node : Node) :
    bodies ((system source scoring attach).successors (.body node)) =
      source.successors node := by
  simp [system, bodies, List.filterMap_map, body?, Function.comp_def]

theorem generated_body_lifts (source : BranchingSystem Node Answer)
    (scoring : Score → List Score) (attach : Node → Node → List Score)
    (roots : List (Task Node Score)) {node : Node}
    (generated : Generated source (bodies roots) node) :
    Generated (system source scoring attach) roots (.body node) := by
  induction generated with
  | @root node member =>
      obtain ⟨task, present, erased⟩ := List.mem_filterMap.mp member
      cases task with
      | body original =>
          have same : original = node := Option.some.inj erased
          subst original
          exact .root present
      | scoring score => simp [body?] at erased
  | @successor parent child _ member ih =>
      exact .successor ih (List.mem_append_left _ (List.mem_map.mpr ⟨child, member, rfl⟩))

theorem generated_body_erases (source : BranchingSystem Node Answer)
    (scoring : Score → List Score) (attach : Node → Node → List Score)
    (roots : List (Task Node Score)) {task : Task Node Score}
    (generated : Generated (system source scoring attach) roots task) :
    ∀ node, body? task = some node → Generated source (bodies roots) node := by
  induction generated with
  | @root task member =>
      intro node erased
      exact .root (List.mem_filterMap.mpr ⟨task, member, erased⟩)
  | @successor parent child _ member ih =>
      intro node erased
      cases parent with
      | body original =>
          rcases List.mem_append.mp member with bodyMember | scoreMember
          · obtain ⟨next, edge, same⟩ := List.mem_map.mp bodyMember
            subst child
            have equal : next = node := Option.some.inj erased
            subst next
            exact .successor (ih original rfl) edge
          · obtain ⟨next, _, same⟩ := List.mem_map.mp scoreMember
            subst child
            simp [body?] at erased
      | scoring score =>
          obtain ⟨next, _, same⟩ := List.mem_map.mp member
          subst child
          simp [body?] at erased

theorem generated_body_iff (source : BranchingSystem Node Answer)
    (scoring : Score → List Score) (attach : Node → Node → List Score)
    (roots : List (Task Node Score)) (node : Node) :
    Generated (system source scoring attach) roots (.body node) ↔
      Generated source (bodies roots) node :=
  ⟨fun generated => generated_body_erases source scoring attach roots generated node rfl,
    generated_body_lifts source scoring attach roots⟩

theorem coverage_erases (source : BranchingSystem Node Answer)
    (scoring : Score → List Score) (attach : Node → Node → List Score)
    (roots : List (Task Node Score))
    (state : BranchingTemporal.Snapshot (Task Node Score) Answer)
    (covered : BoundedPublication.Covers (system source scoring attach) roots state) :
    BoundedPublication.Covers source (bodies roots) (observe state) := by
  intro node answer generated emits
  have lifted := generated_body_lifts source scoring attach roots generated
  rcases covered (.body node) answer lifted emits with seen | remaining
  · left
    exact List.mem_filterMap.mpr ⟨⟨.body node, answer⟩, seen, rfl⟩
  · right
    exact generated_body_erases source scoring attach state.frontier remaining node rfl

theorem controlled_coverage (source : BranchingSystem Node Answer)
    (scoring : Score → List Score) (attach : Node → Node → List Score)
    (controller : Controller (Task Node Score) Answer Memory)
    (roots : List Node) (scores : List Score) (fuel : Nat) :
    BoundedPublication.Covers source roots
      (observe (InferenceControl.Snapshot.run (system source scoring attach) controller fuel
        (InferenceControl.Snapshot.initial controller (admit roots scores))).search) := by
  have covered := coverage_erases source scoring attach (admit roots scores) _
    (BoundedPublication.covers_controlled_run (system source scoring attach) controller
      (admit roots scores) fuel)
  simpa only [bodies_admit] using covered

theorem semantic_closure_complete (source : BranchingSystem Node Answer)
    (scoring : Score → List Score) (attach : Node → Node → List Score)
    (controller : Controller (Task Node Score) Answer Memory)
    (roots : List Node) (scores : List Score) (fuel : Nat)
    (closed : (observe (InferenceControl.Snapshot.run (system source scoring attach) controller fuel
      (InferenceControl.Snapshot.initial controller (admit roots scores))).search).frontier = [])
    (node : Node) (answer : Answer) (generated : Generated source roots node)
    (emits : source.emit node = some answer) :
    (⟨node, answer⟩ : Emission Node Answer) ∈
      (observe (InferenceControl.Snapshot.run (system source scoring attach) controller fuel
        (InferenceControl.Snapshot.initial controller (admit roots scores))).search).events := by
  rcases controlled_coverage source scoring attach controller roots scores fuel
      node answer generated emits with seen | pending
  · exact seen
  · rw [closed] at pending
    have impossible : ∀ target : Node, ¬ Generated source [] target := by
      intro target path
      induction path with
      | root member => simp at member
      | successor _ _ ih => exact ih
    exact False.elim (impossible node pending)

end Mettapedia.GSLT.Core.AdvisoryAttachment
