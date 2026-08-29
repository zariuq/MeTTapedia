import Mettapedia.Machines.RevisionedOccurrenceStore
import Mettapedia.Cybernetics.ObservedVariety
import Mettapedia.CognitiveArchitecture.Agent.MultiAgentFusionNoGo
import Mettapedia.GSLT.Dynamics.ContextualWorldMerge

/-!
# Occurrence-preserving revision lineage

Whole-mind revision is represented as a provenance DAG, not as destructive
replacement.  Every node has a revision-scoped occurrence identifier, a
generation, a payload state, and an authored list of older parent references.
The generation certificate makes the parent relation well-founded.

Fork and merge introduce fresh descendants.  They do not identify parents,
children, or equal payloads.  Comparison is observer-indexed and therefore
does not recover occurrence identity.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Agent.RevisionLineage

open Mettapedia.Machines
open Mettapedia.Cybernetics

universe uState uView

/-- A reference to one prior revision occurrence together with its certified
generation. -/
structure ParentRef (Owner Revision : Type) where
  id : StoreOccurrenceId Owner Revision
  generation : Nat
  deriving DecidableEq

/-- One immutable node of a revision lineage.  Parent order is retained and
duplicates are forbidden; every parent is older and occurrence-distinct from
the child. -/
structure Node (Owner Revision : Type)
    (State : Type uState) where
  id : StoreOccurrenceId Owner Revision
  generation : Nat
  state : State
  parents : List (ParentRef Owner Revision)
  parents_nodup : parents.Nodup
  parent_older : ∀ parent, parent ∈ parents → parent.generation < generation
  parent_fresh : ∀ parent, parent ∈ parents → parent.id ≠ id

namespace Node

variable {Owner Revision : Type}
variable {State : Type uState}

def ref (node : Node Owner Revision State) : ParentRef Owner Revision :=
  ⟨node.id, node.generation⟩

/-- `parent` is an immediate authored parent occurrence of `child`. -/
def IsParent (parent child : Node Owner Revision State) : Prop :=
  parent.ref ∈ child.parents

theorem generation_lt_of_isParent {parent child : Node Owner Revision State}
    (isParent : parent.IsParent child) :
    parent.generation < child.generation :=
  child.parent_older parent.ref isParent

theorem id_ne_of_isParent {parent child : Node Owner Revision State}
    (isParent : parent.IsParent child) :
    parent.id ≠ child.id :=
  child.parent_fresh parent.ref isParent

/-- The local generation certificates make the complete immediate-parent
relation well-founded. -/
theorem isParent_wellFounded :
    WellFounded (fun parent child : Node Owner Revision State =>
      parent.IsParent child) := by
  apply (measure (fun node : Node Owner Revision State => node.generation)).wf.mono
  intro parent child isParent
  exact generation_lt_of_isParent isParent

end Node

/-! ## Non-destructive fork and merge constructors -/

/-- A fork retains one parent and creates two occurrence-distinct children.
The children may have equal payload states. -/
structure Fork {Owner Revision : Type}
    {State : Type uState} (parent : Node Owner Revision State) where
  left : Node Owner Revision State
  right : Node Owner Revision State
  parent_of_left : parent.IsParent left
  parent_of_right : parent.IsParent right
  children_distinct : left.id ≠ right.id

namespace Fork

variable {Owner Revision : Type}
variable {State : Type uState} {parent : Node Owner Revision State}

theorem left_fresh (fork : Fork parent) : fork.left.id ≠ parent.id := by
  exact (Node.id_ne_of_isParent fork.parent_of_left).symm

theorem right_fresh (fork : Fork parent) : fork.right.id ≠ parent.id := by
  exact (Node.id_ne_of_isParent fork.parent_of_right).symm

/-- View both children as occurrence-preserving contextual worlds.  Equal
payload facts remain separate list occurrences and retain their distinct
lineage worlds. -/
def contextualChildren [DecidableEq Owner] [DecidableEq Revision]
    (fork : Fork parent) :
    Mettapedia.GSLT.Dynamics.ContextualWorldMerge.Carrier State
      (StoreOccurrenceId Owner Revision) :=
  [ { fact := fork.left.state, worlds := {fork.left.id} }
  , { fact := fork.right.state, worlds := {fork.right.id} }
  ]

end Fork

/-- A merge creates one new descendant with both occurrence-distinct parents.
It does not remove either parent or assert that their payload evidence glues. -/
structure Merge {Owner Revision : Type}
    {State : Type uState}
    (left right : Node Owner Revision State) where
  child : Node Owner Revision State
  parents_distinct : left.id ≠ right.id
  left_parent : left.IsParent child
  right_parent : right.IsParent child

namespace Merge

variable {Owner Revision : Type}
variable {State : Type uState}
variable {left right : Node Owner Revision State}

theorem child_fresh_left (merge : Merge left right) :
    merge.child.id ≠ left.id := by
  exact (Node.id_ne_of_isParent merge.left_parent).symm

theorem child_fresh_right (merge : Merge left right) :
    merge.child.id ≠ right.id := by
  exact (Node.id_ne_of_isParent merge.right_parent).symm

theorem parent_generations_lt (merge : Merge left right) :
    left.generation < merge.child.generation ∧
      right.generation < merge.child.generation :=
  ⟨Node.generation_lt_of_isParent merge.left_parent,
    Node.generation_lt_of_isParent merge.right_parent⟩

end Merge

/-! ## Observer-indexed comparison -/

/-- Two lineage occurrences are observationally equivalent for a selected
state observer.  This is deliberately weaker than occurrence equality. -/
def ObservationallyEquivalent
    {Owner Revision : Type}
    {State : Type uState} {View : Type uView}
    (observer : Observer State View)
    (left right : Node Owner Revision State) : Prop :=
  observer.observe left.state = observer.observe right.state

/-- An observer-indexed comparison may use a relation richer than equality
without becoming a global identity judgment. -/
def Compare
    {Owner Revision : Type}
    {State : Type uState} {View : Type uView}
    (observer : Observer State View) (relation : View → View → Prop)
    (left right : Node Owner Revision State) : Prop :=
  relation (observer.observe left.state) (observer.observe right.state)

/-! ## Positive and negative controls -/

namespace Canary

abbrev Owner := Unit
abbrev Revision := Nat
abbrev State := Bool

def occurrence (revision index : Nat) : StoreOccurrenceId Owner Revision :=
  ⟨⟨(), revision⟩, index⟩

def parent : Node Owner Revision State where
  id := occurrence 0 0
  generation := 0
  state := false
  parents := []
  parents_nodup := by simp
  parent_older := by simp
  parent_fresh := by simp

def leftCopy : Node Owner Revision State where
  id := occurrence 1 0
  generation := 1
  state := true
  parents := [parent.ref]
  parents_nodup := by simp
  parent_older := by
    intro prior member
    simp only [List.mem_singleton] at member
    subst prior
    decide
  parent_fresh := by
    intro prior member
    simp only [List.mem_singleton] at member
    subst prior
    decide

def rightCopy : Node Owner Revision State where
  id := occurrence 1 1
  generation := 1
  state := true
  parents := [parent.ref]
  parents_nodup := by simp
  parent_older := by
    intro prior member
    simp only [List.mem_singleton] at member
    subst prior
    decide
  parent_fresh := by
    intro prior member
    simp only [List.mem_singleton] at member
    subst prior
    decide

def equalStateFork : Fork parent where
  left := leftCopy
  right := rightCopy
  parent_of_left := by simp [Node.IsParent, leftCopy]
  parent_of_right := by simp [Node.IsParent, rightCopy]
  children_distinct := by decide

/-- Required negative control: copying an equal payload creates distinct
lineage occurrences. -/
theorem equal_state_distinct_copies :
    equalStateFork.left.state = equalStateFork.right.state ∧
      equalStateFork.left.id ≠ equalStateFork.right.id := by
  exact ⟨rfl, equalStateFork.children_distinct⟩

def stateObserver : Observer State State := Observer.identity State

/-- Even an exact state observer cannot recover occurrence identity from two
equal-state copies. -/
theorem observational_equivalence_not_occurrence_identity :
    ObservationallyEquivalent stateObserver
        equalStateFork.left equalStateFork.right ∧
      equalStateFork.left.id ≠ equalStateFork.right.id := by
  exact ⟨rfl, equalStateFork.children_distinct⟩

def contextualCopies := equalStateFork.contextualChildren

/-- The contextual-world carrier preserves both equal-state copy occurrences
and their exact lineage worlds; its set projection is intentionally coarser. -/
theorem contextual_worlds_preserve_copy_occurrences :
    contextualCopies.length = 2 ∧
      (Mettapedia.GSLT.Dynamics.ContextualWorldMerge.bagProjection
        contextualCopies).count true = 2 ∧
      Mettapedia.GSLT.Dynamics.ContextualWorldMerge.worldsFor true
        contextualCopies = {leftCopy.id, rightCopy.id} := by
  decide

def merged : Node Owner Revision State where
  id := occurrence 2 0
  generation := 2
  state := false
  parents := [leftCopy.ref, rightCopy.ref]
  parents_nodup := by
    simp [leftCopy, rightCopy, Node.ref, occurrence]
  parent_older := by
    intro prior member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  parent_fresh := by
    intro prior member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide

def mergeCopies : Merge leftCopy rightCopy where
  child := merged
  parents_distinct := by decide
  left_parent := by simp [Node.IsParent, merged]
  right_parent := by simp [Node.IsParent, merged]

theorem merge_is_new_multi_parent_descendant :
    leftCopy.IsParent mergeCopies.child ∧
      rightCopy.IsParent mergeCopies.child ∧
      mergeCopies.child.id ≠ leftCopy.id ∧
      mergeCopies.child.id ≠ rightCopy.id := by
  exact ⟨mergeCopies.left_parent, mergeCopies.right_parent,
    mergeCopies.child_fresh_left, mergeCopies.child_fresh_right⟩

/-- Pairwise agreement remains insufficient evidence for a global fusion.
Lineage construction and semantic gluing are therefore separate interfaces. -/
theorem pairwise_compatible_but_nongluable :
    MultiAgentFusionNoGo.antiChart.leftMinus =
        MultiAgentFusionNoGo.antiChart.rightMinus ∧
      MultiAgentFusionNoGo.antiChart.leftPlus =
        MultiAgentFusionNoGo.antiChart.rightPlus ∧
      ¬ ∃ joint : MultiAgentFusionNoGo.Joint3,
        MultiAgentFusionNoGo.RealizesAllPairs joint
          MultiAgentFusionNoGo.antiChart :=
  MultiAgentFusionNoGo.pairwise_compatible_not_gluable

end Canary

#print axioms Node.isParent_wellFounded
#print axioms Fork.left_fresh
#print axioms Merge.parent_generations_lt
#print axioms Canary.equal_state_distinct_copies
#print axioms Canary.observational_equivalence_not_occurrence_identity
#print axioms Canary.contextual_worlds_preserve_copy_occurrences
#print axioms Canary.merge_is_new_multi_parent_descendant
#print axioms Canary.pairwise_compatible_but_nongluable

end Mettapedia.CognitiveArchitecture.Agent.RevisionLineage
