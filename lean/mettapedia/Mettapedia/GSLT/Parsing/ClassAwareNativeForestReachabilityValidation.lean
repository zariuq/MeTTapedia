import Mettapedia.GSLT.Parsing.ClassAwareNativeForestIdentityInventory

/-!
# Executable reachability validation for a native packed forest

The neutral C forest contract rejects nodes which are not reachable from an
exported root.  This module mirrors that finite check independently in Lean.
Membership in the computed closure constructs the existing semantic
`Reachable` judgment; it is not inferred from node or choice counts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareNativeForestReachabilityValidation

open Mettapedia.GSLT.Parsing.ClassAwareNativeForestContract
open Mettapedia.GSLT.Parsing.ClassAwareNativeForestStructuralValidation

/-- The optional binary prefix followed by the mandatory right child. -/
def choiceTargets (choice : Choice) : List Nat :=
  choice.prefixNode.toList ++ [choice.childNode]

/-- All outgoing targets whose choice declares this physical parent. -/
def nodeSuccessors (view : ForestView) (parentIndex : Nat) : List Nat :=
  (view.choices.filter fun choice => choice.parent == parentIndex).flatMap
    choiceTargets

/-- A single physical graph edge through either the prefix or child field. -/
def OneHop (view : ForestView) (parentIndex childIndex : Nat) : Prop :=
  ∃ choice, choice ∈ view.choices ∧
    choice.parent = parentIndex ∧
    (choice.prefixNode = some childIndex ∨
      childIndex = choice.childNode)

theorem mem_nodeSuccessors_iff
    (view : ForestView) (parentIndex childIndex : Nat) :
    childIndex ∈ nodeSuccessors view parentIndex ↔
      OneHop view parentIndex childIndex := by
  simp [nodeSuccessors, choiceTargets, OneHop, and_assoc]

/-- Positional choice ownership entails the parent-indexed ownership used by
the semantic forest derivations. -/
theorem choiceAtOwned_toOwnedChoice
    {view : ForestView} {choiceIndex : Nat} {choice : Choice}
    (ownedAt : ChoiceAtOwned view choiceIndex choice) :
    OwnedChoice view choice.parent choice := by
  rcases ownedAt with
    ⟨parent, localIndex, parentAt, localValid,
      choiceIndexExact, choiceAt⟩
  refine ⟨parent, localIndex, parentAt, localValid, ?_, rfl⟩
  rwa [← choiceIndexExact]

/-- One checked physical edge extends semantic reachability. -/
theorem oneHop_reachable
    {view : ForestView} (arrays : ForestArraysCoherent view)
    {parentIndex childIndex : Nat}
    (parentReachable : Reachable view parentIndex)
    (hop : OneHop view parentIndex childIndex) :
    Reachable view childIndex := by
  rcases hop with
    ⟨choice, choiceMember, parentExact, prefixExact | childExact⟩
  all_goals
    rw [List.mem_iff_getElem] at choiceMember
    rcases choiceMember with
      ⟨choiceIndex, choiceIndexValid, choiceAtIndex⟩
    have choiceAt : view.choices[choiceIndex]? = some choice := by
      rw [List.getElem?_eq_some_iff]
      exact ⟨choiceIndexValid, choiceAtIndex⟩
    have ownedAt := arrays.choicesOwned choiceIndex choice choiceAt
    have owned : OwnedChoice view parentIndex choice := by
      rw [← parentExact]
      exact choiceAtOwned_toOwnedChoice ownedAt
  · exact Reachable.prefix parentReachable owned prefixExact
  · rw [childExact]
    exact Reachable.child parentReachable owned

/-- One monotone root-closure round. -/
def expand (view : ForestView) (seen : List Nat) : List Nat :=
  (seen ++ seen.flatMap (nodeSuccessors view)).eraseDups

/-- Root closure after a fixed number of rounds.  The node count is used by
the complete validator; the soundness theorem holds for every round count. -/
def reachableWithin (view : ForestView) : Nat → List Nat
  | 0 => view.roots.eraseDups
  | rounds + 1 => expand view (reachableWithin view rounds)

theorem expand_sound
    {view : ForestView} (arrays : ForestArraysCoherent view)
    {seen : List Nat}
    (seenSound : ∀ index, index ∈ seen → Reachable view index)
    {index : Nat} (member : index ∈ expand view seen) :
    Reachable view index := by
  simp only [expand, List.mem_eraseDups, List.mem_append,
    List.mem_flatMap] at member
  rcases member with direct | ⟨parentIndex, parentMember, successorMember⟩
  · exact seenSound index direct
  · exact oneHop_reachable arrays (seenSound parentIndex parentMember)
      ((mem_nodeSuccessors_iff view parentIndex index).mp successorMember)

theorem reachableWithin_sound
    {view : ForestView} (arrays : ForestArraysCoherent view)
    (rounds : Nat) {index : Nat}
    (member : index ∈ reachableWithin view rounds) :
    Reachable view index := by
  induction rounds generalizing index with
  | zero =>
      exact Reachable.root (by simpa [reachableWithin] using member)
  | succ rounds inductionHypothesis =>
      exact expand_sound arrays
        (fun candidate candidateMember =>
          inductionHypothesis candidateMember)
        (by simpa [reachableWithin] using member)

/-- Every physical node occurrence appears in the finite root closure. -/
def validateReachable (view : ForestView) : Bool :=
  (List.range view.nodes.length).all fun index =>
    decide (index ∈ reachableWithin view view.nodes.length)

/-- The executable closure check proves exactly the reachability premise of
`Represents`. -/
theorem validateReachable_sound
    {view : ForestView} (arrays : ForestArraysCoherent view)
    (accepted : validateReachable view = true) :
    ∀ index node, view.nodes[index]? = some node → Reachable view index := by
  intro index node nodeAt
  rw [List.getElem?_eq_some_iff] at nodeAt
  have indexMember : index ∈ List.range view.nodes.length := by
    simp [nodeAt.1]
  have closureMember :
      index ∈ reachableWithin view view.nodes.length := by
    exact of_decide_eq_true
      ((List.all_eq_true.mp accepted) index indexMember)
  exact reachableWithin_sound arrays view.nodes.length closureMember

/-- The two purely structural premises of `Represents`, before semantic
family decoding and identity interpretation. -/
structure StructurallyComplete (view : ForestView) : Prop where
  arraysCoherent : ForestArraysCoherent view
  nodesReachable : ∀ index node,
    view.nodes[index]? = some node → Reachable view index

def validateStructure (view : ForestView) : Bool :=
  validateArrays view && validateReachable view

theorem validateStructure_sound {view : ForestView}
    (accepted : validateStructure view = true) :
    StructurallyComplete view := by
  rw [validateStructure, Bool.and_eq_true_iff] at accepted
  have arrays := validateArrays_sound accepted.1
  exact {
    arraysCoherent := arrays
    nodesReachable := validateReachable_sound arrays accepted.2
  }

/-! ## Positive and negative controls -/

private def rootOnlyNode : Node := {
  kind := .epsilon
  scalarStart := 0
  scalarStop := 0
  byteStart := 0
  byteStop := 0
  choiceBegin := 0
  choiceCount := 0
}

private def rootOnlyView : ForestView := {
  nodes := [rootOnlyNode]
  choices := []
  roots := [0]
  codepoints := []
  byteOffsets := [0]
}

theorem rootOnly_validateStructure :
    validateStructure rootOnlyView = true := by
  decide

theorem rootOnly_structurallyComplete :
    StructurallyComplete rootOnlyView :=
  validateStructure_sound rootOnly_validateStructure

/-- Array coherence alone does not authorize unreachable shadow nodes. -/
theorem unreachable_node_arrays_still_coherent :
    validateArrays { rootOnlyView with
      nodes := [rootOnlyNode, rootOnlyNode] } = true := by
  decide

/-- The complete structural validator rejects the same shadow node. -/
theorem unreachable_node_rejected :
    validateStructure { rootOnlyView with
      nodes := [rootOnlyNode, rootOnlyNode] } = false := by
  decide

end Mettapedia.GSLT.Parsing.ClassAwareNativeForestReachabilityValidation
