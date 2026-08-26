import Mettapedia.GSLT.Parsing.ClassAwareNativeForestWire

/-!
# Executable structural validation of a native packed forest

The C neutral-forest validator is independently mirrored here as a small
finite checker over the decoded `ForestView`.  Its soundness theorem produces
the structural `ForestArraysCoherent` premise required by the semantic
`Represents` contract.  Semantic identity tables, finite family derivations,
and reachability remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareNativeForestStructuralValidation

open Mettapedia.GSLT.Parsing.ClassAwareNativeForestContract

/-- The local structural obligation at one physical node-array occurrence. -/
def NodeEntryCoherent (view : ForestView) (index : Nat) (node : Node) : Prop :=
  view.nodes[index]? = some node ∧
    NodeSpanCoherent view node ∧
    node.choiceBegin + node.choiceCount ≤ view.choices.length

/-- A decidable ownership view in which the parent and local choice offset are
determined by the choice occurrence itself. -/
def ChoiceEntryCoherent (view : ForestView) (choiceIndex : Nat)
    (choice : Choice) : Prop :=
  match view.nodes[choice.parent]? with
  | none => False
  | some parent =>
      parent.choiceBegin ≤ choiceIndex ∧
        choiceIndex < parent.choiceBegin + parent.choiceCount ∧
        view.choices[choiceIndex]? = some choice

/-- One exported root points to a span-coherent node. -/
def RootEntryCoherent (view : ForestView) (rootIndex : Nat) : Prop :=
  match view.nodes[rootIndex]? with
  | none => False
  | some node => NodeSpanCoherent view node

def nodeEntryValid (view : ForestView) (index : Nat) (node : Node) : Bool :=
  view.nodes[index]? == some node &&
    decide (node.scalarStart ≤ node.scalarStop) &&
    view.byteOffsets[node.scalarStart]? == some node.byteStart &&
    view.byteOffsets[node.scalarStop]? == some node.byteStop &&
    decide (node.choiceBegin + node.choiceCount ≤ view.choices.length)

def choiceEntryValid (view : ForestView) (choiceIndex : Nat)
    (choice : Choice) : Bool :=
  match view.nodes[choice.parent]? with
  | none => false
  | some parent =>
      decide (parent.choiceBegin ≤ choiceIndex) &&
        decide (choiceIndex < parent.choiceBegin + parent.choiceCount) &&
        view.choices[choiceIndex]? == some choice

def rootEntryValid (view : ForestView) (rootIndex : Nat) : Bool :=
  match view.nodes[rootIndex]? with
  | none => false
  | some node =>
      decide (node.scalarStart ≤ node.scalarStop) &&
        view.byteOffsets[node.scalarStart]? == some node.byteStart &&
        view.byteOffsets[node.scalarStop]? == some node.byteStop

theorem nodeEntryValid_eq_true_iff
    (view : ForestView) (index : Nat) (node : Node) :
    nodeEntryValid view index node = true ↔
      NodeEntryCoherent view index node := by
  simp [nodeEntryValid, NodeEntryCoherent, NodeSpanCoherent, and_assoc]

theorem choiceEntryValid_eq_true_iff
    (view : ForestView) (choiceIndex : Nat) (choice : Choice) :
    choiceEntryValid view choiceIndex choice = true ↔
      ChoiceEntryCoherent view choiceIndex choice := by
  cases nodeLookup : view.nodes[choice.parent]? <;>
    simp [choiceEntryValid, ChoiceEntryCoherent, nodeLookup,
      and_assoc]

theorem rootEntryValid_eq_true_iff
    (view : ForestView) (rootIndex : Nat) :
    rootEntryValid view rootIndex = true ↔
      RootEntryCoherent view rootIndex := by
  cases nodeLookup : view.nodes[rootIndex]? <;>
    simp [rootEntryValid, RootEntryCoherent, NodeSpanCoherent, nodeLookup,
      and_assoc]

/-- Checking the finite node table.  `zipIdx` makes physical occurrence
identity explicit rather than searching by node equality. -/
def validateNodes (view : ForestView) : Bool :=
  view.nodes.zipIdx.all fun entry =>
    nodeEntryValid view entry.2 entry.1

/-- Checking the finite choice table at each exact array occurrence. -/
def validateChoices (view : ForestView) : Bool :=
  view.choices.zipIdx.all fun entry =>
    choiceEntryValid view entry.2 entry.1

/-- Checking the exported root occurrences. -/
def validateRoots (view : ForestView) : Bool :=
  view.roots.all fun rootIndex => rootEntryValid view rootIndex

/-- Complete executable structural-array check. -/
def validateArrays (view : ForestView) : Bool :=
  validateNodes view && validateChoices view && validateRoots view

/-- The decidable ownership view is exactly the existing semantic ownership
predicate, not a weaker approximation. -/
theorem choiceEntryCoherent_iff_choiceAtOwned
    (view : ForestView) (choiceIndex : Nat) (choice : Choice) :
    ChoiceEntryCoherent view choiceIndex choice ↔
      ChoiceAtOwned view choiceIndex choice := by
  unfold ChoiceAtOwned
  cases nodeLookup : view.nodes[choice.parent]? with
  | none =>
    simp only [ChoiceEntryCoherent, nodeLookup]
    constructor
    · intro impossible
      contradiction
    · rintro ⟨parent, localIndex, parentAt, localLt, indexEq, choiceAt⟩
      cases parentAt
  | some parent =>
    simp only [ChoiceEntryCoherent, nodeLookup]
    constructor
    · rintro ⟨beginLe, indexLt, choiceAt⟩
      refine ⟨parent, choiceIndex - parent.choiceBegin,
        rfl, ?_, ?_, choiceAt⟩
      · omega
      · omega
    · rintro ⟨found, localIndex, foundAt, localLt, indexEq, choiceAt⟩
      cases foundAt
      exact ⟨by omega, by omega, choiceAt⟩

private theorem zipIdx_member_of_getElem
    {Alpha : Type} (items : List Alpha) (index : Nat) (item : Alpha)
    (lookup : items[index]? = some item) :
    (item, index) ∈ items.zipIdx := by
  rw [List.getElem?_eq_some_iff] at lookup
  rcases lookup with ⟨indexValid, itemEq⟩
  rw [List.mem_iff_getElem]
  refine ⟨index, ?_, ?_⟩
  · simpa using indexValid
  · rw [List.getElem_zipIdx]
    simp [itemEq]

theorem validateNodes_sound {view : ForestView}
    (accepted : validateNodes view = true) :
    ∀ (index : Nat) (node : Node),
      view.nodes[index]? = some node →
        NodeSpanCoherent view node ∧
          node.choiceBegin + node.choiceCount ≤ view.choices.length := by
  intro index node nodeAt
  have checked := (List.all_eq_true.mp accepted) (node, index)
    (zipIdx_member_of_getElem view.nodes index node nodeAt)
  exact (nodeEntryValid_eq_true_iff view index node).mp checked |>.2

theorem validateChoices_sound {view : ForestView}
    (accepted : validateChoices view = true) :
    ∀ (index : Nat) (choice : Choice),
      view.choices[index]? = some choice → ChoiceAtOwned view index choice := by
  intro index choice choiceAt
  have checked := (List.all_eq_true.mp accepted) (choice, index)
    (zipIdx_member_of_getElem view.choices index choice choiceAt)
  exact (choiceEntryCoherent_iff_choiceAtOwned view index choice).mp
    ((choiceEntryValid_eq_true_iff view index choice).mp checked)

theorem validateRoots_sound {view : ForestView}
    (accepted : validateRoots view = true) :
    ∀ (index : Nat), index ∈ view.roots → ∃ node, NodeAt view index node := by
  intro index member
  have checked : rootEntryValid view index = true :=
    (List.all_eq_true.mp accepted) index member
  have coherent := (rootEntryValid_eq_true_iff view index).mp checked
  unfold RootEntryCoherent at coherent
  cases nodeLookup : view.nodes[index]? with
  | none =>
      rw [nodeLookup] at coherent
      contradiction
  | some node =>
      rw [nodeLookup] at coherent
      exact ⟨node, nodeLookup, coherent⟩

/-- Successful finite checking supplies precisely the structural-array premise
of `Represents`. -/
theorem validateArrays_sound {view : ForestView}
    (accepted : validateArrays view = true) : ForestArraysCoherent view := by
  rw [validateArrays, Bool.and_eq_true_iff, Bool.and_eq_true_iff] at accepted
  exact {
    nodesCoherent := validateNodes_sound accepted.1.1
    choicesOwned := validateChoices_sound accepted.1.2
    rootsValid := validateRoots_sound accepted.2
  }

/-! ## Positive and negative controls -/

private def canarySymbolNode : Node := {
  kind := .symbol 3
  scalarStart := 0
  scalarStop := 1
  byteStart := 0
  byteStop := 1
  choiceBegin := 0
  choiceCount := 1
}

private def canaryTerminalNode : Node := {
  kind := .terminal 10 (.scalar 65)
  scalarStart := 0
  scalarStop := 1
  byteStart := 0
  byteStop := 1
  choiceBegin := 1
  choiceCount := 0
}

private def canaryChoice : Choice := {
  parent := 0
  prefixNode := none
  childNode := 1
  productionIndex := 7
  scalarPivot := 0
  bytePivot := 0
}

private def canaryView : ForestView := {
  nodes := [canarySymbolNode, canaryTerminalNode]
  choices := [canaryChoice]
  roots := [0]
  codepoints := [65]
  byteOffsets := [0, 1]
}

theorem canary_validateArrays : validateArrays canaryView = true := by decide

theorem canary_arraysCoherent : ForestArraysCoherent canaryView :=
  validateArrays_sound canary_validateArrays

/-- A byte offset inconsistent with a scalar span is rejected. -/
theorem corrupted_span_rejected :
    validateArrays {canaryView with byteOffsets := [0, 2]} = false := by
  decide

/-- A choice which claims a non-owning parent occurrence is rejected. -/
theorem orphan_choice_rejected :
    validateArrays {canaryView with choices :=
      [{canaryChoice with parent := 1}]} = false := by
  decide

/-- An out-of-bounds exported root is rejected. -/
theorem invalid_root_rejected :
    validateArrays {canaryView with roots := [2]} = false := by decide

end Mettapedia.GSLT.Parsing.ClassAwareNativeForestStructuralValidation
