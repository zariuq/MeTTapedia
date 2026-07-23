import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.FiniteDampedSettling

/-!
# Fixed-address frontier transitions

The typed-workspace and selective-belief decoders share one discrete state
machine.  Active holes occupy a preorder frontier.  Applying the previous
operator removes its head, allocates fresh child addresses from the old
`nextFree` cursor, prepends those children, and preserves the remaining tail.
Carrier contents are parametric; only child initialization differs.

This module states that transition independently of tensor storage, proves its
budget arithmetic, and gives exact workspace and belief row layouts.  The
source checker separately pins the tensor slices, rounding boundary, gather
indices, masking, and child-write loop.  No floating-point or neural-primitive
equivalence is claimed here.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

universe u

/-- One row of carrier contents together with the active fixed-address
frontier and the first never-allocated address. -/
structure FixedAddressState (Content : Type u) where
  contents : List Content
  frontier : List ℕ
  nextFree : ℕ
  deriving Repr, DecidableEq

namespace FixedAddressState

variable {Content : Type u}

/-- Fresh addresses allocated to the children of the current hole. -/
def childAddresses (state : FixedAddressState Content) (arity : ℕ) : List ℕ :=
  (List.range arity).map fun argumentIndex => state.nextFree + argumentIndex

/-- The semantic preorder transition: new children precede the unconsumed old
frontier.  The old active head is consumed exactly once. -/
def transitionedFrontier (state : FixedAddressState Content) (arity : ℕ) : List ℕ :=
  state.childAddresses arity ++ state.frontier.drop 1

/-- Initialize every freshly allocated child address.  `List.set` is a no-op
outside the content array; the source-side capacity guard rules that case out
before calling the transition. -/
def initializeChildren (state : FixedAddressState Content) (arity : ℕ)
    (childValue : ℕ → Content) : List Content :=
  (List.range arity).foldl
    (fun contents argumentIndex =>
      contents.set (state.nextFree + argumentIndex) (childValue argumentIndex))
    state.contents

/-- Apply the previous action exactly when the nonnegative position is
positive.  Position zero is the initial scoring row and performs no transition. -/
def applyPreviousAction (state : FixedAddressState Content) (position arity : ℕ)
    (childValue : ℕ → Content) : FixedAddressState Content :=
  if position = 0 then state
  else
    { contents := state.initializeChildren arity childValue
      frontier := state.transitionedFrontier arity
      nextFree := state.nextFree + arity }

@[simp] theorem applyPreviousAction_zero
    (state : FixedAddressState Content) (arity : ℕ) (childValue : ℕ → Content) :
    state.applyPreviousAction 0 arity childValue = state := by
  simp [applyPreviousAction]

@[simp] theorem applyPreviousAction_succ
    (state : FixedAddressState Content) (position arity : ℕ)
    (childValue : ℕ → Content) :
    state.applyPreviousAction (position + 1) arity childValue =
      { contents := state.initializeChildren arity childValue
        frontier := state.transitionedFrontier arity
        nextFree := state.nextFree + arity } := by
  simp [applyPreviousAction]

@[simp] theorem childAddresses_length
    (state : FixedAddressState Content) (arity : ℕ) :
    (state.childAddresses arity).length = arity := by
  simp [childAddresses]

/-- Consuming one active hole and prepending `arity` children gives the exact
open-hole recurrence used by the top-down adapter. -/
theorem transitionedFrontier_length
    (state : FixedAddressState Content) (arity : ℕ)
    (hactive : state.frontier ≠ []) :
    (state.transitionedFrontier arity).length =
      state.frontier.length - 1 + arity := by
  have hpositive : 0 < state.frontier.length := List.length_pos_iff.mpr hactive
  simp [transitionedFrontier, childAddresses]
  omega

/-- The slot-capacity test is exactly the bounded-completion test once the
cursor invariant `nextFree = actionsUsed + openHoles` is known. -/
theorem boundedCompletion_iff_cursorFits
    (state : FixedAddressState Content) (actionsUsed arity capacity : ℕ)
    (hactive : state.frontier ≠ [])
    (hcursor : state.nextFree = actionsUsed + state.frontier.length) :
    actionsUsed + 1 + (state.frontier.length - 1 + arity) ≤ capacity ↔
      state.nextFree + arity ≤ capacity := by
  have hpositive : 0 < state.frontier.length := List.length_pos_iff.mpr hactive
  omega

/-- The cursor identity is inductive across every real action transition. -/
theorem cursorIdentity_preserved
    (state : FixedAddressState Content) (position arity actionsUsed : ℕ)
    (childValue : ℕ → Content)
    (hposition : 0 < position)
    (hactive : state.frontier ≠ [])
    (hcursor : state.nextFree = actionsUsed + state.frontier.length) :
    (state.applyPreviousAction position arity childValue).nextFree =
      (actionsUsed + 1) +
        (state.applyPreviousAction position arity childValue).frontier.length := by
  obtain ⟨position, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hposition)
  rw [applyPreviousAction_succ]
  rw [transitionedFrontier_length state arity hactive]
  simp only
  have hfrontierPositive : 0 < state.frontier.length :=
    List.length_pos_iff.mpr hactive
  omega

/-- Active addresses remain below the updated cursor. -/
theorem transitionedFrontier_lt_nextFree
    (state : FixedAddressState Content) (arity address : ℕ)
    (hold : ∀ old ∈ state.frontier, old < state.nextFree)
    (haddress : address ∈ state.transitionedFrontier arity) :
    address < state.nextFree + arity := by
  rw [transitionedFrontier, List.mem_append] at haddress
  rcases haddress with hchild | holdTail
  · rw [childAddresses, List.mem_map] at hchild
    obtain ⟨argumentIndex, hindex, rfl⟩ := hchild
    have hlt : argumentIndex < arity := by
      simpa using (List.mem_range.mp hindex)
    omega
  · have hin : address ∈ state.frontier := List.mem_of_mem_drop holdTail
    exact lt_of_lt_of_le (hold address hin) (Nat.le_add_right state.nextFree arity)

/-- Child and surviving-tail addresses cannot alias when all old addresses lie
strictly below the old allocation cursor. -/
theorem childAddresses_disjoint_tail
    (state : FixedAddressState Content) (arity : ℕ)
    (hold : ∀ old ∈ state.frontier, old < state.nextFree) :
    List.Disjoint (state.childAddresses arity) (state.frontier.drop 1) := by
  rw [List.disjoint_left]
  intro child hchild holdTail
  rw [childAddresses, List.mem_map] at hchild
  obtain ⟨argumentIndex, hindex, rfl⟩ := hchild
  have holdMem : state.nextFree + argumentIndex ∈ state.frontier :=
    List.mem_of_mem_drop holdTail
  have holdLt := hold (state.nextFree + argumentIndex) holdMem
  omega

/-- Preorder allocation preserves pairwise distinct active addresses. -/
theorem transitionedFrontier_nodup
    (state : FixedAddressState Content) (arity : ℕ)
    (hnodup : state.frontier.Nodup)
    (hold : ∀ old ∈ state.frontier, old < state.nextFree) :
    (state.transitionedFrontier arity).Nodup := by
  rw [transitionedFrontier, List.nodup_append]
  constructor
  · exact (List.nodup_range.map (fun _ _ equality => Nat.add_left_cancel equality))
  constructor
  · exact hnodup.drop
  · have hdisjoint := state.childAddresses_disjoint_tail arity hold
    rw [List.disjoint_left] at hdisjoint
    rintro child hchild old holdTail rfl
    exact hdisjoint hchild holdTail

/-! ## Source-shaped packed rows -/

/-- Pad the active prefix with the source sentinel `-1`. -/
def paddedFrontier (capacity : ℕ) (state : FixedAddressState Content) : List ℤ :=
  state.frontier.map Int.ofNat ++
    List.replicate (capacity - state.frontier.length) (-1)

/-- The source appends the padded frontier, frontier length, and allocation
cursor after the carrier payload. -/
def packedDiscrete (capacity : ℕ) (state : FixedAddressState Content) : List ℤ :=
  state.paddedFrontier capacity ++
    [Int.ofNat state.frontier.length, Int.ofNat state.nextFree]

theorem paddedFrontier_length
    (capacity : ℕ) (state : FixedAddressState Content)
    (hcapacity : state.frontier.length ≤ capacity) :
    (state.paddedFrontier capacity).length = capacity := by
  simp [paddedFrontier]
  omega

theorem packedDiscrete_length
    (capacity : ℕ) (state : FixedAddressState Content)
    (hcapacity : state.frontier.length ≤ capacity) :
    (state.packedDiscrete capacity).length = capacity + 2 := by
  simp [packedDiscrete, state.paddedFrontier_length capacity hcapacity]

/-- Dropping the fixed-width frontier exposes exactly length then cursor. -/
theorem packedDiscrete_drop_capacity
    (capacity : ℕ) (state : FixedAddressState Content)
    (hcapacity : state.frontier.length ≤ capacity) :
    (state.packedDiscrete capacity).drop capacity =
      [Int.ofNat state.frontier.length, Int.ofNat state.nextFree] := by
  have hlength := state.paddedFrontier_length capacity hcapacity
  have hdrop : (state.paddedFrontier capacity).drop capacity = [] := by
    calc
      (state.paddedFrontier capacity).drop capacity =
          (state.paddedFrontier capacity).drop
            (state.paddedFrontier capacity).length := by
              exact congrArg
                (fun index => (state.paddedFrontier capacity).drop index)
                hlength.symm
      _ = [] := by simp
  rw [packedDiscrete, List.drop_append_of_le_length (by omega), hdrop]
  rfl

/-- Embed integral discrete metadata into the exact-rational row used to model
the source's common floating tensor. -/
def encodedDiscrete (capacity : ℕ) (state : FixedAddressState Content) : List ℚ :=
  (state.packedDiscrete capacity).map fun value => (value : ℚ)

/-- Workspace packing has one flattened carrier payload followed by the common
discrete tail. -/
def packWorkspaceRow (capacity : ℕ) (payload : List ℚ)
    (state : FixedAddressState Content) : List ℚ :=
  payload ++ state.encodedDiscrete capacity

/-- Belief packing has positive then negative evidence payloads followed by
the same common discrete tail. -/
def packBeliefRow (capacity : ℕ) (positive negative : List ℚ)
    (state : FixedAddressState Content) : List ℚ :=
  positive ++ negative ++ state.encodedDiscrete capacity

@[simp] theorem packWorkspaceRow_drop_payload
    (capacity : ℕ) (payload : List ℚ) (state : FixedAddressState Content) :
    (state.packWorkspaceRow capacity payload).drop payload.length =
      state.encodedDiscrete capacity := by
  simp [packWorkspaceRow]

@[simp] theorem packBeliefRow_drop_payloads
    (capacity : ℕ) (positive negative : List ℚ)
    (state : FixedAddressState Content) :
    (state.packBeliefRow capacity positive negative).drop
        (positive.length + negative.length) = state.encodedDiscrete capacity := by
  simp [packBeliefRow]

end FixedAddressState

/-! ## Executable positive and negative fixtures -/

namespace FixedAddressFrontierFixtures

def initial : FixedAddressState ℕ where
  contents := [10, 0, 0, 0]
  frontier := [0]
  nextFree := 1

def childValue (argumentIndex : ℕ) : ℕ := 20 + argumentIndex

def afterBinary : FixedAddressState ℕ :=
  initial.applyPreviousAction 1 2 childValue

def afterUnary : FixedAddressState ℕ :=
  afterBinary.applyPreviousAction 2 1 (fun _ => 30)

/-- A binary action consumes root address zero, initializes addresses one and
two, and exposes those addresses in preorder. -/
theorem binary_transition_exact :
    afterBinary =
      { contents := [10, 20, 21, 0]
        frontier := [1, 2]
        nextFree := 3 } := by
  decide

/-- The next unary child is prepended before the surviving second child. -/
theorem unary_transition_exact :
    afterUnary =
      { contents := [10, 20, 21, 30]
        frontier := [3, 2]
        nextFree := 4 } := by
  decide

theorem initial_cursor_identity : initial.nextFree = 0 + initial.frontier.length := by
  decide

theorem afterBinary_cursor_identity :
    afterBinary.nextFree = 1 + afterBinary.frontier.length := by
  decide

theorem afterUnary_cursor_identity :
    afterUnary.nextFree = 2 + afterUnary.frontier.length := by
  decide

/-- A tail-first reinterpretation changes which fixed address is active. -/
def tailFirstUnaryFrontier : List ℕ :=
  afterBinary.frontier.drop 1 ++ afterBinary.childAddresses 1

theorem tail_first_frontier_is_wrong :
    tailFirstUnaryFrontier ≠ afterUnary.frontier := by
  decide

/-- Allocating from the updated cursor instead of the saved old cursor writes
the wrong content slots, including one out-of-capacity no-op. -/
def updatedCursorBinaryContents : List ℕ :=
  (List.range 2).foldl
    (fun contents argumentIndex =>
      contents.set (initial.nextFree + 2 + argumentIndex) (childValue argumentIndex))
    initial.contents

theorem updated_cursor_child_writes_are_wrong :
    updatedCursorBinaryContents ≠ afterBinary.contents := by
  decide

theorem afterUnary_packed_discrete_exact :
    afterUnary.packedDiscrete 4 = [3, 2, -1, -1, 2, 4] := by
  decide

/-- Swapping frontier length and cursor is observable once they differ. -/
theorem swapped_length_cursor_layout_is_wrong :
    [3, 2, -1, -1, 4, 2] ≠ afterUnary.packedDiscrete 4 := by
  decide

end FixedAddressFrontierFixtures

#print axioms FixedAddressState.transitionedFrontier_length
#print axioms FixedAddressState.boundedCompletion_iff_cursorFits
#print axioms FixedAddressState.cursorIdentity_preserved
#print axioms FixedAddressState.transitionedFrontier_lt_nextFree
#print axioms FixedAddressState.transitionedFrontier_nodup
#print axioms FixedAddressState.packedDiscrete_drop_capacity
#print axioms FixedAddressState.packWorkspaceRow_drop_payload
#print axioms FixedAddressState.packBeliefRow_drop_payloads
#print axioms FixedAddressFrontierFixtures.binary_transition_exact
#print axioms FixedAddressFrontierFixtures.unary_transition_exact
#print axioms FixedAddressFrontierFixtures.tail_first_frontier_is_wrong
#print axioms FixedAddressFrontierFixtures.updated_cursor_child_writes_are_wrong
#print axioms FixedAddressFrontierFixtures.swapped_length_cursor_layout_is_wrong

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
