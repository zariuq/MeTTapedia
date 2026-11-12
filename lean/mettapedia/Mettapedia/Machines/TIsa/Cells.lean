import Mettapedia.Machines.TIsa.Scalar
import Mettapedia.GSLT.Logic.ResourceFrame
import Mathlib.Data.Finset.Image

/-!
# Scalar operations as existing resource transforms

A scalar action consumes the old destination cell, keeps its other input
cells, and produces the computed destination. Inputs are deduplicated by key,
so reading a cell twice or also writing it requires only one occurrence.

The operational object is `ResourceInteraction.System`. Finite assignments are
an independent readback representation, not another machine state authority.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Cells

open Mettapedia.GSLT.Causality.ResourceInteraction

universe u

variable {Key : Type u} [DecidableEq Key]

structure Cell (Key : Type u) where
  key : Key
  value : Word
  deriving DecidableEq, Repr

def encode (keys : Finset Key) (values : Key → Word) : Multiset (Cell Key) :=
  keys.val.map fun key => ⟨key, values key⟩

omit [DecidableEq Key] in
@[simp] theorem mem_encode (keys : Finset Key) (values : Key → Word)
    (key : Key) (value : Word) :
    Cell.mk key value ∈ encode keys values ↔ key ∈ keys ∧ values key = value := by
  simp [encode, Cell.mk.injEq]

omit [DecidableEq Key] in
theorem encode_congr (keys : Finset Key) (left right : Key → Word)
    (agree : ∀ key ∈ keys, left key = right key) : encode keys left = encode keys right := by
  exact Multiset.map_congr rfl fun key member => congrArg (Cell.mk key) (agree key member)

omit [DecidableEq Key] in
theorem encode_le_iff (left right : Finset Key) (before after : Key → Word) :
    encode left before ≤ encode right after ↔
      left ⊆ right ∧ ∀ key ∈ left, before key = after key := by
  constructor
  · intro included
    have seen : ∀ key ∈ left, key ∈ right ∧ after key = before key := by
      intro key member
      exact (mem_encode right after key (before key)).mp
        (Multiset.mem_of_le included ((mem_encode left before key (before key)).mpr ⟨member, rfl⟩))
    exact ⟨fun key member => (seen key member).1,
      fun key member => (seen key member).2.symm⟩
  · rintro ⟨included, agree⟩
    rw [encode_congr left before after agree]
    exact Multiset.map_le_map (Finset.val_le_iff.mpr included)

theorem encode_insert (key : Key) (keys : Finset Key) (absent : key ∉ keys)
    (values : Key → Word) :
    encode (insert key keys) values = {⟨key, values key⟩} + encode keys values := by
  simp [encode, Finset.insert_val_of_notMem absent]

theorem encode_split (keys : Finset Key) (values : Key → Word) (key : Key)
    (member : key ∈ keys) :
    encode keys values = {⟨key, values key⟩} + encode (keys.erase key) values := by
  simpa [Finset.insert_erase member] using
    encode_insert key (keys.erase key) (by simp) values

theorem encode_update (keys : Finset Key) (values : Key → Word) (key : Key)
    (value : Word) (member : key ∈ keys) :
    encode keys (Function.update values key value) =
      {⟨key, value⟩} + encode (keys.erase key) values := by
  rw [encode_split keys (Function.update values key value) key member]
  have unchanged : encode (keys.erase key) (Function.update values key value) =
      encode (keys.erase key) values := by
    apply encode_congr
    intro other present
    simp only [Finset.mem_erase] at present
    exact Function.update_of_ne present.1 _ _
  simp only [unchanged, Function.update_self]

structure Action (Key : Type u) where
  scalar : Scalar
  inputs : List Key
  destination : Key
  deriving DecidableEq, Repr

def Action.support (action : Action Key) : Finset Key :=
  insert action.destination action.inputs.toFinset

def Action.readKeys (action : Action Key) : Finset Key :=
  action.inputs.toFinset.erase action.destination

/-- Instantiation evidence is the evaluated scalar guard, not a stored verdict. -/
structure Invocation (action : Action Key) where
  before : Key → Word
  result : Word
  computes : action.scalar.evaluate (action.inputs.map before) = some result

/-- Scalar instructions are a profile of the existing resource calculus. -/
def system : System (Cell Key) where
  Site := Action Key
  Instance := Invocation
  consume := fun {action} invocation => {⟨action.destination, invocation.before action.destination⟩}
  read := fun {action} invocation => encode action.readKeys invocation.before
  produce := fun {action} invocation => {⟨action.destination, invocation.result⟩}

theorem demand_eq (action : Action Key) (invocation : Invocation action) :
    system.consume invocation + system.read invocation =
      encode action.support invocation.before := by
  change {⟨action.destination, invocation.before action.destination⟩} +
    encode (action.inputs.toFinset.erase action.destination) invocation.before = _
  rw [← encode_insert action.destination _ (by simp)]
  congr 1
  ext key
  simp [Action.support]
  tauto

theorem enabled_iff (action : Action Key) (invocation : Invocation action)
    (keys : Finset Key) (values : Key → Word) :
    system.Enables (encode keys values) invocation ↔
      action.support ⊆ keys ∧
      ∀ key ∈ action.support, invocation.before key = values key := by
  unfold System.Enables
  rw [demand_eq, encode_le_iff]

theorem enabled_computes (action : Action Key) (invocation : Invocation action)
    (keys : Finset Key) (values : Key → Word)
    (enabled : system.Enables (encode keys values) invocation) :
    action.scalar.evaluate (action.inputs.map values) = some invocation.result := by
  obtain ⟨_, agree⟩ := (enabled_iff action invocation keys values).mp enabled
  have arguments : action.inputs.map invocation.before = action.inputs.map values := by
    apply List.map_congr_left
    intro key member
    exact agree key (by simp [Action.support, member])
  rw [← arguments]
  exact invocation.computes

theorem fire_refines_update (action : Action Key) (invocation : Invocation action)
    (keys : Finset Key) (values : Key → Word)
    (enabled : system.Enables (encode keys values) invocation) :
    system.fire (encode keys values) invocation =
      encode keys (Function.update values action.destination invocation.result) := by
  obtain ⟨included, agree⟩ := (enabled_iff action invocation keys values).mp enabled
  have destinationPresent : action.destination ∈ keys :=
    included (by simp [Action.support])
  have destinationValue : invocation.before action.destination = values action.destination :=
    agree _ (by simp [Action.support])
  change encode keys values - {⟨action.destination, invocation.before action.destination⟩} +
    {⟨action.destination, invocation.result⟩} = _
  rw [destinationValue, encode_split keys values action.destination destinationPresent]
  rw [encode_update keys values action.destination invocation.result destinationPresent]
  rw [add_tsub_cancel_left]
  exact add_comm _ _

/-- Every supported scalar update has an actual resource firing. -/
theorem scalar_update_realized (action : Action Key) (keys : Finset Key)
    (values : Key → Word) (value : Word) (inScope : action.support ⊆ keys)
    (computes : action.scalar.evaluate (action.inputs.map values) = some value) :
    ∃ invocation : Invocation action,
      system.Enables (encode keys values) invocation ∧
      system.fire (encode keys values) invocation =
        encode keys (Function.update values action.destination value) := by
  let invocation : Invocation action := ⟨values, value, computes⟩
  have enabled : system.Enables (encode keys values) invocation :=
    (enabled_iff action invocation keys values).mpr ⟨inScope, fun _ _ => rfl⟩
  exact ⟨invocation, enabled, fire_refines_update action invocation keys values enabled⟩

/-- A firing cannot invent a scalar result on a canonical encoded state. -/
theorem scalar_update_reflected (action : Action Key) (invocation : Invocation action)
    (keys : Finset Key) (values : Key → Word)
    (enabled : system.Enables (encode keys values) invocation) :
    action.scalar.evaluate (action.inputs.map values) = some invocation.result ∧
      system.fire (encode keys values) invocation =
        encode keys (Function.update values action.destination invocation.result) :=
  ⟨enabled_computes action invocation keys values enabled,
    fire_refines_update action invocation keys values enabled⟩

/-- Extra resources are preserved by replaying this same admitted firing. -/
theorem fire_preserves_frame (action : Action Key) (invocation : Invocation action)
    (keys : Finset Key) (values : Key → Word) (frame : Multiset (Cell Key))
    (enabled : system.Enables (encode keys values) invocation) :
    system.fire (encode keys values + frame) invocation =
      encode keys (Function.update values action.destination invocation.result) + frame := by
  rw [Mettapedia.GSLT.Logic.ResourceFrame.fire_add_frame
    system ⟨action, invocation⟩ enabled frame]
  rw [fire_refines_update action invocation keys values enabled]

namespace Controls

private def double : Action Nat := ⟨.binary .add, [0, 0], 0⟩

private def invocation : Invocation double :=
  ⟨fun _ => 7, 14, by decide⟩

/-- Both inputs and the destination refer to one physical resource. -/
example : system.consume invocation = {⟨0, 7⟩} ∧ system.read invocation = 0 := by decide

example : system.Enables (encode ({0} : Finset Nat) (fun _ => 7)) invocation := by
  unfold System.Enables system
  decide

example : ¬system.Enables (encode ({0} : Finset Nat) (fun _ => 8)) invocation := by
  unfold System.Enables system
  decide

example : ¬system.Enables (0 : Multiset (Cell Nat)) invocation := by
  unfold System.Enables system
  decide

example : system.fire (encode ({0} : Finset Nat) (fun _ => 7)) invocation =
    ({⟨0, 14⟩} : Multiset (Cell Nat)) := by decide

end Controls

end Mettapedia.Machines.TIsa.Cells
