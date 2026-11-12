import Mettapedia.Machines.TIsa.CellEffects
import Mettapedia.Machines.TIsa.Bytes
import Mettapedia.Machines.TIsa.Address

/-!
# Loads and stores as byte-resource recipes

Capabilities, registers and individual bytes are ordinary cells. A dynamic
address selects a finite footprint; the guard checks that choice against
the actual pointer and capability cells. Read-only views can share byte keys.
Stores consume exactly their byte keys and preserve every other cell.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Memory

open Cells CellEffects

inductive Key (Register : Type) where
  | register (name : Register)
  | byte (address : Nat)
  | capabilityBase (region : Nat)
  | capabilityLength (region : Nat)
  | capabilityMode (region : Nat)
  deriving DecidableEq, Repr

inductive Width where
  | byte | word32 | word64
  deriving DecidableEq, Repr

def Width.bytes : Width → Nat
  | .byte => 1
  | .word32 => 4
  | .word64 => 8

def Width.load (width : Width) (signed : Bool) (bytes : List (BitVec 8)) : Word :=
  match width, signed with
  | .word32, true => load32Signed bytes
  | _, _ => packBytes bytes

def byteKeys {Register : Type} (address count : Nat) : List (Key Register) :=
  (List.range count).map fun index => .byte (address + index)

def capabilityKeys {Register : Type} (region : Nat) : List (Key Register) :=
  [.capabilityBase region, .capabilityLength region, .capabilityMode region]

def access? (base length pointer : Word) (displacement : Int) (width : Nat) : Option Nat := do
  let range : ByteRange := ⟨base.toNat, length.toNat⟩
  let address ← checkedAddress? range pointer.toNat 0 0 displacement
  range.access? (address - range.base) width

theorem access?_no_wrap (base length pointer : Word) (displacement : Int) (width address : Nat)
    (accepted : access? base length pointer displacement width = some address) :
    address + width ≤ 2 ^ 64 := by
  simp only [access?, Option.bind_eq_bind, Option.bind_eq_some_iff] at accepted
  obtain ⟨formed, _, accepted⟩ := accepted
  exact ByteRange.access?_no_wrap _ _ _ _ accepted

theorem access?_inside (base length pointer : Word) (displacement : Int) (width address index : Nat)
    (accepted : access? base length pointer displacement width = some address)
    (within : index < width) :
    (ByteRange.mk base.toNat length.toNat).Contains (address + index) := by
  simp only [access?, Option.bind_eq_bind, Option.bind_eq_some_iff] at accepted
  obtain ⟨formed, _, accepted⟩ := accepted
  exact ByteRange.access?_inside _ _ _ _ _ accepted within

def byteWords (bytes : List (BitVec 8)) : List Word := bytes.map (BitVec.zeroExtend 64)

def readByteWords? (words : List Word) : Option (List (BitVec 8)) :=
  if words.all (fun value => decide (value.toNat < 256)) then
    some (words.map fun value => value.extractLsb' 0 8)
  else none

structure Access (Register : Type) where
  region : Nat
  pointer : Register
  displacement : Int
  width : Width
  deriving DecidableEq, Repr

structure Load (Register : Type) extends Access Register where
  destination : Register
  signed : Bool
  deriving DecidableEq, Repr

structure Store (Register : Type) extends Access Register where
  source : Register
  deriving DecidableEq, Repr

def Load.recipe {Register : Type} (load : Load Register) (address : Nat) : Recipe (Key Register) where
  inputs := capabilityKeys load.region ++ .register load.pointer :: byteKeys address load.width.bytes
  outputs := [.register load.destination]
  guard := fun inputs outputs => match inputs, outputs with
    | base :: length :: mode :: pointer :: bytes, [result] =>
        (mode == 1 || mode == 2) &&
        access? base length pointer load.displacement load.width.bytes == some address &&
        bytes.length == load.width.bytes &&
        (readByteWords? bytes).map (load.width.load load.signed) == some result
    | _, _ => false

def Store.recipe {Register : Type} (store : Store Register) (address : Nat) : Recipe (Key Register) where
  inputs := capabilityKeys store.region ++ [.register store.pointer, .register store.source]
  outputs := byteKeys address store.width.bytes
  guard := fun inputs outputs => match inputs with
    | [base, length, mode, pointer, value] =>
        mode == 2 && access? base length pointer store.displacement store.width.bytes == some address &&
        outputs == byteWords (unpackBytes store.width.bytes value)
    | _ => false

variable {Register : Type} [DecidableEq Register]

omit [DecidableEq Register] in
theorem Store.guard_iff (store : Store Register) (address : Nat) (before after : Key Register → Word) :
    (store.recipe address).guard ((store.recipe address).inputs.map before)
      ((store.recipe address).outputs.map after) = true ↔
      before (.capabilityMode store.region) = 2 ∧
      access? (before (.capabilityBase store.region)) (before (.capabilityLength store.region))
        (before (.register store.pointer)) store.displacement store.width.bytes = some address ∧
      (byteKeys address store.width.bytes).map after =
        byteWords (unpackBytes store.width.bytes (before (.register store.source))) := by
  simp [recipe, capabilityKeys, Bool.and_eq_true, and_assoc]

theorem Store.write_footprint (store : Store Register) (address : Nat) :
    (store.recipe address).writes = (byteKeys address store.width.bytes).toFinset := rfl

theorem Load.write_footprint (load : Load Register) (address : Nat) :
    (load.recipe address).writes = {.register load.destination} := by
  simp [Recipe.writes, recipe]

/-- Every byte contributing to a load is an explicit shared input resource. -/
theorem Load.reads_byte (load : Load Register) (address index : Nat) (within : index < load.width.bytes) :
    Key.byte (address + index) ∈ (load.recipe address).reads := by
  simp [Recipe.reads, Recipe.writes, recipe, capabilityKeys, byteKeys, within]

omit [DecidableEq Register] in
theorem Load.guard_iff (load : Load Register) (address : Nat) (before after : Key Register → Word) :
    (load.recipe address).guard ((load.recipe address).inputs.map before)
      ((load.recipe address).outputs.map after) = true ↔
      (before (.capabilityMode load.region) = 1 ∨ before (.capabilityMode load.region) = 2) ∧
      access? (before (.capabilityBase load.region)) (before (.capabilityLength load.region))
        (before (.register load.pointer)) load.displacement load.width.bytes = some address ∧
      (readByteWords? ((byteKeys address load.width.bytes).map before)).map (load.width.load load.signed) =
        some (after (.register load.destination)) := by
  simp [recipe, capabilityKeys, byteKeys, Bool.and_eq_true, and_assoc]

theorem Store.preserves_register (store : Store Register) (address : Nat)
    (before after : Key Register → Word) (register : Register) :
    overwrite (store.recipe address).writes before after (.register register) = before (.register register) := by
  simp [overwrite, Recipe.writes, recipe, byteKeys]

theorem Load.preserves_byte (load : Load Register) (address : Nat)
    (before after : Key Register → Word) (other : Nat) :
    overwrite (load.recipe address).writes before after (.byte other) = before (.byte other) := by
  simp [overwrite, Recipe.writes, recipe]

theorem Store.preserves_outside (store : Store Register) (address other : Nat)
    (before after : Key Register → Word)
    (outside : other < address ∨ address + store.width.bytes ≤ other) :
    overwrite (store.recipe address).writes before after (.byte other) = before (.byte other) := by
  apply if_neg
  simp only [Recipe.writes, recipe, List.mem_toFinset, byteKeys, List.mem_map, List.mem_range]
  rintro ⟨index, bound, same⟩
  have equal : address + index = other := Key.byte.inj same
  omega

inductive Operation (Register : Type) where
  | load (action : Load Register)
  | store (action : Store Register)
  deriving DecidableEq, Repr

def Operation.recipe (operation : Operation Register) (address : Nat) : Recipe (Key Register) :=
  match operation with
  | .load action => action.recipe address
  | .store action => action.recipe address

/-- Addresses are rule instantiations, not additional program instructions. -/
def program (operations : List (Operation Register)) :
    Mettapedia.GSLT.Causality.ResourceInteraction.System (Cell (Key Register)) where
  Site := Fin operations.length
  Instance := fun index => Σ address : Nat, Invocation (operations[index].recipe address)
  consume := fun {index} invocation =>
    encode (operations[index].recipe invocation.1).writes invocation.2.before
  read := fun {index} invocation =>
    encode (operations[index].recipe invocation.1).reads invocation.2.before
  produce := fun {index} invocation =>
    encode (operations[index].recipe invocation.1).writes invocation.2.after

theorem program_rewrite_iff (operations : List (Operation Register)) (keys : Finset (Key Register))
    (before : Key Register → Word) (result : Multiset (Cell (Key Register))) :
    (program operations).theory.rewrites (encode keys before) result ↔
      ∃ operation ∈ operations, ∃ address : Nat, ∃ after : Key Register → Word,
        (operation.recipe address).support ⊆ keys ∧
        (operation.recipe address).guard ((operation.recipe address).inputs.map before)
          ((operation.recipe address).outputs.map after) = true ∧
        result = encode keys (overwrite (operation.recipe address).writes before after) := by
  constructor
  · rintro ⟨index, ⟨address, invocation⟩, enabled, rfl⟩
    change Fin operations.length at index
    have baseEnabled : CellEffects.system.Enables (encode keys before) invocation := enabled
    exact ⟨operations[index], List.getElem_mem index.isLt, address, invocation.after,
      ((enabled_iff _ invocation keys before).mp baseEnabled).1,
      enabled_guard _ invocation keys before baseEnabled,
      fire_refines_overwrite _ invocation keys before baseEnabled⟩
  · rintro ⟨operation, member, address, after, included, guarded, rfl⟩
    obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
    let invocation : Invocation (operations[index].recipe address) := ⟨before, after, guarded⟩
    have enabled : CellEffects.system.Enables (encode keys before) invocation :=
      (enabled_iff _ invocation keys before).mpr ⟨included, fun _ _ => rfl⟩
    exact ⟨index, ⟨address, invocation⟩, enabled,
      (fire_refines_overwrite _ invocation keys before enabled).symm⟩

namespace Controls

example : access? 100 8 100 4 4 = some 104 := by decide
example : access? 100 8 100 4 8 = none := by decide
example : access? 100 8 0 (-1) 1 = none := by decide
example : access? 18446744073709551612 8 18446744073709551612 0 8 = none := by decide
example : readByteWords? [255, 0] = some [255, 0] := by decide
example : readByteWords? [256] = none := by decide

private def store : Store Nat := ⟨⟨0, 0, 0, .word32⟩, 1⟩
private def load : Load Nat := ⟨⟨0, 0, 0, .word64⟩, 1, false⟩

example : (store.recipe 100).guard [100, 8, 2, 100, 305419896] [120, 86, 52, 18] = true := by decide
example : (store.recipe 100).guard [100, 8, 1, 100, 305419896] [120, 86, 52, 18] = false := by decide
example : (store.recipe 100).guard [100, 8, 2, 100, 305419896] [120, 86, 52, 19] = false := by decide

example : Key.byte 107 ∈ (load.recipe 100).reads := by decide
example : (load.recipe 100).guard [100, 8, 1, 100, 0, 1, 0, 0, 0, 0, 0, 0] [256] = true := by decide
example : (load.recipe 100).guard [100, 8, 1, 100, 0, 2, 0, 0, 0, 0, 0, 0] [512] = true := by decide
example : (load.recipe 100).guard [100, 8, 1, 100, 0, 2, 0, 0, 0, 0, 0, 0] [256] = false := by decide

end Controls

end Mettapedia.Machines.TIsa.Memory
