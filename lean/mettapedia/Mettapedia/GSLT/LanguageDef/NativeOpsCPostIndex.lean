import Mettapedia.GSLT.LanguageDef.NativeOpsCSyntax
import Mettapedia.Machines.OrderedDependencyCapacity

/-!
# Unsigned post-increment array stores in the admitted C syntax

The primitive models `array[count++] = value` using a finite slot list and an
actual UInt32 counter. The returned index is the old counter; the increment
and the slot write are separate operations. A missing slot has no defined
store transition. It is not an invented runtime error or allocator failure.

The list-prefix specification is independent of the slot-update implementation.
Its correspondence needs a live slot and a capacity bounded by UINT32_MAX.
Physical pointer realization, field layout and exclusion of concurrent readers
are not supplied by this array model or by syntactic recognition.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.PostIndex

universe u
variable {Value : Type u}

structure Array32 (Value : Type u) where
  slots : List Value
  count : UInt32
  deriving Repr

def Array32.active (array : Array32 Value) : List Value :=
  array.slots.take array.count.toNat

def Array32.Sized (array : Array32 Value) : Prop :=
  array.slots.length ≤ Mettapedia.Machines.OrderedDependencyCapacity.maximum

def Array32.Room (array : Array32 Value) : Prop :=
  array.count.toNat < array.slots.length

def postIndex (array : Array32 Value) : Nat × Array32 Value :=
  (array.count.toNat, { array with count := array.count + 1 })

def writeSlot (array : Array32 Value) (index : Nat) (value : Value) :
    Option (Array32 Value) :=
  if index < array.slots.length then
    some { array with slots := array.slots.set index value }
  else none

def store (array : Array32 Value) (value : Value) : Option (Array32 Value) :=
  if array.count.toNat < array.slots.length then
    some ⟨array.slots.set array.count.toNat value, array.count + 1⟩
  else none

theorem store_is_postIndex_then_write (array : Array32 Value) (value : Value) :
    store array value = writeSlot (postIndex array).2 (postIndex array).1 value := rfl

def storeThenIncrement (array : Array32 Value) (value : Value) : Option (Array32 Value) :=
  (writeSlot array array.count.toNat value).map fun written =>
    { written with count := written.count + 1 }

/-- The count side effect may occur after the independent slot write as well.
Both permitted schedules yield the same final pair of fields. -/
theorem independent_side_effect_orders_agree (array : Array32 Value) (value : Value) :
    storeThenIncrement array value = store array value := by
  by_cases room : array.count.toNat < array.slots.length <;>
    simp [storeThenIncrement, store, writeSlot, room]

theorem postIndex_returns_old_count (array : Array32 Value) :
    (postIndex array).1 = array.count.toNat := rfl

theorem increment_is_exact (array : Array32 Value)
    (sized : array.Sized) (room : array.Room) :
    (array.count + 1).toNat = array.count.toNat + 1 := by
  rw [UInt32.toNat_add]
  apply Nat.mod_eq_of_lt
  change array.slots.length ≤ 4294967295 at sized
  change array.count.toNat < array.slots.length at room
  change array.count.toNat + 1 < 2 ^ 32
  omega

theorem store_defined (array : Array32 Value) (value : Value)
    (room : array.Room) :
    store array value = some ⟨array.slots.set array.count.toNat value, array.count + 1⟩ := by
  exact if_pos room

theorem store_missing_iff (array : Array32 Value) (value : Value) :
    store array value = none ↔ ¬ array.Room := by
  by_cases room : array.count.toNat < array.slots.length <;>
    simp [store, Array32.Room, room]

theorem store_realizes_append {array after : Array32 Value} {value : Value}
    (sized : array.Sized) (stored : store array value = some after) :
    after.active = array.active ++ [value] ∧
      after.count.toNat = array.count.toNat + 1 ∧
      after.slots.length = array.slots.length ∧ after.Sized := by
  have room : array.Room := by
    by_contra absent
    have missing := (store_missing_iff array value).mpr absent
    rw [missing] at stored
    contradiction
  have same := (store_defined array value room).symm.trans stored
  cases Option.some.inj same
  have exactCount := increment_is_exact array sized room
  have slot : array.count.toNat < array.slots.length := room
  have changedSlot : array.count.toNat <
      (array.slots.set array.count.toNat value).length := by simpa using slot
  constructor
  · simp only [Array32.active, exactCount]
    rw [List.take_succ_eq_append_getElem changedSlot,
      List.take_set_of_le (Nat.le_refl _), List.getElem_set_self]
  · exact ⟨exactCount, List.length_set, by simpa [Array32.Sized] using sized⟩

theorem store_keeps_old_prefix {array after : Array32 Value} {value : Value}
    (stored : store array value = some after) :
    after.slots.take array.count.toNat = array.slots.take array.count.toNat := by
  unfold store at stored
  split at stored
  · cases Option.some.inj stored
    exact List.take_set_of_le (Nat.le_refl _)
  · contradiction

/-- Recognition keeps the owner, array field, count field and RHS identity.
Different owners in the array and count operands are not silently identified. -/
structure StoreSyntax where
  owner : Name
  arrayField : Name
  countField : Name
  value : Name
  deriving DecidableEq, Repr

def storeSyntax? : CStatement → Option StoreSyntax
  | .assign (.index (.field (.identifier owner) arrayField true)
      (.postIncrement (.field (.identifier countOwner) countField true)))
      (.identifier value) =>
    if owner = countOwner then some ⟨owner, arrayField, countField, value⟩ else none
  | _ => none

def StoreSyntax.statement (site : StoreSyntax) : CStatement :=
  .assign (.index (.field (.identifier site.owner) site.arrayField true)
    (.postIncrement (.field (.identifier site.owner) site.countField true)))
    (.identifier site.value)

theorem recognizes_authored_store (site : StoreSyntax) :
    storeSyntax? site.statement = some site := by
  cases site
  simp [StoreSyntax.statement, storeSyntax?]

def executeStore (resolve : StoreSyntax → Option (Array32 Value × Value))
    (statement : CStatement) : Option (Array32 Value) :=
  match storeSyntax? statement with
  | none => none
  | some site => (resolve site).bind fun operands => store operands.1 operands.2

theorem recognized_store_execution (resolve : StoreSyntax → Option (Array32 Value × Value))
    (site : StoreSyntax) (array : Array32 Value) (value : Value)
    (resolved : resolve site = some (array, value)) :
    executeStore resolve site.statement = store array value := by
  simp [executeStore, recognizes_authored_store, resolved]

namespace Controls

def array : Array32 Nat := ⟨[11, 99, 88], 1⟩

theorem append_uses_old_index :
    (store array 22).map Array32.active = some [11, 22] := by decide

/-- Publishing the increment before the write exposes the old spare value. -/
theorem increment_alone_is_not_append :
    (postIndex array).2.active = [11, 99] ∧
      (postIndex array).2.active ≠ array.active ++ [22] := by decide

theorem full_array_has_no_defined_store : store (⟨[11], 1⟩ : Array32 Nat) 22 = none :=
  by decide

theorem unconditional_unsigned_increment_wraps :
    ((4294967295 : UInt32) + 1).toNat = 0 := by decide

theorem mismatched_owner_is_not_admitted :
    storeSyntax? (.assign
      (.index (.field (.identifier "left".toList) "slots".toList true)
        (.postIncrement (.field (.identifier "right".toList) "count".toList true)))
      (.identifier "value".toList)) = none := by decide

end Controls

#print axioms increment_is_exact
#print axioms store_is_postIndex_then_write
#print axioms independent_side_effect_orders_agree
#print axioms store_defined
#print axioms store_missing_iff
#print axioms store_realizes_append
#print axioms store_keeps_old_prefix
#print axioms recognizes_authored_store
#print axioms recognized_store_execution
#print axioms Controls.append_uses_old_index
#print axioms Controls.increment_alone_is_not_append
#print axioms Controls.full_array_has_no_defined_store
#print axioms Controls.unconditional_unsigned_increment_wraps
#print axioms Controls.mismatched_owner_is_not_admitted

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.PostIndex
