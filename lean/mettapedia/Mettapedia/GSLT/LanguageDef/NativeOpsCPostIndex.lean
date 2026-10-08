import Mettapedia.GSLT.LanguageDef.NativeOpsCSyntax
import Mettapedia.Machines.OrderedDependencyCapacity
import Mettapedia.Algebra.OccurrenceIdentity

/-!
# Unsigned array stores and last-live exchanges in the admitted C syntax

The primitive models `array[count++] = value` using a finite slot list and an
actual unsigned counter. The UInt32 profile is compared with the common
bounded-word operation used for wider extents. The returned index is the old counter; the increment
and the slot write are separate operations. A missing slot has no defined
store transition. It is not an invented runtime error or allocator failure.

The list-prefix specification is independent of the slot-update implementation.
Its correspondence needs a live slot and a capacity bounded by UINT32_MAX.
The last-live exchange additionally uses a bounded word extent, retains every
backing cell, and refines the independent occurrence-removal specification.
Physical pointer realization, field layout and exclusion of concurrent readers
are not supplied by these array models or by syntactic recognition.
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

structure AppendSyntax where
  owner : Name
  arrayField : Name
  countField : Name
  deriving DecidableEq, Repr

def appendSyntax? : CStatement → Option (AppendSyntax × CExpr)
  | .assign (.index (.field (.identifier owner) arrayField true)
      (.postIncrement (.field (.identifier countOwner) countField true))) value =>
    if owner = countOwner then some (⟨owner, arrayField, countField⟩, value) else none
  | _ => none

def AppendSyntax.statement (site : AppendSyntax) (value : CExpr) : CStatement :=
  .assign (.index (.field (.identifier site.owner) site.arrayField true)
    (.postIncrement (.field (.identifier site.owner) site.countField true))) value

theorem recognizes_authored_append (site : AppendSyntax) (value : CExpr) :
    appendSyntax? (site.statement value) = some (site, value) := by
  cases site
  simp [AppendSyntax.statement, appendSyntax?]


/-- Recognition keeps the owner, array field, count field and RHS identity.
Different owners in the array and count operands are not silently identified. -/
structure StoreSyntax where
  owner : Name
  arrayField : Name
  countField : Name
  value : Name
  deriving DecidableEq, Repr

def storeSyntax? (statement : CStatement) : Option StoreSyntax :=
  match appendSyntax? statement with
  | some (site, .identifier value) =>
      some ⟨site.owner, site.arrayField, site.countField, value⟩
  | _ => none

def StoreSyntax.statement (site : StoreSyntax) : CStatement :=
  (⟨site.owner, site.arrayField, site.countField⟩ : AppendSyntax).statement
    (.identifier site.value)

theorem recognizes_authored_store (site : StoreSyntax) :
    storeSyntax? site.statement = some site := by
  cases site
  simp [StoreSyntax.statement, AppendSyntax.statement, storeSyntax?, appendSyntax?]

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

namespace WordStore

variable {width : Nat}

/-- A bounded-word count and its backing slots. Physical layout remains external. -/
def store (slots : List Value) (count : BitVec width) (value : Value) :
    Option (BitVec width × List Value) :=
  if count.toNat < slots.length then
    some (count + 1, slots.set count.toNat value)
  else none

theorem increment_is_exact (slots : List Value) (count : BitVec width)
    (sized : slots.length < 2 ^ width) (room : count.toNat < slots.length) :
    (count + 1).toNat = count.toNat + 1 := by
  have positive : 0 < width := by
    by_contra absent
    have zero : width = 0 := by omega
    have short : slots.length < 1 := by simpa only [zero, pow_zero] using sized
    omega
  have unit : (1 : BitVec width).toNat = 1 := BitVec.toNat_one positive
  rw [BitVec.toNat_add, unit, Nat.mod_eq_of_lt (by omega)]

theorem active_prefix_append (slots : List Value) (count : BitVec width)
    (value : Value) (sized : slots.length < 2 ^ width)
    (room : count.toNat < slots.length) :
    (slots.set count.toNat value).take (count + 1).toNat =
      slots.take count.toNat ++ [value] := by
  rw [increment_is_exact slots count sized room]
  have changedSlot : count.toNat < (slots.set count.toNat value).length := by
    simpa using room
  rw [List.take_succ_eq_append_getElem changedSlot,
    List.take_set_of_le (Nat.le_refl _), List.getElem_set_self]

theorem stored_post (slots : List Value) (count : BitVec width)
    (value : Value) (sized : slots.length < 2 ^ width)
    {next : BitVec width} {after : List Value}
    (stored : store slots count value = some (next, after)) :
    after.take next.toNat = slots.take count.toNat ++ [value] ∧
      next.toNat = count.toNat + 1 ∧ after.length = slots.length ∧
      after.take count.toNat = slots.take count.toNat := by
  unfold store at stored
  split at stored
  next room =>
    cases Option.some.inj stored
    exact ⟨active_prefix_append slots count value sized room,
      increment_is_exact slots count sized room, List.length_set,
      List.take_set_of_le (Nat.le_refl _)⟩
  next absent => cases stored

theorem uint32_store_to_word_store
    (array : Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.PostIndex.Array32 Value)
    (value : Value) :
    (Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.PostIndex.store array value).map
      (fun result => (result.count.toBitVec, result.slots)) =
      store array.slots array.count.toBitVec value := by
  simp only [Mettapedia.GSLT.LanguageDef.NativeOps.NativeC.PostIndex.store,
    store, UInt32.toNat_toBitVec]
  split <;> simp [UInt32.toBitVec_add]

/-- The resolver retains the supplied RHS. Pointer, layout and evaluation
contracts remain explicit at the caller's typed operand boundary. -/
def executeAppend (resolve : AppendSyntax → CExpr →
    Option (List Value × BitVec width × Value)) (statement : CStatement) :
    Option (BitVec width × List Value) :=
  match appendSyntax? statement with
  | none => none
  | some (site, rhs) => (resolve site rhs).bind fun operands =>
      store operands.1 operands.2.1 operands.2.2

theorem recognized_append_execution (resolve : AppendSyntax → CExpr →
    Option (List Value × BitVec width × Value)) (site : AppendSyntax) (rhs : CExpr)
    (slots : List Value) (count : BitVec width) (value : Value)
    (resolved : resolve site rhs = some (slots, count, value)) :
    executeAppend resolve (site.statement rhs) = store slots count value := by
  simp [executeAppend, recognizes_authored_append, resolved]


namespace Controls


theorem word64_append_preserves_spares :
    store [11, 999, 888] (1 : BitVec 64) 22 = some (2, [11, 22, 888]) :=
  by decide +kernel

theorem full_backing_array_refuses :
    store [11] (1 : BitVec 64) 22 = none := by decide +kernel

theorem absent_width_bound_can_wrap :
    store [11, 22, 33, 44] (3 : BitVec 2) 55 =
      some (0, [11, 22, 33, 55]) := by decide +kernel


end Controls

end WordStore

namespace LastExchange

open Mettapedia.Algebra.OccurrenceIdentity

variable {width : Nat}

/-- A live unsigned extent is decremented before the last initialized slot
is read. The backing slots, including the retired and spare cells, remain. -/
def exchangeLast (slots : List Value) (count : BitVec width) (index : Nat) :
    Option (BitVec width × List Value) :=
  if index < count.toNat then do
    let next := count - 1
    let last ← slots[next.toNat]?
    some (next, slots.set index last)
  else none

theorem decrement_is_exact (count : BitVec width) (positiveWidth : 0 < width)
    (positive : 0 < count.toNat) : (count - 1).toNat = count.toNat - 1 := by
  have unit : (1 : BitVec width).toNat = 1 := BitVec.toNat_one positiveWidth
  rw [BitVec.toNat_sub_of_not_usubOverflow (by
    simp only [BitVec.usubOverflow, unit, decide_eq_true_eq, Nat.not_lt]
    omega), unit]

theorem exchange_preserves_backing_extent (slots : List Value) (count : BitVec width)
    (index : Nat) (next : BitVec width) (after : List Value)
    (exchanged : exchangeLast slots count index = some (next, after)) :
    after.length = slots.length := by
  unfold exchangeLast at exchanged
  split at exchanged
  · cases last : slots[(count - 1).toNat]? with
    | none =>
        simp only [last, bind, Option.bind_none] at exchanged
        cases exchanged
    | some value =>
        simp only [last, bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at exchanged
        rcases exchanged with ⟨rfl, rfl⟩
        exact List.length_set
  · cases exchanged

/-- The list specification removes a selected occurrence and exchanges the
last live occurrence. It does not expose spare backing cells as live rows. -/
theorem exchange_refines_live_prefix (slots : List Value) (count : BitVec width)
    (index : Nat) (positiveWidth : 0 < width)
    (sized : count.toNat ≤ slots.length) (inside : index < count.toNat) :
    ∃ selected remaining next after,
      exchangeLast slots count index = some (next, after) ∧
      extractByLast index (slots.take count.toNat) = some (selected, remaining) ∧
      next.toNat + 1 = count.toNat ∧
      after.take next.toNat = remaining ∧ after.length = slots.length := by
  have positive : 0 < count.toNat := by omega
  have decremented := decrement_is_exact count positiveWidth positive
  have selectedInside : index < slots.length := by omega
  have lastInside : count.toNat - 1 < slots.length := by omega
  let selected := slots[index]'selectedInside
  let last := slots[count.toNat - 1]'lastInside
  have selectedRead : slots[index]? = some selected := List.getElem?_eq_getElem selectedInside
  have lastRead : slots[count.toNat - 1]? = some last := List.getElem?_eq_getElem lastInside
  have extent : (slots.take count.toNat).length = count.toNat :=
    List.length_take_of_le sized
  have prefixLast : (slots.take count.toNat).getLast? = some last := by
    rw [List.getLast?_eq_getElem?, extent, List.getElem?_take_of_lt (by omega)]
    exact lastRead
  have prefixSelected : (slots.take count.toNat)[index]? = some selected := by
    rw [List.getElem?_take_of_lt inside]
    exact selectedRead
  have writtenPrefix : (slots.set index last).take (count.toNat - 1) =
      ((slots.take count.toNat).set index last).dropLast := by
    rw [List.dropLast_eq_take, List.length_set, extent,
      List.take_set, List.take_set, List.take_take]
    rw [Nat.min_eq_left (by omega)]
  refine ⟨selected, ((slots.take count.toNat).set index last).dropLast,
    count - 1, slots.set index last, ?_, ?_, ?_, ?_, List.length_set⟩
  · simp only [exchangeLast, if_pos inside, decremented, lastRead, bind, Option.bind_some]
  · rw [extractByLast_correspondence]
    simp only [extractByLastIndexed, prefixSelected, prefixLast, bind, Option.bind_some]
  · omega
  · rw [decremented]
    exact writtenPrefix

structure ExchangeSyntax where
  owner : Name
  arrayField : Name
  countField : Name
  index : Name
  deriving DecidableEq, Repr

def ExchangeSyntax.statement (site : ExchangeSyntax) : CStatement :=
  .assign (.index (.field (.identifier site.owner) site.arrayField true)
      (.identifier site.index))
    (.index (.field (.identifier site.owner) site.arrayField true)
      (.unary .decrement (.field (.identifier site.owner) site.countField true)))

def exchangeSyntax? : CStatement → Option ExchangeSyntax
  | .assign (.index (.field (.identifier owner) array true) (.identifier index))
      (.index (.field (.identifier readOwner) readArray true)
        (.unary .decrement (.field (.identifier countOwner) count true))) =>
      if owner = readOwner ∧ owner = countOwner ∧ array = readArray then
        some ⟨owner, array, count, index⟩ else none
  | _ => none

theorem recognizes_authored_exchange (site : ExchangeSyntax) :
    exchangeSyntax? site.statement = some site := by
  cases site
  simp [ExchangeSyntax.statement, exchangeSyntax?]

/-- Resolving a recognized site supplies its live backing array and word
extent. This does not supply pointer authority or a physical field layout. -/
def executeExchange (resolve : ExchangeSyntax →
    Option (List Value × BitVec width × Nat)) (statement : CStatement) :
    Option (BitVec width × List Value) :=
  match exchangeSyntax? statement with
  | none => none
  | some site => (resolve site).bind fun operands =>
      exchangeLast operands.1 operands.2.1 operands.2.2

theorem recognized_exchange_execution (resolve : ExchangeSyntax →
    Option (List Value × BitVec width × Nat)) (site : ExchangeSyntax)
    (slots : List Value) (count : BitVec width) (index : Nat)
    (resolved : resolve site = some (slots, count, index)) :
    executeExchange resolve site.statement = exchangeLast slots count index := by
  simp [executeExchange, recognizes_authored_exchange, resolved]

namespace Controls

theorem spare_cells_do_not_become_live :
    exchangeLast [11, 22, 33, 999] (3 : BitVec 64) 0 =
      some (2, [33, 22, 33, 999]) := by decide +kernel

theorem selected_last_is_a_self_write :
    exchangeLast [11, 22, 33, 999] (3 : BitVec 64) 2 =
      some (2, [11, 22, 33, 999]) := by decide +kernel

theorem a_spare_index_is_not_live :
    exchangeLast [11, 22, 33, 999] (3 : BitVec 64) 3 = none := by decide +kernel

theorem empty_live_prefix_does_not_decrement :
    exchangeLast [999] (0 : BitVec 64) 0 = none ∧
      ((0 : BitVec 64) - 1).toNat = 18446744073709551615 := by decide +kernel

theorem missing_last_slot_has_no_defined_exchange :
    exchangeLast [11] (2 : BitVec 64) 0 = none := by decide +kernel

theorem a_different_count_owner_is_not_admitted :
    exchangeSyntax? (.assign
      (.index (.field (.identifier "left".toList) "rows".toList true) (.identifier ['i']))
      (.index (.field (.identifier "left".toList) "rows".toList true)
        (.unary .decrement (.field (.identifier "right".toList) "count".toList true)))) =
      none := by decide +kernel

end Controls


#print axioms decrement_is_exact
#print axioms exchange_preserves_backing_extent
#print axioms exchange_refines_live_prefix
#print axioms recognizes_authored_exchange
#print axioms recognized_exchange_execution

end LastExchange

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
