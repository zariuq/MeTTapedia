import Mettapedia.GSLT.LanguageDef.NativeOpsByteViews
import Mettapedia.GSLT.LanguageDef.NativeOpsMemoryEffects

/-!
Typed byte-copy effects for the execution interface. The source snapshots the
borrowed block and writes bounded byte values in order; the target independently
reads native byte cells and writes bit-vector values. Empty copies read and
write nothing. The nonoverlapping storage domain of C memcpy is explicit;
missing source or destination cells have no defined transition. A copy does
not allocate storage, change ownership or manufacture a completed observation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeExecutionByteCopy

open NativeOps (Address SourceMemory TargetMemory SourceValue TargetValue MemoryRelated)
open NativeOps.ByteViews (advance sourceBlock targetBlock)

def sourceByte (byte : UInt8) : SourceValue := .byte byte.toBitVec.toFin

def targetByte (byte : UInt8) : TargetValue := .byte byte.toBitVec

theorem byte_correspondence (byte : UInt8) :
    NativeOps.encodeValue (sourceByte byte) = targetByte byte := rfl

def sourceStore (memory : SourceMemory) (address : Address) : List UInt8 → Option SourceMemory
  | [] => some memory
  | byte :: rest => do
      let changed ← NativeOps.sourceWrite memory address (sourceByte byte)
      sourceStore changed (advance address) rest

def targetStore (memory : TargetMemory) (address : Address) : List UInt8 → Option TargetMemory
  | [] => some memory
  | byte :: rest =>
      match NativeOps.targetWrite memory address (targetByte byte) with
      | none => none
      | some changed => targetStore changed (advance address) rest

theorem store_forward (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (address : Address) (bytes : List UInt8)
    (post : SourceMemory) (stored : sourceStore source address bytes = some post) :
    ∃ native, targetStore target address bytes = some native ∧ MemoryRelated post native := by
  induction bytes generalizing source target address post with
  | nil =>
    have same : source = post := Option.some.inj stored
    exact ⟨target, rfl, same ▸ related⟩
  | cons byte rest ih =>
    cases wrote : NativeOps.sourceWrite source address (sourceByte byte) with
    | none => simp only [sourceStore, wrote, bind, Option.bind_none] at stored; cases stored
    | some changed =>
      have tail : sourceStore changed (advance address) rest = some post := by
        simpa only [sourceStore, wrote, bind, Option.bind_some] using stored
      obtain ⟨nativeChanged, nativeWrite, changedRelated⟩ :=
        NativeOps.memory_write_forward source target related address (sourceByte byte) changed wrote
      rw [byte_correspondence] at nativeWrite
      obtain ⟨native, nativeTail, memories⟩ := ih changed nativeChanged changedRelated
        (advance address) post tail
      exact ⟨native, by simp only [targetStore, nativeWrite, nativeTail], memories⟩

theorem store_backward (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (address : Address) (bytes : List UInt8)
    (native : TargetMemory) (stored : targetStore target address bytes = some native) :
    ∃ post, sourceStore source address bytes = some post ∧ MemoryRelated post native := by
  induction bytes generalizing source target address native with
  | nil =>
    have same : target = native := Option.some.inj stored
    exact ⟨source, rfl, same ▸ related⟩
  | cons byte rest ih =>
    cases wrote : NativeOps.targetWrite target address (targetByte byte) with
    | none => simp only [targetStore, wrote] at stored; cases stored
    | some changed =>
      have tail : targetStore changed (advance address) rest = some native := by
        simpa only [targetStore, wrote] using stored
      have encodedWrite : NativeOps.targetWrite target address
          (NativeOps.encodeValue (sourceByte byte)) = some changed := by
        rw [byte_correspondence]
        exact wrote
      obtain ⟨sourceChanged, sourceWrite, changedRelated⟩ :=
        NativeOps.memory_write_backward source target related address (sourceByte byte) changed encodedWrite
      obtain ⟨post, sourceTail, memories⟩ := ih sourceChanged changed changedRelated
        (advance address) native tail
      exact ⟨post, by simp only [sourceStore, sourceWrite, bind, Option.bind_some, sourceTail], memories⟩

def disjoint (input output : Address) (count : Nat) : Prop :=
  input.storage ≠ output.storage ∨
    (input.fields = [] ∧ output.fields = [] ∧
      (input.element + count ≤ output.element ∨ output.element + count ≤ input.element))

instance (input output : Address) (count : Nat) : Decidable (disjoint input output count) := by
  unfold disjoint
  infer_instance

def sourceCopy (memory : SourceMemory) (input output : Address) (count : Nat) :
    Option SourceMemory :=
  if count = 0 then some memory
  else if disjoint input output count then do
    let bytes ← sourceBlock memory input count
    sourceStore memory output bytes
  else none

def targetCopy (memory : TargetMemory) (input output : Address) (count : Nat) :
    Option TargetMemory :=
  if count ≠ 0 then
    if disjoint input output count then
      match targetBlock memory input count with
      | none => none
      | some bytes => targetStore memory output bytes
    else none
  else some memory

theorem copy_forward (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (input output : Address) (count : Nat)
    (post : SourceMemory) (copied : sourceCopy source input output count = some post) :
    ∃ native, targetCopy target input output count = some native ∧ MemoryRelated post native := by
  by_cases empty : count = 0
  · have same : source = post := Option.some.inj (by simpa only [sourceCopy, if_pos empty] using copied)
    exact ⟨target, by simp only [targetCopy, empty, ne_eq, not_true_eq_false, if_false], same ▸ related⟩
  · simp only [sourceCopy, if_neg empty] at copied
    by_cases separate : disjoint input output count
    · simp only [if_pos separate] at copied
      cases read : sourceBlock source input count with
      | none => simp only [read, bind, Option.bind_none] at copied; cases copied
      | some bytes =>
        have stored : sourceStore source output bytes = some post := by
          simpa only [read, bind, Option.bind_some] using copied
        obtain ⟨native, wrote, memories⟩ := store_forward source target related output bytes post stored
        exact ⟨native, by simp only [targetCopy, if_pos empty, if_pos separate,
          NativeOps.ByteViews.block_correspondence source target related, read, wrote], memories⟩
    · simp only [if_neg separate] at copied; cases copied

theorem copy_backward (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (input output : Address) (count : Nat)
    (native : TargetMemory) (copied : targetCopy target input output count = some native) :
    ∃ post, sourceCopy source input output count = some post ∧ MemoryRelated post native := by
  by_cases empty : count = 0
  · have same : target = native := Option.some.inj (by
      simpa only [targetCopy, empty, ne_eq, not_true_eq_false, if_false] using copied)
    exact ⟨source, by simp only [sourceCopy, if_pos empty], same ▸ related⟩
  · simp only [targetCopy, if_pos empty,
      NativeOps.ByteViews.block_correspondence source target related] at copied
    by_cases separate : disjoint input output count
    · simp only [if_pos separate] at copied
      cases read : sourceBlock source input count with
      | none => simp only [read] at copied; cases copied
      | some bytes =>
        have stored : targetStore target output bytes = some native := by simpa only [read] using copied
        obtain ⟨post, wrote, memories⟩ := store_backward source target related output bytes native stored
        exact ⟨post, by simp only [sourceCopy, if_neg empty, if_pos separate, read,
          bind, Option.bind_some, wrote], memories⟩
    · simp only [if_neg separate] at copied; cases copied

theorem store_preserves_owned (memory post : SourceMemory) (address : Address) (bytes : List UInt8)
    (stored : sourceStore memory address bytes = some post) : post.owned = memory.owned := by
  induction bytes generalizing memory address with
  | nil => cases stored; rfl
  | cons byte rest ih =>
    cases wrote : NativeOps.sourceWrite memory address (sourceByte byte) with
    | none => simp only [sourceStore, wrote, bind, Option.bind_none] at stored; cases stored
    | some changed =>
      have tail : sourceStore changed (advance address) rest = some post := by
        simpa only [sourceStore, wrote, bind, Option.bind_some] using stored
      exact (ih changed (advance address) tail).trans
        (NativeOps.source_write_preserves_owned memory address (sourceByte byte) changed wrote)

theorem store_preserves_earlier_read (memory post : SourceMemory) (address earlier : Address)
    (bytes : List UInt8) (stored : sourceStore memory address bytes = some post)
    (before : earlier.storage ≠ address.storage ∨ earlier.element < address.element) :
    NativeOps.sourceRead post earlier = NativeOps.sourceRead memory earlier := by
  induction bytes generalizing memory address with
  | nil => cases stored; rfl
  | cons byte rest ih =>
    cases wrote : NativeOps.sourceWrite memory address (sourceByte byte) with
    | none => simp only [sourceStore, wrote, bind, Option.bind_none] at stored; cases stored
    | some changed =>
      have tail : sourceStore changed (advance address) rest = some post := by
        simpa only [sourceStore, wrote, bind, Option.bind_some] using stored
      have nextBefore : earlier.storage ≠ (advance address).storage ∨
          earlier.element < (advance address).element := by
        cases before with
        | inl different => exact Or.inl different
        | inr smaller => exact Or.inr (Nat.lt_succ_of_lt smaller)
      have other : earlier.storage ≠ address.storage ∨ earlier.element ≠ address.element :=
        before.imp id Nat.ne_of_lt
      exact (ih changed (advance address) tail nextBefore).trans
        (NativeOps.source_write_preserves_other_reads memory address (sourceByte byte)
          changed wrote earlier other)

theorem source_byte_readback (byte : UInt8) :
    NativeOps.ByteViews.sourceByte (sourceByte byte) = some byte := by
  rw [← NativeOps.ByteViews.scalar_byte_correspondence (sourceByte byte), byte_correspondence]
  rfl

theorem stored_contents (memory post : SourceMemory) (address : Address) (bytes : List UInt8)
    (stored : sourceStore memory address bytes = some post) :
    sourceBlock post address bytes.length = some bytes := by
  induction bytes generalizing memory address with
  | nil => rfl
  | cons byte rest ih =>
    cases wrote : NativeOps.sourceWrite memory address (sourceByte byte) with
    | none => simp only [sourceStore, wrote, bind, Option.bind_none] at stored; cases stored
    | some changed =>
      have tail : sourceStore changed (advance address) rest = some post := by
        simpa only [sourceStore, wrote, bind, Option.bind_some] using stored
      have first : NativeOps.ByteViews.sourceAt post address = some byte := by
        have untouched := store_preserves_earlier_read changed post (advance address) address rest
          tail (Or.inr (Nat.lt_succ_self address.element))
        simp only [NativeOps.ByteViews.sourceAt, untouched,
          NativeOps.source_read_after_write memory address (sourceByte byte) changed wrote,
          Option.bind_some, source_byte_readback]
      simp only [List.length_cons, sourceBlock, first, bind, Option.bind_some,
        ih changed (advance address) tail]

theorem target_stored_contents (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (address : Address) (bytes : List UInt8)
    (native : TargetMemory) (stored : targetStore target address bytes = some native) :
    targetBlock native address bytes.length = some bytes := by
  obtain ⟨post, wrote, memories⟩ := store_backward source target related address bytes native stored
  rw [NativeOps.ByteViews.block_correspondence post native memories]
  exact stored_contents source post address bytes wrote

theorem empty_copy_needs_no_cells (memory : SourceMemory) (input output : Address) :
    sourceCopy memory input output 0 = some memory := rfl

theorem overlapping_nonempty_copy_is_undefined (memory : SourceMemory) (input output : Address)
    (count : Nat) (nonempty : count ≠ 0) (overlap : ¬disjoint input output count) :
    sourceCopy memory input output count = none := by
  simp only [sourceCopy, if_neg nonempty, if_neg overlap]

end Mettapedia.GSLT.LanguageDef.NativeExecutionByteCopy
