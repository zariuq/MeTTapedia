import Mettapedia.GSLT.LanguageDef.NativeOpsSyntax
import Mettapedia.GSLT.LanguageDef.NativeOpsMemoryGuards

/-!
# Logical live storage for compact native operations

Addresses name live storage, an element and a sequence of record fields.  They
are logical locations, not physical integers.  A concrete pointer realization
must relate them to live correctly typed storage and preserve aliases.  A null
check alone does not establish that relation.  Missing storage or invalid
record paths have no defined memory transition, rather than an invented C
runtime fault.  Record values carry their declared ordered fields.

Source scalars are bounded naturals; target scalars are bit vectors.  Reads and
writes are defined independently, and correspondence covers nested records,
array views, references and exact live ownership extents.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeWord64 (Word Byte encode)

structure Address where
  storage : Nat
  element : Nat
  fields : List Nat
  deriving DecidableEq, Repr

inductive SourceValue where
  | unit
  | word (value : Word)
  | byte (value : Byte)
  | bool (value : Bool)
  | record (name : String) (fields : List SourceValue)
  | reference (address : Option Address)
  | array (element : NativeType) (address : Option Address) (length : Word)
  deriving Repr

inductive TargetValue where
  | unit
  | word (value : BitVec 64)
  | byte (value : BitVec 8)
  | bool (value : Bool)
  | record (name : String) (fields : List TargetValue)
  | reference (address : Option Address)
  | array (element : NativeType) (address : Option Address) (length : BitVec 64)
  deriving Repr

mutual
  def encodeValue : SourceValue → TargetValue
    | .unit => .unit
    | .word value => .word (encode value)
    | .byte value => .byte (encode value)
    | .bool value => .bool value
    | .record name fields => .record name (encodeValues fields)
    | .reference address => .reference address
    | .array element address length => .array element address (encode length)

  def encodeValues : List SourceValue → List TargetValue
    | [] => []
    | value :: rest => encodeValue value :: encodeValues rest
end

mutual
  def decodeValue : TargetValue → SourceValue
    | .unit => .unit
    | .word value => .word value.toFin
    | .byte value => .byte value.toFin
    | .bool value => .bool value
    | .record name fields => .record name (decodeValues fields)
    | .reference address => .reference address
    | .array element address length => .array element address length.toFin

  def decodeValues : List TargetValue → List SourceValue
    | [] => []
    | value :: rest => decodeValue value :: decodeValues rest
end

mutual
  theorem decode_encode_value (value : SourceValue) : decodeValue (encodeValue value) = value := by
    cases value with
    | record name fields =>
        simp only [encodeValue, decodeValue, decode_encode_values fields]
    | _ => rfl
  termination_by sizeOf value

  theorem decode_encode_values (values : List SourceValue) :
      decodeValues (encodeValues values) = values := by
    cases values with
    | nil => rfl
    | cons value rest => simp only [encodeValues, decodeValues, decode_encode_value value,
        decode_encode_values rest]
  termination_by sizeOf values
end

mutual
  theorem encode_decode_value (value : TargetValue) : encodeValue (decodeValue value) = value := by
    cases value with
    | record name fields =>
        simp only [decodeValue, encodeValue, encode_decode_values fields]
    | word value => simp [encodeValue, decodeValue, encode, BitVec.ofFin_toFin]
    | byte value => simp [encodeValue, decodeValue, encode, BitVec.ofFin_toFin]
    | array element address length => simp [encodeValue, decodeValue, encode, BitVec.ofFin_toFin]
    | _ => rfl
  termination_by sizeOf value

  theorem encode_decode_values (values : List TargetValue) :
      encodeValues (decodeValues values) = values := by
    cases values with
    | nil => rfl
    | cons value rest => simp only [decodeValues, encodeValues, encode_decode_value value,
        encode_decode_values rest]
  termination_by sizeOf values
end

theorem encodeValue_injective : Function.Injective encodeValue := by
  intro left right equal
  have decoded := congrArg decodeValue equal
  simpa only [decode_encode_value] using decoded

def sourceReadPath : List Nat → SourceValue → Option SourceValue
  | [], value => some value
  | index :: rest, .record _ fields => fields[index]?.bind (sourceReadPath rest)
  | _ :: _, _ => none

def targetReadPath : List Nat → TargetValue → Option TargetValue
  | [], value => some value
  | index :: rest, .record _ fields => fields[index]?.bind (targetReadPath rest)
  | _ :: _, _ => none

theorem encodeValues_getElem? (values : List SourceValue) (index : Nat) :
    (encodeValues values)[index]? = (values[index]?).map encodeValue := by
  induction values generalizing index with
  | nil => simp [encodeValues]
  | cons value rest ih => cases index <;> simp [encodeValues, ih]

theorem read_path_correspondence (path : List Nat) (value : SourceValue) :
    targetReadPath path (encodeValue value) = (sourceReadPath path value).map encodeValue := by
  induction path generalizing value with
  | nil => rfl
  | cons index rest ih =>
      cases value with
      | record name fields =>
          simp only [sourceReadPath, encodeValue, targetReadPath, encodeValues_getElem?]
          cases selected : fields[index]? <;> simp [ih]
      | _ => rfl

def sourceWritePath : List Nat → SourceValue → SourceValue → Option SourceValue
  | [], replacement, _ => some replacement
  | index :: rest, replacement, .record name fields => do
      let child ← fields[index]?
      let updated ← sourceWritePath rest replacement child
      some (.record name (fields.set index updated))
  | _ :: _, _, _ => none

def targetWritePath : List Nat → TargetValue → TargetValue → Option TargetValue
  | [], replacement, _ => some replacement
  | index :: rest, replacement, .record name fields => do
      let child ← fields[index]?
      let updated ← targetWritePath rest replacement child
      some (.record name (fields.set index updated))
  | _ :: _, _, _ => none

/-- A readable field path has a defined replacement in the same record.
This is a law of the admitted memory model, not permission to access a
concurrent or externally owned address. -/
theorem targetWritePath_defined_of_read {path : List Nat} {before observed : TargetValue}
    (read : targetReadPath path before = some observed) (replacement : TargetValue) :
    ∃ after, targetWritePath path replacement before = some after := by
  induction path generalizing before with
  | nil => exact ⟨replacement, rfl⟩
  | cons index rest ih =>
      cases before with
      | record name fields =>
          cases selected : fields[index]? with
          | none => simp [targetReadPath, selected] at read
          | some child =>
              have childRead : targetReadPath rest child = some observed := by
                simpa [targetReadPath, selected] using read
              obtain ⟨updated, written⟩ := ih childRead
              exact ⟨.record name (fields.set index updated), by
                simp [targetWritePath, selected, written]⟩
      | unit | word _ | byte _ | bool _ | reference _ | array _ _ _ =>
          simp [targetReadPath] at read

/-- A defined nested-field write can be read back at the same path. -/
theorem targetReadPath_after_write {path : List Nat} {replacement before after : TargetValue}
    (written : targetWritePath path replacement before = some after) :
    targetReadPath path after = some replacement := by
  induction path generalizing before after with
  | nil =>
      simp only [targetWritePath] at written
      cases Option.some.inj written
      rfl
  | cons index rest ih =>
      cases before with
      | record name fields =>
          cases selected : fields[index]? with
          | none => simp [targetWritePath, selected] at written
          | some child =>
              cases changed : targetWritePath rest replacement child with
              | none => simp [targetWritePath, selected, changed] at written
              | some updated =>
                  have same : TargetValue.record name (fields.set index updated) = after := by
                    simpa [targetWritePath, selected, changed] using written
                  subst after
                  have inside : index < fields.length :=
                    (List.getElem?_eq_some_iff.mp selected).1
                  simp [targetReadPath, List.getElem?_set_self inside, ih changed]
      | _ => simp [targetWritePath] at written

theorem encodeValues_set (values : List SourceValue) (index : Nat) (replacement : SourceValue) :
    encodeValues (values.set index replacement) =
      (encodeValues values).set index (encodeValue replacement) := by
  induction values generalizing index with
  | nil => rfl
  | cons value rest ih => cases index <;> simp [encodeValues, ih]

theorem write_path_correspondence (path : List Nat) (replacement value : SourceValue) :
    targetWritePath path (encodeValue replacement) (encodeValue value) =
      (sourceWritePath path replacement value).map encodeValue := by
  induction path generalizing value with
  | nil => rfl
  | cons index rest ih =>
      cases value with
      | record name fields =>
          simp only [sourceWritePath, encodeValue, targetWritePath, encodeValues_getElem?]
          cases selected : fields[index]? with
          | none => rfl
          | some child =>
              simp only [Option.map_some, bind, Option.bind, ih]
              cases changed : sourceWritePath rest replacement child <;>
                simp [encodeValue, encodeValues_set]
      | _ => rfl

abbrev SourceCells := Nat → Nat → Option SourceValue
abbrev TargetCells := Nat → Nat → Option TargetValue

structure SourceMemory where
  cells : SourceCells
  owned : Nat → Option Word

structure TargetMemory where
  cells : TargetCells
  owned : Nat → Option (BitVec 64)

def MemoryRelated (source : SourceMemory) (target : TargetMemory) : Prop :=
  (∀ storage element, target.cells storage element =
    (source.cells storage element).map encodeValue) ∧
  (∀ storage, target.owned storage = (source.owned storage).map encode)

/-- The independent memory relation determines the whole native memory,
 including all live cells and the allocation ownership map. -/
theorem memory_related_target_unique {source : SourceMemory} {one two : TargetMemory}
    (first : MemoryRelated source one) (second : MemoryRelated source two) : one = two := by
  have cells : one.cells = two.cells := by
    funext storage element
    exact (first.1 storage element).trans (second.1 storage element).symm
  have owned : one.owned = two.owned := by
    funext storage
    exact (first.2 storage).trans (second.2 storage).symm
  cases one
  cases two
  cases cells
  cases owned
  rfl

def sourceRead (memory : SourceMemory) (address : Address) : Option SourceValue :=
  (memory.cells address.storage address.element).bind (sourceReadPath address.fields)

def targetRead (memory : TargetMemory) (address : Address) : Option TargetValue :=
  (memory.cells address.storage address.element).bind (targetReadPath address.fields)

theorem memory_read_correspondence (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (address : Address) :
    targetRead target address = (sourceRead source address).map encodeValue := by
  simp only [targetRead, sourceRead, related.1]
  cases source.cells address.storage address.element <;> simp [read_path_correspondence]

theorem memory_read_result_iff (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (address : Address) (value : SourceValue) :
    targetRead target address = some (encodeValue value) ↔ sourceRead source address = some value := by
  rw [memory_read_correspondence source target related]
  cases sourceRead source address <;> simp [encodeValue_injective.eq_iff]

theorem memory_read_missing_iff (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (address : Address) :
    targetRead target address = none ↔ sourceRead source address = none := by
  rw [memory_read_correspondence source target related]
  cases sourceRead source address <;> simp

def sourceStoreCell (memory : SourceMemory) (storage element : Nat)
    (value : SourceValue) : SourceMemory :=
  { memory with cells := fun candidate index =>
      if candidate = storage ∧ index = element then some value else memory.cells candidate index }

def targetStoreCell (memory : TargetMemory) (storage element : Nat)
    (value : TargetValue) : TargetMemory :=
  { memory with cells := fun candidate index =>
      if candidate = storage then
        if index = element then some value else memory.cells candidate index
      else memory.cells candidate index }

def sourceWrite (memory : SourceMemory) (address : Address) (value : SourceValue) :
    Option SourceMemory := do
  let previous ← memory.cells address.storage address.element
  let updated ← sourceWritePath address.fields value previous
  some (sourceStoreCell memory address.storage address.element updated)

def targetWrite (memory : TargetMemory) (address : Address) (value : TargetValue) :
    Option TargetMemory := do
  let previous ← memory.cells address.storage address.element
  let updated ← targetWritePath address.fields value previous
  some (targetStoreCell memory address.storage address.element updated)

/-- Separate storage identities retain independent cell updates. The actual
memory map commutes; this does not identify invocation histories or owners. -/
theorem targetStoreCell_commute_other_storage (memory : TargetMemory)
    (first second firstIndex secondIndex : Nat) (firstValue secondValue : TargetValue)
    (different : first ≠ second) :
    targetStoreCell (targetStoreCell memory first firstIndex firstValue)
        second secondIndex secondValue =
      targetStoreCell (targetStoreCell memory second secondIndex secondValue)
        first firstIndex firstValue := by
  have same : (targetStoreCell (targetStoreCell memory first firstIndex firstValue)
        second secondIndex secondValue).cells =
      (targetStoreCell (targetStoreCell memory second secondIndex secondValue)
        first firstIndex firstValue).cells := by
    funext candidate index
    by_cases atFirst : candidate = first
    · subst candidate
      simp [targetStoreCell, different]
    · by_cases atSecond : candidate = second
      · subst candidate
        simp [targetStoreCell, different.symm]
      · simp [targetStoreCell, atFirst, atSecond]
  exact congrArg (fun cells => TargetMemory.mk cells memory.owned) same

theorem targetRead_storeCell_other_storage (memory : TargetMemory) (address : Address)
    (storage index : Nat) (value : TargetValue) (different : address.storage ≠ storage) :
    targetRead (targetStoreCell memory storage index value) address = targetRead memory address := by
  simp [targetRead, targetStoreCell, different]

/-- Definedness and the exact written memory survive an independent local
declaration. An undefined write remains undefined. -/
theorem targetWrite_storeCell_other_storage (memory : TargetMemory) (address : Address)
    (storage index : Nat) (localValue replacement : TargetValue)
    (different : address.storage ≠ storage) :
    targetWrite (targetStoreCell memory storage index localValue) address replacement =
      (targetWrite memory address replacement).map
        (fun written => targetStoreCell written storage index localValue) := by
  have readCell : (targetStoreCell memory storage index localValue).cells
      address.storage address.element = memory.cells address.storage address.element := by
    simp [targetStoreCell, different]
  simp only [targetWrite, readCell]
  cases previous : memory.cells address.storage address.element with
  | none => rfl
  | some before =>
      cases updated : targetWritePath address.fields replacement before with
      | none => simp only [bind, Option.bind, updated, Option.map_none]
      | some after =>
          simp only [bind, Option.bind, updated, Option.map_some]
          exact congrArg some (targetStoreCell_commute_other_storage memory storage
            address.storage index address.element localValue after different.symm)

/-- Reading a live field supplies the memory-model precondition for replacing
that field. It does not grant ownership or authorize physical publication. -/
theorem targetWrite_defined_of_read {memory : TargetMemory} {address : Address}
    {observed : TargetValue} (read : targetRead memory address = some observed)
    (replacement : TargetValue) :
    ∃ post, targetWrite memory address replacement = some post := by
  cases selected : memory.cells address.storage address.element with
  | none => simp [targetRead, selected] at read
  | some before =>
      have fieldRead : targetReadPath address.fields before = some observed := by
        simpa [targetRead, selected] using read
      obtain ⟨after, written⟩ := targetWritePath_defined_of_read fieldRead replacement
      exact ⟨targetStoreCell memory address.storage address.element after, by
        simp [targetWrite, selected, written]⟩

/-- The memory operation updates one live cell and leaves allocation ownership
unchanged. Missing cells never obtain a defined write through this law. -/
theorem targetRead_after_write {memory post : TargetMemory} {address : Address}
    {replacement : TargetValue} (written : targetWrite memory address replacement = some post) :
    targetRead post address = some replacement ∧ post.owned = memory.owned := by
  cases old : memory.cells address.storage address.element with
  | none => simp [targetWrite, old] at written
  | some before =>
      cases changed : targetWritePath address.fields replacement before with
      | none => simp [targetWrite, old, changed] at written
      | some after =>
          have same : targetStoreCell memory address.storage address.element after = post := by
            simpa [targetWrite, old, changed] using written
          subst post
          constructor
          · simpa [targetRead, targetStoreCell] using targetReadPath_after_write changed
          · rfl

theorem store_cell_correspondence (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (storage element : Nat) (value : SourceValue) :
    MemoryRelated (sourceStoreCell source storage element value)
      (targetStoreCell target storage element (encodeValue value)) := by
  constructor
  · intro candidate index
    by_cases sameStorage : candidate = storage <;> by_cases sameIndex : index = element <;>
      simp [sourceStoreCell, targetStoreCell, sameStorage, sameIndex, related.1]
  · exact related.2

theorem memory_write_forward (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (address : Address) (value : SourceValue)
    (result : SourceMemory) (wrote : sourceWrite source address value = some result) :
    ∃ native, targetWrite target address (encodeValue value) = some native ∧
      MemoryRelated result native := by
  cases previous : source.cells address.storage address.element with
  | none => simp [sourceWrite, previous, bind, Option.bind] at wrote
  | some old =>
      cases changed : sourceWritePath address.fields value old with
      | none => simp [sourceWrite, previous, changed, bind, Option.bind] at wrote
      | some updated =>
          have same : sourceStoreCell source address.storage address.element updated = result :=
            by simpa [sourceWrite, previous, changed, bind, Option.bind] using wrote
          subst result
          refine ⟨targetStoreCell target address.storage address.element (encodeValue updated),
            ?_, store_cell_correspondence source target related _ _ _⟩
          simp [targetWrite, related.1, previous, write_path_correspondence, changed,
            bind, Option.bind]

theorem memory_write_backward (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (address : Address) (value : SourceValue)
    (native : TargetMemory) (wrote : targetWrite target address (encodeValue value) = some native) :
    ∃ result, sourceWrite source address value = some result ∧ MemoryRelated result native := by
  cases previous : source.cells address.storage address.element with
  | none => simp [targetWrite, related.1, previous, bind, Option.bind] at wrote
  | some old =>
      cases changed : sourceWritePath address.fields value old with
      | none =>
          simp [targetWrite, related.1, previous, write_path_correspondence, changed,
            bind, Option.bind] at wrote
      | some updated =>
          have same : targetStoreCell target address.storage address.element (encodeValue updated) =
              native := by
            simpa [targetWrite, related.1, previous, write_path_correspondence, changed,
              bind, Option.bind] using wrote
          subst native
          refine ⟨sourceStoreCell source address.storage address.element updated, ?_,
            store_cell_correspondence source target related _ _ _⟩
          simp [sourceWrite, previous, changed, bind, Option.bind]

theorem memory_write_missing_iff (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (address : Address) (value : SourceValue) :
    targetWrite target address (encodeValue value) = none ↔ sourceWrite source address value = none := by
  cases previous : source.cells address.storage address.element with
  | none => simp [sourceWrite, targetWrite, related.1, previous, bind, Option.bind]
  | some old =>
      cases changed : sourceWritePath address.fields value old <;>
        simp [sourceWrite, targetWrite, related.1, previous, write_path_correspondence, changed,
          bind, Option.bind]

/-- Ordered field transport reads each source field at the moment its write
occurs. Overlapping source and destination records therefore retain C's
sequential behavior; the source record is not snapshotted in advance. -/
def sourceCopyFields (source destination : Address) :
    List (Nat × Nat) → SourceMemory → Option SourceMemory
  | [], memory => some memory
  | (readIndex, writeIndex) :: rest, memory => do
      let value ← sourceRead memory { source with fields := source.fields ++ [readIndex] }
      let written ← sourceWrite memory { destination with fields := destination.fields ++ [writeIndex] } value
      sourceCopyFields source destination rest written

def targetCopyFields (source destination : Address) :
    List (Nat × Nat) → TargetMemory → Option TargetMemory
  | [], memory => some memory
  | (readIndex, writeIndex) :: rest, memory => do
      let value ← targetRead memory { source with fields := source.fields ++ [readIndex] }
      let written ← targetWrite memory { destination with fields := destination.fields ++ [writeIndex] } value
      targetCopyFields source destination rest written

theorem field_copies_forward (sourceAddress destination : Address)
    (fields : List (Nat × Nat)) {source : SourceMemory} {target : TargetMemory}
    (related : MemoryRelated source target) {after : SourceMemory}
    (copied : sourceCopyFields sourceAddress destination fields source = some after) :
    ∃ native, targetCopyFields sourceAddress destination fields target = some native ∧
      MemoryRelated after native := by
  induction fields generalizing source target with
  | nil =>
      cases Option.some.inj copied
      exact ⟨target, rfl, related⟩
  | cons field rest ih =>
      rcases field with ⟨readIndex, writeIndex⟩
      cases loaded : sourceRead source { sourceAddress with fields := sourceAddress.fields ++ [readIndex] } with
      | none => simp [sourceCopyFields, loaded] at copied
      | some value =>
          cases written : sourceWrite source
              { destination with fields := destination.fields ++ [writeIndex] } value with
          | none => simp [sourceCopyFields, loaded, written] at copied
          | some middle =>
              have remaining : sourceCopyFields sourceAddress destination rest middle = some after := by
                simpa [sourceCopyFields, loaded, written] using copied
              obtain ⟨nativeMiddle, nativeWrite, middleRelated⟩ :=
                memory_write_forward source target related _ value middle written
              obtain ⟨native, tail, afterRelated⟩ := ih middleRelated remaining
              exact ⟨native, by
                simp [targetCopyFields, memory_read_correspondence source target related,
                  loaded, nativeWrite, tail], afterRelated⟩

theorem field_copies_backward (sourceAddress destination : Address)
    (fields : List (Nat × Nat)) {source : SourceMemory} {target : TargetMemory}
    (related : MemoryRelated source target) {native : TargetMemory}
    (copied : targetCopyFields sourceAddress destination fields target = some native) :
    ∃ after, sourceCopyFields sourceAddress destination fields source = some after ∧
      MemoryRelated after native := by
  induction fields generalizing source target with
  | nil =>
      cases Option.some.inj copied
      exact ⟨source, rfl, related⟩
  | cons field rest ih =>
      rcases field with ⟨readIndex, writeIndex⟩
      cases loaded : sourceRead source { sourceAddress with fields := sourceAddress.fields ++ [readIndex] } with
      | none =>
          simp [targetCopyFields, memory_read_correspondence source target related, loaded] at copied
      | some value =>
          have nativeLoad : targetRead target
              { sourceAddress with fields := sourceAddress.fields ++ [readIndex] } = some (encodeValue value) := by
            simp [memory_read_correspondence source target related, loaded]
          cases written : targetWrite target
              { destination with fields := destination.fields ++ [writeIndex] } (encodeValue value) with
          | none => simp [targetCopyFields, nativeLoad, written] at copied
          | some middle =>
              have remaining : targetCopyFields sourceAddress destination rest middle = some native := by
                simpa [targetCopyFields, nativeLoad, written] using copied
              obtain ⟨sourceMiddle, sourceWrite, middleRelated⟩ :=
                memory_write_backward source target related _ value middle written
              obtain ⟨after, tail, afterRelated⟩ := ih middleRelated remaining
              exact ⟨after, by simp [sourceCopyFields, loaded, sourceWrite, tail], afterRelated⟩

theorem field_copies_missing_iff (sourceAddress destination : Address)
    (fields : List (Nat × Nat)) {source : SourceMemory} {target : TargetMemory}
    (related : MemoryRelated source target) :
    targetCopyFields sourceAddress destination fields target = none ↔
      sourceCopyFields sourceAddress destination fields source = none := by
  constructor
  · intro missing
    cases copied : sourceCopyFields sourceAddress destination fields source with
    | none => rfl
    | some after =>
        obtain ⟨native, copied, _⟩ := field_copies_forward sourceAddress destination fields related copied
        rw [missing] at copied
        contradiction
  · intro missing
    cases copied : targetCopyFields sourceAddress destination fields target with
    | none => rfl
    | some native =>
        obtain ⟨after, copied, _⟩ := field_copies_backward sourceAddress destination fields related copied
        rw [missing] at copied
        contradiction

/-- Native field transport does not allocate or acquire ownership of payloads. -/
theorem target_field_copies_owned (source destination : Address)
    (fields : List (Nat × Nat)) {memory after : TargetMemory}
    (copied : targetCopyFields source destination fields memory = some after) :
    after.owned = memory.owned := by
  induction fields generalizing memory with
  | nil => cases Option.some.inj copied; rfl
  | cons field rest ih =>
      rcases field with ⟨readIndex, writeIndex⟩
      cases loaded : targetRead memory { source with fields := source.fields ++ [readIndex] } with
      | none => simp [targetCopyFields, loaded] at copied
      | some value =>
          cases written : targetWrite memory { destination with fields := destination.fields ++ [writeIndex] } value with
          | none => simp [targetCopyFields, loaded, written] at copied
          | some middle =>
              have remaining : targetCopyFields source destination rest middle = some after := by
                simpa [targetCopyFields, loaded, written] using copied
              exact (ih remaining).trans (targetRead_after_write written).2

namespace FieldCopyControls

def address : Address := ⟨1, 0, []⟩

def source : SourceMemory :=
  ⟨fun storage element => if storage = 1 ∧ element = 0 then
      some (.record "Triple" [.word 7, .word 11, .word 13]) else none,
   fun storage => if storage = 1 then some 1 else none⟩

def target : TargetMemory :=
  ⟨fun storage element => if storage = 1 ∧ element = 0 then
      some (.record "Triple" [.word 7, .word 11, .word 13]) else none,
   fun storage => if storage = 1 then some 1 else none⟩

def sourceObservation (fields : List (Nat × Nat)) : Option SourceValue :=
  (sourceCopyFields address address fields source).bind
    (fun after => sourceRead after ⟨1, 0, [2]⟩)

def targetObservation (fields : List (Nat × Nat)) : Option TargetValue :=
  (targetCopyFields address address fields target).bind
    (fun after => targetRead after ⟨1, 0, [2]⟩)

/-- The second read sees the first assignment through the existing alias. -/
theorem aliased_source_read_after_write :
    sourceObservation [(0, 1), (1, 2)] = some (.word 7) := by rfl

theorem aliased_target_read_after_write :
    targetObservation [(0, 1), (1, 2)] = some (.word 7) := by rfl

theorem reordered_assignments_change_observation :
    targetObservation [(1, 2), (0, 1)] ≠ targetObservation [(0, 1), (1, 2)] := by
  intro same
  have impossible : (some (.word 11) : Option TargetValue) = some (.word 7) := same
  have words := TargetValue.word.inj (Option.some.inj impossible)
  have values := congrArg BitVec.toNat words
  contradiction

theorem omitted_assignment_changes_observation :
    targetObservation [(1, 2)] ≠ targetObservation [(0, 1), (1, 2)] := by
  intro same
  have impossible : (some (.word 11) : Option TargetValue) = some (.word 7) := same
  have words := TargetValue.word.inj (Option.some.inj impossible)
  have values := congrArg BitVec.toNat words
  contradiction

theorem nonexistent_field_is_not_zero :
    targetCopyFields address address [(3, 1)] target = none := by rfl

end FieldCopyControls

def sourceRelease (memory : SourceMemory) (storage : Nat) : SourceMemory :=
  { cells := fun candidate index => if candidate = storage then none else memory.cells candidate index
    owned := fun candidate => if candidate = storage then none else memory.owned candidate }

def targetRelease (memory : TargetMemory) (storage : Nat) : TargetMemory :=
  { cells := fun candidate index => if candidate = storage then none else memory.cells candidate index
    owned := fun candidate => if candidate = storage then none else memory.owned candidate }

theorem release_correspondence (source : SourceMemory) (target : TargetMemory)
    (related : MemoryRelated source target) (storage : Nat) :
    MemoryRelated (sourceRelease source storage) (targetRelease target storage) := by
  constructor
  · intro candidate index
    by_cases same : candidate = storage <;> simp [sourceRelease, targetRelease, same, related.1]
  · intro candidate
    by_cases same : candidate = storage <;> simp [sourceRelease, targetRelease, same, related.2]

theorem released_storage_has_no_cells (memory : TargetMemory) (storage element : Nat) :
    (targetRelease memory storage).cells storage element = none := by simp [targetRelease]

theorem released_storage_has_no_ownership (memory : TargetMemory) (storage : Nat) :
    (targetRelease memory storage).owned storage = none := by simp [targetRelease]

end Mettapedia.GSLT.LanguageDef.NativeOps
