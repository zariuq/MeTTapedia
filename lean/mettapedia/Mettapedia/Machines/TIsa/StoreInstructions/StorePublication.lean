import Mettapedia.Machines.TIsa.StoreInstructions.PackedUpdates
import Mettapedia.Machines.TIsa.StoreInstructions.PackedIndex
import Mettapedia.Machines.TIsa.X86PlacedQwordStore

/-!
# Publish a store and its index together

The ordinary array operations construct a private successor. Its
index must be built from those same occurrences: a take may move
the position of a survivor. Once both are ready, a single native
word update selects the new snapshot. The theorem concerns native
instruction endpoints; it is not a concurrent memory-ordering law.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.StorePublication

open Derivation (Store)
open PackedOccurrences (Codes pack unpack packRow take make? pack_take pack_make)
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (CodeApart Cell Reads footprint)
open X86BoundedStore (Instruction Fits layout bytes count physical displacement)
local instance : MemoryPrimitives := X86Memory.ordinary

universe u

structure Snapshot where
  data : PackedOccurrences.Layout
  index : PackedIndex.Layout

variable {V : Type u} {keys : ℕ}

def encode (codes : Codes V) (classify : V → Fin keys) (before : Store V) : Option Snapshot := do
  let data ← pack codes before
  let index ← PackedIndex.pack (PackedIndex.fromKeys classify before)
  pure ⟨data, index⟩

theorem encode_views (codes : Codes V) (classify : V → Fin keys)
    {before : Store V} {snapshot : Snapshot} (formed : encode codes classify before = some snapshot) :
    pack codes before = some snapshot.data ∧ PackedIndex.pack (PackedIndex.fromKeys classify before) = some snapshot.index := by
  obtain ⟨data, packed, following⟩ := Option.bind_eq_some_iff.mp formed
  obtain ⟨index, indexed, found⟩ := Option.bind_eq_some_iff.mp following
  cases found
  exact ⟨packed, indexed⟩

theorem reads_published (codes : Codes V) (classify : V → Fin keys)
    {source : Store V} {snapshot : Snapshot} (formed : encode codes classify source = some snapshot) (key : Fin keys) :
    PackedIndex.candidates codes snapshot.data snapshot.index key.val =
      some (source.occurrences.filter (fun occurrence => classify occurrence.2 == key)) := by
  obtain ⟨data, index⟩ := encode_views codes classify formed
  exact PackedIndex.candidates_fromKeys codes classify data index key

def removeAll : PackedOccurrences.Layout → List ℕ → PackedOccurrences.Layout
  | data, [] => data
  | data, identity :: rest => removeAll (take data identity) rest

def appendAll (codes : Codes V) : PackedOccurrences.Layout → List V → Option PackedOccurrences.Layout
  | data, [] => some data
  | data, value :: rest => (make? codes data value).bind (fun next => appendAll codes next rest)

theorem removeAll_exact (codes : Codes V) (taken : List ℕ) :
    ∀ {source : Store V} {memory : PackedOccurrences.Layout}, pack codes source = some memory →
      pack codes (source.takeAll taken) = some (removeAll memory taken) := by
  induction taken with
  | nil => exact fun formed => formed
  | cons identity rest ih =>
    intro source memory formed
    exact ih (pack_take codes formed identity)

private theorem append_preserves_failure (codes : Codes V) (source : Store V) (value : V)
    (refused : pack codes source = none) : pack codes (source.add value) = none := by
  cases formed : pack codes (source.add value) with
  | none => rfl
  | some whole =>
    unfold pack at formed
    split at formed
    next room =>
      obtain ⟨rows, mapped, _⟩ := Option.map_eq_some_iff.mp formed
      change (source.occurrences ++ [(source.fresh, value)]).mapM (packRow codes) = some rows at mapped
      rw [List.mapM_append] at mapped
      obtain ⟨earlier, cameFrom, _⟩ := Option.bind_eq_some_iff.mp mapped
      have prefixRoom : source.occurrences.length < 2 ^ 64 ∧ source.fresh < 2 ^ 64 := by
        have length : (source.add value).occurrences.length = source.occurrences.length + 1 := by simp [Store.add]
        rw [length] at room
        exact ⟨Nat.lt_of_succ_lt room.1, Nat.lt_of_succ_lt room.2⟩
      rw [pack, if_pos prefixRoom, cameFrom] at refused
      cases refused
    next => cases formed

theorem appendAll_exact (codes : Codes V) (made : List V) (source : Store V) :
    (pack codes source).bind (fun memory => appendAll codes memory made) = pack codes (source.makeAll made) := by
  induction made generalizing source with
  | nil => cases initial : pack codes source <;> simp [initial, appendAll, Store.makeAll]
  | cons value rest ih =>
    rw [Store.makeAll, ← ih]
    cases original : pack codes source with
    | none => rw [append_preserves_failure _ _ _ original]; rfl
    | some data =>
      rw [pack_make codes original]
      rfl

def indexPrepared (codes : Codes V) (classify : V → Fin keys) (data : PackedOccurrences.Layout) : Option Snapshot :=
  match unpack codes data with
  | none => none
  | some source => (PackedIndex.pack (PackedIndex.fromKeys classify source)).map (Snapshot.mk data)

def prepare (codes : Codes V) (classify : V → Fin keys) (before : Snapshot) (taken : List ℕ) (made : List V) :
    Option Snapshot :=
  (appendAll codes (removeAll before.data taken) made).bind (indexPrepared codes classify)

theorem prepare_exact (codes : Codes V) (classify : V → Fin keys) {source : Store V} {before : Snapshot}
    (formed : encode codes classify source = some before) (taken : List ℕ) (made : List V) :
    prepare codes classify before taken made = encode codes classify ((source.takeAll taken).makeAll made) := by
  have preserved := (encode_views codes classify formed).1
  have takenPack := removeAll_exact codes taken preserved
  have madePack := appendAll_exact codes made (source.takeAll taken)
  rw [takenPack] at madePack
  change (appendAll codes (removeAll before.data taken) made).bind (indexPrepared codes classify) = _
  change appendAll codes (removeAll before.data taken) made = _ at madePack
  rw [madePack]
  unfold encode
  cases update : pack codes ((source.takeAll taken).makeAll made) with
  | none => rfl
  | some data =>
    have unpacked := (PackedOccurrences.pack_roundtrip codes update).1
    simp only [indexPrepared, bind, Option.bind_some, unpacked]
    cases PackedIndex.pack (PackedIndex.fromKeys classify ((source.takeAll taken).makeAll made)) <;> rfl

def stage (catalog : Array Snapshot) (value : Snapshot) : Option (Array Snapshot × Word) :=
  if catalog.size < 2 ^ 64 then some (catalog.push value, BitVec.ofNat 64 catalog.size) else none

theorem staged_exact {catalog now : Array Snapshot} {snapshot : Snapshot} {handle : Word}
    (staged : stage catalog snapshot = some (now, handle)) :
    now[handle.toNat]? = some snapshot ∧ ∀ older < catalog.size, now[older]? = catalog[older]? := by
  unfold stage at staged
  split at staged
  next within =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj staged)
    refine ⟨?_, ?_⟩
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt within, Array.getElem?_push_size]
    · intro older smaller
      rw [Array.getElem?_push, if_neg (Nat.ne_of_lt smaller)]
  next => cases staged

def ReadsSnapshot (catalog : Array Snapshot) (native : X86RegisterRefinement.State)
    (root : BitVec 48) (snapshot : Snapshot) : Prop :=
  ∃ code, Reads native root code ∧ catalog[code.toNat]? = some snapshot

theorem old_snapshot_after_staging {catalog now : Array Snapshot} {snapshot old : Snapshot} {handle older : Word}
    (staged : stage catalog snapshot = some (now, handle))
    {native : X86RegisterRefinement.State} {root : BitVec 48}
    (pointer : Reads native root older) (previous : catalog[older.toNat]? = some old) :
    ReadsSnapshot now native root old := by
  have within := (Array.getElem?_eq_some_iff.mp previous).choose
  exact ⟨older, pointer, ((staged_exact staged).2 _ within).trans previous⟩

/-- This is the native publication of an already prepared batch. The
caller's store and all the words of its index change view at the same
instruction endpoint. Compiling the preparation itself is separate. -/
theorem lower_publish_x86 (codes : Codes V) (classify : V → Fin keys)
    {source : Store V} {before target : Snapshot} {catalog nextCatalog : Array Snapshot} {handle : Word}
    (packed : encode codes classify source = some before) (taken : List ℕ) (made : List V)
    (prepared : prepare codes classify before taken made = some target)
    (staged : stage catalog target = some (nextCatalog, handle))
    (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {native : X86RegisterRefinement.State} {base root : BitVec 48} {offset : ℕ}
    {code : Instruction} (point : At image native base offset)
    (checked : X86PlacedQwordStore.Checked image offset code)
    (facts : X86Bounds.Facts (layout code) native) (wide : code.wide = true)
    (inside : Fits (X86PlacedQwordStore.input point checked facts))
    (cell : Cell facts.pointer (displacement code)) (located : cell.address = root)
    (ready : lookup native (physical code.source) = some handle)
    (outsideCode : CodeApart image base (footprint cell.address)) :
    letI : OtherOpcodeHandlers := X86PlacedQwordStore.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ next,
      (X86FuelPrefix.fetches (count code)).run native = .ok () next ∧
      ReadsSnapshot nextCatalog next root target ∧
      encode codes classify ((source.takeAll taken).makeAll made) = some target ∧
      X86StateFrame.Frame X86Bounds.writes (footprint cell.address) native next ∧
      Nonempty (At image next base (offset + (bytes code).length)) := by
  obtain ⟨next, ran, frame, readyWord, continuation⟩ :=
    X86PlacedQwordStore.writes other extra vector point checked facts wide inside handle cell ready outsideCode
  exact ⟨next, ran, ⟨handle, located ▸ readyWord, (staged_exact staged).1⟩,
    (prepare_exact codes classify packed taken made).symm.trans prepared, frame, continuation⟩

section SelectedUpdate

open Derivation (Matcher)

variable {T B : Type*}

/-- A TAKE or MAKE whose source slot was successfully read. -/
inductive Update (before : StoreInstructions.State V B) where
  | take (level slot identity : ℕ) (present : (before.levels level).taken[slot]? = some identity)
  | make (level slot : ℕ) (value : V) (present : (before.levels level).made[slot]? = some value)

variable {st : StoreInstructions.State V B}

def Update.taken : Update st → List ℕ
  | .take _ _ identity _ => [identity]
  | .make .. => []

def Update.made : Update st → List V
  | .take .. => []
  | .make _ _ value _ => [value]

def Update.operation : Update st → P1Source.Instruction (TransformOp T) true
  | .take level slot _ _ => .transform (.take level slot)
  | .make level slot _ _ => .transform (.make level slot)

def Update.result (pending : Update st) : StoreInstructions.State V B :=
  {st with store := (st.store.takeAll pending.taken).makeAll pending.made}

theorem Update.executed [DecidableEq V] (matcher : Matcher T V B) (pending : Update st) :
    executeInstruction matcher st pending.operation = .ok pending.result := by
  cases pending <;> simp [Update.operation, Update.result, Update.taken, Update.made, executeInstructionWith, P1Source.Instruction.view, StoreProfile.step,
    Store.takeAll, Store.makeAll, *]

/-- TAKE and MAKE can publish their prepared array changes using the
same native instruction. The native store selects the snapshot that
represents the actual source update, not one provided by a second
matcher. The private preparation is still an explicit prerequisite. -/
theorem lower_update_publication_x86 [DecidableEq V] (matcher : Matcher T V B) (pending : Update st)
    (codes : Codes V) (classify : V → Fin keys)
    {before target : Snapshot} {catalog nextCatalog : Array Snapshot} {handle : Word}
    (packed : encode codes classify st.store = some before)
    (prepared : prepare codes classify before pending.taken pending.made = some target)
    (staged : stage catalog target = some (nextCatalog, handle))
    (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {native : X86RegisterRefinement.State} {base root : BitVec 48} {offset : ℕ}
    {code : Instruction} (point : At image native base offset)
    (checked : X86PlacedQwordStore.Checked image offset code)
    (facts : X86Bounds.Facts (layout code) native) (wide : code.wide = true)
    (inside : Fits (X86PlacedQwordStore.input point checked facts))
    (cell : Cell facts.pointer (displacement code)) (located : cell.address = root)
    (ready : lookup native (physical code.source) = some handle)
    (outsideCode : CodeApart image base (footprint cell.address)) :
    letI : OtherOpcodeHandlers := X86PlacedQwordStore.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ next abstract,
      (X86FuelPrefix.fetches (count code)).run native = .ok () next ∧
      executeInstruction matcher st pending.operation = .ok abstract ∧
      ReadsSnapshot nextCatalog next root target ∧ encode codes classify abstract.store = some target ∧
      X86StateFrame.Frame X86Bounds.writes (footprint cell.address) native next ∧
      Nonempty (At image next base (offset + (bytes code).length)) := by
  obtain ⟨next, fetched, visible, encoded, frame, following⟩ :=
    lower_publish_x86 codes classify packed pending.taken pending.made prepared staged
      other extra vector point checked facts wide inside cell located ready outsideCode
  exact ⟨next, pending.result, fetched, pending.executed matcher, visible, encoded, frame, following⟩

end SelectedUpdate

namespace Examples

private def wordCodes : Codes Word := ⟨some, some, fun encoded => by cases encoded; rfl⟩
private def baseStore : Store Word := ⟨[(7, 42), (9, 42), (12, 13)], 13⟩
private def category (value : Word) : Fin 2 := if value = 42 then 1 else 0

theorem prepared_index_follows_the_survivor {old next : Snapshot}
    (packed : encode wordCodes category baseStore = some old)
    (ready : prepare wordCodes category old [7] [] = some next) :
    PackedIndex.candidates wordCodes next.data next.index 1 = some [(9, 42)] := by
  have snapshot := (prepare_exact wordCodes category packed [7] []).symm.trans ready
  refine (reads_published wordCodes category snapshot (1 : Fin 2)).trans ?_
  decide +kernel

theorem stale_positions_select_the_wrong_value :
    ((pack wordCodes (baseStore.remove 7)).bind (fun data =>
      (PackedIndex.pack [[2], [0, 1]]).bind (fun oldIndex =>
        PackedIndex.candidates wordCodes data oldIndex 1))) =
      some [(9, 42), (12, 13)] := by
  decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.StorePublication
