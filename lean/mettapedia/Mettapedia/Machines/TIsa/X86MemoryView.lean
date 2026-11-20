import Mettapedia.Machines.TIsa.X86CanonicalSpan
import Mettapedia.Machines.TIsa.Memory
import Mettapedia.Machines.TIsa.Layout
import Mettapedia.Machines.TIsa.X86StateFrame

/-!
# Register, byte and capability readbacks from the original x86 state

The source carrier is the established memory-cell vocabulary. Register cells
use the canonical register placement; byte cells use the proved canonical
physical-key projection. Descriptor words are assembled from eight actual
backing bytes, with missing, wrapping and noncanonical spans refused.

Region bases and lengths occupy the runtime frame's existing sixteen-byte
slots. Modes come from immutable declarations, not an extra runtime field.
Region 255 is the existing read-only frame view. The representation records
these observations; it introduces no machine execution or additional runtime.

Finite register and physical-byte read footprints support framed observations
through writes. Descriptor footprints include the actual RDI-based backing
bytes, so their preservation requires physical exclusions from the write set.

A reader is an observation, not a proof that a CPU load is admitted. Alignment,
entry validation, native load/store execution, descriptor-write exclusions
and whole-program admission/hosting retain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86MemoryView

open _root_.X86Registers X86RegisterRefinement X86Execution

abbrev Key := Memory.Key (Fin 12)
abbrev World := Multiset (Cells.Cell Key)

def memory (native : State) : Nat → Option (BitVec 8) := fun address => native.mem.get? address

theorem lookup_memory_update (native : State) (bytes : Std.ExtHashMap Nat (BitVec 8)) (index : Fin 16) :
    lookup { native with mem := bytes } index = lookup native index := rfl

theorem memory_update (native : State) (bytes : Std.ExtHashMap Nat (BitVec 8)) (address : Nat) :
    memory { native with mem := bytes } address = bytes.get? address := rfl

theorem memory_insert (native : State) (written address : Nat) (value : BitVec 8) :
    memory { native with mem := native.mem.insert written value } address =
      if written == address then some value else memory native address :=
  Std.ExtHashMap.getElem?_insert

def span (pointer : Word) : Prop :=
  pointer.toNat + 8 ≤ 2 ^ 64 ∧
    ∀ offset : Fin 8, X86CanonicalSpan.Canonical (pointer + BitVec.ofNat 64 offset.val)

theorem span_iff_area (pointer : Word) : span pointer ↔ X86CanonicalSpan.Area pointer 8 := by
  constructor
  · rintro ⟨bounded,canonical⟩
    exact ⟨bounded,fun offset within => canonical ⟨offset,within⟩⟩
  · rintro ⟨bounded,canonical⟩
    exact ⟨bounded,fun offset => canonical offset.val offset.isLt⟩

instance (pointer : Word) : Decidable (span pointer) :=
  inferInstanceAs (Decidable (pointer.toNat + 8 ≤ 2 ^ 64 ∧
    ∀ offset : Fin 8, X86CanonicalSpan.Canonical (pointer + BitVec.ofNat 64 offset.val)))

def wordAt? (bytes : Nat → Option (BitVec 8)) (pointer : Word) : Option Word :=
  if span pointer then
    ((List.range 8).mapM fun offset => bytes (X86CanonicalSpan.physicalKey
      (pointer + BitVec.ofNat 64 offset))).map packBytes
  else none

theorem sequence_congr {α β : Type} (items : List α) (left right : α → Option β)
    (same : ∀ item ∈ items, left item = right item) : items.mapM left = items.mapM right := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    rw [List.mapM_cons,List.mapM_cons,same head (by simp),ih (by intro item member; exact same item (by simp [member]))]

theorem sequence_missing {α β : Type} (items : List α) (read : α → Option β)
    (item : α) (member : item ∈ items) (missing : read item = none) : items.mapM read = none := by
  induction items with
  | nil => simp at member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | later
    · simp [List.mapM_cons,missing]
    · rw [List.mapM_cons,ih later]
      cases read head <;> rfl

theorem wordAt?_known (bytes : Nat → Option (BitVec 8)) (pointer value : Word) (admitted : span pointer)
    (known : ∀ offset < 8, bytes (X86CanonicalSpan.physicalKey (pointer + BitVec.ofNat 64 offset)) =
      some (value.extractLsb' (8 * offset) 8)) : wordAt? bytes pointer = some value := by
  rw [wordAt?,if_pos admitted]
  have reads := sequence_congr (List.range 8)
    (fun offset => bytes (X86CanonicalSpan.physicalKey (pointer + BitVec.ofNat 64 offset)))
    (fun offset => some (value.extractLsb' (8 * offset) 8))
    (by intro offset member; exact known offset (List.mem_range.mp member))
  rw [reads]
  have collected : (List.range 8).mapM (fun offset => some (value.extractLsb' (8 * offset) 8)) =
      some ((List.range 8).map (fun offset => value.extractLsb' (8 * offset) 8)) := List.mapM_pure
  rw [collected,Option.map_some]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro bit within
  interval_cases bit <;> simp [List.range_succ,packBytes]

theorem wordAt?_missing (bytes : Nat → Option (BitVec 8)) (pointer : Word) (offset : Fin 8)
    (missing : bytes (X86CanonicalSpan.physicalKey (pointer + BitVec.ofNat 64 offset.val)) = none) :
    wordAt? bytes pointer = none := by
  unfold wordAt?
  split
  · rw [sequence_missing (List.range 8) _ offset.val (List.mem_range.mpr offset.isLt) missing]
    rfl
  · rfl

def field? (native : State) (offset : Nat) : Option Word := do
  let pointer ← lookup native 7
  wordAt? (memory native) (pointer + BitVec.ofNat 64 offset)

def readback (modes : Fin 9 → Word) (native : State) : Key → Option Word
  | .register register => lookup native (placed (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64) (Registers.logicalSlot register))
  | .byte address =>
      if address < 2 ^ 64 ∧ X86CanonicalSpan.Canonical (BitVec.ofNat 64 address) then
        (memory native (X86CanonicalSpan.physicalKey (BitVec.ofNat 64 address))).map (BitVec.zeroExtend 64)
      else none
  | .capabilityBase region =>
      if region = 255 then lookup native 7
      else if region < 9 then field? native (16 * region) else none
  | .capabilityLength region =>
      if region = 255 then some (BitVec.ofNat 64 frameLayout.size)
      else if region < 9 then field? native (16 * region + 8) else none
  | .capabilityMode region =>
      if region = 255 then some 1
      else if inside : region < 9 then some (modes ⟨region, inside⟩) else none

theorem readback_byte_known (modes : Fin 9 → Word) (native : State) (address : Nat) (value : BitVec 8)
    (bounded : address < 2 ^ 64) (canonical : X86CanonicalSpan.Canonical (BitVec.ofNat 64 address))
    (present : memory native (X86CanonicalSpan.physicalKey (BitVec.ofNat 64 address)) = some value) :
    readback modes native (.byte address) = some (value.zeroExtend 64) := by
  rw [readback,if_pos ⟨bounded,canonical⟩,present]
  rfl

theorem readback_nonregister (modes : Fin 9 → Word) (before after : State)
    (sameMemory : memory after = memory before) (sameFrame : lookup after 7 = lookup before 7)
    (key : Key) (readonly : ∀ register, key ≠ Memory.Key.register register) :
    readback modes after key = readback modes before key := by
  cases key with
  | register register => exact False.elim (readonly register rfl)
  | byte address => simp only [readback, sameMemory]
  | capabilityBase region => simp only [readback, field?, sameFrame, sameMemory]
  | capabilityLength region => simp only [readback, field?, sameFrame, sameMemory]
  | capabilityMode region => rfl

def wordReads (pointer : Word) : Finset Nat :=
  (Finset.range 8).image fun offset => X86CanonicalSpan.physicalKey (pointer + BitVec.ofNat 64 offset)

theorem wordAt?_congr (before after : Nat → Option (BitVec 8)) (pointer : Word)
    (same : ∀ address ∈ wordReads pointer, after address = before address) :
    wordAt? after pointer = wordAt? before pointer := by
  unfold wordAt?
  split
  · rw [sequence_congr (List.range 8) _ _ (by
      intro offset member
      apply same
      exact Finset.mem_image.mpr ⟨offset, Finset.mem_range.mpr (List.mem_range.mp member), rfl⟩)]
  · rfl

def fieldReads (native : State) (offset : Nat) : Finset Nat :=
  match lookup native 7 with
  | none => ∅
  | some pointer => wordReads (pointer + BitVec.ofNat 64 offset)

theorem field?_congr (before after : State) (offset : Nat)
    (samePointer : lookup after 7 = lookup before 7)
    (same : ∀ address ∈ fieldReads before offset, memory after address = memory before address) :
    field? after offset = field? before offset := by
  unfold field?
  rw [samePointer]
  cases known : lookup before 7 with
  | none => rfl
  | some pointer =>
      apply wordAt?_congr
      simpa only [fieldReads, known] using same

def registerReads : Key → Finset Register
  | .register register =>
      {key (placed (Registers.canonical .x86_64) (Registers.canonical_admitted .x86_64) (Registers.logicalSlot register))}
  | .capabilityBase region => if region = 255 ∨ region < 9 then {.rdi} else ∅
  | .capabilityLength region => if region ≠ 255 ∧ region < 9 then {.rdi} else ∅
  | _ => ∅

def memoryReads (native : State) : Key → Finset Nat
  | .byte address => {X86CanonicalSpan.physicalKey (BitVec.ofNat 64 address)}
  | .capabilityBase region =>
      if region = 255 then ∅ else if region < 9 then fieldReads native (16 * region) else ∅
  | .capabilityLength region =>
      if region = 255 then ∅ else if region < 9 then fieldReads native (16 * region + 8) else ∅
  | _ => ∅

theorem readback_framed (modes : Fin 9 → Word) (before after : State)
    (registerWrites : Finset Register) (byteWrites : Finset Nat)
    (frame : X86StateFrame.Frame registerWrites byteWrites before after) (observed : Key)
    (registers : ∀ register ∈ registerReads observed, register ∉ registerWrites)
    (bytes : ∀ address ∈ memoryReads before observed, address ∉ byteWrites) :
    readback modes after observed = readback modes before observed := by
  cases observed with
  | register register =>
      apply frame.lookup
      exact registers _ (by simp [registerReads])
  | byte address =>
      simp only [readback]
      rw [show memory after (X86CanonicalSpan.physicalKey (BitVec.ofNat 64 address)) =
        memory before (X86CanonicalSpan.physicalKey (BitVec.ofNat 64 address)) from
          frame.memory _ (bytes _ (by simp [memoryReads]))]
  | capabilityBase region =>
      by_cases frameRegion : region = 255
      · subst region
        change lookup after 7 = lookup before 7
        exact frame.lookup 7 (registers .rdi (by simp [registerReads]))
      · by_cases valid : region < 9
        · simp only [readback, frameRegion, valid, if_false, if_true]
          apply field?_congr
          · exact frame.lookup 7 (registers .rdi (by simp [registerReads, valid]))
          · intro address member
            exact frame.memory address (bytes address (by simpa only [memoryReads, frameRegion, valid, if_false, if_true] using member))
        · simp only [readback, frameRegion, valid, if_false]
  | capabilityLength region =>
      by_cases frameRegion : region = 255
      · simp only [readback, frameRegion, if_true]
      · by_cases valid : region < 9
        · simp only [readback, frameRegion, valid, if_false, if_true]
          apply field?_congr
          · exact frame.lookup 7 (registers .rdi (by simp [registerReads, frameRegion, valid]))
          · intro address member
            exact frame.memory address (bytes address (by simpa only [memoryReads, frameRegion, valid, if_false, if_true] using member))
        · simp only [readback, frameRegion, valid, if_false]
  | capabilityMode _ => rfl

theorem registerReads_no_rip (observed : Key) : .rip ∉ registerReads observed := by
  cases observed with
  | register register => fin_cases register <;> decide
  | byte _ => simp [registerReads]
  | capabilityBase region => simp only [registerReads]; split <;> simp
  | capabilityLength region => simp only [registerReads]; split <;> simp
  | capabilityMode _ => simp [registerReads]

theorem readback_store_frame (modes : Fin 9 → Word) (before after : State) (byteWrites : Finset Nat)
    (frame : X86StateFrame.Frame {.rip} byteWrites before after) (observed : Key)
    (separate : ∀ address ∈ memoryReads before observed, address ∉ byteWrites) :
    readback modes after observed = readback modes before observed := by
  apply readback_framed modes before after {.rip} byteWrites frame observed
  · intro register member forbidden
    have same : register = .rip := Finset.mem_singleton.mp forbidden
    exact registerReads_no_rip observed (same ▸ member)
  · exact separate

structure View where
  keys : Finset Key
  registers : ∀ register, Memory.Key.register register ∈ keys
  modes : Fin 9 → Word

def represents (view : View) (world : World) (native : State) : Prop :=
  ∃ values : Key → Word, world = Cells.encode view.keys values ∧
    ∀ key ∈ view.keys, readback view.modes native key = some (values key)

namespace Controls

private def highWord : Word := 0x8000000000000001#64
private def highBytes (address : Nat) : Option (BitVec 8) :=
  if 2 ^ 52 - 8 ≤ address ∧ address < 2 ^ 52 then
    some (highWord.extractLsb' (8 * (address - (2 ^ 52 - 8))) 8)
  else none

theorem high_word_read : wordAt? highBytes (-8#64) = some highWord := by
  apply wordAt?_known _ _ _ (by decide)
  intro offset within
  interval_cases offset <;> decide

theorem wrapping_word_refused : wordAt? highBytes (-7#64) = none := by
  rw [wordAt?,if_neg (by decide)]

end Controls

#print axioms span_iff_area
#print axioms wordAt?_known
#print axioms wordAt?_missing
#print axioms readback_nonregister
#print axioms Controls.high_word_read
#print axioms Controls.wrapping_word_refused

end Mettapedia.Machines.TIsa.X86MemoryView
