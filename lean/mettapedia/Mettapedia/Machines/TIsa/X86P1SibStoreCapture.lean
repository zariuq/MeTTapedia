import Mettapedia.Machines.TIsa.X86SibStore
import Mettapedia.Machines.TIsa.X86P1LoadCapture
import Mettapedia.Machines.TIsa.X86Bounds
import Mettapedia.Machines.TIsa.X86IndexedAddress

/-!
# The adapter's four R12-based output stores

The current p1 bundle emits the adapter's copy loop twice: a fast path, entered
when the loop-entry test decides its hoisted checks, and a checked slow path.
Each copy contains the four output stores of the loop body.

The zero-offset store is a STORE-DIRECT: only the eight-byte SIB MOV. Its R12
address comes from the preceding ADDR-INDEX of the same copy, which compares
the scaled index plus four with region five's length and rejects to the shared
invalid-input entry. A seven-byte LOAD-DIRECT lies between that guard and the
store. The three positive-offset stores are STORE spans: the parameterized
bounds prefix, rejecting to the same entry, followed by the same MOV form.

Loaded full-image bytes derive the byte premises of every MOV and bounds
prefix, and code/write separation retains the whole image after the MOV. The
guard is an instance of the generic indexed-address check: four fetches form
R12 from RCX and the scaled RAX in range, three reach the invalid-input entry
otherwise. That the guard covers the store needs RCX to hold region five's
base, a loop invariant of the surrounding adapter; it, the intervening load
and the surrounding adapter execution remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86P1SibStoreCapture
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable def image : P1Capture.Program :=
  ImportedP1.programs[14]'(by rw [ImportedP1.exact_count.2]; decide)

theorem selected_by_name :
    ImportedP1.programs.find? (fun program => program.name == "ordinary_flat_adapter") = some image := by
  kernel_reflexivity

theorem byte_extent : image.size = 3778 := by kernel_reflexivity

/-- The two emitted copies of the copy loop's body. -/
inductive Copy where
  | fast
  | slow
  deriving DecidableEq, Repr

/-- The shared invalid-input entry, `mov eax, 3`, 57 bytes before the end of the image. -/
def invalidEntry : Nat := 3721

theorem invalid_entry_from_end : invalidEntry + 57 = image.size := by rw [byte_extent]; rfl

theorem invalid_entry_bytes (byte : Fin 5) :
    image.view.read (invalidEntry + byte.val) = ([0xb8, 3, 0, 0, 0][byte.val]?).map (BitVec.ofNat 8) := by
  fin_cases byte <;> kernel_reflexivity

def sourcePath (slot : Fin 4) : List Nat :=
  [1, 1, 1, 1] ++ List.replicate 8 0 ++ [1] ++ List.replicate (7 - 2 * slot.val) 0 ++ [1]

def displacement (slot : Fin 4) : BitVec 32 := BitVec.ofNat 32 (4 * slot.val)

theorem source_instruction (slot : Fin 4) :
    image.source.body.atPath (sourcePath slot) =
      some (.instruction (.store .word32 5 10 (displacement slot) 11)) := by
  fin_cases slot <;> kernel_reflexivity

/-- The MOV of each store, in each copy. -/
def tailAt : Copy → Fin 4 → Nat
  | .fast, slot => match slot.val with
    | 0 => 887
    | 1 => 1000
    | 2 => 1113
    | _ => 1226
  | .slow, slot => match slot.val with
    | 0 => 1431
    | 1 => 1544
    | 2 => 1657
    | _ => 1770

/-- The STORE spans of the positive-offset stores; `slot` indexes source slot `slot.succ`. -/
def spanStart : Copy → Fin 3 → Nat
  | .fast, slot => match slot.val with
    | 0 => 951
    | 1 => 1064
    | _ => 1177
  | .slow, slot => match slot.val with
    | 0 => 1495
    | 1 => 1608
    | _ => 1721

def spanLength : Nat := 57

/-- Where the native code of a store starts: the zero-offset STORE-DIRECT, or a STORE span. -/
def entryAt (copy : Copy) (slot : Fin 4) : Nat :=
  if within : slot.val = 0 then tailAt copy 0 else spanStart copy ⟨slot.val - 1, by omega⟩

/-- Fetched instructions of a store's native code: one MOV, or nine bounds instructions and the MOV. -/
def storeSteps (slot : Fin 4) : Nat := if slot.val = 0 then 1 else 10

theorem entryAt_zero (copy : Copy) : entryAt copy 0 = tailAt copy 0 := rfl

theorem entryAt_succ (copy : Copy) (slot : Fin 3) : entryAt copy slot.succ = spanStart copy slot := by
  cases copy <;> fin_cases slot <;> rfl

theorem storeSteps_zero : storeSteps 0 = 1 := rfl

theorem storeSteps_succ (slot : Fin 3) : storeSteps slot.succ = 10 := by fin_cases slot <;> rfl

def boundsLayout (copy : Copy) (slot : Fin 3) : X86Bounds.Layout where
  pointer := 12
  region := 5
  offset := ⟨4 * (slot.val + 1), by have := slot.isLt; omega⟩
  count := 4
  reject := invalidEntry - spanStart copy slot

theorem offset_steps (copy : Copy) (slot : Fin 3) :
    X86Bounds.offsetSteps (boundsLayout copy slot) + 6 = storeSteps slot.succ := by
  cases copy <;> fin_cases slot <;> rfl

theorem prefix_end (copy : Copy) (slot : Fin 3) :
    spanStart copy slot + X86Bounds.exitAt (boundsLayout copy slot) = tailAt copy slot.succ := by
  cases copy <;> fin_cases slot <;> decide

theorem span_end (copy : Copy) (slot : Fin 3) : spanStart copy slot + spanLength = tailAt copy slot.succ + 8 := by
  cases copy <;> fin_cases slot <;> decide

theorem prefix_bytes (copy : Copy) (slot : Fin 3) (byte : Fin (X86Bounds.exitAt (boundsLayout copy slot))) :
    image.view.read (spanStart copy slot + byte.val) =
      ((X86Bounds.code (boundsLayout copy slot))[byte.val]?).map (BitVec.ofNat 8) := by
  cases copy <;> fin_cases slot <;> fin_cases byte <;> kernel_reflexivity

def boundsContext (copy : Copy) (slot : Fin 3) (base : Int) (start : BitVec 48)
    (placed : start.toInt = base + spanStart copy slot) (upper : base + 3778 < (2 ^ 47 : Int)) :
    X86Bounds.Context (boundsLayout copy slot) start where
  extent := 3778 - spanStart copy slot
  upper := by rw [placed]; cases copy <;> fin_cases slot <;> simp only [spanStart] <;> omega
  codeWithin := by cases copy <;> fin_cases slot <;> decide
  rejectWithin := by cases copy <;> fin_cases slot <;> decide
  overflowDelta := by cases copy <;> fin_cases slot <;> decide
  shortDelta := by cases copy <;> fin_cases slot <;> decide
  rangeDelta := by cases copy <;> fin_cases slot <;> decide

theorem prefix_loaded (copy : Copy) (slot : Fin 3) (state : State) (base : Int) (start : BitVec 48)
    (placed : start.toInt = base + spanStart copy slot) (loaded : X86P1LoadCapture.Loaded image state base) :
    codeLoaded state start.toInt (X86Bounds.code (boundsLayout copy slot)) := by
  intro byte value present
  have within : byte < X86Bounds.exitAt (boundsLayout copy slot) := by
    simpa only [X86Bounds.code_length] using (List.getElem?_eq_some_iff.mp present).1
  have captured := prefix_bytes copy slot ⟨byte, within⟩
  rw [present, Option.map_some] at captured
  have shifted : address base (spanStart copy slot + byte) = address start.toInt byte := by
    unfold address
    rw [placed]
    congr 1
    omega
  have extent : spanStart copy slot + byte < image.size := by
    rw [byte_extent]
    have prefixSmall : X86Bounds.exitAt (boundsLayout copy slot) = 49 := by cases copy <;> fin_cases slot <;> rfl
    have startSmall : spanStart copy slot ≤ 1721 := by cases copy <;> fin_cases slot <;> decide
    omega
  simpa only [shifted] using (loaded _ extent).trans captured

theorem containing_span (copy : Copy) (slot : Fin 3) :
    image.spans.any (fun span => span.offset == spanStart copy slot && span.length == spanLength &&
      span.kind == "STORE" && span.path == some (sourcePath slot.succ)) = true := by
  cases copy <;> fin_cases slot <;> kernel_reflexivity

theorem direct_span (copy : Copy) :
    image.spans.any (fun span => span.offset == tailAt copy 0 && span.length == 8 &&
      span.kind == "STORE-DIRECT" && span.path == some (sourcePath 0)) = true := by
  cases copy <;> kernel_reflexivity

theorem tail_bytes (copy : Copy) (slot : Fin 4) (byte : Fin 8) :
    image.view.read (tailAt copy slot + byte.val) =
      ((X86SibStore.code 13 (displacement slot))[byte.val]?).map (BitVec.ofNat 8) := by
  cases copy <;> fin_cases slot <;> fin_cases byte <;> kernel_reflexivity

theorem captured_loaded (copy : Copy) (slot : Fin 4) (state : State) (base : Int) (start : BitVec 48)
    (placed : start.toInt = base + tailAt copy slot) (loaded : X86P1LoadCapture.Loaded image state base) :
    codeLoaded state start.toInt (X86SibStore.code 13 (displacement slot)) := by
  intro byte value present
  have within : byte < 8 := by simpa only [X86SibStore.code_length] using (List.getElem?_eq_some_iff.mp present).1
  have captured := tail_bytes copy slot ⟨byte, within⟩
  rw [present, Option.map_some] at captured
  have shifted : address base (tailAt copy slot + byte) = address start.toInt byte := by
    unfold address
    rw [placed]
    congr 1
    omega
  have extent : tailAt copy slot + byte < image.size := by
    rw [byte_extent]
    cases copy <;> fin_cases slot <;> simp only [tailAt] <;> omega
  simpa only [shifted] using (loaded _ extent).trans captured

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (copy : Copy) (slot : Fin 4) (state : State) (base : Int) (origin : X86LegacyFetch.Basis state)
    (placed : origin.address.toInt = base + tailAt copy slot)
    (loaded : X86P1LoadCapture.Loaded image state base)
    (visible : Vector (BitVec 16) 6) (controls : Vector (BitVec 64) 17)
    (baseValue value : Word) (flags : BitVec 32) (dataAddress : BitVec 48)
    (baseKnown : lookup state 12 = some baseValue) (sourceKnown : lookup state 13 = some value)
    (controlKnown : state.regs.get? .ctrs = some controls) (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (quiet : state.regs.get? .log_register_writes = some false)
    (upper : origin.address.toInt + 8 < (2 ^ 47 : Int))
    (dataUpper : dataAddress.toInt + 4 ≤ (2 ^ 47 : Int))
    (effective : baseValue + (displacement slot).signExtend 64 = dataAddress.signExtend 64)
    (safe : X86FrameLoad.alignmentEnabled controls flags visible = false ∨ dataAddress &&& (3#48) = (0#48))
    (separate : ∀ index < image.size,
      ((address base index).signExtend 52).toNat ∉ X86SibStore.writes dataAddress) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run state = .ok () after ∧
      X86StateFrame.Frame {.rip} (X86SibStore.writes dataAddress) state after ∧
      after = X86SibStore.result state dataAddress (address origin.address.toInt 8) value ∧
      X86P1LoadCapture.Loaded image after base := by
  let input : X86SibStore.Inputs state 13 (displacement slot) :=
    { toBasis := origin
      visible := visible
      controls := controls
      baseValue := baseValue
      value := value
      flags := flags
      dataAddress := dataAddress
      baseKnown := baseKnown
      sourceKnown := sourceKnown
      controlKnown := controlKnown
      flagsKnown := flagsKnown
      visibleKnown := visibleKnown
      quiet := quiet
      upper := upper
      dataUpper := dataUpper
      effective := effective
      safe := safe
      loaded := captured_loaded copy slot state base origin.address placed loaded }
  obtain ⟨run, frame⟩ := X86SibStore.executes other vector state 13 (displacement slot) input
  refine ⟨_, run, frame, rfl, ?_⟩
  intro index within
  rw [frame.memory _ (separate index within)]
  exact loaded index within

/-! ## The guard of the zero-offset store -/

/-- The source address instruction forming the zero-offset store's R12 address. -/
def guardPath : List Nat := [1, 1, 1, 1] ++ List.replicate 8 0 ++ [1] ++ List.replicate 9 0 ++ [1]

/-- The source load between the guard and the zero-offset store. -/
def loadPath : List Nat := [1, 1, 1, 1] ++ List.replicate 8 0 ++ [1] ++ List.replicate 8 0 ++ [1]

theorem guard_instruction :
    image.source.body.atPath guardPath = some (.instruction (.address 5 10 3 (some 8) 2 0)) := by
  kernel_reflexivity

theorem load_instruction :
    image.source.body.atPath loadPath = some (.instruction (.load .u32z .word32 0 11 7 0)) := by
  kernel_reflexivity

def guardAt : Copy → Nat
  | .fast => 855
  | .slow => 1399

/-- `lea r15, [rax*4+4]`; `cmp r15, [rdi+0x58]` (region five's length); `ja` to the
invalid-input entry; `lea r12, [rcx+rax*4]`. -/
def guardCode (copy : Copy) : List Nat :=
  [0x4c, 0x8d, 0x3c, 0x85] ++ X86Bounds.little32 4 ++
    [0x4c, 0x3b, 0xbf] ++ X86Bounds.little32 0x58 ++
    [0x0f, 0x87] ++ X86Bounds.little32 (BitVec.ofInt 32 ((invalidEntry : Int) - (guardAt copy + 21))) ++
    [0x4c, 0x8d, 0x24, 0x81]

theorem guardCode_length (copy : Copy) : (guardCode copy).length = 25 := by
  cases copy <;> rfl

theorem guard_bytes (copy : Copy) (byte : Fin 25) :
    image.view.read (guardAt copy + byte.val) = ((guardCode copy)[byte.val]?).map (BitVec.ofNat 8) := by
  cases copy <;> fin_cases byte <;> kernel_reflexivity

theorem guard_span (copy : Copy) :
    image.spans.any (fun span => span.offset == guardAt copy && span.length == 25 &&
      span.kind == "ADDR-INDEX" && span.path == some guardPath) = true := by
  cases copy <;> kernel_reflexivity

theorem load_span (copy : Copy) :
    image.spans.any (fun span => span.offset == guardAt copy + 25 && span.length == 7 &&
      span.kind == "LOAD-DIRECT" && span.path == some loadPath) = true := by
  cases copy <;> kernel_reflexivity

/-- Guard, then the seven-byte load, then the zero-offset MOV. -/
theorem guard_then_store (copy : Copy) : guardAt copy + 25 + 7 = tailAt copy 0 := by
  cases copy <;> rfl

/-- The guard as an instance of the narrow indexed-address check: R12 from RCX and RAX scaled by
four, extent four, against region five's length field at frame offset `0x58`. -/
def guardShape : X86IndexedAddress.Shape := ⟨12, ⟨0, by decide⟩, 2, ⟨1, by decide⟩, 4#32, 0x58#32⟩

theorem guardCode_eq (copy : Copy) :
    guardCode copy = X86IndexedAddress.code guardShape (guardAt copy) invalidEntry := by
  cases copy <;> rfl

theorem guard_checked (copy : Copy) :
    X86IndexedAddress.Checked image.view (guardAt copy) invalidEntry guardShape := by
  cases copy <;> exact of_decide_eq_true (by kernel_reflexivity)

/-- A loaded image is placed for the generic fetch facts. -/
theorem placed_of_loaded (state : State) (base : Int) (loaded : X86P1LoadCapture.Loaded image state base) :
    X86CodePlacement.Placed state base image.view := by
  intro index byte present
  have within : index < image.size := by
    by_contra outside
    simp [P1Capture.Program.view, outside] at present
  exact (loaded index within).trans present

open X86PlacedInstruction (At) in
open X86PlacedMemory (Cell Controls Reads) in
/-- With the scaled index plus four within region five's length, the guard forms R12 in four fetches
and continues at the intervening load. -/
theorem guard_succeeds (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (copy : Copy) {state : State} {base : BitVec 48}
    (point : At image.view state base (guardAt copy)) (controls : Controls state)
    (frame regionBase index length : Word) (cell : Cell frame 0x58#32)
    (frameKnown : lookup state 7 = some frame) (baseKnown : lookup state 1 = some regionBase)
    (indexKnown : lookup state 0 = some index) (lengthRead : Reads state cell.address length)
    (fits : index.toNat * 4 + 4 ≤ length.toNat) :
    letI : OtherOpcodeHandlers := X86IndexedAddress.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 4).run state = .ok () after ∧
      RegisterFrame (X86IndexedAddress.writes 12) state after ∧
      lookup after 12 = some (regionBase + index * 4#64) ∧
      Nonempty (At image.view after base (guardAt copy + 25)) :=
  X86IndexedAddress.succeeds other extra vector point guardShape (guard_checked copy) controls frame regionBase index
    length cell frameKnown baseKnown indexKnown lengthRead (by decide) fits

open X86PlacedInstruction (At) in
open X86PlacedMemory (Cell Controls Reads) in
/-- Beyond the length, the guard reaches the shared invalid-input entry in three fetches. -/
theorem guard_rejects (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (copy : Copy) {state : State} {base : BitVec 48}
    (point : At image.view state base (guardAt copy)) (controls : Controls state)
    (frame index length : Word) (cell : Cell frame 0x58#32)
    (frameKnown : lookup state 7 = some frame) (indexKnown : lookup state 0 = some index)
    (lengthRead : Reads state cell.address length) (narrow : index.toNat < 2 ^ 32)
    (above : length.toNat < index.toNat * 4 + 4) :
    letI : OtherOpcodeHandlers := X86IndexedAddress.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 3).run state = .ok () after ∧ RegisterFrame {.r15, .rflags, .rip} state after ∧
      Nonempty (At image.view after base invalidEntry) :=
  X86IndexedAddress.rejects other extra vector point guardShape (guard_checked copy) controls frame index length
    cell frameKnown indexKnown lengthRead (by decide) (by change index.toNat * 4 + 4 < _; omega) above

/-! ## Negative controls -/

/-- No copy has a bounds-prefixed STORE span for the zero-offset store. -/
theorem no_prefixed_zero_store :
    image.spans.any (fun span => span.kind == "STORE" && span.path == some (sourcePath 0)) = false := by
  kernel_reflexivity

/-- The zero-offset guard is the 25-byte form without an index-overflow test in both copies. -/
theorem guard_not_overflow_form (copy : Copy) :
    image.spans.any (fun span => span.offset == guardAt copy && span.length == 50) = false := by
  cases copy <;> kernel_reflexivity

/-- The guard rejects to the current invalid-input entry, not to the previous image's at 3160. -/
theorem guard_stale_target_refused (copy : Copy) :
    ¬ X86IndexedAddress.Checked image.view (guardAt copy) 3160 guardShape := by
  intro checked
  have jump := checked.2.2.2.2.2.1
  have actual := (guard_checked copy).2.2.2.2.2.1
  cases copy <;> exact absurd (actual.symm.trans jump) (by decide +kernel)

/-- The guard compares with region five's length field, not its base field at `0x50`. -/
theorem guard_base_field_refused (copy : Copy) :
    ¬ X86IndexedAddress.Checked image.view (guardAt copy) invalidEntry { guardShape with field := 0x50#32 } := by
  intro checked
  have compare := checked.2.2.2.2.1
  have actual := (guard_checked copy).2.2.2.2.1
  cases copy <;> exact absurd (actual.symm.trans compare) (by decide +kernel)

/-- The zero-offset layout of the bounds constructor, as it would precede the direct MOV. -/
def zeroLayout (copy : Copy) : X86Bounds.Layout :=
  ⟨12, 5, ⟨0, by decide⟩, 4, invalidEntry - (tailAt copy 0 - 36)⟩

/-- The previous zero-offset span, a 36-byte bounds prefix before its MOV, is absent. -/
theorem zero_prefix_absent (copy : Copy) :
    ¬ ∀ byte : Fin 36, image.view.read (tailAt copy 0 - 36 + byte.val) =
      ((X86Bounds.code (zeroLayout copy))[byte.val]?).map (BitVec.ofNat 8) := by
  intro claimed
  have first := claimed ⟨0, by decide⟩
  have expected : ((X86Bounds.code (zeroLayout copy))[0]?).map (BitVec.ofNat 8) = some (0x4d#8) := by
    cases copy <;> rfl
  cases copy
  · have actual : image.view.read 851 = some (0x4c#8) := by kernel_reflexivity
    exact absurd (actual.symm.trans (first.trans expected)) (by decide)
  · have actual : image.view.read 1395 = some (0x4c#8) := by kernel_reflexivity
    exact absurd (actual.symm.trans (first.trans expected)) (by decide)

/-- A prefix rejecting to the previous image's invalid-input entry, 3160, is refused. -/
theorem stale_reject_refused (copy : Copy) (slot : Fin 3) :
    ¬ ∀ byte : Fin 49, image.view.read (spanStart copy slot + byte.val) =
      ((X86Bounds.code { boundsLayout copy slot with reject := 3160 - spanStart copy slot })[byte.val]?).map
        (BitVec.ofNat 8) := by
  intro claimed
  have stale := claimed ⟨19, by decide⟩
  cases copy <;> fin_cases slot <;>
    exact absurd ((prefix_bytes _ _ ⟨19, by decide⟩).symm.trans stale) (by decide +kernel)

end Mettapedia.Machines.TIsa.X86P1SibStoreCapture
