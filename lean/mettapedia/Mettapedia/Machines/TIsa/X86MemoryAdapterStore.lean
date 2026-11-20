import Mettapedia.Machines.TIsa.X86MemoryStore
import Mettapedia.Machines.TIsa.X86MemoryBounds
import Mettapedia.Machines.TIsa.X86P1SibStoreCapture
import Mettapedia.Machines.TIsa.X86MemoryFieldLoad
import Mettapedia.Machines.TIsa.X86BoundsPrefixes

/-!
# The calculus store joined to the captured adapter stores

The four actual p1 stores, in both emitted copies of the adapter's copy loop,
derive their successful native paths from genuine source firings. Their
existing source readbacks construct the descriptor and pointer facts; the
original Sail executions then establish the updated representation, exact
physical frame, full image and CPU profile.

The zero-offset store is one fetched MOV. Its access check is supplied by the
source firing; in the image it is enforced by the preceding address guard of
its copy, whose execution is captured with the store bytes. Each
positive-offset store executes the nine-instruction bounds prefix and the MOV.
Every fetched execution prefix retains its declared register/byte frame. The
existing GSLT program WP transfers arbitrary source postconditions to these
native blocks; addresses remain rewrite instances of the store operation.
Physical descriptor/code exclusions and alignment readiness remain explicit.

A negative control shows that the direct MOV checks nothing itself: from a
represented pointer at the region end, where the source store is refused, it
still writes past the region. A fixture at each copy's guard, with the scaled
index in RAX, supplies the guard's concrete boundary controls. Composing the
guard, the intervening load and
the MOV through the loop body, the handler/ABI, the full adapter and the
generic compiler remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86MemoryAdapterStore
open _root_.X86Registers X86RegisterRefinement X86Execution X86MemoryView X86MemoryReadback
open Cells CellEffects X86MemoryStore
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open X86P1SibStoreCapture (Copy)
local instance : MemoryPrimitives := X86Memory.ordinary

theorem memoryReads_pointer (before after : State) (same : lookup after 7 = lookup before 7) (observed : Key) :
    memoryReads after observed = memoryReads before observed := by
  cases observed <;> simp only [memoryReads, fieldReads, same]

theorem alignment_agrees (profile : X86Readiness.Profile) (native : State)
    (holds : profile.Holds native) (flags : BitVec 32) (flagsKnown : native.regs.get? .rflags = some flags) :
    X86FrameLoad.alignmentEnabled profile.controls flags profile.visible = profile.enabled := by
  obtain ⟨_controls, _visible, seen, seenKnown, ac⟩ := holds
  have same : seen = flags := Option.some.inj (seenKnown.symm.trans flagsKnown)
  subst seen
  simp only [X86FrameLoad.alignmentEnabled, X86Readiness.Profile.enabled, ac]

theorem source_access_fits (base length pointer : Word) (offset : X86BoundsArithmetic.Offset)
    (count : Fin 128) (address : Nat)
    (rangeFits : base.toNat + length.toNat < 2 ^ 64)
    (pointerLower : base.toNat ≤ pointer.toNat) (pointerUpper : pointer.toNat ≤ base.toNat + length.toNat)
    (accepted : Memory.access? base length pointer (X86PositiveImmediate.immediate32 offset).toInt count.val = some address) :
    address = pointer.toNat + offset.val ∧
      (pointer - base).toNat + offset.val + count.val ≤ length.toNat := by
  have source := (P1Memory.access?_iff_inside base length pointer (X86PositiveImmediate.immediate32 offset)
    count.val address rangeFits pointerLower pointerUpper).mp accepted
  rw [X86BoundsArithmetic.offset_toInt] at source
  have coordinate : address = pointer.toNat + offset.val := by omega
  refine ⟨coordinate, ?_⟩
  apply (X86BoundsArithmetic.source_guard base length pointer offset count rangeFits pointerLower pointerUpper).mpr
  simpa only [coordinate] using accepted

/-- The source displacement of a store as a bounds-constructor offset. -/
def slotOffset (slot : Fin 4) : X86BoundsArithmetic.Offset := ⟨4 * slot.val, by have := slot.isLt; omega⟩

theorem slot_access_fits (slot : Fin 4) (values : Key → Word) (address : Nat)
    (rangeFits : (values (.capabilityBase 5)).toNat + (values (.capabilityLength 5)).toNat < 2 ^ 64)
    (pointerLower : (values (.capabilityBase 5)).toNat ≤ (values (.register 10)).toNat)
    (pointerUpper : (values (.register 10)).toNat ≤ (values (.capabilityBase 5)).toNat + (values (.capabilityLength 5)).toNat)
    (access : Memory.access? (values (.capabilityBase 5)) (values (.capabilityLength 5)) (values (.register 10))
      (X86P1SibStoreCapture.displacement slot).toInt 4 = some address) :
    address = (values (.register 10)).toNat + 4 * slot.val ∧
      (values (.register 10) - values (.capabilityBase 5)).toNat + 4 * slot.val + 4 ≤
        (values (.capabilityLength 5)).toNat :=
  source_access_fits _ _ _ (slotOffset slot) 4 address rangeFits pointerLower pointerUpper access

/-- The captured MOV of any store, from a state represented by a source configuration in which
the store fires. Bounds are not executed here; they are the firing's. -/
theorem captured_mov_profile (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (copy : Copy) (slot : Fin 4) (view : View) (values : Key → Word)
    (native : State) (base : Int) (origin : X86LegacyFetch.Basis native)
    (profile : X86Readiness.Profile) (flags : BitVec 32)
    (known : ∀ observed ∈ view.keys, readback view.modes native observed = some (values observed))
    (holds : profile.Holds native) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (placed : origin.address.toInt = base + X86P1SibStoreCapture.tailAt copy slot)
    (upper : base + 3778 < (2 ^ 47 : Int))
    (loaded : X86P1LoadCapture.Loaded X86P1SibStoreCapture.image native base)
    (rangeFits : (values (.capabilityBase 5)).toNat + (values (.capabilityLength 5)).toNat < 2 ^ 64)
    (pointerLower : (values (.capabilityBase 5)).toNat ≤ (values (.register 10)).toNat)
    (pointerUpper : (values (.register 10)).toNat ≤ (values (.capabilityBase 5)).toNat + (values (.capabilityLength 5)).toNat)
    (address : Nat) (following : World)
    (source : (CellEffects.profile [P1Memory.storeRecipe .word32 5 10 11
      (X86P1SibStoreCapture.displacement slot).toInt address]).theory.rewrites (encode view.keys values) following)
    (safe : profile.enabled = false ∨ target address &&& (3#48) = (0#48))
    (descriptors : DescriptorsApart view native (X86SibStore.writes (target address)))
    (codeApart : ∀ index < X86P1SibStoreCapture.image.size,
      ((X86Execution.address base index).signExtend 52).toNat ∉ X86SibStore.writes (target address)) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 1).run native = .ok () after ∧
      X86StateFrame.Frame {.rip} (X86SibStore.writes (target address)) native after ∧
      represents view following after ∧ after.regs.get? .rflags = some flags ∧
      after.regs.get? .rip = some ((X86Execution.address base (X86P1SibStoreCapture.tailAt copy slot + 8)).signExtend 64) ∧
      X86P1LoadCapture.Loaded X86P1SibStoreCapture.image after base ∧
      X86ControlFlags.Preserved native after ∧ profile.Holds after := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨_produced, included, _mode, access, _output, _followingEq⟩ :=
    (source_store_iff .word32 5 10 11 (X86P1SibStoreCapture.displacement slot).toInt address view.keys values following).mp source
  have bytesPresent : ∀ offset < 4, Memory.Key.byte (address + offset) ∈ view.keys := by
    intro offset within
    apply included
    apply Finset.mem_union_left
    simp [CellEffects.Recipe.writes, P1Memory.storeRecipe, P1Memory.storeSpec, Memory.Store.recipe,
      Memory.byteKeys, P1Memory.memoryWidth, Memory.Width.bytes, within]
  have area := represented_byte_area view values native address 4 (by decide) known bytesPresent
  obtain ⟨addressEq, _fits⟩ := slot_access_fits slot values address rangeFits pointerLower pointerUpper access
  have dataUpper : (target address).toInt + 4 ≤ (2 ^ 47 : Int) := by
    rw [target, X86CanonicalSpan.narrow_toInt _ (X86CanonicalSpan.area_base _ 4 (by decide) area)]
    exact X86CanonicalSpan.area_signed_upper _ 4 (by decide) area
  have effective : values (.register 10) + (X86P1SibStoreCapture.displacement slot).signExtend 64 =
      (target address).signExtend 64 := by
    have offsetWord : (X86P1SibStoreCapture.displacement slot).signExtend 64 = BitVec.ofNat 64 (4 * slot.val) := by
      fin_cases slot <;> rfl
    have coordinate : values (.register 10) + (X86P1SibStoreCapture.displacement slot).signExtend 64 =
        BitVec.ofNat 64 address := by
      rw [offsetWord, addressEq, BitVec.ofNat_add, BitVec.ofNat_toNat]
      rfl
    exact coordinate.trans (X86CanonicalSpan.narrow_representation _ (X86CanonicalSpan.area_base _ 4 (by decide) area)).symm
  have tailSafe : X86FrameLoad.alignmentEnabled profile.controls flags profile.visible = false ∨
      target address &&& (3#48) = (0#48) := by
    rw [alignment_agrees profile native holds flags flagsKnown]
    exact safe
  have tailUpper : origin.address.toInt + 8 < (2 ^ 47 : Int) := by
    rw [placed]
    have small : X86P1SibStoreCapture.tailAt copy slot + 8 ≤ 3778 := by
      cases copy <;> fin_cases slot <;> decide
    omega
  have baseKnown : lookup native 12 = some (values (.register 10)) := known (.register 10) (view.registers 10)
  have sourceKnown : lookup native 13 = some (values (.register 11)) := known (.register 11) (view.registers 11)
  obtain ⟨after, run, frame, resultEq, afterImage⟩ := X86P1SibStoreCapture.executes
    (X86Bounds.handlers other extra) vector copy slot native base origin placed loaded profile.visible profile.controls
    (values (.register 10)) (values (.register 11)) flags (target address) baseKnown sourceKnown holds.1
    flagsKnown holds.2.1 quiet tailUpper dataUpper effective tailSafe codeApart
  have afterFlags : after.regs.get? .rflags = some flags := (frame.registers .rflags (by decide)).trans flagsKnown
  have control : X86ControlFlags.Preserved native after := by
    unfold X86ControlFlags.Preserved
    rw [frame.registers .rflags (by decide)]
  refine ⟨after, run, frame, ?_, afterFlags, ?_, afterImage, control,
    profile.after_control native after _ _ frame (by decide) control ⟨flags, afterFlags⟩ holds⟩
  · rw [resultEq]
    exact store_represents view values native 5 10 11 _ address following _ known source descriptors
  · rw [resultEq]
    simp only [X86SibStore.result, X86DataStore.result, X86Move.putPointer, Std.ExtDHashMap.get?_insert,
      beq_self_eq_true, dite_true]
    rw [placed]
    simp only [X86Execution.address, Nat.cast_add, Int.add_assoc]
    rfl

/-- A positive-offset store: the bounds prefix of its STORE span, then its MOV. -/
theorem captured_checked_store_profile_prefixes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (copy : Copy) (slot : Fin 3) (view : View) (values : Key → Word)
    (native : State) (base : Int) (origin : X86LegacyFetch.Basis native)
    (profile : X86Readiness.Profile) (flags : BitVec 32)
    (known : ∀ observed ∈ view.keys, readback view.modes native observed = some (values observed))
    (frameArea : X86CanonicalSpan.Area (values (.register 0)) frameLayout.size)
    (frameAligned : (values (.register 0)).toNat % 8 = 0)
    (holds : profile.Holds native) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (placed : origin.address.toInt = base + X86P1SibStoreCapture.spanStart copy slot)
    (upper : base + 3778 < (2 ^ 47 : Int))
    (loaded : X86P1LoadCapture.Loaded X86P1SibStoreCapture.image native base)
    (rangeFits : (values (.capabilityBase 5)).toNat + (values (.capabilityLength 5)).toNat < 2 ^ 64)
    (pointerLower : (values (.capabilityBase 5)).toNat ≤ (values (.register 10)).toNat)
    (pointerUpper : (values (.register 10)).toNat ≤ (values (.capabilityBase 5)).toNat + (values (.capabilityLength 5)).toNat)
    (address : Nat) (following : World)
    (source : (CellEffects.profile [P1Memory.storeRecipe .word32 5 10 11
      (X86P1SibStoreCapture.displacement slot.succ).toInt address]).theory.rewrites (encode view.keys values) following)
    (safe : profile.enabled = false ∨ target address &&& (3#48) = (0#48))
    (descriptors : DescriptorsApart view native (X86SibStore.writes (target address)))
    (codeApart : ∀ index < X86P1SibStoreCapture.image.size,
      ((X86Execution.address base index).signExtend 52).toNat ∉ X86SibStore.writes (target address)) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags,
      (X86FuelPrefix.fetches (X86P1SibStoreCapture.storeSteps slot.succ)).run native = .ok () after ∧
      X86StateFrame.Frame X86Bounds.writes (X86SibStore.writes (target address)) native after ∧
      represents view following after ∧ after.regs.get? .rflags = some nextFlags ∧
      after.regs.get? .rip = some ((X86Execution.address base (X86P1SibStoreCapture.tailAt copy slot.succ + 8)).signExtend 64) ∧
      X86P1LoadCapture.Loaded X86P1SibStoreCapture.image after base ∧
      X86ControlFlags.Preserved native after ∧ profile.Holds after ∧
      ∀ count ≤ X86P1SibStoreCapture.storeSteps slot.succ,
        ∀ observed, (X86FuelPrefix.fetches count).run native = .ok () observed →
          X86StateFrame.Frame X86Bounds.writes (X86SibStore.writes (target address)) native observed := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  let layout := X86P1SibStoreCapture.boundsLayout copy slot
  obtain ⟨_produced, included, _mode, access, _output, _followingEq⟩ :=
    (source_store_iff .word32 5 10 11 (X86P1SibStoreCapture.displacement slot.succ).toInt address view.keys values following).mp source
  have basePresent : Memory.Key.capabilityBase 5 ∈ view.keys := by
    apply included
    simp [CellEffects.Recipe.support, P1Memory.storeRecipe, P1Memory.storeSpec, Memory.Store.recipe, Memory.capabilityKeys]
  have lengthPresent : Memory.Key.capabilityLength 5 ∈ view.keys := by
    apply included
    simp [CellEffects.Recipe.support, P1Memory.storeRecipe, P1Memory.storeSpec, Memory.Store.recipe, Memory.capabilityKeys]
  obtain ⟨_addressEq, fits⟩ := slot_access_fits slot.succ values address rangeFits pointerLower pointerUpper access
  have fitsLayout : (values (.register 10) - values (.capabilityBase 5)).toNat + layout.offset.val + layout.count.val ≤
      (values (.capabilityLength 5)).toNat := by
    have offsetVal : layout.offset.val = 4 * slot.succ.val := by simp [layout, X86P1SibStoreCapture.boundsLayout]
    have countVal : layout.count.val = 4 := rfl
    rw [offsetVal, countVal]
    exact fits
  let observed := X86MemoryBounds.facts view values native layout 10 profile flags (by rfl)
    known basePresent lengthPresent frameArea frameAligned holds flagsKnown quiet
  let geometry := X86P1SibStoreCapture.boundsContext copy slot base origin.address placed upper
  let input : X86Bounds.Inputs layout native origin :=
    { observed with geometry := geometry, loaded := X86P1SibStoreCapture.prefix_loaded copy slot native base origin.address placed loaded }
  obtain ⟨middle, middleFlags, prefixRun, prefixFrame, middleFlagsKnown, middleRip, control⟩ :=
    X86Bounds.succeeds_control other extra vector layout native origin input fitsLayout
  have middleKnown (observed : Key) (member : observed ∈ view.keys) :
      readback view.modes middle observed = some (values observed) :=
    (X86MemoryBounds.bounds_preserves_readback view.modes native middle prefixFrame observed).trans (known observed member)
  have middleProfile : profile.Holds middle := profile.after_control native middle _ _
    (X86StateFrame.registerOnly prefixFrame) X86Bounds.writes_data control ⟨middleFlags, middleFlagsKnown⟩ holds
  have room : X86Bounds.exitAt layout + 3 ≤ geometry.extent := by
    change X86Bounds.exitAt layout + 3 ≤ 3778 - X86P1SibStoreCapture.spanStart copy slot
    cases copy <;> fin_cases slot <;> decide
  let nextOrigin := rebase native middle origin (prefixFrame.mono X86Bounds.writes_data) geometry.upper
    (X86Bounds.exitAt layout) room middleRip
  have nextPlaced : nextOrigin.address.toInt = base + X86P1SibStoreCapture.tailAt copy slot.succ := by
    change (X86Execution.address origin.address.toInt (X86Bounds.exitAt layout)).toInt = _
    rw [address_toInt _ (by simpa using BitVec.le_toInt origin.address) geometry.upper _ (by omega), placed]
    have endpoint := X86P1SibStoreCapture.prefix_end copy slot
    dsimp only [layout]
    omega
  have middleImage : X86P1LoadCapture.Loaded X86P1SibStoreCapture.image middle base := by
    intro index within
    rw [prefixFrame.memory]
    exact loaded index within
  have samePointer := prefixFrame.lookup 7 (by decide)
  have middleDescriptors : DescriptorsApart view middle (X86SibStore.writes (target address)) := by
    constructor
    · intro region member address present
      exact descriptors.1 region member address (by simpa only [memoryReads_pointer native middle samePointer] using present)
    · intro region member address present
      exact descriptors.2 region member address (by simpa only [memoryReads_pointer native middle samePointer] using present)
  obtain ⟨after, tailRun, tailFrame, represented, afterFlags, rip, afterImage, tailControl, afterProfile⟩ :=
    captured_mov_profile other extra vector copy slot.succ view values middle base nextOrigin profile middleFlags
      middleKnown middleProfile middleFlagsKnown
      (by rw [prefixFrame.registers .log_register_writes (by decide)]; exact quiet)
      nextPlaced upper middleImage rangeFits pointerLower pointerUpper address following source safe
      middleDescriptors codeApart
  have combined : X86StateFrame.Frame X86Bounds.writes (X86SibStore.writes (target address)) native after :=
    ((X86StateFrame.registerOnly prefixFrame).trans tailFrame).mono (by decide) (by simp)
  have steps : X86P1SibStoreCapture.storeSteps slot.succ = (X86Bounds.offsetSteps layout + 5) + 1 :=
    (X86P1SibStoreCapture.offset_steps copy slot).symm
  have completeRun : (X86FuelPrefix.fetches (X86P1SibStoreCapture.storeSteps slot.succ)).run native = .ok () after := by
    rw [steps, X86FuelPrefix.fetches_add, run_bind, prefixRun]
    exact tailRun
  refine ⟨after, middleFlags, completeRun, combined, represented, afterFlags, rip, afterImage,
    control.trans tailControl, afterProfile, ?_⟩
  intro count within seen executed
  rw [steps] at within
  by_cases prefixOnly : count ≤ X86Bounds.offsetSteps layout + 5
  · have framed := X86Bounds.success_prefix_frame other extra vector layout native origin input fitsLayout count prefixOnly seen executed
    exact (X86StateFrame.registerOnly framed).mono (by rfl) (by simp)
  · have last : count = X86P1SibStoreCapture.storeSteps slot.succ := by omega
    rw [last] at executed
    have same := X86FuelPrefix.fetches_deterministic _ native after seen completeRun executed
    subst seen
    exact combined

/-- Every store's native code from its entry: one MOV at zero offset, else bounds and MOV. -/
theorem captured_store_profile_prefixes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (copy : Copy) (slot : Fin 4) (view : View) (values : Key → Word)
    (native : State) (base : Int) (origin : X86LegacyFetch.Basis native)
    (profile : X86Readiness.Profile) (flags : BitVec 32)
    (known : ∀ observed ∈ view.keys, readback view.modes native observed = some (values observed))
    (frameArea : X86CanonicalSpan.Area (values (.register 0)) frameLayout.size)
    (frameAligned : (values (.register 0)).toNat % 8 = 0)
    (holds : profile.Holds native) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (placed : origin.address.toInt = base + X86P1SibStoreCapture.entryAt copy slot)
    (upper : base + 3778 < (2 ^ 47 : Int))
    (loaded : X86P1LoadCapture.Loaded X86P1SibStoreCapture.image native base)
    (rangeFits : (values (.capabilityBase 5)).toNat + (values (.capabilityLength 5)).toNat < 2 ^ 64)
    (pointerLower : (values (.capabilityBase 5)).toNat ≤ (values (.register 10)).toNat)
    (pointerUpper : (values (.register 10)).toNat ≤ (values (.capabilityBase 5)).toNat + (values (.capabilityLength 5)).toNat)
    (address : Nat) (following : World)
    (source : (CellEffects.profile [P1Memory.storeRecipe .word32 5 10 11
      (X86P1SibStoreCapture.displacement slot).toInt address]).theory.rewrites (encode view.keys values) following)
    (safe : profile.enabled = false ∨ target address &&& (3#48) = (0#48))
    (descriptors : DescriptorsApart view native (X86SibStore.writes (target address)))
    (codeApart : ∀ index < X86P1SibStoreCapture.image.size,
      ((X86Execution.address base index).signExtend 52).toNat ∉ X86SibStore.writes (target address)) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags,
      (X86FuelPrefix.fetches (X86P1SibStoreCapture.storeSteps slot)).run native = .ok () after ∧
      X86StateFrame.Frame X86Bounds.writes (X86SibStore.writes (target address)) native after ∧
      represents view following after ∧ after.regs.get? .rflags = some nextFlags ∧
      after.regs.get? .rip = some ((X86Execution.address base (X86P1SibStoreCapture.tailAt copy slot + 8)).signExtend 64) ∧
      X86P1LoadCapture.Loaded X86P1SibStoreCapture.image after base ∧
      X86ControlFlags.Preserved native after ∧ profile.Holds after ∧
      ∀ count ≤ X86P1SibStoreCapture.storeSteps slot,
        ∀ observed, (X86FuelPrefix.fetches count).run native = .ok () observed →
          X86StateFrame.Frame X86Bounds.writes (X86SibStore.writes (target address)) native observed := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  rcases Fin.eq_zero_or_eq_succ slot with rfl | ⟨checked, rfl⟩
  · obtain ⟨after, run, frame, represented, afterFlags, rip, afterImage, control, afterProfile⟩ :=
      captured_mov_profile other extra vector copy 0 view values native base origin profile flags known holds
        flagsKnown quiet placed upper loaded rangeFits pointerLower pointerUpper address following source safe
        descriptors codeApart
    have widened : X86StateFrame.Frame X86Bounds.writes (X86SibStore.writes (target address)) native after :=
      frame.mono (by decide) (subset_refl _)
    refine ⟨after, flags, run, widened, represented, afterFlags, rip, afterImage, control, afterProfile, ?_⟩
    intro count within seen executed
    change count ≤ 1 at within
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp within with rfl | rfl
    · rw [X86FuelPrefix.fetches_zero] at executed
      cases executed
      exact X86StateFrame.Frame.refl _ _ native
    · have same := X86FuelPrefix.fetches_deterministic 1 native after seen run executed
      subst seen
      exact widened
  · exact captured_checked_store_profile_prefixes other extra vector copy checked view values native base origin
      profile flags known frameArea frameAligned holds flagsKnown quiet
      (by rw [← X86P1SibStoreCapture.entryAt_succ]; exact placed) upper loaded rangeFits pointerLower pointerUpper
      address following source safe descriptors codeApart

theorem captured_store_profile (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (copy : Copy) (slot : Fin 4) (view : View) (values : Key → Word)
    (native : State) (base : Int) (origin : X86LegacyFetch.Basis native)
    (profile : X86Readiness.Profile) (flags : BitVec 32)
    (known : ∀ observed ∈ view.keys, readback view.modes native observed = some (values observed))
    (frameArea : X86CanonicalSpan.Area (values (.register 0)) frameLayout.size)
    (frameAligned : (values (.register 0)).toNat % 8 = 0)
    (holds : profile.Holds native) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (placed : origin.address.toInt = base + X86P1SibStoreCapture.entryAt copy slot)
    (upper : base + 3778 < (2 ^ 47 : Int))
    (loaded : X86P1LoadCapture.Loaded X86P1SibStoreCapture.image native base)
    (rangeFits : (values (.capabilityBase 5)).toNat + (values (.capabilityLength 5)).toNat < 2 ^ 64)
    (pointerLower : (values (.capabilityBase 5)).toNat ≤ (values (.register 10)).toNat)
    (pointerUpper : (values (.register 10)).toNat ≤ (values (.capabilityBase 5)).toNat + (values (.capabilityLength 5)).toNat)
    (address : Nat) (following : World)
    (source : (CellEffects.profile [P1Memory.storeRecipe .word32 5 10 11
      (X86P1SibStoreCapture.displacement slot).toInt address]).theory.rewrites (encode view.keys values) following)
    (safe : profile.enabled = false ∨ target address &&& (3#48) = (0#48))
    (descriptors : DescriptorsApart view native (X86SibStore.writes (target address)))
    (codeApart : ∀ index < X86P1SibStoreCapture.image.size,
      ((X86Execution.address base index).signExtend 52).toNat ∉ X86SibStore.writes (target address)) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags,
      (X86FuelPrefix.fetches (X86P1SibStoreCapture.storeSteps slot)).run native = .ok () after ∧
      X86StateFrame.Frame X86Bounds.writes (X86SibStore.writes (target address)) native after ∧
      represents view following after ∧ after.regs.get? .rflags = some nextFlags ∧
      after.regs.get? .rip = some ((X86Execution.address base (X86P1SibStoreCapture.tailAt copy slot + 8)).signExtend 64) ∧
      X86P1LoadCapture.Loaded X86P1SibStoreCapture.image after base ∧
      X86ControlFlags.Preserved native after ∧ profile.Holds after := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,flags,run,frame,represented,flagsKnown,rip,image,control,held,_prefixes⟩ :=
    captured_store_profile_prefixes other extra vector copy slot view values native base origin profile flags known
      frameArea frameAligned holds flagsKnown quiet placed upper loaded rangeFits pointerLower pointerUpper
      address following source safe descriptors codeApart
  exact ⟨after,flags,run,frame,represented,flagsKnown,rip,image,control,held⟩

def sourceOperation (slot : Fin 4) : Memory.Operation P1Source.Reg :=
  .store (P1Memory.storeSpec .word32 5 10 11 (X86P1SibStoreCapture.displacement slot).toInt)

def sourceAction (slot : Fin 4) : Mettapedia.GSLT.Logic.AbstractSeparationLogic.Action World Unit where
  Safe world := ∃ following, (Memory.program [sourceOperation slot]).theory.rewrites world following
  Step world _ following := (Memory.program [sourceOperation slot]).theory.rewrites world following

theorem source_progress (slot : Fin 4) : (sourceAction slot).Progress := by
  rintro world ⟨following,step⟩
  exact ⟨(),following,step⟩

theorem source_step_iff (slot : Fin 4) (keys : Finset Key) (values : Key → Word) (following : World) :
    (sourceAction slot).Step (encode keys values) () following ↔
      ∃ address, (CellEffects.profile [P1Memory.storeRecipe .word32 5 10 11
        (X86P1SibStoreCapture.displacement slot).toInt address]).theory.rewrites (encode keys values) following := by
  change (Memory.program [sourceOperation slot]).theory.rewrites (encode keys values) following ↔ _
  rw [Memory.program_rewrite_iff]
  constructor
  · rintro ⟨operation,member,address,produced,included,guarded,endpoint⟩
    have same : operation = sourceOperation slot := by simpa using member
    subst operation
    exact ⟨address,(profile_rewrite_iff _ _ _ _).mpr
      ⟨_,by simp [sourceOperation,Memory.Operation.recipe,P1Memory.storeRecipe],produced,included,guarded,endpoint⟩⟩
  · rintro ⟨address,source⟩
    obtain ⟨recipe,member,produced,included,guarded,endpoint⟩ := (profile_rewrite_iff _ _ _ _).mp source
    have same : recipe = P1Memory.storeRecipe .word32 5 10 11 (X86P1SibStoreCapture.displacement slot).toInt address := by
      simpa using member
    subst recipe
    exact ⟨sourceOperation slot,by simp,address,produced,included,guarded,endpoint⟩

def sourceAddress (slot : Fin 4) (values : Key → Word) : Nat := (values (.register 10)).toNat + 4 * slot.val

theorem source_access_address (slot : Fin 4) (values : Key → Word) (address : Nat)
    (rangeFits : (values (.capabilityBase 5)).toNat + (values (.capabilityLength 5)).toNat < 2 ^ 64)
    (pointerLower : (values (.capabilityBase 5)).toNat ≤ (values (.register 10)).toNat)
    (pointerUpper : (values (.register 10)).toNat ≤ (values (.capabilityBase 5)).toNat + (values (.capabilityLength 5)).toNat)
    (access : Memory.access? (values (.capabilityBase 5)) (values (.capabilityLength 5)) (values (.register 10))
      (X86P1SibStoreCapture.displacement slot).toInt 4 = some address) :
    address = sourceAddress slot values :=
  (slot_access_fits slot values address rangeFits pointerLower pointerUpper access).1

theorem captured_store_wp (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (copy : Copy) (slot : Fin 4) (view : View) (values : Key → Word)
    (native : State) (base : Int) (origin : X86LegacyFetch.Basis native)
    (profile : X86Readiness.Profile) (flags : BitVec 32)
    (known : ∀ observed ∈ view.keys, readback view.modes native observed = some (values observed))
    (frameArea : X86CanonicalSpan.Area (values (.register 0)) frameLayout.size)
    (frameAligned : (values (.register 0)).toNat % 8 = 0)
    (holds : profile.Holds native) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (placed : origin.address.toInt = base + X86P1SibStoreCapture.entryAt copy slot)
    (upper : base + 3778 < (2 ^ 47 : Int))
    (loaded : X86P1LoadCapture.Loaded X86P1SibStoreCapture.image native base)
    (rangeFits : (values (.capabilityBase 5)).toNat + (values (.capabilityLength 5)).toNat < 2 ^ 64)
    (pointerLower : (values (.capabilityBase 5)).toNat ≤ (values (.register 10)).toNat)
    (pointerUpper : (values (.register 10)).toNat ≤ (values (.capabilityBase 5)).toNat + (values (.capabilityLength 5)).toNat)
    (safe : profile.enabled = false ∨ target (sourceAddress slot values) &&& (3#48) = (0#48))
    (descriptors : DescriptorsApart view native (X86SibStore.writes (target (sourceAddress slot values))))
    (codeApart : ∀ index < X86P1SibStoreCapture.image.size,
      ((X86Execution.address base index).signExtend 52).toNat ∉ X86SibStore.writes (target (sourceAddress slot values)))
    (post : Unit → World → Prop)
    (wp : (Prog.prim slot : Prog (Fin 4) (fun _ => Unit) Unit).wp sourceAction post (encode view.keys values)) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ following after nextFlags,
      post () following ∧ (sourceAction slot).Step (encode view.keys values) () following ∧
      (X86FuelPrefix.fetches (X86P1SibStoreCapture.storeSteps slot)).run native = .ok () after ∧
      X86StateFrame.Frame X86Bounds.writes (X86SibStore.writes (target (sourceAddress slot values))) native after ∧
      represents view following after ∧ after.regs.get? .rflags = some nextFlags ∧
      after.regs.get? .rip = some ((X86Execution.address base (X86P1SibStoreCapture.tailAt copy slot + 8)).signExtend 64) ∧
      X86P1LoadCapture.Loaded X86P1SibStoreCapture.image after base ∧
      X86ControlFlags.Preserved native after ∧ profile.Holds after ∧
      ∀ count ≤ X86P1SibStoreCapture.storeSteps slot,
        ∀ observed, (X86FuelPrefix.fetches count).run native = .ok () observed →
          X86StateFrame.Frame X86Bounds.writes (X86SibStore.writes (target (sourceAddress slot values))) native observed := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨following,step⟩ := wp.1.1
  have run : (Prog.prim slot : Prog (Fin 4) (fun _ => Unit) Unit).Runs sourceAction (encode view.keys values) () following :=
    ⟨(),following,step,rfl,rfl⟩
  have ensured := wp.2 () following run
  obtain ⟨address,firing⟩ := (source_step_iff slot view.keys values following).mp step
  obtain ⟨_produced,_included,_mode,access,_output,_endpoint⟩ :=
    (source_store_iff .word32 5 10 11 (X86P1SibStoreCapture.displacement slot).toInt address view.keys values following).mp firing
  have same : address = sourceAddress slot values := source_access_address slot values address rangeFits pointerLower pointerUpper access
  subst address
  obtain ⟨after,nextFlags,executed,frame,represented,flagsKnown,rip,image,control,held,prefixes⟩ :=
    captured_store_profile_prefixes other extra vector copy slot view values native base origin profile flags known
      frameArea frameAligned holds flagsKnown quiet placed upper loaded rangeFits pointerLower pointerUpper
      _ following firing safe descriptors codeApart
  exact ⟨following,after,nextFlags,ensured,step,executed,frame,represented,flagsKnown,rip,image,control,held,prefixes⟩

namespace Controls

private noncomputable abbrev entry := X86MemoryFieldLoad.entryFixture
private noncomputable abbrev image := X86P1SibStoreCapture.image
private def dataWord : Word := 0x80000001000000ff#64
private def keys : Finset Key := (Finset.univ.image Memory.Key.register) ∪
  ({.capabilityBase 5,.capabilityLength 5,.capabilityMode 5} ∪ (Memory.byteKeys 36864 16).toFinset)
private def view : View where
  keys := keys
  registers := by intro register; simp [keys]
  modes := fun region => if region.val = 5 then 2 else 0

/-- Source values whose R12 register holds `pointer`; region five is `[36864, 36880)`. -/
private noncomputable def valuesAt (pointer : Word) : Key → Word
  | .register register => if register = 10 then pointer else if register = 11 then dataWord else entry.values (.register register)
  | .byte _ => (0xa5#8).zeroExtend 64
  | .capabilityBase _ => 36864
  | .capabilityLength _ => 16
  | .capabilityMode region => if region = 5 then 2 else 0

private noncomputable abbrev values : Key → Word := valuesAt 36864

private def cellAddress (index : Nat) : Nat :=
  if index < 3778 then 4096 + index else if index < 3794 then 32848 + index - 3778 else 36864 + index - 3794
private noncomputable def cellByte (index : Nat) : BitVec 8 :=
  if index < 3778 then BitVec.ofNat 8 (Lean.RArray.get image.data index)
  else if index < 3786 then (36864#64).extractLsb' (8 * (index - 3778)) 8
  else if index < 3794 then (16#64).extractLsb' (8 * (index - 3786)) 8
  else (0xa5#8)
private noncomputable def cells : List (Nat × BitVec 8) :=
  (List.range 3810).map fun index => (cellAddress index, cellByte index)

private theorem address_injective : Function.Injective cellAddress := by
  intro left right same
  unfold cellAddress at same
  split_ifs at same <;> omega

private theorem distinct : cells.Pairwise (fun left right => (left.1 == right.1) = false) := by
  apply List.pairwise_map.mpr
  apply (List.nodup_iff_pairwise_ne.mp (List.nodup_range (n := 3810))).imp
  intro left right different
  exact beq_eq_false_iff_ne.mpr (fun same => different (address_injective same))

/-- The whole image at 4096, region five's descriptor and bytes, R12 at `pointer`, entry at `start`. -/
@[irreducible] private noncomputable def placedAt (start : Nat) (pointer : Word) : State :=
  let registers := entry.native.regs.insert .r12 pointer
  let registers := registers.insert .r13 dataWord
  let registers := registers.insert .rip ((address 4096 start).signExtend 64)
  { entry.native with regs := registers, mem := Std.ExtHashMap.ofList cells }

private noncomputable abbrev before (copy : Copy) (slot : Fin 4) : State :=
  placedAt (X86P1SibStoreCapture.entryAt copy slot) 36864

private theorem cell (start : Nat) (pointer : Word) (index : Fin 3810) :
    (placedAt start pointer).mem.get? (cellAddress index.val) = some (cellByte index.val) := by
  simp only [placedAt]
  exact Std.ExtHashMap.getElem?_ofList_of_mem (by simp) distinct
    (List.mem_map.mpr ⟨index.val,List.mem_range.mpr index.isLt,rfl⟩)

private theorem byte_chunks (chunk : Fin 12) :
    (List.range 320).all (fun offset => if chunk.val * 320 + offset < 3778 then
      Nat.ble (Lean.RArray.get image.data (chunk.val * 320 + offset)) 255 else true) = true := by
  fin_cases chunk <;> kernel_reflexivity

private theorem image_byte (offset : Fin 3778) : image.view.read offset.val =
    some (BitVec.ofNat 8 (Lean.RArray.get image.data offset.val)) := by
  have chunkBound : offset.val / 320 < 12 := by omega
  have remainder : offset.val % 320 < 320 := Nat.mod_lt _ (by decide)
  have coordinate : offset.val / 320 * 320 + offset.val % 320 = offset.val := by omega
  have valid : Nat.ble (Lean.RArray.get image.data offset.val) 255 = true := by
    have point := List.all_eq_true.mp (byte_chunks ⟨offset.val / 320,chunkBound⟩)
      (offset.val % 320) (List.mem_range.mpr remainder)
    simpa only [coordinate,if_pos offset.isLt] using point
  simp only [P1Capture.Program.view,
    show offset.val < image.size from by rw [X86P1SibStoreCapture.byte_extent]; exact offset.isLt, if_true,valid]

private theorem low_physical (value : Nat) (small : value < 2 ^ 47) :
    ((BitVec.ofNat 48 value).signExtend 52).toNat = value := by
  have width : value < 2 ^ 48 := by omega
  have natural : (BitVec.ofNat 48 value).toNat = value := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt width]
  have sign : (BitVec.ofNat 48 value).msb = false := by
    apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    rw [natural]
    omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false sign,BitVec.toNat_setWidth_of_le (by decide),natural]

private theorem loaded (start : Nat) (pointer : Word) : X86P1LoadCapture.Loaded image (placedAt start pointer) 4096 := by
  intro offset within
  rw [X86P1SibStoreCapture.byte_extent] at within
  rw [image_byte ⟨offset,within⟩]
  have observed := cell start pointer ⟨offset,by omega⟩
  simp only [cellAddress,cellByte,if_pos within] at observed
  have physical : ((address 4096 offset).signExtend 52).toNat = 4096 + offset := by
    change ((BitVec.ofNat 48 (4096 + offset)).signExtend 52).toNat = 4096 + offset
    exact low_physical _ (by omega)
  simpa only [physical] using observed

private theorem register_known (start : Nat) (pointer : Word) (register : Fin 12) :
    readback view.modes (placedAt start pointer) (.register register) = some (valuesAt pointer (.register register)) := by
  have initial := entry.known (.register register) (entry.view.registers register)
  fin_cases register
  all_goals
    simp [readback, Registers.logicalSlot, lookup, placed, Registers.canonical,
      Registers.Placement.resolve, key, placedAt, valuesAt, Std.ExtDHashMap.get?_insert] at initial ⊢
    first | exact initial | rfl

private theorem frame_pointer (start : Nat) (pointer : Word) : lookup (placedAt start pointer) 7 = some (32768#64) :=
  register_known start pointer 0

private theorem descriptor_byte (start : Nat) (pointer : Word) (offset : Fin 16) :
    memory (placedAt start pointer) (32848 + offset.val) = some (if offset.val < 8 then
      (36864#64).extractLsb' (8 * offset.val) 8 else (16#64).extractLsb' (8 * (offset.val - 8)) 8) := by
  have codePast : ¬3778 + offset.val < 3778 := by omega
  have capInside : 3778 + offset.val < 3794 := by have := offset.isLt; omega
  have coordinate : 32848 + (3778 + offset.val) - 3778 = 32848 + offset.val := by omega
  have baseTest : (3778 + offset.val < 3786) ↔ offset.val < 8 := by omega
  have baseIndex : 3778 + offset.val - 3778 = offset.val := Nat.add_sub_cancel_left 3778 offset.val
  have lengthIndex : 3778 + offset.val - 3786 = offset.val - 8 := Nat.add_sub_add_left 3778 offset.val 8
  have observed := cell start pointer ⟨3778 + offset.val,by have := offset.isLt; omega⟩
  simpa only [memory,cellAddress,cellByte,if_neg codePast,if_pos capInside,coordinate,baseTest,baseIndex,lengthIndex] using observed

private theorem base_word (start : Nat) (pointer : Word) :
    wordAt? (memory (placedAt start pointer)) (32848#64) = some (36864#64) := by
  apply wordAt?_known _ _ _ (by decide)
  intro offset within
  have point : ∀ offset : Fin 8, X86CanonicalSpan.physicalKey ((32848#64) + BitVec.ofNat 64 offset.val) =
      32848 + offset.val := by decide
  rw [point ⟨offset,within⟩]
  simpa only [if_pos within] using descriptor_byte start pointer ⟨offset,by omega⟩

private theorem length_word (start : Nat) (pointer : Word) :
    wordAt? (memory (placedAt start pointer)) (32856#64) = some (16#64) := by
  apply wordAt?_known _ _ _ (by decide)
  intro offset within
  have point : ∀ offset : Fin 8, X86CanonicalSpan.physicalKey ((32856#64) + BitVec.ofNat 64 offset.val) =
      32856 + offset.val := by decide
  rw [point ⟨offset,within⟩]
  have observed := descriptor_byte start pointer ⟨offset + 8,by omega⟩
  have coordinate : 32848 + (offset + 8) = 32856 + offset := by omega
  simpa only [coordinate,if_neg (by omega : ¬offset + 8 < 8),Nat.add_sub_cancel_right] using observed

private theorem data_byte (start : Nat) (pointer : Word) (offset : Fin 16) :
    memory (placedAt start pointer) (36864 + offset.val) = some (0xa5#8) := by
  have codePast : ¬3794 + offset.val < 3778 := by omega
  have descriptorPast : ¬3794 + offset.val < 3794 := by omega
  have basePast : ¬3794 + offset.val < 3786 := by omega
  have coordinate : 36864 + (3794 + offset.val) - 3794 = 36864 + offset.val := by omega
  have observed := cell start pointer ⟨3794 + offset.val,by have := offset.isLt; omega⟩
  simpa only [memory,cellAddress,cellByte,if_neg codePast,if_neg descriptorPast,if_neg basePast,coordinate] using observed

private theorem known (start : Nat) (pointer : Word) : ∀ observed ∈ view.keys,
    readback view.modes (placedAt start pointer) observed = some (valuesAt pointer observed) := by
  intro observed member
  rcases Finset.mem_union.mp member with registerMember | remaining
  · obtain ⟨name, _member, rfl⟩ := Finset.mem_image.mp registerMember
    exact register_known start pointer name
  · rcases Finset.mem_union.mp remaining with descriptor | byte
    · simp only [Finset.mem_insert,Finset.mem_singleton] at descriptor
      rcases descriptor with rfl | rfl | rfl
      · simpa [readback,field?,frame_pointer,valuesAt] using base_word start pointer
      · simpa [readback,field?,frame_pointer,valuesAt] using length_word start pointer
      · rfl
    · obtain ⟨offset,within,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp byte)
      have bound : offset < 16 := List.mem_range.mp within
      change readback view.modes (placedAt start pointer) (.byte (36864 + offset)) = some ((0xa5#8).zeroExtend 64)
      apply readback_byte_known
      · omega
      · exact (show ∀ index : Fin 16, X86CanonicalSpan.Canonical (BitVec.ofNat 64 (36864 + index.val)) from by decide) ⟨offset,bound⟩
      · have point : ∀ index : Fin 16, X86CanonicalSpan.physicalKey (BitVec.ofNat 64 (36864 + index.val)) = 36864 + index.val := by decide
        rw [point ⟨offset,bound⟩]
        exact data_byte start pointer ⟨offset,bound⟩

private theorem code_location (offset : Nat) (small : offset < 8192) : (address 4096 offset).toInt = 4096 + offset :=
  address_toInt 4096 (extent := offset) (by decide) (by omega) offset (Nat.le_refl _)

private noncomputable def origin (start : Nat) (pointer : Word) (small : start < 4096) :
    X86LegacyFetch.Basis (placedAt start pointer) where
  address := address 4096 start
  opcodeAddress := address 4096 (start + 1)
  modrmAddress := address 4096 (start + 2)
  next := address 4096 (start + 3)
  control := entry.origin.control
  attributes := entry.origin.attributes
  step1 := by rw [code_location start (by omega), code_location (start + 1) (by omega)]; omega
  step2 := by rw [code_location start (by omega), code_location (start + 2) (by omega)]; omega
  step3 := by rw [code_location (start + 2) (by omega), code_location (start + 3) (by omega)]; omega
  status := by simpa [placedAt,Std.ExtDHashMap.get?_insert] using entry.origin.status
  fault := by simpa [placedAt,Std.ExtDHashMap.get?_insert] using entry.origin.fault
  msrs := by simpa [placedAt,Std.ExtDHashMap.get?_insert] using entry.origin.msrs
  segments := by simpa [placedAt,Std.ExtDHashMap.get?_insert] using entry.origin.segments
  longMode := entry.origin.longMode
  codeMode := entry.origin.codeMode
  application := by simpa [placedAt,Std.ExtDHashMap.get?_insert] using entry.origin.application
  rip := by simp [placedAt]

private theorem holds (start : Nat) (pointer : Word) : entry.profile.Holds (placedAt start pointer) := by
  refine ⟨?_,?_,entry.flags,?_,?_⟩
  · simpa [placedAt,Std.ExtDHashMap.get?_insert] using entry.holds.1
  · simpa [placedAt,Std.ExtDHashMap.get?_insert] using entry.holds.2.1
  · simpa [placedAt,Std.ExtDHashMap.get?_insert] using entry.flagsKnown
  · decide

private theorem flags_known (start : Nat) (pointer : Word) :
    (placedAt start pointer).regs.get? .rflags = some entry.flags := by
  simpa [placedAt,Std.ExtDHashMap.get?_insert] using entry.flagsKnown

private theorem quiet (start : Nat) (pointer : Word) :
    (placedAt start pointer).regs.get? .log_register_writes = some false := by
  simpa [placedAt,Std.ExtDHashMap.get?_insert] using entry.quiet

private theorem entry_small (copy : Copy) (slot : Fin 4) : X86P1SibStoreCapture.entryAt copy slot < 4096 := by
  cases copy <;> fin_cases slot <;> decide

private theorem entry_placed (copy : Copy) (slot : Fin 4) :
    (origin (X86P1SibStoreCapture.entryAt copy slot) 36864 (entry_small copy slot)).address.toInt =
      4096 + X86P1SibStoreCapture.entryAt copy slot :=
  code_location _ (by have := entry_small copy slot; omega)

private def location (slot : Fin 4) : Nat := 36864 + 4 * slot.val
private def produced (slot : Fin 4) : Key → Word
  | .byte address => (dataWord.extractLsb' (8 * (address - location slot)) 8).zeroExtend 64
  | _ => 0
private noncomputable def output (slot : Fin 4) : Key → Word := overwrite
  (P1Memory.storeRecipe .word32 5 10 11 (X86P1SibStoreCapture.displacement slot).toInt (location slot)).writes values (produced slot)

theorem source_firing (slot : Fin 4) :
    (CellEffects.profile [P1Memory.storeRecipe .word32 5 10 11
      (X86P1SibStoreCapture.displacement slot).toInt (location slot)]).theory.rewrites
      (encode view.keys values) (encode view.keys (output slot)) := by
  apply (source_store_iff .word32 5 10 11 (X86P1SibStoreCapture.displacement slot).toInt (location slot) view.keys values _).mpr
  refine ⟨produced slot, ?_, rfl, ?_, ?_, rfl⟩
  · fin_cases slot <;> decide
  · fin_cases slot <;> decide
  · fin_cases slot <;> decide

private theorem descriptors_apart (copy : Copy) (slot : Fin 4) :
    DescriptorsApart view (before copy slot) (X86SibStore.writes (target (location slot))) := by
  constructor
  · intro region member
    have same : region = 5 := by simpa [view,keys,Memory.byteKeys] using member
    subst region
    have reads : memoryReads (before copy slot) (.capabilityBase 5) = wordReads (32848#64) := by
      simp [memoryReads,fieldReads,frame_pointer]
    rw [reads]
    have separate : ∀ slot : Fin 4, Disjoint (wordReads (32848#64)) (X86SibStore.writes (target (location slot))) := by decide
    exact Finset.disjoint_left.mp (separate slot)
  · intro region member
    have same : region = 5 := by simpa [view,keys,Memory.byteKeys] using member
    subst region
    have reads : memoryReads (before copy slot) (.capabilityLength 5) = wordReads (32856#64) := by
      simp [memoryReads,fieldReads,frame_pointer]
    rw [reads]
    have separate : ∀ slot : Fin 4, Disjoint (wordReads (32856#64)) (X86SibStore.writes (target (location slot))) := by decide
    exact Finset.disjoint_left.mp (separate slot)

private theorem code_apart (slot : Fin 4) (index : Nat) (within : index < image.size) :
    ((address 4096 index).signExtend 52).toNat ∉ X86SibStore.writes (target (location slot)) := by
  have lower : ∀ slot : Fin 4, X86SibStore.writes (target (location slot)) ⊆ Finset.Icc 36864 36879 := by decide
  have physical : ((address 4096 index).signExtend 52).toNat = 4096 + index := by
    rw [X86P1SibStoreCapture.byte_extent] at within
    change ((BitVec.ofNat 48 (4096 + index)).signExtend 52).toNat = 4096 + index
    exact low_physical (4096 + index) (by omega)
  rw [physical]
  intro member
  have bound := (Finset.mem_Icc.mp (lower slot member)).1
  rw [X86P1SibStoreCapture.byte_extent] at within
  omega

private def protectedPost (_ : Unit) (world : World) : Prop :=
  (⟨.capabilityBase 5,36864⟩ : Cells.Cell Key) ∈ world

theorem source_wp (slot : Fin 4) :
    (Prog.prim slot : Prog (Fin 4) (fun _ => Unit) Unit).wp sourceAction protectedPost (encode view.keys values) := by
  have firing : (sourceAction slot).Step (encode view.keys values) () (encode view.keys (output slot)) :=
    (source_step_iff slot view.keys values _).mpr ⟨location slot,source_firing slot⟩
  refine ⟨⟨⟨encode view.keys (output slot),firing⟩,?_⟩,?_⟩
  · intro reply following _step
    exact Prog.safe_ret sourceAction reply following
  · intro reply following run
    obtain ⟨_answer,middle,step,_same,endpoint⟩ := run
    subst following
    obtain ⟨address,fired⟩ := (source_step_iff slot view.keys values middle).mp step
    obtain ⟨produced,_included,_mode,_access,_output,result⟩ :=
      (source_store_iff .word32 5 10 11 (X86P1SibStoreCapture.displacement slot).toInt address view.keys values middle).mp fired
    change (⟨.capabilityBase 5,36864⟩ : Cells.Cell Key) ∈ middle
    rw [result,Cells.mem_encode]
    refine ⟨by decide,?_⟩
    simp [overwrite,CellEffects.Recipe.writes,P1Memory.storeRecipe,P1Memory.storeSpec,Memory.Store.recipe,Memory.byteKeys,
      values,valuesAt]

theorem impossible_post_refused (slot : Fin 4) :
    ¬ (Prog.prim slot : Prog (Fin 4) (fun _ => Unit) Unit).wp sourceAction (fun _ _ => False) (encode view.keys values) := by
  intro wp
  have firing : (sourceAction slot).Step (encode view.keys values) () (encode view.keys (output slot)) :=
    (source_step_iff slot view.keys values _).mpr ⟨location slot,source_firing slot⟩
  exact wp.2 () _ ⟨(),_,firing,rfl,rfl⟩

theorem wp_and_native (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (copy : Copy) (slot : Fin 4) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ following machine flags,
      protectedPost () following ∧ represents view following machine ∧
      (X86FuelPrefix.fetches (X86P1SibStoreCapture.storeSteps slot)).run (before copy slot) = .ok () machine ∧
      machine.regs.get? .rflags = some flags ∧ X86P1LoadCapture.Loaded image machine 4096 ∧ entry.profile.Holds machine ∧
      ∀ count ≤ X86P1SibStoreCapture.storeSteps slot,
        ∀ observed, (X86FuelPrefix.fetches count).run (before copy slot) = .ok () observed →
          X86StateFrame.Frame X86Bounds.writes (X86SibStore.writes (target (location slot))) (before copy slot) observed := by
  have addressEq : sourceAddress slot values = location slot := rfl
  obtain ⟨following,machine,flags,post,_step,run,_frame,represented,flagsKnown,_rip,imageLoaded,_control,held,prefixes⟩ :=
    captured_store_wp other extra vector copy slot view values (before copy slot) 4096
      (origin _ _ (entry_small copy slot)) entry.profile entry.flags (known _ _)
      (by exact entry.frameArea) (by exact entry.frameAligned) (holds _ _) (flags_known _ _) (quiet _ _)
      (entry_placed copy slot) (by decide) (loaded _ _) (by decide) (by decide) (by decide)
      (Or.inr (by fin_cases slot <;> decide))
      (by simpa only [addressEq] using descriptors_apart copy slot) (by simpa only [addressEq] using code_apart slot)
      protectedPost (source_wp slot)
  exact ⟨following,machine,flags,post,represented,run,flagsKnown,imageLoaded,held,prefixes⟩

theorem source_and_native_prefixes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (copy : Copy) (slot : Fin 4) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ machine nextFlags,
      (X86FuelPrefix.fetches (X86P1SibStoreCapture.storeSteps slot)).run (before copy slot) = .ok () machine ∧
      represents view (encode view.keys (output slot)) machine ∧
      X86StateFrame.Frame X86Bounds.writes (X86SibStore.writes (target (location slot))) (before copy slot) machine ∧
      machine.regs.get? .rflags = some nextFlags ∧
      X86P1LoadCapture.Loaded image machine 4096 ∧ entry.profile.Holds machine ∧
      ∀ count ≤ X86P1SibStoreCapture.storeSteps slot,
        ∀ observed, (X86FuelPrefix.fetches count).run (before copy slot) = .ok () observed →
          X86StateFrame.Frame X86Bounds.writes (X86SibStore.writes (target (location slot))) (before copy slot) observed := by
  obtain ⟨machine,flags,run,frame,represented,flagsKnown,_rip,imageLoaded,_control,profileHeld,prefixes⟩ :=
    captured_store_profile_prefixes other extra vector copy slot view values (before copy slot) 4096
      (origin _ _ (entry_small copy slot)) entry.profile entry.flags (known _ _)
      (by exact entry.frameArea) (by exact entry.frameAligned) (holds _ _) (flags_known _ _) (quiet _ _)
      (entry_placed copy slot) (by decide) (loaded _ _) (by decide) (by decide) (by decide)
      (location slot) (encode view.keys (output slot)) (source_firing slot)
      (Or.inr (by fin_cases slot <;> decide)) (descriptors_apart copy slot) (code_apart slot)
  exact ⟨machine,flags,run,represented,frame,flagsKnown,imageLoaded,profileHeld,prefixes⟩

theorem source_and_native (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (copy : Copy) (slot : Fin 4) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ machine nextFlags,
      (X86FuelPrefix.fetches (X86P1SibStoreCapture.storeSteps slot)).run (before copy slot) = .ok () machine ∧
      represents view (encode view.keys (output slot)) machine ∧
      X86StateFrame.Frame X86Bounds.writes (X86SibStore.writes (target (location slot))) (before copy slot) machine ∧
      machine.regs.get? .rflags = some nextFlags ∧
      X86P1LoadCapture.Loaded image machine 4096 ∧ entry.profile.Holds machine := by
  obtain ⟨machine,flags,run,represented,frame,flagsKnown,imageLoaded,held,_prefixes⟩ :=
    source_and_native_prefixes other extra vector copy slot
  exact ⟨machine,flags,run,represented,frame,flagsKnown,imageLoaded,held⟩

theorem written_first_byte (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (copy : Copy) (slot : Fin 4) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ machine,
      (X86FuelPrefix.fetches (X86P1SibStoreCapture.storeSteps slot)).run (before copy slot) = .ok () machine ∧
      readback view.modes machine (.byte (location slot)) = some (0xff#64) ∧
      readback view.modes machine (.capabilityBase 5) = some (36864#64) ∧
      X86P1LoadCapture.Loaded image machine 4096 ∧ entry.profile.Holds machine := by
  obtain ⟨machine,_flags,run,represented,_frame,_flagsKnown,imageLoaded,profileHeld⟩ := source_and_native other extra vector copy slot
  obtain ⟨assigned,encoded,seen⟩ := represented
  have valuesEq (observed : Key) (member : observed ∈ view.keys) : assigned observed = output slot observed :=
    ((Cells.encode_le_iff view.keys view.keys assigned (output slot)).mp (le_of_eq encoded.symm)).2 observed member
  have point (observed : Key) (member : observed ∈ view.keys) : readback view.modes machine observed = some (output slot observed) :=
    (seen observed member).trans (congrArg some (valuesEq observed member))
  refine ⟨machine,run,?_,?_,imageLoaded,profileHeld⟩
  · have member : Memory.Key.byte (location slot) ∈ view.keys := by fin_cases slot <;> decide
    have read := point _ member
    have outputByte : output slot (.byte (location slot)) = (0xff#64) := by fin_cases slot <;> decide
    exact read.trans (congrArg some outputByte)
  · have read := point (.capabilityBase 5) (by decide)
    have outputBase : output slot (.capabilityBase 5) = (36864#64) := by fin_cases slot <;> decide
    exact read.trans (congrArg some outputBase)

theorem wrong_output_refused (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (copy : Copy) (slot : Fin 4) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ¬ ∃ machine,
      (X86FuelPrefix.fetches (X86P1SibStoreCapture.storeSteps slot)).run (before copy slot) = .ok () machine ∧
      readback view.modes machine (.byte (location slot)) = some (0#64) := by
  obtain ⟨machine,run,written,_rest⟩ := written_first_byte other extra vector copy slot
  rintro ⟨wrong,wrongRun,wrongRead⟩
  rw [run] at wrongRun
  cases wrongRun
  rw [written] at wrongRead
  contradiction

theorem omitted_prefix_write_refused (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (copy : Copy) (slot : Fin 4) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ¬ (∀ count ≤ X86P1SibStoreCapture.storeSteps slot,
      ∀ observed, (X86FuelPrefix.fetches count).run (before copy slot) = .ok () observed →
        X86StateFrame.Frame X86Bounds.writes ∅ (before copy slot) observed) := by
  obtain ⟨machine,run,written,_rest⟩ := written_first_byte other extra vector copy slot
  intro denied
  have frame := denied _ (Nat.le_refl _) machine run
  have unchanged := readback_framed view.modes (before copy slot) machine X86Bounds.writes ∅ frame (.byte (location slot))
    (by simp [registerReads]) (by simp)
  have previous : readback view.modes (before copy slot) (.byte (location slot)) = some ((0xa5#8).zeroExtend 64) :=
    known _ _ _ (by fin_cases slot <;> decide)
  rw [written,previous] at unchanged
  contradiction

private noncomputable def readonlyValues : Key → Word := Function.update values (.capabilityMode 5) 1

private def readonlyView : View := { view with modes := fun region => if region.val = 5 then 1 else 0 }

theorem readonly_represents (copy : Copy) (slot : Fin 4) :
    represents readonlyView (encode view.keys readonlyValues) (before copy slot) := by
  refine ⟨readonlyValues,rfl,?_⟩
  intro observed member
  by_cases changed : observed = .capabilityMode 5
  · subst observed
    rfl
  · have same : readback readonlyView.modes (before copy slot) observed = readback view.modes (before copy slot) observed := by
      cases observed with
      | register _ => rfl
      | byte _ => rfl
      | capabilityBase _ => rfl
      | capabilityLength _ => rfl
      | capabilityMode region =>
          have equal : region = 5 := by simpa [readonlyView,view,keys,Memory.byteKeys] using member
          exact False.elim (changed (congrArg Memory.Key.capabilityMode equal))
    rw [same]
    simpa only [readonlyValues,Function.update_of_ne changed] using known _ _ observed member

theorem readonly_store_refused (slot : Fin 4) :
    ¬ ∃ following, (CellEffects.profile [P1Memory.storeRecipe .word32 5 10 11
      (X86P1SibStoreCapture.displacement slot).toInt (location slot)]).theory.rewrites
      (encode view.keys readonlyValues) following := by
  rintro ⟨following,firing⟩
  obtain ⟨_produced,_included,mode,_rest⟩ :=
    (source_store_iff .word32 5 10 11 (X86P1SibStoreCapture.displacement slot).toInt (location slot) view.keys readonlyValues following).mp firing
  change (1#64) = (2#64) at mode
  contradiction

private noncomputable def aliasAfter : State := X86SibStore.result (before .fast 0) (32848#48) (4096#48) (42#64)

private theorem alias_word : wordAt? (memory aliasAfter) (32848#64) = some (42#64) := by
  apply wordAt?_known _ _ _ (by decide)
  intro offset within
  have physical : ∀ index : Fin 8, X86CanonicalSpan.physicalKey ((32848#64) + BitVec.ofNat 64 index.val) =
      32848 + index.val := by decide
  rw [physical ⟨offset,within⟩]
  by_cases low : offset < 4
  · have point : ∀ index : Fin 4, X86WriteWords.physicalAddress (32848#48) index.val = 32848 + index.val := by decide
    have observed := X86DataStore.byte_readback (before .fast 0) false (32848#48) (4096#48) (42#64)
      (by decide) offset low
    rw [point ⟨offset,low⟩, low32_extract (42#64) ⟨offset,low⟩] at observed
    exact observed
  · have outside : ∀ index : Fin 8, 4 ≤ index.val →
        32848 + index.val ∉ X86SibStore.writes (32848#48) := by decide
    have frame := X86DataStore.result_frame false (before .fast 0) (32848#48) (4096#48) (42#64)
    change (X86DataStore.result false (before .fast 0) (32848#48) (4096#48) (42#64)).mem.get? (32848 + offset) = _
    have notWritten : 32848 + offset ∉ X86SibStore.writes (32848#48) :=
      outside ⟨offset,within⟩ (by change 4 ≤ offset; omega)
    rw [frame.memory (32848 + offset) notWritten]
    have observed := descriptor_byte (X86P1SibStoreCapture.entryAt .fast 0) 36864 ⟨offset,by omega⟩
    have same : ∀ index : Fin 8, 4 ≤ index.val →
        (36864#64).extractLsb' (8 * index.val) 8 = (42#64).extractLsb' (8 * index.val) 8 := by decide
    rw [if_pos within, same ⟨offset,within⟩ (by change 4 ≤ offset; omega)] at observed
    exact observed

theorem descriptor_alias_changes :
    X86StateFrame.Frame {.rip} (X86SibStore.writes (32848#48)) (before .fast 0) aliasAfter ∧
      readback view.modes (before .fast 0) (.capabilityBase 5) = some (36864#64) ∧
      readback view.modes aliasAfter (.capabilityBase 5) = some (42#64) ∧
      ¬ readback view.modes aliasAfter (.capabilityBase 5) = readback view.modes (before .fast 0) (.capabilityBase 5) := by
  have frame := X86DataStore.result_frame false (before .fast 0) (32848#48) (4096#48) (42#64)
  have beforeKnown : readback view.modes (before .fast 0) (.capabilityBase 5) = some (36864#64) := known _ _ _ (by decide)
  have pointer : lookup aliasAfter 7 = some (32768#64) := (frame.lookup 7 (by decide)).trans (frame_pointer _ _)
  have afterKnown : readback view.modes aliasAfter (.capabilityBase 5) = some (42#64) := by
    simpa [readback,field?,pointer] using alias_word
  refine ⟨frame,beforeKnown,afterKnown,?_⟩
  rw [beforeKnown,afterKnown]
  decide

theorem descriptor_alias_not_protected : ¬ DescriptorsApart view (before .fast 0) (X86SibStore.writes (32848#48)) := by
  intro descriptors
  have read : 32848 ∈ memoryReads (before .fast 0) (.capabilityBase 5) := by
    simp only [memoryReads,show ¬(5 : Nat) = 255 from by decide,show (5 : Nat) < 9 from by decide,if_false,if_true,
      fieldReads,frame_pointer]
    apply Finset.mem_image.mpr
    exact ⟨0,by decide,rfl⟩
  exact descriptors.1 5 (by decide) 32848 read (by decide)

private theorem end_unmapped (start : Nat) (pointer : Word) : (placedAt start pointer).mem.get? 36880 = none := by
  have absent : (cells.map Prod.fst).contains 36880 = false := by
    apply Bool.eq_false_iff.mpr
    intro present
    have member := List.contains_iff_mem.mp present
    simp only [cells,List.map_map,Function.comp_def] at member
    obtain ⟨index,bounded,coordinate⟩ := List.mem_map.mp member
    have within : index < 3810 := List.mem_range.mp bounded
    unfold cellAddress at coordinate
    split_ifs at coordinate <;> omega
  simpa only [placedAt,Std.ExtHashMap.get?_eq_getElem?] using
    Std.ExtHashMap.getElem?_ofList_of_contains_eq_false absent

/-- R12 at the end of region five, at the zero-offset MOV of `copy`. -/
private noncomputable abbrev escaped (copy : Copy) : State := placedAt (X86P1SibStoreCapture.tailAt copy 0) 36880

/-- The zero-offset MOV checks nothing itself. The state represents a source configuration in which
the zero-offset store is refused, yet the one fetched MOV completes and writes the first byte past the
region, where nothing was mapped. Its safety rests on the address guard of its copy. -/
theorem unguarded_direct_store_escapes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (copy : Copy) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    represents view (encode view.keys (valuesAt 36880)) (escaped copy) ∧
      (¬ ∃ address following, (CellEffects.profile [P1Memory.storeRecipe .word32 5 10 11
        (X86P1SibStoreCapture.displacement 0).toInt address]).theory.rewrites (encode view.keys (valuesAt 36880)) following) ∧
      (escaped copy).mem.get? 36880 = none ∧
      ∃ machine, (X86FuelPrefix.fetches 1).run (escaped copy) = .ok () machine ∧
        machine.mem.get? 36880 = some (0xff#8) := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  have small : X86P1SibStoreCapture.tailAt copy 0 < 4096 := by cases copy <;> decide
  refine ⟨⟨valuesAt 36880,rfl,known _ _⟩,?_,end_unmapped _ _,?_⟩
  · rintro ⟨address,following,firing⟩
    obtain ⟨_produced,_included,_mode,access,_rest⟩ :=
      (source_store_iff .word32 5 10 11 (X86P1SibStoreCapture.displacement 0).toInt address view.keys
        (valuesAt 36880) following).mp firing
    have refused : Memory.access? (36864#64) (16#64) (36880#64) (X86P1SibStoreCapture.displacement 0).toInt 4 = none := by
      decide
    exact absurd (refused.symm.trans access) (by simp)
  · have separate : ∀ index < image.size,
        ((address 4096 index).signExtend 52).toNat ∉ X86SibStore.writes (36880#48) := by
      intro index within
      have physical : ((address 4096 index).signExtend 52).toNat = 4096 + index := by
        rw [X86P1SibStoreCapture.byte_extent] at within
        change ((BitVec.ofNat 48 (4096 + index)).signExtend 52).toNat = 4096 + index
        exact low_physical (4096 + index) (by omega)
      have lower : X86SibStore.writes (36880#48) ⊆ Finset.Icc 36880 36883 := by decide
      rw [physical]
      intro member
      have bound := (Finset.mem_Icc.mp (lower member)).1
      rw [X86P1SibStoreCapture.byte_extent] at within
      omega
    obtain ⟨machine,run,_frame,resultEq,_image⟩ := X86P1SibStoreCapture.executes (X86Bounds.handlers other extra) vector
      copy 0 (escaped copy) 4096 (origin _ 36880 small) (code_location _ (by omega)) (loaded _ _)
      entry.profile.visible entry.profile.controls (36880#64) dataWord entry.flags (36880#48)
      (register_known _ 36880 10) (register_known _ 36880 11) (holds _ _).1 (flags_known _ _) (holds _ _).2.1
      (quiet _ _) (by
        change (address 4096 (X86P1SibStoreCapture.tailAt copy 0)).toInt + 8 < (2 ^ 47 : Int)
        rw [code_location _ (by omega)]
        omega) (by decide) (by decide)
      (Or.inr (by decide)) separate
    refine ⟨machine,run,?_⟩
    rw [resultEq]
    have written := X86DataStore.byte_readback (escaped copy) false (36880#48)
      (address (origin _ 36880 small).address.toInt 8) dataWord (by decide) 0 (by decide)
    rw [show X86WriteWords.physicalAddress (36880#48) 0 = 36880 from by decide,
      low32_extract dataWord ⟨0,by decide⟩] at written
    exact written

structure EntryFixture (copy : Copy) (slot : Fin 4) where
  view : View
  values : Key → Word
  native : State
  origin : X86LegacyFetch.Basis native
  profile : X86Readiness.Profile
  flags : BitVec 32
  known : ∀ observed ∈ view.keys, readback view.modes native observed = some (values observed)
  basePresent : Memory.Key.capabilityBase 5 ∈ view.keys
  lengthPresent : Memory.Key.capabilityLength 5 ∈ view.keys
  modePresent : Memory.Key.capabilityMode 5 ∈ view.keys
  frameEq : values (.register 0) = 32768
  baseEq : values (.capabilityBase 5) = 36864
  lengthEq : values (.capabilityLength 5) = 16
  pointerEq : values (.register 10) = 36864
  modeEq : values (.capabilityMode 5) = 2
  frameArea : X86CanonicalSpan.Area (values (.register 0)) frameLayout.size
  frameAligned : (values (.register 0)).toNat % 8 = 0
  holds : profile.Holds native
  flagsKnown : native.regs.get? .rflags = some flags
  quiet : native.regs.get? .log_register_writes = some false
  placed : origin.address.toInt = 4096 + X86P1SibStoreCapture.entryAt copy slot
  loaded : X86P1LoadCapture.Loaded X86P1SibStoreCapture.image native 4096
  endUnmapped : native.mem.get? 36880 = none

noncomputable def entryFixture (copy : Copy) (slot : Fin 4) : EntryFixture copy slot where
  view := view
  values := values
  native := before copy slot
  origin := origin _ _ (entry_small copy slot)
  profile := entry.profile
  flags := entry.flags
  known := known _ _
  basePresent := by decide
  lengthPresent := by decide
  modePresent := by decide
  frameEq := by decide
  baseEq := rfl
  lengthEq := rfl
  pointerEq := rfl
  modeEq := rfl
  frameArea := by apply X86CanonicalSpan.area_low; decide
  frameAligned := by decide
  holds := holds _ _
  flagsKnown := flags_known _ _
  quiet := quiet _ _
  placed := entry_placed copy slot
  loaded := loaded _ _
  endUnmapped := end_unmapped _ _

/-! ### The zero-offset store's guard -/

private theorem guard_small (copy : Copy) : X86P1SibStoreCapture.guardAt copy < 4096 := by
  cases copy <;> decide

private theorem base_int : (4096#48 : BitVec 48).toInt = 4096 := by decide

/-- The zero-offset store's guard at `guardAt copy`, with RAX, the scaled index, set to `index`. -/
noncomputable def guardState (copy : Copy) (index : Word) : State :=
  put (placedAt (X86P1SibStoreCapture.guardAt copy) 36864) 0 index

/-- Region five's length word in the frame, at `0x58` from RDI. -/
def lengthCell : X86PlacedMemory.Cell (32768#64) 0x58#32 where
  address := 32856#48
  effective := by decide
  upper := by decide
  aligned := by decide

structure GuardFixture (copy : Copy) (index : Word) where
  point : X86PlacedInstruction.At image.view (guardState copy index) 4096#48 (X86P1SibStoreCapture.guardAt copy)
  controls : X86PlacedMemory.Controls (guardState copy index)
  regionBase : Word
  frameKnown : lookup (guardState copy index) 7 = some (32768#64)
  baseKnown : lookup (guardState copy index) 1 = some regionBase
  indexKnown : lookup (guardState copy index) 0 = some index
  lengthRead : X86PlacedMemory.Reads (guardState copy index) lengthCell.address (16#64)
  loaded : X86P1LoadCapture.Loaded image (guardState copy index) 4096

private theorem guard_loaded (copy : Copy) (index : Word) :
    X86P1LoadCapture.Loaded image (guardState copy index) 4096 :=
  loaded (X86P1SibStoreCapture.guardAt copy) 36864

private theorem guard_length (copy : Copy) (index : Word) :
    X86PlacedMemory.Reads (guardState copy index) lengthCell.address (16#64) := by
  intro offset within
  have point : ∀ offset : Fin 8, X86WriteWords.physicalAddress (32856#48) offset.val = 32856 + offset.val := by
    decide
  rw [show lengthCell.address = 32856#48 from rfl, point ⟨offset,within⟩]
  have observed := descriptor_byte (X86P1SibStoreCapture.guardAt copy) 36864 ⟨offset + 8,by omega⟩
  have coordinate : 32848 + (offset + 8) = 32856 + offset := by omega
  change (placedAt (X86P1SibStoreCapture.guardAt copy) 36864).mem.get? (32856 + offset) = _
  simpa only [memory,coordinate,if_neg (by omega : ¬offset + 8 < 8),Nat.add_sub_cancel_right] using observed

private noncomputable def guardOrigin (copy : Copy) :=
  origin (X86P1SibStoreCapture.guardAt copy) 36864 (guard_small copy)

noncomputable def guardFixture (copy : Copy) (index : Word) : GuardFixture copy index where
  point := {
    mode := { X86PlainFetch.Facts.ofBasis (guardOrigin copy) with
      status := (put_other_register _ 0 _ .ms_reg (by decide)).trans (guardOrigin copy).status
      fault := (put_other_register _ 0 _ .fault_reg (by decide)).trans (guardOrigin copy).fault
      msrs := (put_other_register _ 0 _ .msrs (by decide)).trans (guardOrigin copy).msrs
      segments := (put_other_register _ 0 _ .seg_hidden_attrs (by decide)).trans (guardOrigin copy).segments
      application := (put_other_register _ 0 _ .app_view (by decide)).trans (guardOrigin copy).application }
    placed := by
      rw [base_int]
      exact X86P1SibStoreCapture.placed_of_loaded _ 4096 (guard_loaded copy index)
    upper := by
      rw [base_int]
      change (4096 : Int) + image.size < 2 ^ 47
      rw [X86P1SibStoreCapture.byte_extent]
      decide
    rip := by
      rw [base_int]
      exact (put_other_register _ 0 _ .rip (by decide)).trans (guardOrigin copy).rip
    flags := entry.flags
    knownFlags := (put_flags _ 0 _).trans (flags_known _ _)
    quiet := (put_other_register _ 0 _ .log_register_writes (by decide)).trans (quiet _ _) }
  controls := {
    visible := entry.profile.visible
    controls := entry.profile.controls
    visibleKnown := (put_other_register _ 0 _ .seg_visibles (by decide)).trans (holds _ _).2.1
    controlsKnown := (put_other_register _ 0 _ .ctrs (by decide)).trans (holds _ _).1 }
  regionBase := valuesAt 36864 (.register 3)
  frameKnown := (lookup_put_other _ 0 7 _ (by decide)).trans (frame_pointer _ _)
  baseKnown := (lookup_put_other _ 0 1 _ (by decide)).trans (register_known _ _ 3)
  indexKnown := lookup_put_same _ 0 _
  lengthRead := guard_length copy index
  loaded := guard_loaded copy index

end Controls

end Mettapedia.Machines.TIsa.X86MemoryAdapterStore
