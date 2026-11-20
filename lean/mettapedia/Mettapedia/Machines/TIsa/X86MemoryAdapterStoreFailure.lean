import Mettapedia.Machines.TIsa.X86MemoryAdapterStore
import Mettapedia.Machines.TIsa.X86P1InvalidCapture

/-!
# Actual adapter STORE rejection and its shared invalid-input handler

The source instruction supplies the existing bounds-failure recipe. Its guard
requires no bytes at the rejected address. In both copies of the loop body, the
bounds prefix of each positive-offset store reaches the actual shared handler;
the handler writes the two outcome words and reaches the actual exit. The
zero-offset store has no bounds prefix: its address guard rejects into the same
handler. Loaded bytes and physical exclusions remain explicit. Public ABI
composition, other outcomes and the generic emitter theorem are separate
obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86MemoryAdapterStoreFailure
open _root_.X86Registers X86RegisterRefinement X86Execution X86MemoryView X86MemoryReadback
open Cells CellEffects X86MemoryStore
open X86P1SibStoreCapture (Copy)
local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable abbrev image := X86P1SibStoreCapture.image

def failureRecipe (slot : Fin 4) : Recipe Key :=
  P1Memory.boundsFailureRecipe true .word32 5 10 (X86P1SibStoreCapture.displacement slot).toInt

theorem captured_edges (slot : Fin 4) (activation address : Nat) (point next invalid : Word) :
    (image.source.body.atPath (X86P1SibStoreCapture.sourcePath slot)).bind
      (fun statement => match statement with
        | .instruction instruction => P1Memory.memoryEdges? instruction address activation point next invalid
        | _ => none) =
      some [Control.Edge.mk activation point next
        (P1Memory.storeRecipe .word32 5 10 11 (X86P1SibStoreCapture.displacement slot).toInt address),
        Control.Edge.mk activation point invalid (failureRecipe slot)] := by
  rw [X86P1SibStoreCapture.source_instruction]
  rfl

theorem source_failure_iff (slot : Fin 4) (keys : Finset Key) (values : Key → Word) (following : World) :
    (CellEffects.profile [failureRecipe slot]).theory.rewrites (encode keys values) following ↔
      (failureRecipe slot).support ⊆ keys ∧ values (.capabilityMode 5) = 2 ∧
      Memory.access? (values (.capabilityBase 5)) (values (.capabilityLength 5))
        (values (.register 10)) (X86P1SibStoreCapture.displacement slot).toInt 4 = none ∧
      following = encode keys values := by
  rw [profile_rewrite_iff]
  constructor
  · rintro ⟨recipe,member,produced,included,guarded,endpoint⟩
    have same : recipe = failureRecipe slot := List.mem_singleton.mp member
    subst recipe
    obtain ⟨mode,rejected⟩ := (P1Memory.bounds_failure_guard_iff true .word32 5 10
      (X86P1SibStoreCapture.displacement slot).toInt values produced).mp guarded
    refine ⟨included,mode,rejected,?_⟩
    have unchanged : CellEffects.overwrite (failureRecipe slot).writes values produced = values := by
      funext observed
      change (if observed ∈ (∅ : Finset Key) then produced observed else values observed) = values observed
      exact if_neg (Finset.notMem_empty observed)
    exact endpoint.trans (congrArg (encode keys) unchanged)
  · rintro ⟨included,mode,rejected,rfl⟩
    refine ⟨failureRecipe slot,by simp,values,included,?_,?_⟩
    · exact (P1Memory.bounds_failure_guard_iff true .word32 5 10
        (X86P1SibStoreCapture.displacement slot).toInt values values).mpr ⟨mode,rejected⟩
    · apply congrArg (encode keys)
      funext observed
      change values observed = (if observed ∈ (∅ : Finset Key) then values observed else values observed)
      exact (if_neg (Finset.notMem_empty observed)).symm

theorem failure_excludes_store (slot : Fin 4) (keys : Finset Key) (values : Key → Word)
    (rejected following : World) (address : Nat)
    (failure : (CellEffects.profile [failureRecipe slot]).theory.rewrites (encode keys values) rejected) :
    ¬ (CellEffects.profile [P1Memory.storeRecipe .word32 5 10 11
      (X86P1SibStoreCapture.displacement slot).toInt address]).theory.rewrites (encode keys values) following := by
  obtain ⟨_included,_mode,outside,_endpoint⟩ := (source_failure_iff slot keys values rejected).mp failure
  intro success
  obtain ⟨_produced,_support,_writable,inside,_output,_result⟩ :=
    (X86MemoryStore.source_store_iff .word32 5 10 11 (X86P1SibStoreCapture.displacement slot).toInt
      address keys values following).mp success
  change Memory.access? (values (.capabilityBase 5)) (values (.capabilityLength 5))
    (values (.register 10)) (X86P1SibStoreCapture.displacement slot).toInt 4 = some address at inside
  rw [outside] at inside
  cases inside

/-- The shared handler ends at the exit, 28 bytes before the end of the image. -/
def exitAt : Nat := X86P1SibStoreCapture.invalidEntry + 29

theorem exit_from_end : exitAt + 28 = image.size := by
  rw [X86P1SibStoreCapture.byte_extent]
  rfl

theorem invalid_bytes (byte : Fin 29) :
    image.view.read (X86P1SibStoreCapture.invalidEntry + byte.val) =
      (X86P1InvalidCapture.code[byte.val]?).map (BitVec.ofNat 8) := by
  fin_cases byte <;> kernel_reflexivity

theorem captured_reject (copy : Copy) (slot : Fin 3) :
    X86P1SibStoreCapture.spanStart copy slot + (X86P1SibStoreCapture.boundsLayout copy slot).reject =
      X86P1SibStoreCapture.invalidEntry := by
  cases copy <;> fin_cases slot <;> decide

/-- The bounds prefix of the store at source slot `slot.succ` rejects to the shared handler. -/
theorem failed_prefix (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
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
    (loaded : X86P1LoadCapture.Loaded image native base)
    (rangeFits : (values (.capabilityBase 5)).toNat + (values (.capabilityLength 5)).toNat < 2 ^ 64)
    (pointerLower : (values (.capabilityBase 5)).toNat ≤ (values (.register 10)).toNat)
    (pointerUpper : (values (.register 10)).toNat ≤ (values (.capabilityBase 5)).toNat + (values (.capabilityLength 5)).toNat)
    (following : World)
    (source : (CellEffects.profile [failureRecipe slot.succ]).theory.rewrites (encode view.keys values) following) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    following = encode view.keys values ∧
      ∃ after nextFlags,
        (X86FuelPrefix.fetches (X86Bounds.boundsSteps (X86P1SibStoreCapture.boundsLayout copy slot)
          (values (.capabilityBase 5)) (values (.register 10)) (values (.capabilityLength 5)))).run native = .ok () after ∧
        RegisterFrame X86Bounds.writes native after ∧
        (∀ observed, readback view.modes after observed = readback view.modes native observed) ∧
        after.regs.get? .rflags = some nextFlags ∧
        after.regs.get? .rip = some ((address base X86P1SibStoreCapture.invalidEntry).signExtend 64) ∧
        X86P1LoadCapture.Loaded image after base ∧ X86ControlFlags.Preserved native after ∧ profile.Holds after := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨included,_mode,rejected,same⟩ := (source_failure_iff slot.succ view.keys values following).mp source
  have basePresent : Memory.Key.capabilityBase 5 ∈ view.keys := by
    apply included
    simp [failureRecipe,P1Memory.boundsFailureRecipe,Recipe.support,Memory.capabilityKeys]
  have lengthPresent : Memory.Key.capabilityLength 5 ∈ view.keys := by
    apply included
    simp [failureRecipe,P1Memory.boundsFailureRecipe,Recipe.support,Memory.capabilityKeys]
  let layout := X86P1SibStoreCapture.boundsLayout copy slot
  have loadedHere := X86P1SibStoreCapture.prefix_loaded copy slot native base origin.address placed loaded
  obtain ⟨after,executed,framed,readbacks,pointer,control,held⟩ :=
    X86MemoryBounds.source_classifies_profile other extra vector view values native layout 10 profile flags
      rfl known basePresent lengthPresent frameArea frameAligned holds flagsKnown quiet origin
      (X86P1SibStoreCapture.boundsContext copy slot base origin.address placed upper) loadedHere rangeFits
      pointerLower pointerUpper
  have outside : ¬ Memory.access? (values (.capabilityBase 5)) (values (.capabilityLength 5))
      (values (.register 10)) (X86PositiveImmediate.immediate32 layout.offset).toInt layout.count.val =
      some ((values (.register 10)).toNat + layout.offset.val) := by
    change ¬ Memory.access? _ _ _ (X86P1SibStoreCapture.displacement slot.succ).toInt 4 = _
    intro present
    rw [rejected] at present
    cases present
  change after.regs.get? .rip = some ((if Memory.access? (values (.capabilityBase 5))
    (values (.capabilityLength 5)) (values (.register 10))
    (X86PositiveImmediate.immediate32 layout.offset).toInt layout.count.val =
    some ((values (.register 10)).toNat + layout.offset.val)
    then X86Bounds.position origin.address (X86Bounds.exitAt layout)
    else X86Bounds.position origin.address layout.reject).signExtend 64) at pointer
  rw [if_neg outside] at pointer
  have shifted : X86Bounds.position origin.address layout.reject =
      address base X86P1SibStoreCapture.invalidEntry := by
    unfold X86Bounds.position address
    rw [placed]
    congr 1
    have endpoint := captured_reject copy slot
    change X86P1SibStoreCapture.spanStart copy slot + layout.reject = X86P1SibStoreCapture.invalidEntry at endpoint
    omega
  obtain ⟨nextFlags,newKnown⟩ := X86ControlFlags.flags_present control flags flagsKnown
  refine ⟨same,after,nextFlags,executed,framed,readbacks,newKnown,?_,?_,control,held⟩
  · simpa only [shifted] using pointer
  · intro index within
    rw [framed.memory]
    exact loaded index within

noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  X86Bounds.handlers (X86UnconditionalJump.linked other) extra

theorem failure_installed (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86P1InvalidCapture.handlers (handlers other extra) = handlers other extra := rfl

/-- The source failure of the store at slot `slot.succ`: the bounds prefix, then the shared
handler, which writes outcome three and reaches the exit. -/
theorem failed_store (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
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
    (loaded : X86P1LoadCapture.Loaded image native base)
    (rangeFits : (values (.capabilityBase 5)).toNat + (values (.capabilityLength 5)).toNat < 2 ^ 64)
    (pointerLower : (values (.capabilityBase 5)).toNat ≤ (values (.register 10)).toNat)
    (pointerUpper : (values (.register 10)).toNat ≤ (values (.capabilityBase 5)).toNat + (values (.capabilityLength 5)).toNat)
    (receipt : X86FailureHandler.FrameFacts native)
    (apart : ∀ index < image.size,
      ((address base index).signExtend 52).toNat ∉ X86P1RefusedCapture.writes receipt)
    (following : World)
    (source : (CellEffects.profile [failureRecipe slot.succ]).theory.rewrites (encode view.keys values) following) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    following = encode view.keys values ∧
      ∃ after nextFlags,
        (X86FuelPrefix.fetches (X86Bounds.boundsSteps (X86P1SibStoreCapture.boundsLayout copy slot)
          (values (.capabilityBase 5)) (values (.register 10)) (values (.capabilityLength 5)) + 4)).run native = .ok () after ∧
        after.regs.get? .rip = some ((address base exitAt).signExtend 64) ∧ lookup after 0 = some (3#64) ∧
        (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress receipt.statusAddress byte) =
          some ((3#64).extractLsb' (8 * byte) 8)) ∧
        (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress receipt.resultAddress byte) =
          some ((3#64).extractLsb' (8 * byte) 8)) ∧
        X86StateFrame.Frame {.rax,.rip,.rflags,.r14,.r15} (X86P1RefusedCapture.writes receipt) native after ∧
        after.regs.get? .rflags = some nextFlags ∧ X86P1LoadCapture.Loaded image after base ∧
        X86ControlFlags.Preserved native after ∧ profile.Holds after ∧
        ∀ count ≤ X86Bounds.boundsSteps (X86P1SibStoreCapture.boundsLayout copy slot)
          (values (.capabilityBase 5)) (values (.register 10)) (values (.capabilityLength 5)) + 4,
          ∀ observed, (X86FuelPrefix.fetches count).run native = .ok () observed →
            X86StateFrame.Frame {.rax,.rip,.rflags,.r14,.r15} (X86P1RefusedCapture.writes receipt) native observed := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨same,middle,nextFlags,first,firstFrame,_readbacks,middleFlagsKnown,pointer,imageMiddle,control,held⟩ :=
    failed_prefix (X86UnconditionalJump.linked other) extra vector copy slot view values native base origin profile
      flags known frameArea frameAligned holds flagsKnown quiet placed upper loaded rangeFits pointerLower
      pointerUpper following source
  let layout := X86P1SibStoreCapture.boundsLayout copy slot
  let geometry := X86P1SibStoreCapture.boundsContext copy slot base origin.address placed upper
  have shifted : X86Bounds.position origin.address layout.reject =
      address base X86P1SibStoreCapture.invalidEntry := by
    unfold X86Bounds.position address
    rw [placed]
    congr 1
    have endpoint := captured_reject copy slot
    change X86P1SibStoreCapture.spanStart copy slot + layout.reject = X86P1SibStoreCapture.invalidEntry at endpoint
    omega
  let nextOrigin := X86Execution.rebase native middle origin (firstFrame.mono X86Bounds.writes_data)
    geometry.upper layout.reject
    (by
      change (X86P1SibStoreCapture.boundsLayout copy slot).reject + 3 ≤ 3778 - X86P1SibStoreCapture.spanStart copy slot
      cases copy <;> fin_cases slot <;> decide)
    (by
      change middle.regs.get? .rip = some ((X86Bounds.position origin.address layout.reject).signExtend 64)
      rw [shifted]
      exact pointer)
  have nextPlaced : nextOrigin.address.toInt = base + X86P1SibStoreCapture.invalidEntry := by
    change (X86Bounds.position origin.address layout.reject).toInt = _
    rw [X86Bounds.position_exact layout origin.address geometry layout.reject geometry.rejectWithin,placed]
    have endpoint := captured_reject copy slot
    change X86P1SibStoreCapture.spanStart copy slot + layout.reject = X86P1SibStoreCapture.invalidEntry at endpoint
    omega
  let nextFacts : X86FailureHandler.FrameFacts middle := {
    receipt with
    frameKnown := (firstFrame.lookup 7 (by decide)).trans receipt.frameKnown
    controlsKnown := (firstFrame.registers .ctrs (by decide)).trans receipt.controlsKnown
    visibleKnown := (firstFrame.registers .seg_visibles (by decide)).trans receipt.visibleKnown
    flags := nextFlags
    flagsKnown := middleFlagsKnown
    quiet := (firstFrame.registers .log_register_writes (by decide)).trans receipt.quiet }
  have extent : X86P1SibStoreCapture.invalidEntry + 32 < image.size := by
    rw [X86P1SibStoreCapture.byte_extent]
    decide
  have imageUpper : base + image.size < (2 ^ 47 : Int) := by
    simpa only [X86P1SibStoreCapture.byte_extent,Nat.cast_ofNat] using upper
  let handlerInput := X86P1InvalidCapture.imageInput image X86P1SibStoreCapture.invalidEntry invalid_bytes
    extent middle base nextOrigin nextFacts nextPlaced imageUpper imageMiddle apart
  have last := X86P1InvalidCapture.image_executes (handlers other extra) vector image
    X86P1SibStoreCapture.invalidEntry invalid_bytes extent middle base nextOrigin nextFacts nextPlaced imageUpper
    imageMiddle apart
  rw [failure_installed] at last
  obtain ⟨after,second,rip,value,status,output,lastFrame,finalFlags,imageAfter⟩ := last
  have combined : X86StateFrame.Frame {.rax,.rip,.rflags,.r14,.r15}
      (X86P1RefusedCapture.writes receipt) native after := by
    apply ((X86StateFrame.registerOnly firstFrame).trans lastFrame).mono
    · decide
    · simp only [Finset.empty_union]
      exact Finset.Subset.refl _
  have lastControl : X86ControlFlags.Preserved middle after := by
    unfold X86ControlFlags.Preserved
    rw [lastFrame.registers .rflags (by decide)]
  have preserved := control.trans lastControl
  refine ⟨same,after,nextFlags,X86FuelPrefix.fetches_then _ 4 native middle after first second,rip,value,status,
    output,combined,finalFlags,imageAfter,preserved,profile.after_control native after _ _ combined (by decide)
      preserved ⟨nextFlags,finalFlags⟩ holds,?_⟩
  intro count within observed candidate
  let bound := X86Bounds.boundsSteps layout (values (.capabilityBase 5))
    (values (.register 10)) (values (.capabilityLength 5))
  change count ≤ bound + 4 at within
  by_cases prefixOnly : count ≤ bound
  · obtain ⟨included,_mode,_rejected,_endpoint⟩ := (source_failure_iff slot.succ view.keys values following).mp source
    have basePresent : Memory.Key.capabilityBase 5 ∈ view.keys := by
      apply included
      simp [failureRecipe,P1Memory.boundsFailureRecipe,Recipe.support,Memory.capabilityKeys]
    have lengthPresent : Memory.Key.capabilityLength 5 ∈ view.keys := by
      apply included
      simp [failureRecipe,P1Memory.boundsFailureRecipe,Recipe.support,Memory.capabilityKeys]
    let facts := X86MemoryBounds.facts view values native layout 10 profile flags rfl known
      basePresent lengthPresent frameArea frameAligned holds flagsKnown quiet
    let input : X86Bounds.Inputs layout native origin := {
      facts with
      geometry := geometry
      loaded := X86P1SibStoreCapture.prefix_loaded copy slot native base origin.address placed loaded }
    have frame := X86Bounds.execution_prefix_frame (X86UnconditionalJump.linked other) extra vector
      layout native origin input count prefixOnly observed candidate
    exact (X86StateFrame.registerOnly frame).mono (by decide) (by simp)
  · have countEq : count = bound + (count - bound) := by omega
    rw [countEq] at candidate
    obtain ⟨intermediate,firstSeen,rest⟩ := X86BlockCompiler.fetches_split bound (count - bound) native observed candidate
    have equal := X86FuelPrefix.fetches_deterministic bound native middle intermediate first firstSeen
    subst intermediate
    have handlerFrame := X86P1InvalidCapture.execution_prefix_frame (handlers other extra) vector middle handlerInput
      (count - bound) (by omega) observed
    rw [failure_installed] at handlerFrame
    apply ((X86StateFrame.registerOnly firstFrame).trans (handlerFrame rest)).mono
    · decide
    · simp only [Finset.empty_union]
      exact Finset.Subset.refl _

/-! ## The zero-offset store

The zero-offset store has no bounds prefix (`X86P1SibStoreCapture.no_prefixed_zero_store`). Its
rejection is the address guard's, three fetches into the same shared handler. -/

noncomputable abbrev guardHandlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  X86IndexedAddress.handlers (X86P1InvalidCapture.handlers other) extra

theorem guard_failure_installed (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86P1InvalidCapture.handlers (guardHandlers other extra) = guardHandlers other extra := rfl

open X86PlacedInstruction (At) in
open X86PlacedMemory (Cell Reads) in
/-- Beyond region five's length, the zero-offset store's guard and the shared handler write
outcome three and reach the exit in seven fetches. -/
theorem guard_failed (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (copy : Copy) {native : State} {base : BitVec 48}
    (point : At image.view native base (X86P1SibStoreCapture.guardAt copy))
    (receipt : X86FailureHandler.FrameFacts native) (cell : Cell receipt.frame 0x58#32)
    (index length : Word) (indexKnown : lookup native 0 = some index)
    (lengthRead : Reads native cell.address length) (narrow : index.toNat < 2 ^ 32)
    (above : length.toNat < index.toNat * 4 + 4)
    (loaded : X86P1LoadCapture.Loaded image native base.toInt)
    (apart : ∀ index < image.size,
      ((address base.toInt index).signExtend 52).toNat ∉ X86P1RefusedCapture.writes receipt) :
    letI : OtherOpcodeHandlers := guardHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after,
      (X86FuelPrefix.fetches 7).run native = .ok () after ∧
      after.regs.get? .rip = some ((address base.toInt exitAt).signExtend 64) ∧ lookup after 0 = some (3#64) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress receipt.statusAddress byte) =
        some ((3#64).extractLsb' (8 * byte) 8)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress receipt.resultAddress byte) =
        some ((3#64).extractLsb' (8 * byte) 8)) ∧
      X86StateFrame.Frame {.rax,.rip,.rflags,.r15} (X86P1RefusedCapture.writes receipt) native after ∧
      X86P1LoadCapture.Loaded image after base.toInt := by
  let : OtherOpcodeHandlers := guardHandlers other extra
  let : VectorOpcodeHandlers := vector
  let controls : X86PlacedMemory.Controls native :=
    ⟨receipt.visible, receipt.controls, receipt.visibleKnown, receipt.controlsKnown⟩
  obtain ⟨middle,first,firstFrame,⟨target⟩⟩ :=
    X86P1SibStoreCapture.guard_rejects (X86P1InvalidCapture.handlers other) extra vector copy point controls
      receipt.frame index length cell receipt.frameKnown indexKnown lengthRead narrow above
  have imageMiddle : X86P1LoadCapture.Loaded image middle base.toInt := by
    intro offset within
    rw [firstFrame.memory]
    exact loaded offset within
  have entryInside : X86P1SibStoreCapture.invalidEntry + 3 ≤ image.view.size := by
    change _ ≤ image.size
    rw [X86P1SibStoreCapture.byte_extent]
    decide
  let nextOrigin := target.basis entryInside
  have nextPlaced : nextOrigin.address.toInt = base.toInt + X86P1SibStoreCapture.invalidEntry :=
    target.location _ (Nat.le_of_add_right_le entryInside)
  let nextFacts : X86FailureHandler.FrameFacts middle := {
    receipt with
    frameKnown := (firstFrame.lookup 7 (by decide)).trans receipt.frameKnown
    controlsKnown := (firstFrame.registers .ctrs (by decide)).trans receipt.controlsKnown
    visibleKnown := (firstFrame.registers .seg_visibles (by decide)).trans receipt.visibleKnown
    flags := target.flags
    flagsKnown := target.knownFlags
    quiet := (firstFrame.registers .log_register_writes (by decide)).trans receipt.quiet }
  have extent : X86P1SibStoreCapture.invalidEntry + 32 < image.size := by
    rw [X86P1SibStoreCapture.byte_extent]
    decide
  have last := X86P1InvalidCapture.image_executes (X86IndexedAddress.handlers (X86P1InvalidCapture.handlers other) extra)
    vector image X86P1SibStoreCapture.invalidEntry invalid_bytes extent middle base.toInt nextOrigin nextFacts
    nextPlaced target.upper imageMiddle apart
  rw [guard_failure_installed] at last
  obtain ⟨after,second,rip,value,status,output,lastFrame,_finalFlags,imageAfter⟩ := last
  refine ⟨after,X86FuelPrefix.fetches_then 3 4 native middle after first second,rip,value,status,output,?_,
    imageAfter⟩
  apply ((X86StateFrame.registerOnly firstFrame).trans lastFrame).mono
  · decide
  · simp only [Finset.empty_union]
    exact Finset.Subset.refl _

namespace Controls

private noncomputable abbrev entry (copy : Copy) (slot : Fin 3) :=
  X86MemoryAdapterStore.Controls.entryFixture copy slot.succ

private noncomputable def before (copy : Copy) (slot : Fin 3) : State := put (entry copy slot).native 12 (36880#64)
private noncomputable def values (copy : Copy) (slot : Fin 3) : Key → Word :=
  Function.update (entry copy slot).values (.register 10) (36880#64)

private theorem base_value (copy : Copy) (slot : Fin 3) : values copy slot (.capabilityBase 5) = 36864 := by
  rw [values,Function.update_of_ne (by decide : Memory.Key.capabilityBase 5 ≠ Memory.Key.register (10 : Fin 12))]
  exact (entry copy slot).baseEq

private theorem length_value (copy : Copy) (slot : Fin 3) : values copy slot (.capabilityLength 5) = 16 := by
  rw [values,Function.update_of_ne (by decide : Memory.Key.capabilityLength 5 ≠ Memory.Key.register (10 : Fin 12))]
  exact (entry copy slot).lengthEq

private theorem frame_value (copy : Copy) (slot : Fin 3) : values copy slot (.register 0) = 32768 := by
  rw [values,Function.update_of_ne (by decide : Memory.Key.register (0 : Fin 12) ≠ Memory.Key.register (10 : Fin 12))]
  exact (entry copy slot).frameEq

private theorem pointer_value (copy : Copy) (slot : Fin 3) : values copy slot (.register 10) = 36880 :=
  Function.update_self _ _ _

private theorem register_known (copy : Copy) (slot : Fin 3) (register : Fin 12) :
    readback (entry copy slot).view.modes (before copy slot) (.register register) =
      some (values copy slot (.register register)) := by
  have initial := (entry copy slot).known (.register register) ((entry copy slot).view.registers register)
  by_cases same : register = 10
  · subst register
    change lookup (put (entry copy slot).native 12 (36880#64)) 12 = some (36880#64)
    exact lookup_put_same _ 12 _
  · have mapped : X86MemoryFieldLoad.physical register ≠ 12 := by
      have mapping : ∀ register : Fin 12, X86MemoryFieldLoad.physical register = 12 ↔ register = 10 := by decide
      exact fun equal => same ((mapping register).mp equal)
    have different : Memory.Key.register register ≠ Memory.Key.register 10 := by
      intro equal
      cases equal
      exact same rfl
    change lookup (put (entry copy slot).native 12 (36880#64)) (X86MemoryFieldLoad.physical register) =
      some (Function.update (entry copy slot).values (.register 10) (36880#64) (.register register))
    rw [Function.update_of_ne different,lookup_put_other _ 12 _ _ mapped.symm]
    exact initial

private theorem known (copy : Copy) (slot : Fin 3) : ∀ observed ∈ (entry copy slot).view.keys,
    readback (entry copy slot).view.modes (before copy slot) observed = some (values copy slot observed) := by
  intro observed member
  by_cases register : ∃ name, observed = Memory.Key.register name
  · obtain ⟨name,rfl⟩ := register
    exact register_known copy slot name
  · have unchanged := readback_nonregister (entry copy slot).view.modes (entry copy slot).native (before copy slot) rfl
      (lookup_put_other _ 12 7 _ (by decide)) observed (by intro name same; exact register ⟨name,same⟩)
    rw [unchanged]
    have different : observed ≠ Memory.Key.register 10 := fun same => register ⟨10,same⟩
    simpa only [values,Function.update_of_ne different] using (entry copy slot).known observed member

private noncomputable def origin (copy : Copy) (slot : Fin 3) : X86LegacyFetch.Basis (before copy slot) where
  address := (entry copy slot).origin.address
  opcodeAddress := (entry copy slot).origin.opcodeAddress
  modrmAddress := (entry copy slot).origin.modrmAddress
  next := (entry copy slot).origin.next
  control := (entry copy slot).origin.control
  attributes := (entry copy slot).origin.attributes
  step1 := (entry copy slot).origin.step1
  step2 := (entry copy slot).origin.step2
  step3 := (entry copy slot).origin.step3
  status := (put_other_register _ 12 _ .ms_reg (by decide)).trans (entry copy slot).origin.status
  fault := (put_other_register _ 12 _ .fault_reg (by decide)).trans (entry copy slot).origin.fault
  msrs := (put_other_register _ 12 _ .msrs (by decide)).trans (entry copy slot).origin.msrs
  segments := (put_other_register _ 12 _ .seg_hidden_attrs (by decide)).trans (entry copy slot).origin.segments
  longMode := (entry copy slot).origin.longMode
  codeMode := (entry copy slot).origin.codeMode
  application := (put_other_register _ 12 _ .app_view (by decide)).trans (entry copy slot).origin.application
  rip := (put_other_register _ 12 _ .rip (by decide)).trans (entry copy slot).origin.rip

private theorem origin_placed (copy : Copy) (slot : Fin 3) :
    (origin copy slot).address.toInt = 4096 + X86P1SibStoreCapture.spanStart copy slot := by
  have placed := (entry copy slot).placed
  rw [X86P1SibStoreCapture.entryAt_succ] at placed
  exact placed

private theorem profile_holds (copy : Copy) (slot : Fin 3) : (entry copy slot).profile.Holds (before copy slot) := by
  obtain ⟨controls,visible,flags,flagsKnown,ac⟩ := (entry copy slot).holds
  exact ⟨(put_other_register _ 12 _ .ctrs (by decide)).trans controls,
    (put_other_register _ 12 _ .seg_visibles (by decide)).trans visible,
    flags,(put_flags _ 12 _).trans flagsKnown,ac⟩

private theorem frame_pointer (copy : Copy) (slot : Fin 3) : lookup (before copy slot) 7 = some (32768#64) := by
  have known := register_known copy slot 0
  change lookup (before copy slot) 7 = some (values copy slot (.register 0)) at known
  rw [frame_value] at known
  exact known.trans (congrArg some (show (32768 : Word) = (32768#64) from rfl))

private noncomputable def receipt (copy : Copy) (slot : Fin 3) : X86FailureHandler.FrameFacts (before copy slot) where
  frame := 32768
  statusAddress := 32912#48
  resultAddress := 32920#48
  statusUpper := by decide
  resultUpper := by decide
  statusEffective := by decide
  resultEffective := by decide
  statusAligned := by decide
  resultAligned := by decide
  controls := (entry copy slot).profile.controls
  visible := (entry copy slot).profile.visible
  flags := (entry copy slot).flags
  frameKnown := frame_pointer copy slot
  controlsKnown := (profile_holds copy slot).1
  visibleKnown := (profile_holds copy slot).2.1
  flagsKnown := (put_flags _ 12 _).trans (entry copy slot).flagsKnown
  quiet := (put_other_register _ 12 _ .log_register_writes (by decide)).trans (entry copy slot).quiet
  statusOutside := by
    intro byte within
    interval_cases byte <;> decide

theorem source_rejects (copy : Copy) (slot : Fin 3) :
    (CellEffects.profile [failureRecipe slot.succ]).theory.rewrites
      (encode (entry copy slot).view.keys (values copy slot)) (encode (entry copy slot).view.keys (values copy slot)) := by
  apply (source_failure_iff slot.succ _ _ _).mpr
  refine ⟨?_,?_,?_,rfl⟩
  · intro observed member
    have support : (failureRecipe slot.succ).support =
        {.capabilityBase 5,.capabilityLength 5,.capabilityMode 5,.register 10} := rfl
    rw [support] at member
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact (entry copy slot).basePresent
    · exact (entry copy slot).lengthPresent
    · exact (entry copy slot).modePresent
    · exact (entry copy slot).view.registers 10
  · rw [values,Function.update_of_ne (by decide : Memory.Key.capabilityMode 5 ≠ Memory.Key.register (10 : Fin 12))]
    exact (entry copy slot).modeEq
  · rw [base_value,length_value,pointer_value]
    fin_cases slot <;> decide

theorem rejected_data_unmapped (copy : Copy) (slot : Fin 3) : (before copy slot).mem.get? 36880 = none :=
  (entry copy slot).endUnmapped

private theorem code_physical (index : Nat) (within : index < 3778) :
    ((address 4096 index).signExtend 52).toNat = 4096 + index := by
  change ((BitVec.ofNat 48 (4096 + index)).signExtend 52).toNat = 4096 + index
  have small : 4096 + index < 2 ^ 48 := by omega
  have natural : (BitVec.ofNat 48 (4096 + index)).toNat = 4096 + index := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  have sign : (BitVec.ofNat 48 (4096 + index)).msb = false := by
    apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    rw [natural]
    omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false sign,BitVec.toNat_setWidth_of_le (by decide),natural]

private theorem code_apart (copy : Copy) (slot : Fin 3) : ∀ index < image.size,
    ((address 4096 index).signExtend 52).toNat ∉ X86P1RefusedCapture.writes (receipt copy slot) := by
  intro index within member
  rw [X86P1SibStoreCapture.byte_extent] at within
  have footprint : X86P1RefusedCapture.writes (receipt copy slot) = Finset.Icc 32912 32927 := by
    change X86WriteWords.written (32912#48) (List.range 8) ∪
      X86WriteWords.written (32920#48) (List.range 8) = Finset.Icc 32912 32927
    decide
  rw [code_physical index within,footprint] at member
  have lower := (Finset.mem_Icc.mp member).1
  omega

/-- The pointer at the end of region five: every positive-offset store, in both copies,
rejects to the shared handler and returns outcome three at the exit. -/
theorem runs_to_invalid (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (copy : Copy) (slot : Fin 3) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags,
      (X86FuelPrefix.fetches (X86Bounds.offsetSteps (X86P1SibStoreCapture.boundsLayout copy slot) + 9)).run
        (before copy slot) = .ok () after ∧
      lookup after 0 = some (3#64) ∧ after.regs.get? .rip = some ((address 4096 exitAt).signExtend 64) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress (32912#48) byte) =
        some ((3#64).extractLsb' (8 * byte) 8)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress (32920#48) byte) =
        some ((3#64).extractLsb' (8 * byte) 8)) ∧
      X86StateFrame.Frame {.rax,.rip,.rflags,.r14,.r15} (X86P1RefusedCapture.writes (receipt copy slot))
        (before copy slot) after ∧
      after.mem.get? 36880 = none ∧ after.regs.get? .rflags = some nextFlags ∧
      X86P1LoadCapture.Loaded image after 4096 ∧ (entry copy slot).profile.Holds after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨_same,after,nextFlags,run,pointer,value,status,output,framed,flagsKnown,loaded,_control,held,_prefixes⟩ :=
    failed_store other extra vector copy slot (entry copy slot).view (values copy slot) (before copy slot) 4096
      (origin copy slot) (entry copy slot).profile (entry copy slot).flags (known copy slot)
      (by rw [frame_value]; apply X86CanonicalSpan.area_low; decide)
      (by rw [frame_value]; decide) (profile_holds copy slot)
      ((put_flags _ 12 _).trans (entry copy slot).flagsKnown)
      ((put_other_register _ 12 _ .log_register_writes (by decide)).trans (entry copy slot).quiet)
      (origin_placed copy slot) (by decide) (entry copy slot).loaded
      (by rw [base_value,length_value]; decide)
      (by rw [base_value,pointer_value]; decide)
      (by rw [base_value,length_value,pointer_value]; decide)
      (receipt copy slot) (code_apart copy slot) _ (source_rejects copy slot)
  have count : X86Bounds.boundsSteps (X86P1SibStoreCapture.boundsLayout copy slot)
      (values copy slot (.capabilityBase 5)) (values copy slot (.register 10))
      (values copy slot (.capabilityLength 5)) =
      X86Bounds.offsetSteps (X86P1SibStoreCapture.boundsLayout copy slot) + 5 := by
    rw [base_value,pointer_value,length_value]
    cases copy <;> fin_cases slot <;> decide
  rw [count] at run
  refine ⟨after,nextFlags,?_,value,pointer,status,output,framed,?_,flagsKnown,loaded,held⟩
  · simpa only [Nat.add_assoc] using run
  · rw [framed.memory 36880 (by
      change 36880 ∉ X86WriteWords.written (32912#48) (List.range 8) ∪
        X86WriteWords.written (32920#48) (List.range 8)
      decide)]
    exact rejected_data_unmapped copy slot

theorem fired_outcome_refused (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (copy : Copy) (slot : Fin 3) (after : State) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches (X86Bounds.offsetSteps (X86P1SibStoreCapture.boundsLayout copy slot) + 9)).run
      (before copy slot) = .ok () after →
      lookup after 0 ≠ some (1#64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  intro candidate fired
  obtain ⟨proved,_flags,run,value,_rest⟩ := runs_to_invalid other extra vector copy slot
  have same := X86FuelPrefix.fetches_deterministic _ (before copy slot) proved after run candidate
  subst after
  rw [value] at fired
  cases fired

/-- The handler's jump displacement byte, `jmp +5` at `invalidEntry + 6`, changed to four. -/
private noncomputable def changedHandler : State :=
  { before .fast 0 with mem := (before .fast 0).mem.insert 7823 (4#8) }

theorem changed_handler_delta : ¬ X86P1LoadCapture.Loaded image changedHandler 4096 := by
  intro loaded
  have observed := loaded 3727 (by rw [X86P1SibStoreCapture.byte_extent]; decide)
  have encoded : image.view.read 3727 = some (5#8) := by kernel_reflexivity
  rw [encoded] at observed
  have coordinate : ((address 4096 3727).signExtend 52).toNat = 7823 := by decide
  rw [coordinate] at observed
  change ((before .fast 0).mem.insert 7823 (4#8)).get? 7823 = some (5#8) at observed
  simp only [Std.ExtHashMap.get?_eq_getElem?,Std.ExtHashMap.getElem?_insert,beq_self_eq_true,ite_true] at observed
  cases observed

/-- The previous image's handler coordinate, 3160, is alignment padding, not the handler. -/
theorem previous_handler_refused : ¬ ∀ byte : Fin 29, image.view.read (3160 + byte.val) =
    (X86P1InvalidCapture.code[byte.val]?).map (BitVec.ofNat 8) := by
  intro claimed
  have actual : image.view.read 3160 = some (0x1f#8) := by kernel_reflexivity
  have first := claimed ⟨0, by decide⟩
  exact absurd (actual.symm.trans first) (by decide)

/-! ### The zero-offset store's guard -/

private noncomputable abbrev guard (copy : Copy) (index : Word) :=
  X86MemoryAdapterStore.Controls.guardFixture copy index

private noncomputable abbrev guardState (copy : Copy) (index : Word) :=
  X86MemoryAdapterStore.Controls.guardState copy index

private theorem base_int : (4096#48 : BitVec 48).toInt = 4096 := by decide

private noncomputable def guardReceipt (copy : Copy) (index : Word) :
    X86FailureHandler.FrameFacts (guardState copy index) where
  frame := 32768
  statusAddress := 32912#48
  resultAddress := 32920#48
  statusUpper := by decide
  resultUpper := by decide
  statusEffective := by decide
  resultEffective := by decide
  statusAligned := by decide
  resultAligned := by decide
  controls := (guard copy index).controls.controls
  visible := (guard copy index).controls.visible
  flags := (guard copy index).point.flags
  frameKnown := (guard copy index).frameKnown
  controlsKnown := (guard copy index).controls.controlsKnown
  visibleKnown := (guard copy index).controls.visibleKnown
  flagsKnown := (guard copy index).point.knownFlags
  quiet := (guard copy index).point.quiet
  statusOutside := by
    intro byte within
    interval_cases byte <;> decide

private theorem guard_apart (copy : Copy) (index : Word) : ∀ offset < image.size,
    ((address (4096#48 : BitVec 48).toInt offset).signExtend 52).toNat ∉
      X86P1RefusedCapture.writes (guardReceipt copy index) := by
  intro offset within member
  rw [base_int] at member
  rw [X86P1SibStoreCapture.byte_extent] at within
  have footprint : X86P1RefusedCapture.writes (guardReceipt copy index) = Finset.Icc 32912 32927 := by
    change X86WriteWords.written (32912#48) (List.range 8) ∪
      X86WriteWords.written (32920#48) (List.range 8) = Finset.Icc 32912 32927
    decide
  rw [code_physical offset within,footprint] at member
  have lower := (Finset.mem_Icc.mp member).1
  omega

/-- With RAX at four, the store's last byte lies past region five's sixteen bytes: in both copies
the guard rejects into the shared handler, which returns outcome three at the exit. -/
theorem guard_runs_to_invalid (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (copy : Copy) :
    letI : OtherOpcodeHandlers := guardHandlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 7).run (guardState copy 4) = .ok () after ∧
      after.regs.get? .rip = some ((address 4096 exitAt).signExtend 64) ∧ lookup after 0 = some (3#64) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress (32912#48) byte) =
        some ((3#64).extractLsb' (8 * byte) 8)) ∧
      (∀ byte < 8, after.mem.get? (X86WriteWords.physicalAddress (32920#48) byte) =
        some ((3#64).extractLsb' (8 * byte) 8)) := by
  obtain ⟨after,run,rip,value,status,output,_frame,_loaded⟩ :=
    guard_failed other extra vector copy (guard copy 4).point (guardReceipt copy 4)
      X86MemoryAdapterStore.Controls.lengthCell 4 16 (guard copy 4).indexKnown (guard copy 4).lengthRead
      (by decide) (by decide) (by rw [base_int]; exact (guard copy 4).loaded) (guard_apart copy 4)
  rw [base_int] at rip
  exact ⟨after,run,rip,value,status,output⟩

/-- RAX at three, the last in-bounds index: the guard forms R12 and continues at the load. -/
theorem guard_last_index_passes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (copy : Copy) :
    letI : OtherOpcodeHandlers := X86IndexedAddress.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 4).run (guardState copy 3) = .ok () after ∧
      lookup after 12 = some ((guard copy 3).regionBase + 3#64 * 4#64) ∧
      Nonempty (X86PlacedInstruction.At image.view after 4096#48 (X86P1SibStoreCapture.guardAt copy + 25)) := by
  obtain ⟨after,run,_frame,formed,next⟩ :=
    X86P1SibStoreCapture.guard_succeeds other extra vector copy (guard copy 3).point (guard copy 3).controls
      (32768#64) (guard copy 3).regionBase 3 16 X86MemoryAdapterStore.Controls.lengthCell
      (guard copy 3).frameKnown (guard copy 3).baseKnown (guard copy 3).indexKnown (guard copy 3).lengthRead
      (by decide)
  exact ⟨after,run,formed,next⟩

end Controls

end Mettapedia.Machines.TIsa.X86MemoryAdapterStoreFailure
