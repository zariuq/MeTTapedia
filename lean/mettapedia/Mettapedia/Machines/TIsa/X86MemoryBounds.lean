import Mettapedia.Machines.TIsa.X86MemoryReadback
import Mettapedia.Machines.TIsa.X86Bounds
import Mettapedia.Machines.TIsa.X86ExecutionProfile

/-!
# Native bounds inputs derived from the shared memory representation

Actual register and descriptor readbacks construct the established bounds
checker facts for every declared capability slot. Frame bytes are derived,
not separately assumed. The original fetched template then classifies the
source access predicate and preserves every represented data observation.
The stronger contract retains the actual control/segment/AC profile through
successful and rejecting paths, using the fetched protected-flag effects.

The nonnegative displacement, nonwrapping capability, in-region pointer,
aligned canonical frame, loaded code and fetch-mode conditions are explicit.
Data access, other memory forms, handler/ABI execution and complete
admission/hosting retain their own obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86MemoryBounds
open _root_.X86Registers X86RegisterRefinement X86Execution X86MemoryView X86MemoryReadback

theorem base_displacement (region : Fin 9) :
    (BitVec.ofNat 32 (16 * region.val)).signExtend 64 = BitVec.ofNat 64 (16 * region.val) := by
  fin_cases region <;> decide

theorem length_displacement (region : Fin 9) :
    (BitVec.ofNat 32 (16 * region.val + 8)).signExtend 64 = BitVec.ofNat 64 (16 * region.val + 8) := by
  fin_cases region <;> decide

theorem read_base_observed (modes : Fin 9 → Word) (native : State) (region : Fin 9) (frame value : Word)
    (frameKnown : lookup native 7 = some frame)
    (observed : readback modes native (.capabilityBase region.val) = some value) :
    wordAt? (memory native) (frame + BitVec.ofNat 64 (16 * region.val)) = some value := by
  have notFrame : region.val ≠ 255 := by have := region.isLt; omega
  have fieldKnown : field? native (16 * region.val) = some value := by
    simpa only [readback,if_neg notFrame,if_pos region.isLt] using observed
  unfold field? at fieldKnown
  rw [frameKnown] at fieldKnown
  exact fieldKnown

theorem read_length_observed (modes : Fin 9 → Word) (native : State) (region : Fin 9) (frame value : Word)
    (frameKnown : lookup native 7 = some frame)
    (observed : readback modes native (.capabilityLength region.val) = some value) :
    wordAt? (memory native) (frame + BitVec.ofNat 64 (16 * region.val + 8)) = some value := by
  have notFrame : region.val ≠ 255 := by have := region.isLt; omega
  have fieldKnown : field? native (16 * region.val + 8) = some value := by
    simpa only [readback,if_neg notFrame,if_pos region.isLt] using observed
  unfold field? at fieldKnown
  rw [frameKnown] at fieldKnown
  exact fieldKnown

theorem read_base (view : View) (values : Key → Word) (native : State) (region : Fin 9)
    (known : ∀ key ∈ view.keys, readback view.modes native key = some (values key))
    (present : Memory.Key.capabilityBase region.val ∈ view.keys) :
    wordAt? (memory native) (values (.register 0) + BitVec.ofNat 64 (16 * region.val)) =
      some (values (.capabilityBase region.val)) :=
  read_base_observed view.modes native region _ _ (known (.register 0) (view.registers 0)) (known _ present)

theorem read_length (view : View) (values : Key → Word) (native : State) (region : Fin 9)
    (known : ∀ key ∈ view.keys, readback view.modes native key = some (values key))
    (present : Memory.Key.capabilityLength region.val ∈ view.keys) :
    wordAt? (memory native) (values (.register 0) + BitVec.ofNat 64 (16 * region.val + 8)) =
      some (values (.capabilityLength region.val)) :=
  read_length_observed view.modes native region _ _ (known (.register 0) (view.registers 0)) (known _ present)

def facts_at (native : State) (layout : X86Bounds.Layout) (profile : X86Readiness.Profile)
    (flags : BitVec 32) (frame pointer base length : Word)
    (frameKnown : lookup native 7 = some frame) (pointerKnown : lookup native layout.pointer = some pointer)
    (baseKnown : wordAt? (memory native) (frame + BitVec.ofNat 64 (16 * layout.region.val)) = some base)
    (lengthKnown : wordAt? (memory native) (frame + BitVec.ofNat 64 (16 * layout.region.val + 8)) = some length)
    (frameArea : X86CanonicalSpan.Area frame frameLayout.size) (frameAligned : frame.toNat % 8 = 0)
    (holds : profile.Holds native) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false) : X86Bounds.Facts layout native := by
  have baseFacts := wordAt?_narrow_bytes native _ _ baseKnown
  have lengthFacts := wordAt?_narrow_bytes native _ _ lengthKnown
  have baseInside : 16 * layout.region.val < frameLayout.size := by
    have := layout.region.isLt
    change 16 * layout.region.val < 192
    omega
  have lengthInside : 16 * layout.region.val + 8 < frameLayout.size := by
    have := layout.region.isLt
    change 16 * layout.region.val + 8 < 192
    omega
  refine {
    frame := frame
    base := base
    pointer := pointer
    length := length
    baseAddress := X86CanonicalSpan.narrow (frame + BitVec.ofNat 64 (16 * layout.region.val))
    lengthAddress := X86CanonicalSpan.narrow (frame + BitVec.ofNat 64 (16 * layout.region.val + 8))
    controls := profile.controls
    visible := profile.visible
    flags := flags
    frameKnown := frameKnown
    pointerKnown := pointerKnown
    baseEffective := ?_
    lengthEffective := ?_
    baseUpper := baseFacts.2.1
    lengthUpper := lengthFacts.2.1
    baseAligned := ?_
    lengthAligned := ?_
    controlKnown := holds.1
    visibleKnown := holds.2.1
    flagsKnown := flagsKnown
    quiet := quiet
    baseBytes := baseFacts.2.2
    lengthBytes := lengthFacts.2.2 }
  · simpa only [X86Bounds.baseDisplacement,base_displacement] using baseFacts.1
  · simpa only [X86Bounds.lengthDisplacement,length_displacement] using lengthFacts.1
  · rw [X86CanonicalSpan.narrow_offset _ frameLayout.size _ (by decide) frameArea baseInside]
    exact X86CanonicalSpan.offset_aligned _ frameLayout.size _ (by decide) frameArea baseInside frameAligned
      (by omega)
  · rw [X86CanonicalSpan.narrow_offset _ frameLayout.size _ (by decide) frameArea lengthInside]
    exact X86CanonicalSpan.offset_aligned _ frameLayout.size _ (by decide) frameArea lengthInside frameAligned
      (by omega)

def facts_observed (modes : Fin 9 → Word) (values : Key → Word) (native : State) (layout : X86Bounds.Layout)
    (pointer : Fin 12) (profile : X86Readiness.Profile) (flags : BitVec 32)
    (mapped : layout.pointer = placed (Registers.canonical .x86_64)
      (Registers.canonical_admitted .x86_64) (Registers.logicalSlot pointer))
    (frameKnown : readback modes native (.register 0) = some (values (.register 0)))
    (pointerKnown : readback modes native (.register pointer) = some (values (.register pointer)))
    (baseKnown : readback modes native (.capabilityBase layout.region.val) = some (values (.capabilityBase layout.region.val)))
    (lengthKnown : readback modes native (.capabilityLength layout.region.val) = some (values (.capabilityLength layout.region.val)))
    (frameArea : X86CanonicalSpan.Area (values (.register 0)) frameLayout.size)
    (frameAligned : (values (.register 0)).toNat % 8 = 0)
    (holds : profile.Holds native) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false) : X86Bounds.Facts layout native :=
  facts_at native layout profile flags (values (.register 0)) (values (.register pointer))
    (values (.capabilityBase layout.region.val)) (values (.capabilityLength layout.region.val))
    frameKnown (by rw [mapped]; exact pointerKnown)
    (read_base_observed modes native layout.region _ _ frameKnown baseKnown)
    (read_length_observed modes native layout.region _ _ frameKnown lengthKnown)
    frameArea frameAligned holds flagsKnown quiet

def facts (view : View) (values : Key → Word) (native : State) (layout : X86Bounds.Layout)
    (pointer : Fin 12) (profile : X86Readiness.Profile) (flags : BitVec 32)
    (mapped : layout.pointer = placed (Registers.canonical .x86_64)
      (Registers.canonical_admitted .x86_64) (Registers.logicalSlot pointer))
    (known : ∀ key ∈ view.keys, readback view.modes native key = some (values key))
    (basePresent : Memory.Key.capabilityBase layout.region.val ∈ view.keys)
    (lengthPresent : Memory.Key.capabilityLength layout.region.val ∈ view.keys)
    (frameArea : X86CanonicalSpan.Area (values (.register 0)) frameLayout.size)
    (frameAligned : (values (.register 0)).toNat % 8 = 0)
    (holds : profile.Holds native) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false) : X86Bounds.Facts layout native :=
  facts_observed view.modes values native layout pointer profile flags mapped
    (known (.register 0) (view.registers 0)) (known (.register pointer) (view.registers pointer))
    (known _ basePresent) (known _ lengthPresent) frameArea frameAligned holds flagsKnown quiet

theorem bounds_preserves_readback (modes : Fin 9 → Word) (before after : State)
    (frame : RegisterFrame X86Bounds.writes before after) (key : Key) :
    readback modes after key = readback modes before key := by
  by_cases register : ∃ name, key = Memory.Key.register name
  · obtain ⟨name,rfl⟩ := register
    apply frame.lookup
    fin_cases name <;> decide
  · have bytes : memory after = memory before := by
      funext address
      change after.mem.get? address = before.mem.get? address
      rw [frame.memory]
    exact readback_nonregister modes before after bytes (frame.lookup 7 (by decide)) key
      (by intro name same; exact register ⟨name,same⟩)

theorem source_classifies_profile (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (view : View) (values : Key → Word) (native : State) (layout : X86Bounds.Layout)
    (pointer : Fin 12) (profile : X86Readiness.Profile) (flags : BitVec 32)
    (mapped : layout.pointer = placed (Registers.canonical .x86_64)
      (Registers.canonical_admitted .x86_64) (Registers.logicalSlot pointer))
    (known : ∀ key ∈ view.keys, readback view.modes native key = some (values key))
    (basePresent : Memory.Key.capabilityBase layout.region.val ∈ view.keys)
    (lengthPresent : Memory.Key.capabilityLength layout.region.val ∈ view.keys)
    (frameArea : X86CanonicalSpan.Area (values (.register 0)) frameLayout.size)
    (frameAligned : (values (.register 0)).toNat % 8 = 0)
    (holds : profile.Holds native) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (origin : X86LegacyFetch.Basis native) (geometry : X86Bounds.Context layout origin.address)
    (loaded : codeLoaded native origin.address.toInt (X86Bounds.code layout))
    (rangeFits : (values (.capabilityBase layout.region.val)).toNat +
      (values (.capabilityLength layout.region.val)).toNat < 2 ^ 64)
    (pointerLower : (values (.capabilityBase layout.region.val)).toNat ≤ (values (.register pointer)).toNat)
    (pointerUpper : (values (.register pointer)).toNat ≤ (values (.capabilityBase layout.region.val)).toNat +
      (values (.capabilityLength layout.region.val)).toNat) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (X86Bounds.boundsSteps layout (values (.capabilityBase layout.region.val))
        (values (.register pointer)) (values (.capabilityLength layout.region.val)))).run native = .ok () after ∧
      RegisterFrame X86Bounds.writes native after ∧
      (∀ key, readback view.modes after key = readback view.modes native key) ∧
      after.regs.get? .rip = some ((if Memory.access? (values (.capabilityBase layout.region.val))
        (values (.capabilityLength layout.region.val)) (values (.register pointer))
        (X86PositiveImmediate.immediate32 layout.offset).toInt layout.count.val =
        some ((values (.register pointer)).toNat + layout.offset.val)
        then X86Bounds.position origin.address (X86Bounds.exitAt layout)
        else X86Bounds.position origin.address layout.reject).signExtend 64) ∧
      X86ControlFlags.Preserved native after ∧ profile.Holds after := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  let observed := facts view values native layout pointer profile flags mapped known basePresent lengthPresent
    frameArea frameAligned holds flagsKnown quiet
  let input : X86Bounds.Inputs layout native origin := { observed with geometry := geometry, loaded := loaded }
  obtain ⟨after,run,frame,rip,control⟩ := X86Bounds.source_classifies_control other extra vector layout native origin input
    rangeFits pointerLower pointerUpper
  exact ⟨after,run,frame,bounds_preserves_readback view.modes native after frame,rip,control,
    profile.after_control native after _ _ (X86StateFrame.registerOnly frame) X86Bounds.writes_data
      control (X86ControlFlags.flags_present control flags flagsKnown) holds⟩

theorem source_classifies (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (view : View) (values : Key → Word) (native : State) (layout : X86Bounds.Layout)
    (pointer : Fin 12) (profile : X86Readiness.Profile) (flags : BitVec 32)
    (mapped : layout.pointer = placed (Registers.canonical .x86_64)
      (Registers.canonical_admitted .x86_64) (Registers.logicalSlot pointer))
    (known : ∀ key ∈ view.keys, readback view.modes native key = some (values key))
    (basePresent : Memory.Key.capabilityBase layout.region.val ∈ view.keys)
    (lengthPresent : Memory.Key.capabilityLength layout.region.val ∈ view.keys)
    (frameArea : X86CanonicalSpan.Area (values (.register 0)) frameLayout.size)
    (frameAligned : (values (.register 0)).toNat % 8 = 0)
    (holds : profile.Holds native) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (origin : X86LegacyFetch.Basis native) (geometry : X86Bounds.Context layout origin.address)
    (loaded : codeLoaded native origin.address.toInt (X86Bounds.code layout))
    (rangeFits : (values (.capabilityBase layout.region.val)).toNat +
      (values (.capabilityLength layout.region.val)).toNat < 2 ^ 64)
    (pointerLower : (values (.capabilityBase layout.region.val)).toNat ≤ (values (.register pointer)).toNat)
    (pointerUpper : (values (.register pointer)).toNat ≤ (values (.capabilityBase layout.region.val)).toNat +
      (values (.capabilityLength layout.region.val)).toNat) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (X86Bounds.boundsSteps layout (values (.capabilityBase layout.region.val))
        (values (.register pointer)) (values (.capabilityLength layout.region.val)))).run native = .ok () after ∧
      RegisterFrame X86Bounds.writes native after ∧
      (∀ key, readback view.modes after key = readback view.modes native key) ∧
      after.regs.get? .rip = some ((if Memory.access? (values (.capabilityBase layout.region.val))
        (values (.capabilityLength layout.region.val)) (values (.register pointer))
        (X86PositiveImmediate.immediate32 layout.offset).toInt layout.count.val =
        some ((values (.register pointer)).toNat + layout.offset.val)
        then X86Bounds.position origin.address (X86Bounds.exitAt layout)
        else X86Bounds.position origin.address layout.reject).signExtend 64) := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,run,frame,readbacks,rip,_control,_profile⟩ := source_classifies_profile
    other extra vector view values native layout pointer profile flags mapped known basePresent lengthPresent frameArea frameAligned holds flagsKnown quiet origin geometry loaded rangeFits pointerLower pointerUpper
  exact ⟨after,run,frame,readbacks,rip⟩

#print axioms facts_observed
#print axioms facts
#print axioms bounds_preserves_readback
#print axioms source_classifies

end Mettapedia.Machines.TIsa.X86MemoryBounds
