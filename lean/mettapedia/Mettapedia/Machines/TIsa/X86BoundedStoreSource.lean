import Mettapedia.Machines.TIsa.X86StoreRepresentation

/-!
# Existing store recipes realized by complete native blocks

The source firing supplies writable mode, bounds, the source word and exact
output bytes. Byte observations establish the canonical target area. Explicit
descriptor exclusions retain the source representation after the actual store.
No initial destination-byte values or native result are separately assumed.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86BoundedStoreSource
open _root_.X86Registers X86RegisterRefinement X86Execution X86MemoryView X86MemoryReadback X86BoundedStore
local instance : MemoryPrimitives := X86Memory.ordinary
abbrev width := X86StoreRepresentation.width
abbrev target := X86StoreRepresentation.target

def recipe (instruction : Instruction) (address : Nat) : CellEffects.Recipe Key :=
  P1Memory.storeRecipe (width instruction.wide) instruction.region.val instruction.base instruction.source
    (displacement instruction).toInt address
def p1 (instruction : Instruction) : P1Source.Instr :=
  .store (width instruction.wide) instruction.region instruction.base (displacement instruction) instruction.source

def wide? : P1Source.Width → Option Bool
  | .word64 => some true | .word32 => some false | _ => none

def fromParts? (wide : Bool) (region : Fin 9) (base source : Fin 12) (offset : BitVec 32)
    (reject : Nat) : Option Instruction :=
  if valid : (physical base).val % 8 ≠ 4 ∧ (physical base).val % 8 ≠ 5 ∧ offset.toNat < 2 ^ 31 then
    some ⟨wide,source,base,region,⟨offset.toNat,valid.2.2⟩,reject,valid.1,valid.2.1⟩ else none

def lower? (source : P1Source.Instr) (reject : Nat) : Option Instruction :=
  match source with
  | .store width region base offset source => (wide? width).bind fun wide => fromParts? wide region base source offset reject
  | _ => none

theorem wide?_meaning {size : P1Source.Width} {wide : Bool} (accepted : wide? size = some wide) : width wide = size := by
  cases size <;> simp [wide?] at accepted <;> subst wide <;> rfl

theorem fromParts?_source {wide : Bool} {region : Fin 9} {base source : Fin 12} {offset : BitVec 32}
    {reject : Nat} {instruction : Instruction} (accepted : fromParts? wide region base source offset reject = some instruction) :
    p1 instruction = .store (width wide) region base offset source := by
  unfold fromParts? at accepted
  split at accepted
  · cases accepted
    simp only [p1,displacement,X86PositiveImmediate.immediate32,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  · cases accepted

theorem lower?_source {source : P1Source.Instr} {reject : Nat} {instruction : Instruction}
    (accepted : lower? source reject = some instruction) : p1 instruction = source := by
  cases source <;> try contradiction
  case store size region base offset source =>
    obtain ⟨wide,selected,built⟩ := Option.bind_eq_some_iff.mp accepted
    have shape := fromParts?_source built
    simpa only [wide?_meaning selected] using shape

theorem from_source (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (instruction : Instruction) (view : View) (values : Key → Word) (native : State)
    (origin : X86LegacyFetch.Basis native) (profile : X86Readiness.Profile) (flags : BitVec 32)
    (known : ∀ location ∈ view.keys, readback view.modes native location = some (values location))
    (frameArea : X86CanonicalSpan.Area (values (.register 0)) frameLayout.size)
    (frameAligned : (values (.register 0)).toNat % 8 = 0)
    (holds : profile.Holds native) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (geometry : X86Bounds.Context (layout instruction) origin.address)
    (tailWithin : X86Bounds.exitAt (layout instruction) + 10 ≤ geometry.extent)
    (loaded : codeLoaded native origin.address.toInt (bytes instruction))
    (rangeFits : (values (.capabilityBase instruction.region.val)).toNat +
      (values (.capabilityLength instruction.region.val)).toNat < 2 ^ 64)
    (pointerLower : (values (.capabilityBase instruction.region.val)).toNat ≤ (values (.register instruction.base)).toNat)
    (pointerUpper : (values (.register instruction.base)).toNat ≤ (values (.capabilityBase instruction.region.val)).toNat +
      (values (.capabilityLength instruction.region.val)).toNat)
    (address : Nat) (following : World)
    (safe : profile.enabled = false ∨ target address &&& BitVec.ofNat 48 (X86DataStore.byteCount instruction.wide - 1) = (0#48))
    (source : (CellEffects.profile [recipe instruction address]).theory.rewrites (Cells.encode view.keys values) following)
    (descriptors : X86MemoryStore.DescriptorsApart view native (X86DataStore.writes instruction.wide (target address))) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches (count instruction)).run native = .ok () after ∧
      X86StateFrame.Frame X86Bounds.writes (X86DataStore.writes instruction.wide (target address)) native after ∧
      represents view following after ∧
      (∀ index < X86DataStore.byteCount instruction.wide,
        after.mem.get? (X86WriteWords.physicalAddress (target address) index) =
          some ((values (.register instruction.source)).extractLsb' (8 * index) 8)) ∧
      after.regs.get? .rip = some ((X86Execution.address origin.address.toInt (bytes instruction).length).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .log_register_writes = some false ∧
      X86ControlFlags.Preserved native after ∧ profile.Holds after ∧
      ∀ prefixCount ≤ count instruction, ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run native = .ok () observed →
          X86StateFrame.Frame X86Bounds.writes (X86DataStore.writes instruction.wide (target address)) native observed := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨produced,included,_mode,access,_output,_endpoint⟩ :=
    (X86MemoryStore.source_store_iff (width instruction.wide) instruction.region.val instruction.base instruction.source
      (displacement instruction).toInt address view.keys values following).mp source
  have basePresent : Memory.Key.capabilityBase instruction.region.val ∈ view.keys := by
    apply included
    simp [CellEffects.Recipe.support,P1Memory.storeRecipe,P1Memory.storeSpec,Memory.Store.recipe,Memory.capabilityKeys]
  have lengthPresent : Memory.Key.capabilityLength instruction.region.val ∈ view.keys := by
    apply included
    simp [CellEffects.Recipe.support,P1Memory.storeRecipe,P1Memory.storeSpec,Memory.Store.recipe,Memory.capabilityKeys]
  have count_eq : (layout instruction).count.val = X86DataStore.byteCount instruction.wide := by
    cases selected : instruction.wide <;> simp [layout,X86DataStore.byteCount,selected]
  have width_eq : (P1Memory.memoryWidth (width instruction.wide)).bytes = X86DataStore.byteCount instruction.wide := by
    cases selected : instruction.wide <;> simp [P1Memory.memoryWidth,width,X86BoundedLoadSource.width,Memory.Width.bytes,X86DataStore.byteCount]
  have bytesIncluded : ∀ index < X86DataStore.byteCount instruction.wide, Memory.Key.byte (address + index) ∈ view.keys := by
    intro index within
    apply included
    apply Finset.mem_union_left
    simp [CellEffects.Recipe.writes,P1Memory.storeRecipe,P1Memory.storeSpec,Memory.Store.recipe,Memory.byteKeys,width_eq,within]
  have area := X86MemoryStore.represented_byte_area view values native address _ (by cases instruction.wide <;> decide) known bytesIncluded
  let facts := X86MemoryBounds.facts view values native (layout instruction) instruction.base profile flags rfl
    known basePresent lengthPresent frameArea frameAligned holds flagsKnown quiet
  let input : Inputs instruction native origin := ⟨facts,geometry,tailWithin,loaded⟩
  have coordinate : address = (values (.register instruction.base)).toNat + instruction.offset.val := by
    have formed := (P1Memory.access?_iff_inside _ _ _ (displacement instruction) _ address rangeFits pointerLower pointerUpper).mp access
    rw [displacement,X86BoundsArithmetic.offset_toInt] at formed
    omega
  have fits : Fits input := by
    apply (X86BoundsArithmetic.source_guard _ _ _ instruction.offset (layout instruction).count rangeFits pointerLower pointerUpper).mpr
    simpa only [displacement,coordinate,count_eq,X86StoreRepresentation.width_bytes] using access
  have canonical := X86CanonicalSpan.area_base _ _ (by cases instruction.wide <;> decide) area
  let data : Writable input := {
    value := values (.register instruction.source)
    sourceKnown := known (.register instruction.source) (view.registers instruction.source)
    dataAddress := target address
    upper := X86CanonicalSpan.area_narrow_upper _ _ (by cases instruction.wide <;> decide) area
    effective := by
      change input.pointer + (displacement instruction).signExtend 64 =
        (X86CanonicalSpan.narrow (BitVec.ofNat 64 address)).signExtend 64
      rw [X86CanonicalSpan.narrow_representation _ canonical,coordinate,BitVec.ofNat_add,BitVec.ofNat_toNat]
      congr 1
      exact X86BoundsArithmetic.offset_signExtend instruction.offset
    safe := by
      have alignment : X86FrameLoad.alignmentEnabled profile.controls flags profile.visible = profile.enabled := by
        obtain ⟨_controls,_visible,seen,seenKnown,ac⟩ := holds
        have same : seen = flags := Option.some.inj (seenKnown.symm.trans flagsKnown)
        subst seen
        simp only [X86FrameLoad.alignmentEnabled,X86Readiness.Profile.enabled,ac]
      change X86FrameLoad.alignmentEnabled profile.controls flags profile.visible = false ∨ _
      rw [alignment]
      exact safe }
  obtain ⟨after,nextFlags,run,frame,stored,rip,flagsRead,nextQuiet,control,prefixes⟩ :=
    succeeds other extra vector instruction native origin input fits data
  refine ⟨after,nextFlags,run,frame,?_,?_,rip,flagsRead,nextQuiet,control,
    profile.after_control native after _ _ frame X86Bounds.writes_data control ⟨nextFlags,flagsRead⟩ holds,prefixes⟩
  · exact X86StoreRepresentation.represents_after_store instruction.wide view values native after instruction.region.val
      instruction.base instruction.source (displacement instruction).toInt address following known source frame stored descriptors
  · intro index within
    simpa only [X86StoreRepresentation.payload_byte instruction.wide _ index within] using stored index within

#print axioms from_source
#print axioms lower?_source
end Mettapedia.Machines.TIsa.X86BoundedStoreSource
