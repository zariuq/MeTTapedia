import Mettapedia.Machines.TIsa.X86BoundedLoad
import Mettapedia.Machines.TIsa.X86MemoryLoadRepresentation
import Mettapedia.Machines.TIsa.X86MemoryStore

/-!
# Resource load firings realized by complete native load templates

The existing byte cells supply the value, canonical address geometry and
backing-byte equations. Descriptor observations supply the native bounds
facts. A successful source firing therefore constructs all data inputs of
the original fetched block; no expected result or machine run is assumed.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86BoundedLoadSource
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86MemoryView X86MemoryReadback X86BoundedLoad
local instance : MemoryPrimitives := X86Memory.ordinary

def width (wide : Bool) : P1Source.Width := if wide then .word64 else .word32
def tag (wide : Bool) : P1Source.TypeTag := if wide then .u64 else .u32z
def recipe (instruction : Instruction) (address : Nat) : CellEffects.Recipe Key :=
  P1Memory.loadRecipe (tag instruction.wide) (width instruction.wide) instruction.region.val
    instruction.destination instruction.base (displacement instruction).toInt address

def p1 (instruction : Instruction) : P1Source.Instr :=
  .load (tag instruction.wide) (width instruction.wide) instruction.region instruction.destination
    instruction.base (displacement instruction)

def wide? : P1Source.TypeTag → P1Source.Width → Option Bool
  | .u64,.word64 => some true
  | .u32z,.word32 => some false
  | _,_ => none

def fromParts? (wide : Bool) (region : Fin 9) (destination base : Fin 12) (offset : BitVec 32)
    (reject : Nat) : Option Instruction :=
  if valid : destination ≠ 0 ∧ (physical base).val % 8 ≠ 4 ∧ (physical base).val % 8 ≠ 5 ∧ offset.toNat < 2 ^ 31 then
    some ⟨wide,destination,base,region,⟨offset.toNat,valid.2.2.2⟩,reject,valid.1,valid.2.1,valid.2.2.1⟩
  else none

def lower? (source : P1Source.Instr) (reject : Nat) : Option Instruction :=
  match source with
  | .load tag width region destination base offset =>
      (wide? tag width).bind fun wide => fromParts? wide region destination base offset reject
  | _ => none

theorem wide?_meaning {ty : P1Source.TypeTag} {size : P1Source.Width} {wide : Bool}
    (accepted : wide? ty size = some wide) : tag wide = ty ∧ width wide = size := by
  cases ty <;> cases size <;> simp [wide?] at accepted <;> subst wide <;> exact ⟨rfl,rfl⟩

theorem fromParts?_source {wide : Bool} {region : Fin 9} {destination base : Fin 12} {offset : BitVec 32}
    {reject : Nat} {instruction : Instruction} (accepted : fromParts? wide region destination base offset reject = some instruction) :
    p1 instruction = .load (tag wide) (width wide) region destination base offset := by
  unfold fromParts? at accepted
  split at accepted
  · cases accepted
    simp only [p1,displacement,X86PositiveImmediate.immediate32,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  · cases accepted

theorem lower?_source {source : P1Source.Instr} {reject : Nat} {instruction : Instruction}
    (accepted : lower? source reject = some instruction) : p1 instruction = source := by
  cases source <;> try contradiction
  case load ty size region destination base offset =>
    obtain ⟨wide,selected,built⟩ := Option.bind_eq_some_iff.mp accepted
    have shape := fromParts?_source built
    obtain ⟨tyEq,sizeEq⟩ := wide?_meaning selected
    simpa only [tyEq,sizeEq] using shape

theorem width_bytes (wide : Bool) : (width wide).bytes = X86DataLoad.byteCount wide := by cases wide <;> rfl
theorem checked_value (wide : Bool) (word : Word) :
    P1Memory.checkedWord (tag wide) word = some (X86DataLoad.value wide word) := by cases wide <;> rfl

theorem displacement_word (instruction : Instruction) :
    (displacement instruction).signExtend 64 = BitVec.ofNat 64 instruction.offset.val :=
  X86BoundsArithmetic.offset_signExtend instruction.offset

theorem packed_four_extract (bytes : List (BitVec 8)) (length : bytes.length = 4) (offset : Fin 4) :
    (packBytes bytes).extractLsb' (8 * offset.val) 8 = bytes[offset.val]'(by omega) := by
  let entry : Fin 4 → BitVec 8 := fun index => bytes[index.val]'(by omega)
  have expanded : List.ofFn entry = bytes := by
    apply List.ext_getElem (by simp only [List.length_ofFn];exact length.symm)
    intro index inside here
    have within : index < 4 := by omega
    interval_cases index <;> simp [entry]
  have packed : packBytes bytes = packBytes [entry 0,entry 1,entry 2,entry 3] := by
    rw [←expanded]
    rfl
  rw [packed]
  fin_cases offset <;> apply BitVec.eq_of_getLsbD_eq <;> intro bit inside
  all_goals interval_cases bit <;> simp [packBytes,entry]

theorem packed_byte (wide : Bool) (bytes : List (BitVec 8)) (length : bytes.length = X86DataLoad.byteCount wide)
    (index : Nat) (within : index < X86DataLoad.byteCount wide) :
    (packBytes bytes).extractLsb' (8 * index) 8 = bytes[index]'(by omega) := by
  cases wide with
  | false => exact packed_four_extract bytes length ⟨index,within⟩
  | true => exact packed_extract bytes length ⟨index,within⟩

theorem source_observes (instruction : Instruction) (view : View) (values : Key → Word) (native : State)
    (address : Nat) (following : World)
    (known : ∀ location ∈ view.keys, readback view.modes native location = some (values location))
    (source : (CellEffects.profile [recipe instruction address]).theory.rewrites (Cells.encode view.keys values) following) :
    ∃ word : Word, (recipe instruction address).support ⊆ view.keys ∧
      Memory.access? (values (.capabilityBase instruction.region.val)) (values (.capabilityLength instruction.region.val))
        (values (.register instruction.base)) (displacement instruction).toInt (X86DataLoad.byteCount instruction.wide) = some address ∧
      X86CanonicalSpan.Area (BitVec.ofNat 64 address) (X86DataLoad.byteCount instruction.wide) ∧
      (∀ index < X86DataLoad.byteCount instruction.wide,
        native.mem.get? (X86WriteWords.physicalAddress (X86CanonicalSpan.narrow (BitVec.ofNat 64 address)) index) =
          some (word.extractLsb' (8 * index) 8)) ∧
      following = Cells.encode view.keys (Function.update values (.register instruction.destination)
        (X86DataLoad.value instruction.wide word)) := by
  obtain ⟨result,included,_mode,access,parsed,endpoint⟩ :=
    (P1Memory.load_rewrite_iff (tag instruction.wide) (width instruction.wide) instruction.region.val
      instruction.destination instruction.base (displacement instruction).toInt address view.keys values following).mp source
  rw [width_bytes] at access parsed
  have positive : 0 < X86DataLoad.byteCount instruction.wide := by cases instruction.wide <;> decide
  have present : ∀ index < X86DataLoad.byteCount instruction.wide, Memory.Key.byte (address + index) ∈ view.keys := by
    intro index within
    apply included
    simp [CellEffects.Recipe.support,CellEffects.Recipe.writes,P1Memory.loadRecipe,
      Memory.capabilityKeys,Memory.byteKeys,width_bytes,within]
  have area := X86MemoryStore.represented_byte_area view values native address _ positive known present
  let bytes := (List.range (X86DataLoad.byteCount instruction.wide)).map fun offset =>
    (values (.byte (address + offset))).extractLsb' 0 8
  have length : bytes.length = X86DataLoad.byteCount instruction.wide := by simp [bytes]
  have observations (offset : Nat) (within : offset < X86DataLoad.byteCount instruction.wide) :=
    byte_observed view.modes native (address + offset) _ (known _ (present offset within))
  have words : (Memory.byteKeys address (X86DataLoad.byteCount instruction.wide)).map values = Memory.byteWords bytes := by
    simp only [Memory.byteKeys,Memory.byteWords,bytes,List.map_map]
    apply List.map_congr_left
    intro offset member
    obtain ⟨byte,_read,equal⟩ := (observations offset (List.mem_range.mp member)).2.2
    simp only [Function.comp_apply]
    rw [equal,byte_extract]
  rw [words,P1Memory.load_byteWords,checked_value] at parsed
  have same := Option.some.inj parsed
  refine ⟨packBytes bytes,included,access,area,?_,?_⟩
  · intro index within
    have key : X86CanonicalSpan.physicalKey (BitVec.ofNat 64 (address + index)) =
        X86WriteWords.physicalAddress (X86CanonicalSpan.narrow (BitVec.ofNat 64 address)) index := by
      rw [BitVec.ofNat_add]
      exact X86CanonicalSpan.physicalKey_offset _ _ _ positive area within
    rw [←key,packed_byte instruction.wide bytes length index within]
    have item : bytes[index]'(by omega) = (values (.byte (address + index))).extractLsb' 0 8 := by simp [bytes]
    rw [item]
    obtain ⟨byte,read,equal⟩ := (observations index within).2.2
    rw [equal,byte_extract]
    exact read
  · simpa only [same] using endpoint

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
    (safe : profile.enabled = false ∨ X86CanonicalSpan.narrow (BitVec.ofNat 64 address) &&&
      BitVec.ofNat 48 (X86DataLoad.byteCount instruction.wide - 1) = (0#48))
    (source : (CellEffects.profile [recipe instruction address]).theory.rewrites (Cells.encode view.keys values) following) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches (count instruction)).run native = .ok () after ∧
      RegisterFrame (writes instruction) native after ∧ represents view following after ∧
      after.regs.get? .rip = some ((X86Execution.address origin.address.toInt (bytes instruction).length).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .log_register_writes = some false ∧
      X86ControlFlags.Preserved native after ∧ profile.Holds after ∧
      ∀ prefixCount ≤ count instruction, ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run native = .ok () observed → RegisterFrame (writes instruction) native observed := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨word,included,access,area,present,endpoint⟩ := source_observes instruction view values native address following known source
  have basePresent : Memory.Key.capabilityBase instruction.region.val ∈ view.keys := by
    apply included
    simp [recipe,CellEffects.Recipe.support,P1Memory.loadRecipe,Memory.capabilityKeys]
  have lengthPresent : Memory.Key.capabilityLength instruction.region.val ∈ view.keys := by
    apply included
    simp [recipe,CellEffects.Recipe.support,P1Memory.loadRecipe,Memory.capabilityKeys]
  let facts := X86MemoryBounds.facts view values native (layout instruction) instruction.base profile flags rfl
    known basePresent lengthPresent frameArea frameAligned holds flagsKnown quiet
  let input : Inputs instruction native origin := ⟨facts,geometry,tailWithin,loaded⟩
  have count_eq : (layout instruction).count.val = X86DataLoad.byteCount instruction.wide := by
    cases selected : instruction.wide <;> simp [layout,X86DataLoad.byteCount,selected]
  have coordinate : address = (values (.register instruction.base)).toNat + instruction.offset.val := by
    have formed := (P1Memory.access?_iff_inside _ _ _ (displacement instruction) _ address rangeFits pointerLower pointerUpper).mp access
    rw [displacement,X86BoundsArithmetic.offset_toInt] at formed
    omega
  have fits : Fits input := by
    apply (X86BoundsArithmetic.source_guard _ _ _ instruction.offset (layout instruction).count rangeFits pointerLower pointerUpper).mpr
    simpa only [displacement,coordinate,count_eq] using access
  have canonical := X86CanonicalSpan.area_base _ _ (by cases instruction.wide <;> decide) area
  let data : Readable input := {
    word := word
    dataAddress := X86CanonicalSpan.narrow (BitVec.ofNat 64 address)
    upper := X86CanonicalSpan.area_narrow_upper _ _ (by cases instruction.wide <;> decide) area
    effective := by
      rw [X86CanonicalSpan.narrow_representation _ canonical,coordinate,BitVec.ofNat_add,BitVec.ofNat_toNat]
      congr 1
      exact displacement_word instruction
    safe := by
      have alignment : X86FrameLoad.alignmentEnabled profile.controls flags profile.visible = profile.enabled := by
        obtain ⟨_controls,_visible,seen,seenKnown,ac⟩ := holds
        have same : seen = flags := Option.some.inj (seenKnown.symm.trans flagsKnown)
        subst seen
        simp only [X86FrameLoad.alignmentEnabled,X86Readiness.Profile.enabled,ac]
      change X86FrameLoad.alignmentEnabled profile.controls flags profile.visible = false ∨ _
      rw [alignment]
      exact safe
    present := present }
  obtain ⟨after,nextFlags,run,frame,result,rip,flagsRead,nextQuiet,control,prefixes⟩ :=
    succeeds other extra vector instruction native origin input fits data
  refine ⟨after,nextFlags,run,frame,?_,rip,flagsRead,nextQuiet,control,
    profile.after_control native after _ _ (X86StateFrame.registerOnly frame) (writes_data instruction)
      control ⟨nextFlags,flagsRead⟩ holds,prefixes⟩
  rw [endpoint]
  exact X86MemoryFieldLoad.load_represents view values native after instruction.destination instruction.unlocked
    (X86DataLoad.value instruction.wide word) known frame result

#print axioms source_observes
#print axioms from_source
#print axioms lower?_source
end Mettapedia.Machines.TIsa.X86BoundedLoadSource
