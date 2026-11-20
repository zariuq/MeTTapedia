import Mettapedia.Machines.TIsa.X86MemoryLoadRepresentation
import Mettapedia.Machines.TIsa.X86P1FieldLoadCapture

/-!
# A source resource firing joined to the captured native field load

The actual R_DERIVE_IS_PROP U64 field-load span at 260..316 executes ten
fetched instructions when its existing source load recipe fires. Its loaded
value, updated representation, register/memory frame and complete image
preservation are derived from shared readbacks. No native execution or
correct-result premise is supplied. Frame/data alignment and entry geometry
remain explicit.

The inhabited fixture installs the whole 647-byte image, real descriptors and
a high-bit word. It proves the source firing and native result, rejects a
truncated result, and exercises the nine-fetch bounds rejection continuation
and its read-only source failure rule. The rejection reaches the shared
invalid-input entry at 590; the previous image's displacement is refused.
Both outcomes preserve the active control/segment/AC profile; negative
controls reject clearing AC. The fixture keeps large memory opaque while
exposing its actual cell equations; no proof limits are increased.

This covers the captured aligned U64 field-load span. Other memory forms,
the generic memory compiler, rejection handler/public ABI and actual
admission/hosting remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86MemoryFieldLoad
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86MemoryView X86MemoryReadback X86MemoryBounds

theorem captured_load_profile (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (view : View) (values : Key → Word) (native : State) (base : Int) (origin : X86LegacyFetch.Basis native)
    (profile : X86Readiness.Profile) (flags : BitVec 32)
    (known : ∀ location ∈ view.keys, readback view.modes native location = some (values location))
    (basePresent : Memory.Key.capabilityBase 0 ∈ view.keys)
    (lengthPresent : Memory.Key.capabilityLength 0 ∈ view.keys)
    (frameArea : X86CanonicalSpan.Area (values (.register 0)) frameLayout.size)
    (frameAligned : (values (.register 0)).toNat % 8 = 0)
    (holds : profile.Holds native) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (placed : origin.address.toInt = base + 260) (upper : base + 647 < (2 ^ 47 : Int))
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage native base)
    (rangeFits : (values (.capabilityBase 0)).toNat + (values (.capabilityLength 0)).toNat < 2 ^ 64)
    (pointerLower : (values (.capabilityBase 0)).toNat ≤ (values (.register 1)).toNat)
    (pointerUpper : (values (.register 1)).toNat ≤ (values (.capabilityBase 0)).toNat + (values (.capabilityLength 0)).toNat)
    (address : Nat) (aligned : address % 8 = 0) (following : World)
    (source : (CellEffects.profile [P1Memory.loadRecipe .u64 .word64 0 6 1 8 address]).theory.rewrites
      (Cells.encode view.keys values) following) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches 10).run native = .ok () after ∧
      RegisterFrame (insert .r10 X86Bounds.writes) native after ∧ represents view following after ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .rip = some ((X86Execution.address base 316).signExtend 64) ∧
      X86P1LoadCapture.Loaded X86P1LoadCapture.propImage after base ∧
      X86ControlFlags.Preserved native after ∧ profile.Holds after := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨value,access,read,followingEq⟩ := source_load_word view values native 0 6 1 8 address following known source
  have addressEq : address = (values (.register 1)).toNat + 8 := by
    have formed := (P1Memory.access?_iff_inside (values (.capabilityBase 0)) (values (.capabilityLength 0))
      (values (.register 1)) (8#32) 8 address rangeFits pointerLower pointerUpper).mp access
    have eight : (8#32).toInt = (8 : Int) := by decide
    rw [eight] at formed
    have same := formed.2.2
    omega
  have fits : (values (.register 1) - values (.capabilityBase 0)).toNat + 16 ≤
      (values (.capabilityLength 0)).toNat := by
    have guard := X86BoundsArithmetic.source_guard (values (.capabilityBase 0)) (values (.capabilityLength 0))
      (values (.register 1)) X86P1FieldLoadCapture.layout.offset X86P1FieldLoadCapture.layout.count rangeFits pointerLower pointerUpper
    change (values (.register 1) - values (.capabilityBase 0)).toNat + 8 + 8 ≤ (values (.capabilityLength 0)).toNat ↔
      Memory.access? (values (.capabilityBase 0)) (values (.capabilityLength 0)) (values (.register 1)) 8 8 =
        some ((values (.register 1)).toNat + 8) at guard
    have accepted := guard.mpr (by simpa only [addressEq] using access)
    omega
  have noWrap := Memory.access?_no_wrap (values (.capabilityBase 0)) (values (.capabilityLength 0))
    (values (.register 1)) 8 8 address access
  have addressBound : address < 2 ^ 64 := by omega
  have admitted := (wordAt?_eq_some_iff (memory native) (BitVec.ofNat 64 address) value).mp read
  have area := (span_iff_area (BitVec.ofNat 64 address)).mp admitted.1
  have canonical := X86CanonicalSpan.area_base (BitVec.ofNat 64 address) 8 (by decide) area
  have dataAligned := X86CanonicalSpan.narrow_aligned (BitVec.ofNat 64 address) canonical
    (by simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt addressBound] using aligned)
  have dataFacts := wordAt?_narrow_bytes native (BitVec.ofNat 64 address) value read
  have effective : values (.register 1) + (8#32).signExtend 64 = (X86CanonicalSpan.narrow (BitVec.ofNat 64 address)).signExtend 64 := by
    have coordinate : values (.register 1) + (8#32).signExtend 64 = BitVec.ofNat 64 address := by
      rw [addressEq,BitVec.ofNat_add,BitVec.ofNat_toNat]
      rfl
    exact coordinate.trans dataFacts.1
  let observed := facts view values native X86P1FieldLoadCapture.layout 1 profile flags (by decide)
    known basePresent lengthPresent frameArea frameAligned holds flagsKnown quiet
  obtain ⟨after,nextFlags,run,frame,result,flagsRead,rip,image,control⟩ := X86P1FieldLoadCapture.load_executes_control other extra vector
    native base origin observed placed upper loaded value _ dataFacts.2.1 effective dataAligned dataFacts.2.2 fits
  refine ⟨after,nextFlags,run,frame,?_,flagsRead,rip,image,control,?_⟩
  · rw [followingEq]
    exact load_represents view values native after 6 (by decide) value known frame result
  · exact profile.after_control native after _ _ (X86StateFrame.registerOnly frame) (by decide)
      control ⟨nextFlags,flagsRead⟩ holds

theorem captured_load (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (view : View) (values : Key → Word) (native : State) (base : Int) (origin : X86LegacyFetch.Basis native)
    (profile : X86Readiness.Profile) (flags : BitVec 32)
    (known : ∀ location ∈ view.keys, readback view.modes native location = some (values location))
    (basePresent : Memory.Key.capabilityBase 0 ∈ view.keys)
    (lengthPresent : Memory.Key.capabilityLength 0 ∈ view.keys)
    (frameArea : X86CanonicalSpan.Area (values (.register 0)) frameLayout.size)
    (frameAligned : (values (.register 0)).toNat % 8 = 0)
    (holds : profile.Holds native) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (placed : origin.address.toInt = base + 260) (upper : base + 647 < (2 ^ 47 : Int))
    (loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage native base)
    (rangeFits : (values (.capabilityBase 0)).toNat + (values (.capabilityLength 0)).toNat < 2 ^ 64)
    (pointerLower : (values (.capabilityBase 0)).toNat ≤ (values (.register 1)).toNat)
    (pointerUpper : (values (.register 1)).toNat ≤ (values (.capabilityBase 0)).toNat + (values (.capabilityLength 0)).toNat)
    (address : Nat) (aligned : address % 8 = 0) (following : World)
    (source : (CellEffects.profile [P1Memory.loadRecipe .u64 .word64 0 6 1 8 address]).theory.rewrites
      (Cells.encode view.keys values) following) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches 10).run native = .ok () after ∧
      RegisterFrame (insert .r10 X86Bounds.writes) native after ∧ represents view following after ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .rip = some ((X86Execution.address base 316).signExtend 64) ∧
      X86P1LoadCapture.Loaded X86P1LoadCapture.propImage after base := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,nextFlags,run,frame,represented,flagsRead,rip,image,_control,_profile⟩ :=
    captured_load_profile other extra vector view values native base origin profile flags known basePresent lengthPresent frameArea frameAligned holds flagsKnown quiet placed upper loaded rangeFits pointerLower pointerUpper address aligned following source
  exact ⟨after,nextFlags,run,frame,represented,flagsRead,rip,image⟩

/-- Actual entry observations for the captured field-load instruction. -/
structure EntryFixture where
  view : View
  values : Key → Word
  native : State
  base : Int
  origin : X86LegacyFetch.Basis native
  profile : X86Readiness.Profile
  flags : BitVec 32
  address : Nat
  known : ∀ location ∈ view.keys, readback view.modes native location = some (values location)
  basePresent : Memory.Key.capabilityBase 0 ∈ view.keys
  lengthPresent : Memory.Key.capabilityLength 0 ∈ view.keys
  modePresent : Memory.Key.capabilityMode 0 ∈ view.keys
  bytesPresent : ∀ offset < 8, Memory.Key.byte (address + offset) ∈ view.keys
  frameArea : X86CanonicalSpan.Area (values (.register 0)) frameLayout.size
  frameAligned : (values (.register 0)).toNat % 8 = 0
  holds : profile.Holds native
  flagsKnown : native.regs.get? .rflags = some flags
  quiet : native.regs.get? .log_register_writes = some false
  placed : origin.address.toInt = base + 260
  upper : base + 647 < (2 ^ 47 : Int)
  loaded : X86P1LoadCapture.Loaded X86P1LoadCapture.propImage native base
  rangeFits : (values (.capabilityBase 0)).toNat + (values (.capabilityLength 0)).toNat < 2 ^ 64
  pointerLower : (values (.capabilityBase 0)).toNat ≤ (values (.register 1)).toNat
  pointerUpper : (values (.register 1)).toNat ≤ (values (.capabilityBase 0)).toNat + (values (.capabilityLength 0)).toNat
  addressEq : address = (values (.register 1)).toNat + 8
  aligned : address % 8 = 0
  codeBeforeFrame : base + 647 ≤ (values (.register 0)).toNat
  frameBeforeData : (values (.register 0)).toNat + frameLayout.size ≤ (values (.capabilityBase 0)).toNat

namespace Controls

private noncomputable abbrev image := X86P1LoadCapture.propImage
private def dataWord : Word := 0x80000001000000ff#64
private def keys : Finset Key := (Finset.univ.image Memory.Key.register) ∪
  {.capabilityBase 0,.capabilityLength 0,.capabilityMode 0,
   .byte 36872,.byte 36873,.byte 36874,.byte 36875,.byte 36876,.byte 36877,.byte 36878,.byte 36879}
private def view : View where
  keys := keys
  registers := by intro register; simp [keys]
  modes := fun region => if region.val = 0 then 1 else 0
private def profile : X86Readiness.Profile where
  controls := Vector.ofFn (fun index => if index.val = 0 then (0x40000#64) else 0)
  visible := Vector.ofFn (fun index => if index.val = 1 then (3#16) else 0)
  ac := 1#1
private def values (length : Word) : Key → Word
  | .register register => if register = 0 then 32768 else if register = 1 then 36864
      else if register = 6 then 0xfedcba9876543210 else 0
  | .byte address => (dataWord.extractLsb' (8 * (address - 36872)) 8).zeroExtend 64
  | .capabilityBase _ => 36864
  | .capabilityLength _ => length
  | .capabilityMode region => if region = 0 then 1 else 0

private def cellAddress (index : Nat) : Nat :=
  if index < 647 then 4096 + index else if index < 663 then 32768 + index - 647 else 36872 + index - 663
private noncomputable def cellByte (length : Word) (index : Nat) : BitVec 8 :=
  if index < 647 then BitVec.ofNat 8 (Lean.RArray.get image.data index)
  else if index < 655 then (36864#64).extractLsb' (8 * (index - 647)) 8
  else if index < 663 then length.extractLsb' (8 * (index - 655)) 8
  else dataWord.extractLsb' (8 * (index - 663)) 8
private noncomputable def cells (length : Word) : List (Nat × BitVec 8) :=
  (List.range 671).map fun index => (cellAddress index,cellByte length index)

private theorem address_injective : Function.Injective cellAddress := by
  intro left right same
  unfold cellAddress at same
  split_ifs at same <;> omega

private theorem distinct (length : Word) : (cells length).Pairwise (fun left right => (left.1 == right.1) = false) := by
  apply List.pairwise_map.mpr
  apply (List.nodup_iff_pairwise_ne.mp (List.nodup_range (n := 671))).imp
  intro left right different
  exact beq_eq_false_iff_ne.mpr (fun equal => different (address_injective equal))

private def modeControl : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else 0)
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else 0)
@[irreducible] private noncomputable def before (length : Word) : State :=
  let registers := (∅ : Std.ExtDHashMap Register RegisterType).insert .ms_reg false
  let registers := registers.insert .fault_reg false
  let registers := registers.insert .msrs modeControl
  let registers := registers.insert .seg_hidden_attrs attributes
  let registers := registers.insert .app_view true
  let registers := registers.insert .rip (4356#64)
  let registers := registers.insert .rdi (values length (.register 0))
  let registers := registers.insert .rsi (values length (.register 1))
  let registers := registers.insert .rdx (values length (.register 2))
  let registers := registers.insert .rcx (values length (.register 3))
  let registers := registers.insert .r8 (values length (.register 4))
  let registers := registers.insert .r9 (values length (.register 5))
  let registers := registers.insert .r10 (values length (.register 6))
  let registers := registers.insert .r11 (values length (.register 7))
  let registers := registers.insert .rax (values length (.register 8))
  let registers := registers.insert .rbx (values length (.register 9))
  let registers := registers.insert .r12 (values length (.register 10))
  let registers := registers.insert .r13 (values length (.register 11))
  let registers := registers.insert .rsp (16384#64)
  let registers := registers.insert .ctrs profile.controls
  let registers := registers.insert .seg_visibles profile.visible
  let registers := registers.insert .rflags (0x40246#32)
  let registers := registers.insert .log_register_writes false
  ⟨registers,(),Std.ExtHashMap.ofList (cells length),(),0,#[]⟩

private theorem cell (length : Word) (index : Fin 671) :
    (before length).mem.get? (cellAddress index.val) = some (cellByte length index.val) := by
  simp only [before]
  exact Std.ExtHashMap.getElem?_ofList_of_mem (by simp) (distinct length)
    (List.mem_map.mpr ⟨index.val,List.mem_range.mpr index.isLt,rfl⟩)

private theorem first_bytes : (List.range 324).all (fun offset => Nat.ble (Lean.RArray.get image.data offset) 255) = true := by
  kernel_reflexivity

private theorem last_bytes : (List.range 323).all (fun offset => Nat.ble (Lean.RArray.get image.data (offset + 324)) 255) = true := by
  kernel_reflexivity

private theorem image_byte (offset : Fin 647) : image.view.read offset.val =
    some (BitVec.ofNat 8 (Lean.RArray.get image.data offset.val)) := by
  have valid : Nat.ble (Lean.RArray.get image.data offset.val) 255 = true := by
    by_cases early : offset.val < 324
    · exact List.all_eq_true.mp first_bytes offset.val (List.mem_range.mpr early)
    · have inside : offset.val - 324 < 323 := by have := offset.isLt; omega
      have same : offset.val - 324 + 324 = offset.val := by omega
      simpa only [same] using List.all_eq_true.mp last_bytes (offset.val - 324) (List.mem_range.mpr inside)
  simp only [P1Capture.Program.view,show offset.val < image.size from by rw [X86P1LoadCapture.byte_extent]; exact offset.isLt,
    if_true,valid]

private theorem low_physical (value : Nat) (small : value < 2 ^ 47) :
    ((BitVec.ofNat 48 value).signExtend 52).toNat = value := by
  have larger : 2 ^ 47 < (2 ^ 48 : Nat) := by decide
  have width : value < 2 ^ 48 := lt_trans small larger
  have natural : (BitVec.ofNat 48 value).toNat = value := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt width]
  have sign : (BitVec.ofNat 48 value).msb = false := by
    apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    rw [natural]
    omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false sign,BitVec.toNat_setWidth_of_le (by decide),natural]

private theorem loaded (length : Word) : X86P1LoadCapture.Loaded image (before length) 4096 := by
  intro offset within
  rw [X86P1LoadCapture.byte_extent] at within
  rw [image_byte ⟨offset,within⟩]
  have observed := cell length ⟨offset,by omega⟩
  simp only [cellAddress,cellByte,if_pos within] at observed
  have physical : ((X86Execution.address 4096 offset).signExtend 52).toNat = 4096 + offset := by
    change ((BitVec.ofNat 48 (4096 + offset)).signExtend 52).toNat = 4096 + offset
    exact low_physical (4096 + offset) (by omega)
  simpa only [physical] using observed

private def origin (length : Word) : X86LegacyFetch.Basis (before length) where
  address := 4356#48
  opcodeAddress := 4357#48
  modrmAddress := 4358#48
  next := 4359#48
  control := modeControl
  attributes := attributes
  step1 := by decide
  step2 := by decide
  step3 := by decide
  status := by simp [before,Std.ExtDHashMap.get?_insert]
  fault := by simp [before,Std.ExtDHashMap.get?_insert]
  msrs := by simp [before,Std.ExtDHashMap.get?_insert]
  segments := by simp [before,Std.ExtDHashMap.get?_insert]
  longMode := by decide
  codeMode := by decide
  application := by simp [before,Std.ExtDHashMap.get?_insert]
  rip := by simp [before,Std.ExtDHashMap.get?_insert]

private theorem frame_pointer (length : Word) : lookup (before length) 7 = some (32768#64) := by
  simp [lookup,key,before,values,Std.ExtDHashMap.get?_insert]
  rfl

private theorem base_word (length : Word) : wordAt? (memory (before length)) (32768#64) = some (36864#64) := by
  apply wordAt?_known _ _ _ (by decide)
  intro offset within
  have observed := cell length ⟨647 + offset,by omega⟩
  have first : ¬647 + offset < 647 := by omega
  have second : 647 + offset < 655 := by omega
  have coordinate : cellAddress (647 + offset) = 32768 + offset := by
    rw [cellAddress,if_neg first,if_pos (by omega)]
    omega
  have value : cellByte length (647 + offset) = (36864#64).extractLsb' (8 * offset) 8 := by
    rw [cellByte,if_neg first,if_pos second,Nat.add_sub_cancel_left]
  rw [coordinate,value] at observed
  interval_cases offset <;> exact observed

private theorem length_word (length : Word) : wordAt? (memory (before length)) (32776#64) = some length := by
  apply wordAt?_known _ _ _ (by decide)
  intro offset within
  have observed := cell length ⟨655 + offset,by omega⟩
  have first : ¬655 + offset < 647 := by omega
  have second : ¬655 + offset < 655 := by omega
  have third : 655 + offset < 663 := by omega
  have coordinate : cellAddress (655 + offset) = 32776 + offset := by
    rw [cellAddress,if_neg first,if_pos third]
    omega
  have value : cellByte length (655 + offset) = length.extractLsb' (8 * offset) 8 := by
    rw [cellByte,if_neg first,if_neg second,if_pos third,Nat.add_sub_cancel_left]
  rw [coordinate,value] at observed
  interval_cases offset <;> exact observed

private theorem data_byte (length : Word) (offset : Fin 8) : memory (before length) (36872 + offset.val) =
    some (dataWord.extractLsb' (8 * offset.val) 8) := by
  have observed := cell length ⟨663 + offset.val,by have := offset.isLt; omega⟩
  have first : ¬663 + offset.val < 647 := by omega
  have second : ¬663 + offset.val < 655 := by omega
  have third : ¬663 + offset.val < 663 := by omega
  have coordinate : cellAddress (663 + offset.val) = 36872 + offset.val := by
    rw [cellAddress,if_neg first,if_neg third]
    omega
  have value : cellByte length (663 + offset.val) = dataWord.extractLsb' (8 * offset.val) 8 := by
    rw [cellByte,if_neg first,if_neg second,if_neg third,Nat.add_sub_cancel_left]
  rw [coordinate,value] at observed
  exact observed

private theorem known (length : Word) : ∀ location ∈ view.keys,
    readback view.modes (before length) location = some (values length location) := by
  intro location member
  rcases Finset.mem_union.mp member with register | other
  · obtain ⟨name,_member,rfl⟩ := Finset.mem_image.mp register
    fin_cases name <;> simp [readback,Registers.logicalSlot,lookup,placed,Registers.canonical,
      Registers.Placement.resolve,key,before,values,Std.ExtDHashMap.get?_insert] <;> rfl
  · simp only [Finset.mem_insert,Finset.mem_singleton] at other
    rcases other with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [readback,field?,frame_pointer,values] using base_word length
    · simpa [readback,field?,frame_pointer,values] using length_word length
    · rfl
    all_goals
      apply readback_byte_known _ _ _ _ (by decide) (by decide)
      first
      | exact data_byte length 0
      | exact data_byte length 1
      | exact data_byte length 2
      | exact data_byte length 3
      | exact data_byte length 4
      | exact data_byte length 5
      | exact data_byte length 6
      | exact data_byte length 7

private theorem profile_before (length : Word) : profile.Holds (before length) := by
  refine ⟨?_,?_,0x40246#32,?_,?_⟩
  · simp [before,Std.ExtDHashMap.get?_insert]
  · simp [before,Std.ExtDHashMap.get?_insert]
  · simp [before,Std.ExtDHashMap.get?_insert]
  · decide

private def output : Key → Word := Function.update (values 16) (.register 6) dataWord

theorem source_firing :
    (CellEffects.profile [P1Memory.loadRecipe .u64 .word64 0 6 1 8 36872]).theory.rewrites
      (Cells.encode view.keys (values 16)) (Cells.encode view.keys output) := by
  apply (P1Memory.load_rewrite_iff .u64 .word64 0 6 1 8 36872 view.keys (values 16) _).mpr
  refine ⟨dataWord,by decide,Or.inl rfl,by decide,?_,rfl⟩
  have bytes : (Memory.byteKeys 36872 P1Source.Width.word64.bytes).map (values 16) =
      Memory.byteWords (unpackBytes 8 dataWord) := by decide
  rw [bytes,P1Memory.load_byteWords,pack_unpack64]
  rfl

theorem word_source_and_native_profile (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ machine, (X86FuelPrefix.fetches 10).run (before 16) = .ok () machine ∧
      readback view.modes machine (.register 6) = some dataWord ∧
      (∀ location ∈ view.keys, location ≠ .register 6 →
        readback view.modes machine location = readback view.modes (before 16) location) ∧
      (∀ address, machine.mem.get? address = (before 16).mem.get? address) ∧
      machine.regs.get? .rip = some (4412#64) ∧ X86P1LoadCapture.Loaded image machine 4096 ∧ profile.Holds machine ∧
      (machine.regs.get? .rflags).map Functions._get_rflagsbits_ac = some (1#1) := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨machine,_flags,run,frame,represented,_flagsKnown,rip,imageLoaded,_control,holds⟩ := captured_load_profile other extra vector view (values 16)
    (before 16) 4096 (origin 16) profile (0x40246#32) (known 16) (by decide) (by decide)
    (by apply X86CanonicalSpan.area_low; decide) (by decide) (profile_before 16)
    (by simp [before,Std.ExtDHashMap.get?_insert]) (by simp [before]) (by decide) (by decide) (loaded 16)
    (by decide) (by decide) (by decide) 36872 (by decide) (Cells.encode view.keys output) source_firing
  obtain ⟨assigned,encoded,seen⟩ := represented
  have valuesEq (location : Key) (member : location ∈ view.keys) : assigned location = output location :=
    ((Cells.encode_le_iff view.keys view.keys assigned output).mp (le_of_eq encoded.symm)).2 location member
  have read (location : Key) (member : location ∈ view.keys) :
      readback view.modes machine location = some (output location) := (seen location member).trans
        (congrArg some (valuesEq location member))
  refine ⟨machine,run,?_,?_,?_,rip,imageLoaded,holds,?_⟩
  · simpa only [output,Function.update_self] using read (.register 6) (view.registers 6)
  · intro location member outside
    rw [read location member,known 16 location member]
    simp only [output,Function.update_of_ne outside]
  · intro address
    rw [frame.memory]
  · obtain ⟨_controls,_visible,flags,flagsKnown,ac⟩ := holds
    rw [flagsKnown]
    simpa only [Option.map_some,profile] using congrArg some ac

theorem word_source_and_native (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ machine, (X86FuelPrefix.fetches 10).run (before 16) = .ok () machine ∧
      readback view.modes machine (.register 6) = some dataWord ∧
      (∀ location ∈ view.keys, location ≠ .register 6 →
        readback view.modes machine location = readback view.modes (before 16) location) ∧
      (∀ address, machine.mem.get? address = (before 16).mem.get? address) ∧
      machine.regs.get? .rip = some (4412#64) ∧ X86P1LoadCapture.Loaded image machine 4096 := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨machine,run,value,reads,memory,rip,imageLoaded,_profile,_ac⟩ :=
    word_source_and_native_profile other extra vector
  exact ⟨machine,run,value,reads,memory,rip,imageLoaded⟩

theorem truncated_word_refused (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ initial, ∀ reached, readback view.modes reached (.register 6) = some (255#64) →
      (X86FuelPrefix.fetches 10).run initial ≠ .ok () reached := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨proved,run,value,_rest⟩ := word_source_and_native other extra vector
  refine ⟨before 16,?_⟩
  intro reached truncated executed
  have same := X86FuelPrefix.fetches_deterministic 10 (before 16) proved reached run executed
  rw [same,truncated] at value
  exact (by decide : (some (255#64) : Option Word) ≠ some dataWord) value

theorem rejected_bounds_profile (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ machine, (X86FuelPrefix.fetches 9).run (before 8) = .ok () machine ∧
      (∀ location, readback view.modes machine location = readback view.modes (before 8) location) ∧
      machine.regs.get? .rip = some (4686#64) ∧ profile.Holds machine ∧
      (machine.regs.get? .rflags).map Functions._get_rflagsbits_ac = some (1#1) := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨machine,run,_frame,read,rip,_control,holds⟩ := source_classifies_profile other extra vector view (values 8) (before 8)
    X86P1FieldLoadCapture.layout 1 profile (0x40246#32) (by decide) (known 8) (by decide) (by decide)
    (by apply X86CanonicalSpan.area_low; decide) (by decide) (profile_before 8)
    (by simp [before,Std.ExtDHashMap.get?_insert]) (by simp [before]) (origin 8)
    (X86P1FieldLoadCapture.context 4096 _ (by decide) (by decide))
    (X86P1FieldLoadCapture.prefix_loaded _ 4096 (origin 8) (by decide) (loaded 8))
    (by decide) (by decide) (by decide)
  change (X86FuelPrefix.fetches 9).run (before 8) = .ok () machine at run
  refine ⟨machine,run,read,?_,holds,?_⟩
  · convert rip using 1
    decide
  · obtain ⟨_controls,_visible,flags,flagsKnown,ac⟩ := holds
    rw [flagsKnown]
    simpa only [Option.map_some,profile] using congrArg some ac

theorem rejected_bounds (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ machine, (X86FuelPrefix.fetches 9).run (before 8) = .ok () machine ∧
      (∀ location, readback view.modes machine location = readback view.modes (before 8) location) ∧
      machine.regs.get? .rip = some (4686#64) := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨machine,run,read,rip,_profile,_ac⟩ := rejected_bounds_profile other extra vector
  exact ⟨machine,run,read,rip⟩

/-- The rejection reaches the shared invalid-input entry at 590. The previous image's
displacement, 340 from the span start, would reach 600; no run of the prefix ends there. -/
theorem stale_displacement_refused (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∀ reached, reached.regs.get? .rip = some ((X86Execution.address 4096 (260 + 340)).signExtend 64) →
      (X86FuelPrefix.fetches 9).run (before 8) ≠ .ok () reached := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨proved,run,_read,rip⟩ := rejected_bounds other extra vector
  intro reached stale executed
  have same := X86FuelPrefix.fetches_deterministic 9 (before 8) proved reached run executed
  rw [same,stale] at rip
  exact absurd rip (by decide)

theorem source_bounds_failure :
    (CellEffects.profile [P1Memory.boundsFailureRecipe false .word64 0 1 8]).theory.rewrites
      (Cells.encode view.keys (values 8)) (Cells.encode view.keys (values 8)) := by
  apply (CellEffects.profile_rewrite_iff _ view.keys (values 8) _).mpr
  refine ⟨P1Memory.boundsFailureRecipe false .word64 0 1 8,by simp,values 8,by decide,by decide,?_⟩
  congr 1

theorem enabled_at_entry :
    X86FrameLoad.alignmentEnabled profile.controls (0x40246#32) profile.visible = true := by decide

theorem cleared_ac_refused (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ initial, ∀ reached, (reached.regs.get? .rflags).map Functions._get_rflagsbits_ac = some (0#1) →
      (X86FuelPrefix.fetches 10).run initial ≠ .ok () reached := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨proved,run,_value,_reads,_memory,_rip,_image,_profile,ac⟩ := word_source_and_native_profile other extra vector
  refine ⟨before 16,?_⟩
  intro reached cleared executed
  have same := X86FuelPrefix.fetches_deterministic 10 (before 16) proved reached run executed
  rw [same,cleared] at ac
  exact (by decide : (some (0#1) : Option (BitVec 1)) ≠ some 1) ac

theorem rejection_cleared_ac_refused (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Bounds.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ initial, ∀ reached, (reached.regs.get? .rflags).map Functions._get_rflagsbits_ac = some (0#1) →
      (X86FuelPrefix.fetches 9).run initial ≠ .ok () reached := by
  let : OtherOpcodeHandlers := X86Bounds.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨proved,run,_reads,_rip,_profile,ac⟩ := rejected_bounds_profile other extra vector
  refine ⟨before 8,?_⟩
  intro reached cleared executed
  have same := X86FuelPrefix.fetches_deterministic 9 (before 8) proved reached run executed
  rw [same,cleared] at ac
  exact (by decide : (some (0#1) : Option (BitVec 1)) ≠ some 1) ac

end Controls

/-- The existing full-image, descriptor-backed high-word entry, with AC active. -/
noncomputable def entryFixture : EntryFixture where
  view := Controls.view
  values := Controls.values 16
  native := Controls.before 16
  base := 4096
  origin := Controls.origin 16
  profile := Controls.profile
  flags := 0x40246#32
  address := 36872
  known := Controls.known 16
  basePresent := by decide
  lengthPresent := by decide
  modePresent := by decide
  bytesPresent := by intro offset within; interval_cases offset <;> decide
  frameArea := by apply X86CanonicalSpan.area_low; decide
  frameAligned := by decide
  holds := Controls.profile_before 16
  flagsKnown := by simp [Controls.before,Std.ExtDHashMap.get?_insert]
  quiet := by simp [Controls.before]
  placed := by decide
  upper := by decide
  loaded := Controls.loaded 16
  rangeFits := by decide
  pointerLower := by decide
  pointerUpper := by decide
  addressEq := by decide
  aligned := by decide
  codeBeforeFrame := by decide
  frameBeforeData := by decide

#print axioms load_represents
#print axioms captured_load
#print axioms Controls.source_firing
#print axioms Controls.word_source_and_native
#print axioms Controls.truncated_word_refused
#print axioms Controls.rejected_bounds
#print axioms Controls.stale_displacement_refused
#print axioms Controls.source_bounds_failure

end Mettapedia.Machines.TIsa.X86MemoryFieldLoad
