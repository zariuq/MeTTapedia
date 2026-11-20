import Mettapedia.Machines.TIsa.X86DwordShift
import Mettapedia.Machines.TIsa.X86Normalize32
import Mettapedia.Machines.TIsa.X86WordPrimitive
import Mettapedia.Machines.TIsa.X86Conditional

/-!
# Typed narrow shift templates over existing p1 resource recipes

The emitted template copies only distinct source/destination registers,
performs a dword shift, then normalizes the returned carrier. Its source
meaning is the existing P1Scalar recipe, including count admission.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86TypedShiftBlock
open _root_.X86Registers X86RegisterRefinement X86Execution X86RegisterEncoding X86FetchEntry X86MaskedFlags
local instance : MemoryPrimitives := X86Memory.ordinary
abbrev physical := X86WordPrimitive.physical

structure Instruction where
  operation : Shift
  signed : Bool
  destination : Fin 12
  source : Fin 12
  amount : Fin 32
  unlocked : destination ≠ 0

def copy (instruction : Instruction) : X86CopyBlock.Copy :=
  ⟨instruction.source,instruction.destination,instruction.unlocked⟩
def copyBytes (instruction : Instruction) : List Nat := X86WordPrimitive.bytes (.copy (copy instruction))
def shiftBytes (instruction : Instruction) : List Nat :=
  X86DwordShift.bytes instruction.operation (physical instruction.destination) (BitVec.ofNat 8 instruction.amount.val)
def normalBytes (instruction : Instruction) : List Nat :=
  X86Normalize32.bytes instruction.signed (physical instruction.destination)
def bytes (instruction : Instruction) : List Nat := copyBytes instruction ++ shiftBytes instruction ++ normalBytes instruction

def count (instruction : Instruction) : Nat := X86WordLibrary.count (.copy (copy instruction)) + 2
def evaluate (instruction : Instruction) (values : Fin 12 → Word) : Word :=
  extend32 instruction.signed (instruction.operation.evaluate (low32 (values instruction.source)) instruction.amount.val)
def rawValue (instruction : Instruction) (values : Fin 12 → Word) : Word :=
  X86Shift32Instruction.evaluate instruction.operation (values instruction.source) (BitVec.ofNat 8 instruction.amount.val)
def writes (instruction : Instruction) : Finset Register := X86BinBlock.clobbers instruction.destination

def p1 (instruction : Instruction) : P1Source.Instr :=
  .shift instruction.operation (if instruction.signed then .i32s else .u32z)
    instruction.destination instruction.source instruction.amount.val

def effect (instruction : Instruction) : CellEffects.Recipe (Fin 12) :=
  P1Scalar.recipe (p1 instruction) instruction.destination

def lower? : P1Source.Instr → Option Instruction
  | .shift operation .u32z destination source amount =>
      if valid : amount < 32 ∧ destination ≠ 0 then
        some ⟨operation,false,destination,source,⟨amount,valid.1⟩,valid.2⟩ else none
  | .shift operation .i32s destination source amount =>
      if valid : amount < 32 ∧ destination ≠ 0 then
        some ⟨operation,true,destination,source,⟨amount,valid.1⟩,valid.2⟩ else none
  | _ => none

theorem lower?_roundtrip (instruction : Instruction) : lower? (p1 instruction) = some instruction := by
  cases instruction with
  | mk operation signed destination source amount unlocked =>
    cases signed <;> simp [p1,lower?,amount.isLt,unlocked]

theorem lower?_source {source : P1Source.Instr} {instruction : Instruction}
    (accepted : lower? source = some instruction) : p1 instruction = source := by
  cases source <;> simp only [lower?] at accepted <;> try contradiction
  split at accepted
  · split at accepted
    · cases accepted
      symm
      assumption
    · cases accepted
  · split at accepted
    · cases accepted
      symm
      assumption
    · cases accepted
  · cases accepted

theorem lower?_large_refused (operation : Shift) (signed : Bool) (destination source : Fin 12)
    (amount : Nat) (large : 32 ≤ amount) :
    lower? (.shift operation (if signed then .i32s else .u32z) destination source amount) = none := by
  cases signed <;> simp [lower?,show ¬(amount < 32 ∧ destination ≠ 0) from by omega]

theorem lower?_protected_refused (operation : Shift) (signed : Bool) (source : Fin 12) (amount : Nat) :
    lower? (.shift operation (if signed then .i32s else .u32z) 0 source amount) = none := by
  cases signed <;> simp [lower?]

theorem computes (instruction : Instruction) (values : Fin 12 → Word) :
    P1Scalar.evaluate (p1 instruction) ((p1 instruction).reads.map values) = some (evaluate instruction values) := by
  cases signed : instruction.signed <;>
    simp [p1,P1Source.Instr.reads,P1Scalar.evaluate,P1Scalar.shiftWord,P1Scalar.narrow,
      P1Scalar.normalize,ScalarType.normalize,evaluate,signed,instruction.amount.isLt,
      show ∀ value : BitVec 32, low32 (value.zeroExtend 64) = value from low32_extend32 false]

theorem rawValue_eq (instruction : Instruction) (values : Fin 12 → Word) :
    rawValue instruction values =
      (instruction.operation.evaluate (low32 (values instruction.source)) instruction.amount.val).zeroExtend 64 := by
  have small : instruction.amount.val < 256 := by have := instruction.amount.isLt; omega
  have sourceCount : (BitVec.ofNat 8 instruction.amount.val).toNat = instruction.amount.val := by
    simp [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  unfold rawValue X86Shift32Instruction.evaluate
  rw [X86Shift32Instruction.admitted_count _ (by rw [sourceCount]; exact instruction.amount.isLt),sourceCount]

theorem normalized_raw (instruction : Instruction) (values : Fin 12 → Word) :
    extend32 instruction.signed (low32 (rawValue instruction values)) = evaluate instruction values := by
  rw [rawValue_eq]
  change extend32 instruction.signed (low32 (extend32 false _)) = _
  rw [low32_extend32]
  rfl

theorem source_step_iff (instruction : Instruction) (keys : Finset (Fin 12))
    (values : Fin 12 → Word) (world : Multiset (Cells.Cell (Fin 12))) :
    (CellEffects.profile [effect instruction]).theory.rewrites (Cells.encode keys values) world ↔
      (effect instruction).support ⊆ keys ∧
        world = Cells.encode keys (Function.update values instruction.destination (evaluate instruction values)) := by
  rw [show effect instruction = P1Scalar.recipe (p1 instruction) instruction.destination from rfl,
    P1Scalar.rewrite_iff]
  simp only [computes,Option.some.injEq]
  constructor
  · rintro ⟨result,included,same,endpoint⟩
    cases same
    exact ⟨included,endpoint⟩
  · rintro ⟨included,endpoint⟩
    exact ⟨evaluate instruction values,included,rfl,endpoint⟩

noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  X86Extend32.linkedHandlers (X86Shift.linkedHandlers (X86BranchGate.handlers other extra))

theorem copy_handlers_agree (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86BranchGate.handlers (X86Extend32.linkedHandlers (X86Shift.linkedHandlers other)) extra = handlers other extra := rfl

theorem shift_handlers_agree (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86Shift.linkedHandlers (X86Extend32.linkedHandlers (X86BranchGate.handlers other extra)) = handlers other extra := rfl

theorem writes_data (instruction : Instruction) : writes instruction ⊆ dataRegisters :=
  X86BinBlock.clobbers_data _

theorem byte_length (instruction : Instruction) : (bytes instruction).length =
    (copyBytes instruction).length + (shiftBytes instruction).length + (normalBytes instruction).length := by
  simp [bytes,Nat.add_assoc]

theorem shift_length_bounds (instruction : Instruction) :
    3 ≤ (shiftBytes instruction).length ∧ (shiftBytes instruction).length ≤ 4 :=
  X86DwordShift.length_bounds _ _ _

theorem normal_length_bounds (instruction : Instruction) :
    2 ≤ (normalBytes instruction).length ∧ (normalBytes instruction).length ≤ 3 :=
  X86Normalize32.length_bounds _ _

theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (instruction : Instruction) (values : Fin 12 → Word) (native : State) (origin : X86LegacyFetch.Basis native)
    (known : lookup native (physical instruction.source) = some (values instruction.source))
    (flags : BitVec 32) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (upper : origin.address.toInt + (bytes instruction).length < (2 ^ 47 : Int))
    (loaded : codeLoaded native origin.address.toInt (bytes instruction)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ copied shifted after nextFlags,
      (X86FuelPrefix.fetches (X86WordLibrary.count (.copy (copy instruction)))).run native = .ok () copied ∧
      Step copied shifted ∧ Step shifted after ∧
      RegisterFrame (writes instruction) native copied ∧ RegisterFrame (writes instruction) native shifted ∧
      RegisterFrame (writes instruction) native after ∧
      lookup after (physical instruction.destination) = some (evaluate instruction values) ∧
      after.regs.get? .rip = some ((address origin.address.toInt (bytes instruction).length).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .log_register_writes = some false ∧
      X86ControlFlags.Preserved native after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have shiftLength := shift_length_bounds instruction
  have normalLength := normal_length_bounds instruction
  have lower : -(2 ^ 47 : Int) ≤ origin.address.toInt := by simpa using BitVec.le_toInt origin.address
  have copyKnown : ∀ register ∈ (X86WordLibrary.effect (.copy (copy instruction))).inputs,
      lookup native (physical register) = some (values register) := by
    intro register member
    have same : register = instruction.source := by
      simpa [X86WordLibrary.effect,X86CopyBlock.Copy.effect,X86ResourceCopy.copyAction,copy] using member
    subst register
    exact known
  have copyUpper : origin.address.toInt + (copyBytes instruction).length + 3 < (2 ^ 47 : Int) := by
    rw [byte_length] at upper
    omega
  have whole : codeLoaded native origin.address.toInt
      (copyBytes instruction ++ (shiftBytes instruction ++ normalBytes instruction)) := by
    simpa only [bytes,List.append_assoc] using loaded
  have copyLoaded := codeLoaded_left native origin.address.toInt (copyBytes instruction)
    (shiftBytes instruction ++ normalBytes instruction) whole
  have copyProof := X86WordPrimitive.executes
    (X86Extend32.linkedHandlers (X86Shift.linkedHandlers other)) extra vector (.copy (copy instruction))
    values native origin copyKnown flags flagsKnown quiet copyUpper copyLoaded
  rw [copy_handlers_agree] at copyProof
  obtain ⟨copied,copyFlags,copyRun,copyFrame,copiedValue,copiedRip,copiedFlags,copiedQuiet,copiedControl,_⟩ := copyProof
  have copyFrame' : RegisterFrame (writes instruction) native copied := copyFrame
  let start : Entry native := Entry.ofBasis origin
  let copyEntry : Entry copied := start.transport (X86StateFrame.registerOnly copyFrame')
    (writes_data instruction) (address origin.address.toInt (copyBytes instruction).length) copiedRip
  have copyPosition : copyEntry.address.toInt = origin.address.toInt + (copyBytes instruction).length := by
    change (address origin.address.toInt (copyBytes instruction).length).toInt = _
    exact address_toInt _ lower upper _ (by rw [byte_length]; omega)
  have copiedWhole := copyFrame'.code_preserved origin.address.toInt (bytes instruction) loaded
  have suffixRead := codeLoaded_right copied origin.address.toInt (copyBytes instruction)
    (shiftBytes instruction ++ normalBytes instruction) (by simpa only [bytes,List.append_assoc] using copiedWhole)
  have shiftLoaded : codeLoaded copied copyEntry.address.toInt (shiftBytes instruction) := by
    rw [copyPosition]
    exact codeLoaded_left copied _ (shiftBytes instruction) (normalBytes instruction) suffixRead
  have shiftUpper : copyEntry.address.toInt + (shiftBytes instruction).length < (2 ^ 47 : Int) := by
    rw [copyPosition]
    rw [byte_length] at upper
    omega
  obtain ⟨output,mask,shiftRun⟩ := X86DwordShift.executes
    (X86Extend32.linkedHandlers (X86BranchGate.handlers other extra)) vector instruction.operation copied
    (physical instruction.destination) (values instruction.source) (BitVec.ofNat 8 instruction.amount.val)
    copyFlags copyEntry copiedValue copiedFlags copiedQuiet shiftUpper shiftLoaded
  have shiftEnd : address copyEntry.address.toInt (shiftBytes instruction).length =
      address origin.address.toInt ((copyBytes instruction).length + (shiftBytes instruction).length) := by
    rw [copyPosition]
    simp only [address,Int.natCast_add,Int.add_assoc]
  rw [shift_handlers_agree] at shiftRun
  change (Functions.x86_fetch_decode_execute ()).run copied =
    .ok () (X86Move.putPointer
      (put (X86Flags.putFlags copied (merged copyFlags output mask)) (physical instruction.destination)
        (rawValue instruction values)) (address copyEntry.address.toInt (shiftBytes instruction).length)) at shiftRun
  rw [shiftEnd] at shiftRun
  let shifted := X86Move.putPointer
    (put (X86Flags.putFlags copied (merged copyFlags output mask)) (physical instruction.destination)
      (rawValue instruction values))
    (address origin.address.toInt ((copyBytes instruction).length + (shiftBytes instruction).length))
  have shiftStep : Step copied shifted := shiftRun
  have smallShift := X86Shift32Instruction.result_frame instruction.operation copied
    (physical instruction.destination) (values instruction.source) (BitVec.ofNat 8 instruction.amount.val)
    copyFlags output mask
    (address origin.address.toInt ((copyBytes instruction).length + (shiftBytes instruction).length))
  have shiftFrame : RegisterFrame (writes instruction) copied shifted := smallShift.mono (by
    intro register member
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    simp only [writes,X86BinBlock.clobbers,Finset.mem_insert,Finset.mem_singleton]
    exact Or.inr member)
  have shiftedFrame : RegisterFrame (writes instruction) native shifted := by
    simpa only [Finset.union_self] using copyFrame'.trans shiftFrame
  have shiftedValue : lookup shifted (physical instruction.destination) = some (rawValue instruction values) := by
    dsimp only [shifted]
    rw [X86Move.lookup_putPointer,lookup_put_same]
  have shiftedRip : shifted.regs.get? .rip = some
      ((address origin.address.toInt ((copyBytes instruction).length + (shiftBytes instruction).length)).signExtend 64) :=
    X86BinBlock.copied_rip _ _ _ _
  have shiftedFlags : shifted.regs.get? .rflags = some (merged copyFlags output mask) := by
    change (X86Move.putPointer
      (put (X86Flags.putFlags copied (merged copyFlags output mask)) (physical instruction.destination)
        (rawValue instruction values)) _).regs.get? .rflags = _
    rw [(pointer_frame _ _).registers .rflags (by decide),put_flags,updated_present]
  have shiftedQuiet : shifted.regs.get? .log_register_writes = some false :=
    (shiftedFrame.registers .log_register_writes (fun member =>
      (by decide : Register.log_register_writes ∉ dataRegisters) (writes_data instruction member))).trans quiet
  let normalEntry : Entry shifted := start.transport (X86StateFrame.registerOnly shiftedFrame)
    (writes_data instruction)
    (address origin.address.toInt ((copyBytes instruction).length + (shiftBytes instruction).length)) shiftedRip
  have normalPosition : normalEntry.address.toInt =
      origin.address.toInt + ((copyBytes instruction).length + (shiftBytes instruction).length) := by
    change (address origin.address.toInt ((copyBytes instruction).length + (shiftBytes instruction).length)).toInt = _
    exact address_toInt _ lower upper _ (by rw [byte_length]; omega)
  have shiftedWhole := shiftedFrame.code_preserved origin.address.toInt (bytes instruction) loaded
  have afterCopy := codeLoaded_right shifted origin.address.toInt (copyBytes instruction)
    (shiftBytes instruction ++ normalBytes instruction) (by simpa only [bytes,List.append_assoc] using shiftedWhole)
  have afterShift := codeLoaded_right shifted (origin.address.toInt + (copyBytes instruction).length)
    (shiftBytes instruction) (normalBytes instruction) afterCopy
  have normalLoaded : codeLoaded shifted normalEntry.address.toInt (normalBytes instruction) := by
    simpa only [normalPosition,Int.natCast_add,Int.add_assoc] using afterShift
  have normalUpper : normalEntry.address.toInt + (normalBytes instruction).length < (2 ^ 47 : Int) := by
    rw [normalPosition]
    rw [byte_length] at upper
    omega
  have normalRun := X86Normalize32.executes (X86Shift.linkedHandlers (X86BranchGate.handlers other extra)) vector
    instruction.signed shifted (physical instruction.destination) (rawValue instruction values)
    normalEntry shiftedValue shiftedQuiet normalUpper normalLoaded
  have normalEnd : address normalEntry.address.toInt (normalBytes instruction).length =
      address origin.address.toInt (bytes instruction).length := by
    rw [normalPosition,byte_length]
    simp only [address,Int.natCast_add,Int.add_assoc]
  change (Functions.x86_fetch_decode_execute ()).run shifted =
    .ok () (X86Move.putPointer
      (put shifted (physical instruction.destination) (extend32 instruction.signed (low32 (rawValue instruction values))))
      (address normalEntry.address.toInt (normalBytes instruction).length)) at normalRun
  rw [normalized_raw,normalEnd] at normalRun
  let after := X86Move.putPointer (put shifted (physical instruction.destination) (evaluate instruction values))
    (address origin.address.toInt (bytes instruction).length)
  have normalStep : Step shifted after := normalRun
  have smallNormal := X86Normalize32.result_frame instruction.signed shifted (physical instruction.destination)
    (rawValue instruction values) (address origin.address.toInt (bytes instruction).length)
  rw [normalized_raw] at smallNormal
  have normalFrame : RegisterFrame (writes instruction) shifted after := smallNormal.mono (by
    intro register member
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl | rfl <;> simp [writes,X86BinBlock.clobbers])
  have frame : RegisterFrame (writes instruction) native after := by
    simpa only [Finset.union_self] using shiftedFrame.trans normalFrame
  have finalFlags : after.regs.get? .rflags = some (merged copyFlags output mask) := by
    change (X86Move.putPointer (put shifted (physical instruction.destination) (evaluate instruction values)) _).regs.get? .rflags = _
    rw [(pointer_frame _ _).registers .rflags (by decide),put_flags,shiftedFlags]
  refine ⟨copied,shifted,after,merged copyFlags output mask,copyRun,shiftStep,normalStep,
    copyFrame',shiftedFrame,frame,?_,?_,finalFlags,?_,?_⟩
  · dsimp only [after]
    rw [X86Move.lookup_putPointer,lookup_put_same]
  · exact X86BinBlock.copied_rip _ _ _ _
  · exact (frame.registers .log_register_writes (fun member =>
      (by decide : Register.log_register_writes ∉ dataRegisters) (writes_data instruction member))).trans quiet
  · apply copiedControl.trans
    unfold X86ControlFlags.Preserved
    rw [finalFlags,copiedFlags]
    simp only [Option.map_some,merged_control]


theorem other_logical (instruction : Instruction) (register : Fin 12)
    (apart : register ≠ instruction.destination) : key (physical register) ∉ writes instruction := by
  change key (physical register) ∉ X86BinBlock.clobbers instruction.destination
  generalize instruction.destination = target at apart ⊢
  revert register target
  decide

theorem copy_count_bound (instruction : Instruction) : X86WordLibrary.count (.copy (copy instruction)) ≤ 1 := by
  change (if instruction.destination = instruction.source then 0 else 1) ≤ 1
  split <;> omega

theorem executes_block (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (instruction : Instruction) (values : Fin 12 → Word) (native : State) (origin : X86LegacyFetch.Basis native)
    (known : lookup native (physical instruction.source) = some (values instruction.source))
    (flags : BitVec 32) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (upper : origin.address.toInt + (bytes instruction).length < (2 ^ 47 : Int))
    (loaded : codeLoaded native origin.address.toInt (bytes instruction)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches (count instruction)).run native = .ok () after ∧
      RegisterFrame (writes instruction) native after ∧
      lookup after (physical instruction.destination) = some (evaluate instruction values) ∧
      after.regs.get? .rip = some ((address origin.address.toInt (bytes instruction).length).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .log_register_writes = some false ∧
      X86ControlFlags.Preserved native after ∧
      ∀ prefixCount ≤ count instruction, ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run native = .ok () observed →
          RegisterFrame (writes instruction) native observed := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨copied,shifted,after,nextFlags,copyRun,shiftStep,normalStep,copyFrame,shiftFrame,frame,
    value,rip,nextKnown,nextQuiet,control⟩ :=
    executes other extra vector instruction values native origin known flags flagsKnown quiet upper loaded
  have firstRun := X86FuelPrefix.fetches_then (X86WordLibrary.count (.copy (copy instruction))) 1
    native copied shifted copyRun (X86FuelPrefix.fetches_one _ _ shiftStep)
  have fullRun := X86FuelPrefix.fetches_then (X86WordLibrary.count (.copy (copy instruction)) + 1) 1
    native shifted after firstRun (X86FuelPrefix.fetches_one _ _ normalStep)
  have run : (X86FuelPrefix.fetches (count instruction)).run native = .ok () after := by
    simpa only [count,Nat.add_assoc,show (1 + 1 : Nat) = 2 from rfl] using fullRun
  refine ⟨after,nextFlags,run,frame,value,rip,nextKnown,nextQuiet,control,?_⟩
  intro prefixCount within observed candidate
  have bound := copy_count_bound instruction
  have withinThree : prefixCount ≤ 3 := by unfold count at within; omega
  interval_cases prefixCount
  · exact X86WordPrimitive.zero_prefixes native _ 0 (by omega) observed candidate
  · by_cases empty : X86WordLibrary.count (.copy (copy instruction)) = 0
    · have same : copied = native := X86FuelPrefix.fetches_deterministic 0 native copied native
        (by simpa only [empty] using copyRun) (X86FuelPrefix.fetches_zero native)
      subst copied
      have same := X86FuelPrefix.fetches_deterministic 1 native shifted observed
        (X86FuelPrefix.fetches_one _ _ shiftStep) candidate
      subst observed
      exact shiftFrame
    · have one : X86WordLibrary.count (.copy (copy instruction)) = 1 := by omega
      have same := X86FuelPrefix.fetches_deterministic 1 native copied observed
        (by simpa only [one] using copyRun) candidate
      subst observed
      exact copyFrame
  · by_cases empty : X86WordLibrary.count (.copy (copy instruction)) = 0
    · have total : count instruction = 2 := by simp [count,empty]
      rw [total] at run
      have same := X86FuelPrefix.fetches_deterministic 2 native after observed run candidate
      subst observed
      exact frame
    · have one : X86WordLibrary.count (.copy (copy instruction)) = 1 := by omega
      have same := X86FuelPrefix.fetches_deterministic 2 native shifted observed
        (by simpa only [one] using firstRun) candidate
      subst observed
      exact shiftFrame
  · have one : X86WordLibrary.count (.copy (copy instruction)) = 1 := by unfold count at within; omega
    have total : count instruction = 3 := by simp [count,one]
    rw [total] at run
    have same := X86FuelPrefix.fetches_deterministic 3 native after observed run candidate
    subst observed
    exact frame


#print axioms executes_block
#print axioms executes
#print axioms lower?_roundtrip
#print axioms lower?_source
#print axioms computes
#print axioms normalized_raw
#print axioms source_step_iff
end Mettapedia.Machines.TIsa.X86TypedShiftBlock
