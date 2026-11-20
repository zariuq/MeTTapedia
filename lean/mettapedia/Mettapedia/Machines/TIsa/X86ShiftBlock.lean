import Mettapedia.Machines.TIsa.X86Shift
import Mettapedia.Machines.TIsa.X86WordPrimitive
import Mettapedia.Machines.TIsa.X86Conditional

/-!
# U64 shift templates with partial input readbacks

A template copies its input only when the source and destination differ,
then executes the original immediate shift. Its mathematical effect is the
existing scalar shift action. Only the input needs a physical readback.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86ShiftBlock
open _root_.X86Registers X86RegisterRefinement X86Execution X86RegisterEncoding
open X86MaskedFlags
local instance : MemoryPrimitives := X86Memory.ordinary
abbrev physical := X86WordPrimitive.physical

structure Instruction where
  operation : Shift
  destination : Fin 12
  source : Fin 12
  amount : Fin 64
  unlocked : destination ≠ 0

def copy (instruction : Instruction) : X86CopyBlock.Copy :=
  ⟨instruction.source,instruction.destination,instruction.unlocked⟩
def copyBytes (instruction : Instruction) : List Nat := X86WordPrimitive.bytes (.copy (copy instruction))
def suffix (instruction : Instruction) : List Nat :=
  [(rex true (X86Shift.extension instruction.operation) (physical instruction.destination)).toNat,
    0xc1,(modRM (X86Shift.extension instruction.operation) (physical instruction.destination)).toNat,
    instruction.amount.val]
def bytes (instruction : Instruction) : List Nat := copyBytes instruction ++ suffix instruction
def count (instruction : Instruction) : Nat := X86WordLibrary.count (.copy (copy instruction)) + 1
def effect (instruction : Instruction) : Cells.Action (Fin 12) :=
  ⟨.shift instruction.operation instruction.amount.val,[instruction.source],instruction.destination⟩
def evaluate (instruction : Instruction) (values : Fin 12 → Word) : Word :=
  instruction.operation.evaluate (values instruction.source) instruction.amount.val
def writes (instruction : Instruction) : Finset Register := X86BinBlock.clobbers instruction.destination
noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) : OtherOpcodeHandlers :=
  X86BranchGate.handlers (X86Shift.linkedHandlers other) extra

theorem handlers_agree (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    X86Shift.linkedHandlers (X86BranchGate.handlers other extra) = handlers other extra := by rfl

theorem computes (instruction : Instruction) (values : Fin 12 → Word) :
    (effect instruction).scalar.evaluate ((effect instruction).inputs.map values) =
      some (evaluate instruction values) := by
  simp [effect,evaluate,Scalar.evaluate,instruction.amount.isLt]

def p1 (instruction : Instruction) : P1Source.Instr :=
  .shift instruction.operation .u64 instruction.destination instruction.source instruction.amount.val

def lower? : P1Source.Instr → Option Instruction
  | .shift operation .u64 destination source amount =>
      if valid : amount < 64 ∧ destination ≠ 0 then
        some ⟨operation,destination,source,⟨amount,valid.1⟩,valid.2⟩
      else none
  | _ => none

theorem lower?_roundtrip (instruction : Instruction) : lower? (p1 instruction) = some instruction := by
  cases instruction with
  | mk operation destination source amount unlocked =>
    dsimp only [p1,lower?]
    rw [dif_pos ⟨amount.isLt,unlocked⟩]

theorem lower?_large_refused (operation : Shift) (destination source : Fin 12) (amount : Nat)
    (large : 64 ≤ amount) : lower? (.shift operation .u64 destination source amount) = none := by
  simp only [lower?,dif_neg (by omega : ¬(amount < 64 ∧ destination ≠ 0))]

theorem lower?_protected_refused (operation : Shift) (source : Fin 12) (amount : Nat) :
    lower? (.shift operation .u64 0 source amount) = none := by simp [lower?]

theorem lower?_source {source : P1Source.Instr} {instruction : Instruction}
    (accepted : lower? source = some instruction) : p1 instruction = source := by
  cases source <;> simp only [lower?] at accepted <;> try contradiction
  split at accepted
  · split at accepted
    · cases accepted
      dsimp only [p1]
      symm
      assumption
    · cases accepted
  · cases accepted

theorem source_evaluate_p1 (instruction : Instruction) (values : Fin 12 → Word) :
    (effect instruction).scalar.evaluate ((effect instruction).inputs.map values) =
      P1Scalar.evaluate (p1 instruction) ((p1 instruction).reads.map values) := by
  simp [effect,p1,Scalar.evaluate,P1Source.Instr.reads,P1Scalar.evaluate,P1Scalar.shiftWord,
    P1Scalar.narrow,instruction.amount.isLt]

theorem writes_data (instruction : Instruction) : writes instruction ⊆ dataRegisters :=
  X86BinBlock.clobbers_data _

theorem other_logical (instruction : Instruction) (register : Fin 12)
    (apart : register ≠ instruction.destination) : key (physical register) ∉ writes instruction := by
  change key (physical register) ∉ X86BinBlock.clobbers instruction.destination
  generalize instruction.destination = target at apart ⊢
  revert register target
  decide

theorem copy_count_bound (instruction : Instruction) : X86WordLibrary.count (.copy (copy instruction)) ≤ 1 := by
  change (if instruction.destination = instruction.source then 0 else 1) ≤ 1
  split <;> omega

theorem suffix_length (instruction : Instruction) : (suffix instruction).length = 4 := by rfl
theorem byte_length (instruction : Instruction) : (bytes instruction).length = (copyBytes instruction).length + 4 := by
  simp [bytes,suffix]

theorem prefix_loaded (instruction : Instruction) (state : State) (base : Int)
    (loaded : codeLoaded state base (bytes instruction)) : codeLoaded state base (copyBytes instruction) := by
  intro index byte found
  apply loaded index byte
  rw [bytes,List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

theorem suffix_byte (instruction : Instruction) (index byte : Nat)
    (found : (suffix instruction)[index]? = some byte) :
    (bytes instruction)[(copyBytes instruction).length + index]? = some byte := by
  rw [bytes,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
  exact found

theorem amount_value : ∀ amount : Fin 64,
    ((BitVec.ofNat 8 amount.val).setWidth 6).toNat = amount.val := by decide

theorem executes_with_copy_pointer (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers)
    (instruction : Instruction) (values : Fin 12 → Word) (native : State) (origin : X86LegacyFetch.Basis native)
    (known : lookup native (physical instruction.source) = some (values instruction.source))
    (flags : BitVec 32) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (upper : origin.address.toInt + (bytes instruction).length + 3 < (2 ^ 47 : Int))
    (loaded : codeLoaded native origin.address.toInt (bytes instruction)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ copied after nextFlags,
      (X86FuelPrefix.fetches (X86WordLibrary.count (.copy (copy instruction)))).run native = .ok () copied ∧
      Step copied after ∧
      RegisterFrame (writes instruction) native copied ∧ RegisterFrame (writes instruction) native after ∧
      lookup after (physical instruction.destination) = some (evaluate instruction values) ∧
      after.regs.get? .rip = some ((address origin.address.toInt (bytes instruction).length).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .log_register_writes = some false ∧
      X86ControlFlags.Preserved native after ∧
      copied.regs.get? .rip = some ((address origin.address.toInt (copyBytes instruction).length).signExtend 64) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have copyKnown : ∀ register ∈ (X86WordLibrary.effect (.copy (copy instruction))).inputs,
      lookup native (physical register) = some (values register) := by
    intro register member
    have same : register = instruction.source := by
      simpa [X86WordLibrary.effect,X86CopyBlock.Copy.effect,X86ResourceCopy.copyAction,copy] using member
    subst register
    exact known
  have boundCopy : origin.address.toInt + (copyBytes instruction).length + 3 < (2 ^ 47 : Int) := by
    rw [byte_length] at upper
    omega
  obtain ⟨copied,copyFlags,copyRun,copyFrame,copiedValue,copiedRip,copiedFlags,copiedQuiet,copiedControl,_⟩ :=
    X86WordPrimitive.executes (X86Shift.linkedHandlers other) extra vector (.copy (copy instruction))
      values native origin copyKnown flags flagsKnown quiet boundCopy (prefix_loaded instruction native _ loaded)
  have copyFrame' : RegisterFrame (writes instruction) native copied := copyFrame
  have copyData : DataFrame native copied := copyFrame.mono (X86WordPrimitive.writes_data _)
  have copyLoaded : codeLoaded copied origin.address.toInt (bytes instruction) := copyFrame.code_preserved _ _ loaded
  have bound : origin.address.toInt + ((bytes instruction).length + 3 : Nat) < (2 ^ 47 : Int) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat,Int.add_assoc] using upper
  let window := windowAt native copied origin copyData (extent := (bytes instruction).length + 3)
    bound (copyBytes instruction).length (by rw [byte_length]; omega) copiedRip
    (bytes instruction) copyLoaded (X86Shift.extension instruction.operation) (physical instruction.destination) (0xc1#8)
    (suffix_byte instruction 0 _ (by rfl)) (suffix_byte instruction 1 _ (by rfl))
    (suffix_byte instruction 2 _ (by rfl))
  have lower : -(2 ^ 47 : Int) ≤ origin.address.toInt := by simpa using BitVec.le_toInt origin.address
  have position_int (offset : Nat) (inside : offset ≤ (bytes instruction).length + 3) :
      (address origin.address.toInt offset).toInt = origin.address.toInt + offset :=
    address_toInt _ lower bound offset inside
  have advance : window.next.toInt + 1 = (address origin.address.toInt (bytes instruction).length).toInt := by
    change (address origin.address.toInt ((copyBytes instruction).length + 3)).toInt + 1 = _
    rw [position_int _ (by rw [byte_length]; omega),position_int _ (by omega),byte_length]
    omega
  have immediate : copied.mem.get? (window.next.signExtend 52).toNat = some (BitVec.ofNat 8 instruction.amount.val) :=
    copyLoaded _ _ (suffix_byte instruction 3 _ (by rfl))
  obtain ⟨output,mask,shiftRun⟩ := X86Shift.fetched (X86BranchGate.handlers other extra) vector
    instruction.operation copied (physical instruction.destination) window
    (address origin.address.toInt (bytes instruction).length) (values instruction.source) copyFlags
    (BitVec.ofNat 8 instruction.amount.val) advance copiedValue copiedFlags copiedQuiet immediate
  let after := X86Move.putPointer
    (put (X86Flags.putFlags copied (merged copyFlags output mask)) (physical instruction.destination)
      (evaluate instruction values)) (address origin.address.toInt (bytes instruction).length)
  have evaluation : X86Shift.evaluate instruction.operation (values instruction.source)
      ((BitVec.ofNat 8 instruction.amount.val).setWidth 6) = evaluate instruction values := by
    cases selected : instruction.operation <;>
      simp [X86Shift.evaluate,evaluate,Shift.evaluate,selected]
  have step : Step copied after := by
    rw [handlers_agree,evaluation] at shiftRun
    exact shiftRun
  have small := X86Shift.result_frame copied (physical instruction.destination) (evaluate instruction values)
    copyFlags output mask (address origin.address.toInt (bytes instruction).length)
  have shiftFrame : RegisterFrame (writes instruction) copied after := small.mono (by
    intro register member
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    simp only [writes,X86BinBlock.clobbers,Finset.mem_insert,Finset.mem_singleton]
    exact Or.inr member)
  have frame : RegisterFrame (writes instruction) native after := by
    simpa only [Finset.union_self] using copyFrame'.trans shiftFrame
  have newFlags : after.regs.get? .rflags = some (merged copyFlags output mask) := by
    have preserved : after.regs.get? .rflags =
        (put (X86Flags.putFlags copied (merged copyFlags output mask)) (physical instruction.destination)
          (evaluate instruction values)).regs.get? .rflags :=
      (pointer_frame _ _).registers .rflags (by decide)
    rw [preserved,put_flags,updated_present]
  refine ⟨copied,after,merged copyFlags output mask,copyRun,step,copyFrame',frame,?_,?_,newFlags,?_,?_,copiedRip⟩
  · dsimp only [after]
    rw [X86Move.lookup_putPointer,lookup_put_same]
  · exact X86BinBlock.copied_rip _ _ _ _
  · exact (frame.registers .log_register_writes (by
      intro member
      exact (by decide : Register.log_register_writes ∉ dataRegisters) (X86BinBlock.clobbers_data _ member))).trans quiet
  · apply copiedControl.trans
    unfold X86ControlFlags.Preserved
    rw [newFlags,copiedFlags]
    simp only [Option.map_some,merged_control]

theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (instruction : Instruction) (values : Fin 12 → Word) (native : State) (origin : X86LegacyFetch.Basis native)
    (known : lookup native (physical instruction.source) = some (values instruction.source))
    (flags : BitVec 32) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (upper : origin.address.toInt + (bytes instruction).length + 3 < (2 ^ 47 : Int))
    (loaded : codeLoaded native origin.address.toInt (bytes instruction)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ copied after nextFlags,
      (X86FuelPrefix.fetches (X86WordLibrary.count (.copy (copy instruction)))).run native = .ok () copied ∧
      Step copied after ∧
      RegisterFrame (writes instruction) native copied ∧ RegisterFrame (writes instruction) native after ∧
      lookup after (physical instruction.destination) = some (evaluate instruction values) ∧
      after.regs.get? .rip = some ((address origin.address.toInt (bytes instruction).length).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .log_register_writes = some false ∧
      X86ControlFlags.Preserved native after := by
  obtain ⟨copied,after,nextFlags,run,step,copyFrame,frame,value,pointer,nextKnown,nextQuiet,control,_⟩ :=
    executes_with_copy_pointer other extra vector instruction values native origin known flags flagsKnown quiet upper loaded
  exact ⟨copied,after,nextFlags,run,step,copyFrame,frame,value,pointer,nextKnown,nextQuiet,control⟩

theorem executes_block_with_prefix_addresses (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers)
    (instruction : Instruction) (values : Fin 12 → Word) (native : State) (origin : X86LegacyFetch.Basis native)
    (known : lookup native (physical instruction.source) = some (values instruction.source))
    (flags : BitVec 32) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (upper : origin.address.toInt + (bytes instruction).length + 3 < (2 ^ 47 : Int))
    (loaded : codeLoaded native origin.address.toInt (bytes instruction)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags,
      (X86FuelPrefix.fetches (count instruction)).run native = .ok () after ∧
      RegisterFrame (writes instruction) native after ∧
      lookup after (physical instruction.destination) = some (evaluate instruction values) ∧
      after.regs.get? .rip = some ((address origin.address.toInt (bytes instruction).length).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .log_register_writes = some false ∧
      X86ControlFlags.Preserved native after ∧
      (∀ prefixCount ≤ count instruction, ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run native = .ok () observed →
          RegisterFrame (writes instruction) native observed) ∧
      X86WordPrimitive.StrictPrefixesIn origin.address.toInt (bytes instruction).length (count instruction) native := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨copied,after,nextFlags,copyRun,step,copyFrame,frame,value,pointer,nextKnown,nextQuiet,control,copiedRip⟩ :=
    executes_with_copy_pointer other extra vector instruction values native origin known flags flagsKnown quiet upper loaded
  have run : (X86FuelPrefix.fetches (count instruction)).run native = .ok () after :=
    X86FuelPrefix.fetches_then _ 1 native copied after copyRun (X86FuelPrefix.fetches_one _ _ step)
  have bound := copy_count_bound instruction
  refine ⟨after,nextFlags,run,frame,value,pointer,nextKnown,nextQuiet,control,?_,?_⟩
  · intro prefixCount within observed candidate
    have withinTwo : prefixCount ≤ 2 := by unfold count at within; omega
    interval_cases prefixCount
    · exact X86WordPrimitive.zero_prefixes native _ 0 (by omega) observed candidate
    · by_cases empty : X86WordLibrary.count (.copy (copy instruction)) = 0
      · have fullCount : count instruction = 1 := by simp [count,empty]
        rw [fullCount] at run
        have same := X86FuelPrefix.fetches_deterministic 1 native after observed run candidate
        subst observed
        exact frame
      · have copiedCount : X86WordLibrary.count (.copy (copy instruction)) = 1 := by omega
        rw [copiedCount] at copyRun
        have same := X86FuelPrefix.fetches_deterministic 1 native copied observed copyRun candidate
        subst observed
        exact copyFrame
    · have fullCount : count instruction = 2 := by unfold count at within ⊢; omega
      rw [fullCount] at run
      have same := X86FuelPrefix.fetches_deterministic 2 native after observed run candidate
      subst observed
      exact frame
  · intro prefixCount shorter observed candidate
    have withinOne : prefixCount ≤ 1 := by unfold count at shorter; omega
    interval_cases prefixCount
    · have same := X86FuelPrefix.fetches_deterministic 0 native native observed
        (X86FuelPrefix.fetches_zero native) candidate
      subst observed
      exact ⟨0,by rw [byte_length]; omega,by simpa [address] using origin.rip⟩
    · have copiedCount : X86WordLibrary.count (.copy (copy instruction)) = 1 := by
        unfold count at shorter
        omega
      rw [copiedCount] at copyRun
      have same := X86FuelPrefix.fetches_deterministic 1 native copied observed copyRun candidate
      subst observed
      exact ⟨(copyBytes instruction).length,by rw [byte_length]; omega,copiedRip⟩

theorem executes_block (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (instruction : Instruction) (values : Fin 12 → Word) (native : State) (origin : X86LegacyFetch.Basis native)
    (known : lookup native (physical instruction.source) = some (values instruction.source))
    (flags : BitVec 32) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false)
    (upper : origin.address.toInt + (bytes instruction).length + 3 < (2 ^ 47 : Int))
    (loaded : codeLoaded native origin.address.toInt (bytes instruction)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags,
      (X86FuelPrefix.fetches (count instruction)).run native = .ok () after ∧
      RegisterFrame (writes instruction) native after ∧
      lookup after (physical instruction.destination) = some (evaluate instruction values) ∧
      after.regs.get? .rip = some ((address origin.address.toInt (bytes instruction).length).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .log_register_writes = some false ∧
      X86ControlFlags.Preserved native after ∧
      ∀ prefixCount ≤ count instruction, ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run native = .ok () observed →
          RegisterFrame (writes instruction) native observed := by
  obtain ⟨after,nextFlags,run,frame,value,pointer,nextKnown,nextQuiet,control,prefixes,_⟩ :=
    executes_block_with_prefix_addresses other extra vector instruction values native origin known flags
      flagsKnown quiet upper loaded
  exact ⟨after,nextFlags,run,frame,value,pointer,nextKnown,nextQuiet,control,prefixes⟩

#print axioms computes
#print axioms lower?_source
#print axioms executes
#print axioms executes_block_with_prefix_addresses
#print axioms executes_block
end Mettapedia.Machines.TIsa.X86ShiftBlock
