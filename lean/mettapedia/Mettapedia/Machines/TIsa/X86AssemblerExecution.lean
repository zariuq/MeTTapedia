import Mettapedia.Machines.TIsa.X86Assembler
import Mettapedia.Machines.TIsa.X86UnconditionalJump
import Mettapedia.Machines.TIsa.X86CodePlacement
import Mettapedia.Machines.TIsa.X86EscapeFetch

/-!
# Assembled near branches executed by the original x86 model

Assembler success derives the branch record, exact loaded bytes and signed
target equation. The original fetched-instruction contract supplies execution
and its register/memory frame. Entry mode, canonical placement and quiet
register logging remain explicit; no native result or target equation is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86AssemblerExecution
open _root_.X86Registers X86RegisterRefinement X86Execution X86Assembler
local instance : MemoryPrimitives := X86Memory.ordinary

theorem encode32_byte (word : BitVec 32) (index : Fin 4) :
    (RelativeBranch.encode32 word)[index.val]? = some (word.extractLsb' (8 * index.val) 8) := by
  fin_cases index
  all_goals
    simp only [RelativeBranch.encode32,unpackBytes,List.getElem?_cons_zero,List.getElem?_cons_succ]
    apply congrArg some
    apply BitVec.eq_of_getLsbD_eq
    intro bit within
    interval_cases bit <;> simp [within]

theorem encode32_list (word : BitVec 32) :
    RelativeBranch.encode32 word = (List.range 4).map (fun index => word.extractLsb' (8 * index) 8) := by
  apply List.ext_getElem?
  intro index
  by_cases within : index < 4
  · rw [List.getElem?_map,List.getElem?_range within,Option.map_some]
    exact encode32_byte word ⟨index,within⟩
  · rw [List.getElem?_eq_none (by rw [RelativeBranch.encode32_length]; omega),
      List.getElem?_eq_none (by simp only [List.length_map,List.length_range]; omega)]

theorem jump_code_byte (word : BitVec 32) (index byte : Nat)
    (present : (X86UnconditionalJump.Block.code word)[index]? = some byte) :
    ([0xe9] ++ RelativeBranch.encode32 word)[index]? = some (BitVec.ofNat 8 byte) := by
  have inside : index < 5 := by
    have bound := (List.getElem?_eq_some_iff.mp present).1
    simpa only [X86UnconditionalJump.Block.code_length] using bound
  cases index with
  | zero =>
    have same : (0xe9 : Nat) = byte := by simpa [X86UnconditionalJump.Block.code] using present
    subst byte
    rfl
  | succ index =>
    have bound : index < 4 := by omega
    have same : (word.extractLsb' (8 * index) 8).toNat = byte := by
      simpa [X86UnconditionalJump.Block.code,bound] using present
    rw [← same]
    simpa only [List.cons_append,List.nil_append,List.getElem?_cons_succ,BitVec.ofNat_toNat,BitVec.setWidth_eq]
      using encode32_byte word ⟨index,bound⟩

def jumpInput (labels : Labels) (emission : Emission) (fixup : Fixup)
    (recorded : fixup.Recorded labels 0 emission.bytes) (inside : fixup.target ≤ emission.bytes.length)
    (plain : fixup.condition = none) (native : State) (base : Int) (origin : X86LegacyFetch.Basis native)
    (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + emission.bytes.length + 3 < (2 ^ 47 : Int))
    (location : origin.address.toInt = base + fixup.offset)
    (loaded : X86CodePlacement.Placed native base (X86Assembler.view emission.bytes))
    (quiet : native.regs.get? .log_register_writes = some false) : X86UnconditionalJump.Block.Inputs native := by
  let word := BitVec.ofInt 32 (RelativeBranch.displacement fixup.field fixup.target)
  have extent : fixup.offset + 5 ≤ emission.bytes.length := by
    have bound := recorded.upper
    rw [Fixup.bytes_length,plain] at bound
    change fixup.offset + (1 + 4) ≤ 0 + emission.bytes.length at bound
    omega
  refine {
    toBasis := origin
    quiet := quiet
    upper := by rw [location]; omega
    displacement := word
    target := address base fixup.target
    jump := ?_
    loaded := ?_ }
  · have target := address_toInt base lower (by omega : base + emission.bytes.length < (2 ^ 47 : Int))
      fixup.target inside
    have signed : word.toInt = RelativeBranch.displacement fixup.field fixup.target :=
      BitVec.toInt_ofInt_eq_self (by decide) recorded.fits.1 recorded.fits.2
    rw [target,location,signed]
    simp only [RelativeBranch.displacement,Fixup.field,plain,prefixLength,Nat.cast_add]
    omega
  · intro index byte present
    have inCode : index < 5 := by
      have bound := (List.getElem?_eq_some_iff.mp present).1
      simpa only [X86UnconditionalJump.Block.code_length] using bound
    have emitted : fixup.bytes[index]? = some (BitVec.ofNat 8 byte) := by
      simpa only [Fixup.bytes,plain,opcodeBytes] using jump_code_byte word index byte present
    have observed := recorded.reads index (by rw [Fixup.bytes_length,plain]; change index < 1 + 4; omega)
    rw [Nat.sub_zero,emitted] at observed
    have nativeByte := loaded (fixup.offset + index) (BitVec.ofNat 8 byte) observed
    have shifted : address base (fixup.offset + index) = address origin.address.toInt index := by
      unfold address
      rw [location]
      congr 1
      omega
    simpa only [shifted] using nativeByte

theorem assembled_jump (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (chunks : List Chunk) (emission : Emission) (assembled : assemble chunks = some emission)
    (fixup : Fixup) (member : fixup ∈ emission.fixups) (plain : fixup.condition = none)
    (native : State) (base : Int) (origin : X86LegacyFetch.Basis native)
    (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + emission.bytes.length + 3 < (2 ^ 47 : Int))
    (location : origin.address.toInt = base + fixup.offset)
    (loaded : X86CodePlacement.Placed native base (X86Assembler.view emission.bytes))
    (quiet : native.regs.get? .log_register_writes = some false) :
    letI : OtherOpcodeHandlers := X86UnconditionalJump.linked other
    letI : VectorOpcodeHandlers := vector
    Step native (X86Move.putPointer native (address base fixup.target)) ∧
      RegisterFrame {.rip} native (X86Move.putPointer native (address base fixup.target)) := by
  let : OtherOpcodeHandlers := X86UnconditionalJump.linked other
  let : VectorOpcodeHandlers := vector
  obtain ⟨_length,labels,_resolved,records⟩ := assemble_correct chunks emission assembled
  let input := jumpInput labels emission fixup (records fixup member).1 (records fixup member).2
    plain native base origin lower upper location loaded quiet
  exact X86UnconditionalJump.Block.executes other vector native input

def conditionCode : X86BranchCondition.Condition → Fin 16
  | .below => 2 | .aboveEqual => 3 | .zero => 4 | .nonzero => 5 | .above => 7

theorem condition_opcode (condition : X86BranchCondition.Condition) :
    BitVec.ofNat 8 (128 + (conditionCode condition).val) = X86BranchCondition.opcode condition := by
  cases condition <;> rfl

theorem conditional_run (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (labels : Labels) (emission : Emission) (fixup : Fixup)
    (recorded : fixup.Recorded labels 0 emission.bytes) (inside : fixup.target ≤ emission.bytes.length)
    (condition : X86BranchCondition.Condition) (kind : fixup.condition = some (conditionCode condition))
    (native : State) (base : Int) (origin : X86LegacyFetch.Basis native)
    (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + emission.bytes.length + 3 < (2 ^ 47 : Int))
    (location : origin.address.toInt = base + fixup.offset)
    (loaded : X86CodePlacement.Placed native base (X86Assembler.view emission.bytes))
    (flags : BitVec 32) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false) :
    letI : OtherOpcodeHandlers := X86EscapeFetch.linked other extra
    letI : VectorOpcodeHandlers := vector
    Step native (X86Move.putPointer native
      (if X86BranchCondition.value condition flags then address base fixup.target else address base (fixup.offset + 6))) ∧
      RegisterFrame {.rip} native (X86Move.putPointer native
        (if X86BranchCondition.value condition flags then address base fixup.target else address base (fixup.offset + 6))) := by
  let : OtherOpcodeHandlers := X86EscapeFetch.linked other extra
  let : VectorOpcodeHandlers := vector
  let word := BitVec.ofInt 32 (RelativeBranch.displacement fixup.field fixup.target)
  have extent : fixup.offset + 6 ≤ emission.bytes.length := by
    have bound := recorded.upper
    rw [Fixup.bytes_length,kind] at bound
    change fixup.offset + (2 + 4) ≤ 0 + emission.bytes.length at bound
    omega
  have finish := address_toInt base lower (by omega : base + emission.bytes.length < (2 ^ 47 : Int))
    (fixup.offset + 6) extent
  have target := address_toInt base lower (by omega : base + emission.bytes.length < (2 ^ 47 : Int))
    fixup.target inside
  have signed : word.toInt = RelativeBranch.displacement fixup.field fixup.target :=
    BitVec.toInt_ofInt_eq_self (by decide) recorded.fits.1 recorded.fits.2
  have fieldPlace : origin.modrmAddress.toInt = base + fixup.field := by
    have next := origin.step2
    rw [location] at next
    simp only [Fixup.field,kind,prefixLength]
    omega
  have opcodePlace : origin.opcodeAddress.toInt = base + fixup.offset + 1 := by
    have next := origin.step1
    rw [location] at next
    omega
  have addressAt (index : Nat) : address base (fixup.offset + index) = address origin.address.toInt index := by
    unfold address
    rw [location]
    congr 1
    omega
  have escapeByte : native.mem.get? (origin.address.signExtend 52).toNat = some (0x0f#8) := by
    have observed := recorded.opcode_reads 0 (by rw [kind]; change (0 : Nat) < 2; decide)
    rw [kind] at observed
    change emission.bytes[fixup.offset + 0]? = some (0x0f#8) at observed
    have original := loaded (fixup.offset + 0) _ observed
    rw [addressAt 0] at original
    simpa only [address,Nat.cast_zero,Int.add_zero,BitVec.ofInt_toInt] using original
  have opcodeByte : native.mem.get? (origin.opcodeAddress.signExtend 52).toNat =
      some (X86BranchCondition.opcode condition) := by
    have observed := recorded.opcode_reads 1 (by rw [kind]; change (1 : Nat) < 2; decide)
    rw [kind] at observed
    change emission.bytes[fixup.offset + 1]? = some (BitVec.ofNat 8 (128 + (conditionCode condition).val)) at observed
    rw [condition_opcode] at observed
    have original := loaded (fixup.offset + 1) _ observed
    have shifted : address base (fixup.offset + 1) = origin.opcodeAddress := by
      unfold address
      rw [Nat.cast_add,Nat.cast_one]
      rw [← Int.add_assoc]
      rw [← opcodePlace,BitVec.ofInt_toInt]
    simpa only [shifted] using original
  have operands : ∀ index < 4,
      native.mem.get? ((address origin.modrmAddress.toInt index).signExtend 52).toNat =
        some (word.extractLsb' (8 * index) 8) := by
    intro index within
    have observed := recorded.operand_reads index within
    rw [encode32_byte _ ⟨index,within⟩] at observed
    have original := loaded (fixup.field + index) _ observed
    have shifted : address base (fixup.field + index) = address origin.modrmAddress.toInt index := by
      unfold address
      rw [fieldPlace,Nat.cast_add]
      congr 1
      omega
    simpa only [shifted] using original
  have run := X86EscapeFetch.fetched_branch other extra vector condition native origin.address origin.opcodeAddress
    origin.modrmAddress (address base (fixup.offset + 6)) (address base fixup.target) origin.control origin.attributes flags word
    origin.step1 (by have first := origin.step1; have second := origin.step2; omega)
    (by rw [fieldPlace,finish]; simp only [Fixup.field,kind,prefixLength,Nat.cast_add,Nat.cast_ofNat]; omega)
    (by rw [target,finish,signed]; simp only [RelativeBranch.displacement,Fixup.field,kind,prefixLength,Nat.cast_add,Nat.cast_ofNat]; omega)
    origin.status origin.fault origin.msrs origin.segments origin.longMode origin.codeMode origin.application origin.rip
    flagsKnown quiet escapeByte opcodeByte operands
  exact ⟨run,pointer_frame _ _⟩

theorem assembled_conditional (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (chunks : List Chunk) (emission : Emission)
    (assembled : assemble chunks = some emission) (fixup : Fixup) (member : fixup ∈ emission.fixups)
    (condition : X86BranchCondition.Condition) (kind : fixup.condition = some (conditionCode condition))
    (native : State) (base : Int) (origin : X86LegacyFetch.Basis native)
    (lower : -(2 ^ 47 : Int) ≤ base) (upper : base + emission.bytes.length + 3 < (2 ^ 47 : Int))
    (location : origin.address.toInt = base + fixup.offset)
    (loaded : X86CodePlacement.Placed native base (X86Assembler.view emission.bytes))
    (flags : BitVec 32) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false) :
    letI : OtherOpcodeHandlers := X86EscapeFetch.linked other extra
    letI : VectorOpcodeHandlers := vector
    Step native (X86Move.putPointer native
      (if X86BranchCondition.value condition flags then address base fixup.target else address base (fixup.offset + 6))) ∧
      RegisterFrame {.rip} native (X86Move.putPointer native
        (if X86BranchCondition.value condition flags then address base fixup.target else address base (fixup.offset + 6))) := by
  obtain ⟨_length,labels,_resolved,records⟩ := assemble_correct chunks emission assembled
  exact conditional_run other extra vector labels emission fixup (records fixup member).1 (records fixup member).2
    condition kind native base origin lower upper location loaded flags flagsKnown quiet

end Mettapedia.Machines.TIsa.X86AssemblerExecution
