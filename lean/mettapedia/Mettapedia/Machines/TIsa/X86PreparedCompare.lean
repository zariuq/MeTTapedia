import Mettapedia.Machines.TIsa.X86SignedCmpFlags
import Mettapedia.Machines.TIsa.X86Comparison
import Mettapedia.Machines.TIsa.X86FuelPrefix
import Mettapedia.Machines.TIsa.X86CmpImmediate64

/-!
# Conditions for the prepared emitter's 64-bit comparisons

The branch emitter uses the opposite condition for its jump to the
false block. Both the materialized comparison and the fused branch
read the same flags set by qword subtraction.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86PreparedCompare

open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

def positive : Comparison → X86NativeJcc.Condition
  | .equal => .ordinary .zero
  | .notEqual => .ordinary .nonzero
  | .lessUnsigned => .ordinary .below
  | .lessEqualUnsigned => .belowEqual
  | .lessSigned => .signedLT
  | .lessEqualSigned => .signedLE

def negative : Comparison → X86NativeJcc.Condition
  | .equal => .ordinary .nonzero
  | .notEqual => .ordinary .zero
  | .lessUnsigned => .ordinary .aboveEqual
  | .lessEqualUnsigned => .ordinary .above
  | .lessSigned => .signedGE
  | .lessEqualSigned => .signedGT

theorem invert_opcode (condition : Comparison) :
    X86NativeJcc.opcode (negative condition) = X86NativeJcc.opcode (positive condition) ^^^ (1#8) := by
  cases condition <;> decide +kernel

structure Flags (left right : Word) (flags : BitVec 32) : Prop where
  carry : Functions._get_rflagsbits_cf flags = Functions.bool_to_bits (left.toNat < right.toNat)
  zero : Functions._get_rflagsbits_zf flags = Functions.bool_to_bits (left = right)
  greaterEqual : X86NativeJcc.selects .signedGE flags = decide (right.toInt ≤ left.toInt)

theorem subtraction_flags (state : State) (left right : Word) (incoming output : BitVec 32)
    (performed : (Functions.gpr_sub_spec_8 left right incoming).run state =
      .ok (left - right, output, 0#32) state) :
    Flags left right (X86Flags.mergeFlags incoming output) := by
  have carry := X86Comparison.sub_carry state left right incoming
  have zero := X86Comparison.sub_zero state left right incoming
  simp only [map_eq_pure_bind, run_bind, performed, run_pure] at carry zero
  refine ⟨?_, ?_, X86SignedCmpFlags.signed_gate state left right incoming output performed⟩
  · rw [X86Comparison.merged_carry]
    exact (EStateM.Result.ok.inj carry).1
  · rw [X86Comparison.merged_zero, (EStateM.Result.ok.inj zero).1]
    have zeroDifference : (left - right).toNat = 0 ↔ left = right := by
      rw [← BitVec.toNat_zero (w := 64), BitVec.toNat_inj,
        BitVec.sub_eq_iff_eq_add, BitVec.zero_add]
    by_cases same : left = right
    · rw [zeroDifference.mpr same]
      simp [Functions.zf_spec, Functions.bool_to_bits, same]
    · have notZero : ((left - right).toNat == 0) = false :=
        beq_eq_false_iff_ne.mpr (fun equal => same (zeroDifference.mp equal))
      rw [Functions.zf_spec, notZero, decide_eq_false same]
      rfl

private theorem condition_bit (flag : Bool) :
    (((1#1) == Functions.bool_to_bits flag) = flag) ∧
      (((0#1) == Functions.bool_to_bits flag) = !flag) := by
  cases flag <;> decide +kernel

theorem condition_values {left right : Word} {flags : BitVec 32}
    (known : Flags left right flags) (condition : Comparison) :
    X86NativeJcc.selects (positive condition) flags = condition.evaluate left right ∧
      X86NativeJcc.selects (negative condition) flags = !(condition.evaluate left right) := by
  have zero : ((1#1) == Functions._get_rflagsbits_zf flags) = decide (left = right) := by
    rw [known.zero]
    exact (condition_bit _).1
  have nonzero : ((0#1) == Functions._get_rflagsbits_zf flags) = !decide (left = right) := by
    rw [known.zero]
    exact (condition_bit _).2
  have below : ((1#1) == Functions._get_rflagsbits_cf flags) = decide (left.toNat < right.toNat) := by
    rw [known.carry]
    exact (condition_bit _).1
  have aboveEqual : ((0#1) == Functions._get_rflagsbits_cf flags) = !decide (left.toNat < right.toNat) := by
    rw [known.carry]
    exact (condition_bit _).2
  have signed : (Functions._get_rflagsbits_sf flags == Functions._get_rflagsbits_of flags) =
      decide (right.toInt ≤ left.toInt) := known.greaterEqual
  have decideEq : (left == right) = decide (left = right) :=
    Bool.eq_iff_iff.mpr (by simp)
  have natEqual : decide (left = right) = decide (left.toNat = right.toNat) :=
    Bool.eq_iff_iff.mpr (by simp [BitVec.toNat_inj])
  have intEqual : decide (left = right) = decide (left.toInt = right.toInt) :=
    Bool.eq_iff_iff.mpr (by simp [BitVec.toInt_inj])
  have unsignedLE : (decide (left.toNat < right.toNat) || decide (left = right)) =
      decide (left.toNat ≤ right.toNat) := by
    rw [natEqual]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega
  have unsignedGT : ((!decide (left.toNat < right.toNat)) && (!decide (left = right))) =
      !decide (left.toNat ≤ right.toNat) := by
    rw [← Bool.not_or, unsignedLE]
  have signedLT : (!decide (right.toInt ≤ left.toInt)) = decide (left.toInt < right.toInt) := by
    rw [← decide_not]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  have signedLE : (decide (left = right) || !decide (right.toInt ≤ left.toInt)) =
      decide (left.toInt ≤ right.toInt) := by
    rw [intEqual, signedLT]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega
  have signedGT : ((!decide (left = right)) && decide (right.toInt ≤ left.toInt)) =
      !decide (left.toInt ≤ right.toInt) := by
    calc
      _ = (!(decide (left = right) || !decide (right.toInt ≤ left.toInt))) := by simp
      _ = _ := by rw [signedLE]
  cases condition <;>
    simp only [positive, negative, X86NativeJcc.selects, X86BranchCondition.value, Comparison.evaluate,
      zero, nonzero, below, aboveEqual, signed, decideEq, BitVec.lt_def, BitVec.le_def,
      BitVec.slt_eq_decide, BitVec.sle_eq_decide, bne, Bool.not_not,
      unsignedLE, unsignedGT, signedLE, signedGT, eq_self, and_self]
  rw [← signedLT, Bool.not_not]
  exact ⟨rfl, rfl⟩

theorem branch_from_flags (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (condition : Comparison) (left right : Word)
    (inputs : X86NativeJcc.Inputs state (negative condition)) (flags : Flags left right inputs.flags) :
    letI : OtherOpcodeHandlers := X86EscapeFetch.linked other extra
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state = .ok ()
      (X86Move.putPointer state
        (if condition.evaluate left right then address inputs.start.toInt 6 else inputs.target)) := by
  let : OtherOpcodeHandlers := X86EscapeFetch.linked other extra
  let : VectorOpcodeHandlers := vector
  rw [X86NativeJcc.fetched other extra vector state (negative condition) inputs, X86NativeJcc.next,
    (condition_values flags condition).2]
  cases condition.evaluate left right <;> rfl

structure BranchSite (state : State) (condition : Comparison) (start : BitVec 48) where
  target : BitVec 48
  displacement : BitVec 32
  upper : start.toInt + 6 < (2^47 : Int)
  jump : target.toInt = start.toInt + 6 + displacement.toInt
  bytes : codeLoaded state start.toInt (X86NativeJcc.code (negative condition) displacement)

private def compareResult (state : State) (next : BitVec 48) (flags : BitVec 32) : State :=
  X86Move.putPointer (X86Flags.putFlags state flags) next

private theorem compare_frame (state : State) (next : BitVec 48) (flags : BitVec 32) :
    RegisterFrame {.rflags, .rip} state (compareResult state next flags) :=
  (flags_frame _ _).trans (pointer_frame _ _)

private def branchInput (state : State) (facts : X86PlainFetch.Facts state)
    (quiet : state.regs.get? .log_register_writes = some false)
    (condition : Comparison) (start : BitVec 48) (site : BranchSite state condition start) (flags : BitVec 32) :
    X86NativeJcc.Inputs (compareResult state start flags) (negative condition) := by
  have framed := compare_frame state start flags
  refine {
    control := facts.control
    attributes := facts.attributes
    status := (framed.registers .ms_reg (by decide)).trans facts.status
    fault := (framed.registers .fault_reg (by decide)).trans facts.fault
    msrs := (framed.registers .msrs (by decide)).trans facts.msrs
    segments := (framed.registers .seg_hidden_attrs (by decide)).trans facts.segments
    longMode := facts.longMode
    codeMode := facts.codeMode
    application := (framed.registers .app_view (by decide)).trans facts.application
    start := start
    target := site.target
    displacement := site.displacement
    flags := flags
    upper := site.upper
    jump := site.jump
    rip := X86FuelPrefix.pointer_rip _ _
    flagsKnown := ?_
    quiet := (framed.registers .log_register_writes (by decide)).trans quiet
    bytes := ?_ }
  · simp [compareResult, X86Move.putPointer,
      X86Flags.putFlags, Std.ExtDHashMap.get?_insert]
  · intro index byte present
    rw [framed.memory]
    exact site.bytes index byte present

noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :=
  X86EscapeFetch.linked (X86FrameIncrement.linkedHandlers (X86Arithmetic.linkedHandlers other)) extra

private theorem finish_fused (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State)
    (facts : X86PlainFetch.Facts state) (quiet : state.regs.get? .log_register_writes = some false)
    (start : BitVec 48) (condition : Comparison) (branch : BranchSite state condition start)
    (left right : Word) (incoming output : BitVec 32)
    (computed : (Functions.gpr_sub_spec_8 left right incoming).run state =
      .ok (left - right, output, 0#32) state)
    (compared : letI : OtherOpcodeHandlers := handlers other extra
      letI : VectorOpcodeHandlers := vector
      (Functions.x86_fetch_decode_execute ()).run state =
        .ok () (compareResult state start (X86Flags.mergeFlags incoming output))) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    let target := if condition.evaluate left right then address start.toInt 6 else branch.target
    ∃ after, (X86FuelPrefix.fetches 2).run state = .ok () after ∧
      after.regs.get? .rip = some (target.signExtend 64) ∧ RegisterFrame {.rflags, .rip} state after ∧
      ∃ flags, after.regs.get? .rflags = some flags := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let merged := X86Flags.mergeFlags incoming output
  let reached := compareResult state start merged
  let site := branchInput state facts quiet condition start branch merged
  have selected := branch_from_flags (X86FrameIncrement.linkedHandlers (X86Arithmetic.linkedHandlers other))
    extra vector reached condition left right site (subtraction_flags state left right incoming output computed)
  let target := if condition.evaluate left right then address start.toInt 6 else branch.target
  refine ⟨X86Move.putPointer reached target, ?_, X86FuelPrefix.pointer_rip .., ?_, ⟨merged, ?_⟩⟩
  · exact X86FuelPrefix.fetches_then 1 1 _ _ _
      (X86FuelPrefix.fetches_one _ _ compared) (X86FuelPrefix.fetches_one _ _ selected)
  · apply RegisterFrame.mono ((compare_frame _ _ _).trans (pointer_frame _ _))
    simp
  · exact ((pointer_frame reached target).registers .rflags (by decide)).trans site.flagsKnown

/-- The register CMP and the following inverse Jcc execute from their
actual qword encodings. The result is independent of the displacement
chosen to lay out the surrounding blocks. -/
theorem fused_register_branch_flags (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (source destination : Fin 16)
    (window : X86LegacyFetch.Window state (0x39#8) true source destination)
    (condition : Comparison) (left right : Word) (flags : BitVec 32)
    (leftRead : lookup state destination = some left) (rightRead : lookup state source = some right)
    (flagRead : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (branch : BranchSite state condition window.next) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    let target := if condition.evaluate left right then address window.next.toInt 6 else branch.target
    ∃ after, (X86FuelPrefix.fetches 2).run state = .ok () after ∧
      after.regs.get? .rip = some (target.signExtend 64) ∧ RegisterFrame {.rflags, .rip} state after ∧
      ∃ flags, after.regs.get? .rflags = some flags := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨output, compared, _, _, computed⟩ :=
    X86Comparison.fetched_compare64_defined (handlers other extra) vector state source destination
      window left right flags rightRead leftRead flagRead quiet
  exact finish_fused other extra vector state (.ofBasis window.toBasis) quiet window.next condition
    branch left right flags output computed compared

theorem fused_immediate_branch_flags (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (origin : X86LegacyFetch.Basis state)
    (destination : Fin 16) (immediate : X86CmpImmediate64.Literal)
    (condition : Comparison) (left : Word) (flags : BitVec 32) (start : BitVec 48)
    (advance : origin.next.toInt + 4 = start.toInt)
    (leftRead : lookup state destination = some left)
    (flagRead : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat =
      some (X86RegisterEncoding.rex true 7 destination))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x81#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat =
      some (X86RegisterEncoding.modRM 7 destination))
    (present : ∀ index < 4, state.mem.get? ((address origin.next.toInt index).signExtend 52).toNat =
      some (immediate.bits.extractLsb' (8 * index) 8))
    (branch : BranchSite state condition start) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    let target := if condition.evaluate left immediate.value then address start.toInt 6 else branch.target
    ∃ after, (X86FuelPrefix.fetches 2).run state = .ok () after ∧
      after.regs.get? .rip = some (target.signExtend 64) ∧ RegisterFrame {.rflags, .rip} state after ∧
      ∃ flags, after.regs.get? .rflags = some flags := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨output, ran, proved⟩ := X86CmpImmediate64.fetched (handlers other extra) vector
    state origin start destination immediate left flags advance leftRead flagRead quiet
    prefixByte opcodeByte modrmByte present
  exact finish_fused other extra vector state (.ofBasis origin) quiet start condition branch
    left immediate.value flags output proved.computed ran

theorem fused_register_branch (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (source destination : Fin 16)
    (window : X86LegacyFetch.Window state (0x39#8) true source destination)
    (condition : Comparison) (left right : Word) (flags : BitVec 32)
    (leftRead : lookup state destination = some left) (rightRead : lookup state source = some right)
    (flagRead : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (branch : BranchSite state condition window.next) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    let target := if condition.evaluate left right then address window.next.toInt 6 else branch.target
    ∃ after, (X86FuelPrefix.fetches 2).run state = .ok () after ∧
      after.regs.get? .rip = some (target.signExtend 64) ∧ RegisterFrame {.rflags, .rip} state after := by
  obtain ⟨after, ran, rip, frame, _⟩ := fused_register_branch_flags other extra vector state source destination
    window condition left right flags leftRead rightRead flagRead quiet branch
  exact ⟨after, ran, rip, frame⟩

theorem fused_immediate_branch (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (origin : X86LegacyFetch.Basis state)
    (destination : Fin 16) (immediate : X86CmpImmediate64.Literal)
    (condition : Comparison) (left : Word) (flags : BitVec 32) (start : BitVec 48)
    (advance : origin.next.toInt + 4 = start.toInt)
    (leftRead : lookup state destination = some left)
    (flagRead : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false)
    (prefixByte : state.mem.get? (origin.address.signExtend 52).toNat =
      some (X86RegisterEncoding.rex true 7 destination))
    (opcodeByte : state.mem.get? (origin.opcodeAddress.signExtend 52).toNat = some (0x81#8))
    (modrmByte : state.mem.get? (origin.modrmAddress.signExtend 52).toNat =
      some (X86RegisterEncoding.modRM 7 destination))
    (present : ∀ index < 4, state.mem.get? ((address origin.next.toInt index).signExtend 52).toNat =
      some (immediate.bits.extractLsb' (8 * index) 8))
    (branch : BranchSite state condition start) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    let target := if condition.evaluate left immediate.value then address start.toInt 6 else branch.target
    ∃ after, (X86FuelPrefix.fetches 2).run state = .ok () after ∧
      after.regs.get? .rip = some (target.signExtend 64) ∧ RegisterFrame {.rflags, .rip} state after := by
  obtain ⟨after, ran, rip, frame, _⟩ := fused_immediate_branch_flags other extra vector state origin destination
    immediate condition left flags start advance leftRead flagRead quiet prefixByte opcodeByte modrmByte present branch
  exact ⟨after, ran, rip, frame⟩

end Mettapedia.Machines.TIsa.X86PreparedCompare
