import Mettapedia.Machines.TIsa.X86Comparison

/-!
# Original branch predicates after fetched comparisons

The complete generated condition evaluator is retained. Its unsigned and
zero predicates are linked to the actual fetched CMP/TEST results, including
the precise frame and missing-register failure. These are flag-condition
composition theorems; near-branch displacement reads, RIP updates and their
full instruction-fetch proof remain separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

tisa_model_file% "Mettapedia/Machines/TIsa/Models/X86Registers/BranchCondition.lean.inc"
  sha256 "920c42e8e2f9f973973e480a9c3b5d94d1e71ec5ac9a8a2685012c59d6725ce9"
  imports [Sail, X86Registers.Defs, X86Registers.SpecializationV1]

namespace Mettapedia.Machines.TIsa.X86BranchCondition

open _root_.X86Registers X86RegisterRefinement
open Sail.ConcurrencyInterfaceV1

inductive Condition where
  | below | aboveEqual | zero | nonzero | above
  deriving DecidableEq

def opcode : Condition → BitVec 8
  | .below => 0x82#8 | .aboveEqual => 0x83#8 | .zero => 0x84#8 | .nonzero => 0x85#8
  | .above => 0x87#8

def value (condition : Condition) (flags : BitVec 32) : Bool :=
  match condition with
  | .below => (1#1) == Functions._get_rflagsbits_cf flags
  | .aboveEqual => (0#1) == Functions._get_rflagsbits_cf flags
  | .zero => (1#1) == Functions._get_rflagsbits_zf flags
  | .nonzero => (0#1) == Functions._get_rflagsbits_zf flags
  | .above => ((0#1) == Functions._get_rflagsbits_cf flags) && ((0#1) == Functions._get_rflagsbits_zf flags)

theorem expression (condition : Condition) :
    Functions.jcc_cmovcc_setcc_spec (opcode condition) =
      (do let flags ← readReg .rflags; pure (value condition flags) : SailM Bool) := by
  cases condition with
  | below | aboveEqual | zero | nonzero => rfl
  | above =>
    funext state
    simp only [opcode, Functions.jcc_cmovcc_setcc_spec,
      show Functions.eq_bits_nat (Sail.BitVec.truncate ((0x87#8) &&& (0x0f#8)) 4) 0 = false from rfl,
      show Functions.eq_bits_nat (Sail.BitVec.truncate ((0x87#8) &&& (0x0f#8)) 4) 1 = false from rfl,
      show Functions.eq_bits_nat (Sail.BitVec.truncate ((0x87#8) &&& (0x0f#8)) 4) 2 = false from rfl,
      show Functions.eq_bits_nat (Sail.BitVec.truncate ((0x87#8) &&& (0x0f#8)) 4) 3 = false from rfl,
      show Functions.eq_bits_nat (Sail.BitVec.truncate ((0x87#8) &&& (0x0f#8)) 4) 4 = false from rfl,
      show Functions.eq_bits_nat (Sail.BitVec.truncate ((0x87#8) &&& (0x0f#8)) 4) 5 = false from rfl,
      show Functions.eq_bits_nat (Sail.BitVec.truncate ((0x87#8) &&& (0x0f#8)) 4) 6 = false from rfl,
      show Functions.eq_bits_nat (Sail.BitVec.truncate ((0x87#8) &&& (0x0f#8)) 4) 7 = true from rfl,
      Bool.false_eq_true, ite_false, ite_true]
    simp only [pure_bind]
    change (_root_.X86Registers.readReg .rflags >>= fun first =>
      (fun second => ((0#1) == Functions._get_rflagsbits_cf first) &&
        ((0#1) == Functions._get_rflagsbits_zf second)) <$> _root_.X86Registers.readReg .rflags : SailM Bool).run state =
      ((fun flags => ((0#1) == Functions._get_rflagsbits_cf flags) &&
        ((0#1) == Functions._get_rflagsbits_zf flags)) <$> _root_.X86Registers.readReg .rflags : SailM Bool).run state
    unfold _root_.X86Registers.readReg PreSail.readReg
    simp only [map_eq_pure_bind, run_bind, run_get]
    cases present : state.regs.get? .rflags with
    | none => rfl
    | some flags => simp only [present, run_pure]

theorem executes (condition : Condition) (state : State) (flags : BitVec 32)
    (present : state.regs.get? .rflags = some flags) :
    (Functions.jcc_cmovcc_setcc_spec (opcode condition)).run state =
      .ok (value condition flags) state := by
  rw [expression, run_bind, readRegister_exact, present]
  rfl

theorem missing_flags (condition : Condition) (state : State)
    (missing : state.regs.get? .rflags = none) :
    (Functions.jcc_cmovcc_setcc_spec (opcode condition)).run state = .error .Unreachable state := by
  rw [expression, run_bind, readRegister_exact, missing]

theorem above_equal_from_carry (state : State) (carry : BitVec 1)
    (present : (state.regs.get? .rflags).map Functions._get_rflagsbits_cf = some carry) :
    (Functions.jcc_cmovcc_setcc_spec (0x83#8)).run state = .ok ((0#1) == carry) state := by
  cases flagsKnown : state.regs.get? .rflags with
  | none => simp only [flagsKnown, Option.map_none, reduceCtorEq] at present
  | some flags =>
    have same := Option.some.inj (by simpa only [flagsKnown, Option.map_some] using present)
    simpa only [opcode, value, same] using executes .aboveEqual state flags flagsKnown

theorem zero_from_flag (state : State) (zero : BitVec 1)
    (present : (state.regs.get? .rflags).map Functions._get_rflagsbits_zf = some zero) :
    (Functions.jcc_cmovcc_setcc_spec (0x84#8)).run state = .ok ((1#1) == zero) state := by
  cases flagsKnown : state.regs.get? .rflags with
  | none => simp only [flagsKnown, Option.map_none, reduceCtorEq] at present
  | some flags =>
    have same := Option.some.inj (by simpa only [flagsKnown, Option.map_some] using present)
    simpa only [opcode, value, same] using executes .zero state flags flagsKnown

theorem unsigned_sense (left right : Word) :
    ((0#1) == Functions.bool_to_bits (left.toNat < right.toNat)) = decide (right.toNat ≤ left.toNat) := by
  by_cases below : left.toNat < right.toNat
  · have above : ¬right.toNat ≤ left.toNat := by omega
    simp [Functions.bool_to_bits, below, above]
  · have above : right.toNat ≤ left.toNat := by omega
    simp [Functions.bool_to_bits, below, above]

theorem zero_sense (number : Nat) :
    ((1#1) == Functions.zf_spec number) = decide (number = 0) := by
  by_cases zero : number = 0 <;> simp [Functions.zf_spec, zero]

local instance : MemoryPrimitives := X86Memory.ordinary

theorem compare_then_above_equal (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (source destination : Fin 16)
    (window : X86LegacyFetch.Window state (0x39#8) true source destination)
    (left right : Word) (flags : BitVec 32)
    (sourceKnown : lookup state source = some right)
    (destinationKnown : lookup state destination = some left)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (do Functions.x86_fetch_decode_execute (); Functions.jcc_cmovcc_setcc_spec (0x83#8)).run state =
      .ok (decide (right.toNat ≤ left.toNat)) after ∧
      X86Execution.RegisterFrame {.rflags, .rip} state after := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, executed, carry, _, frame⟩ := X86Comparison.fetched_compare_observes other vector state
    source destination window left right flags sourceKnown destinationKnown flagsKnown quiet
  refine ⟨after, ?_, frame⟩
  simp only [run_bind, executed]
  rw [above_equal_from_carry after _ carry, unsigned_sense]

theorem test_then_zero (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (source destination : Fin 16)
    (window : X86LegacyFetch.Window state (0x85#8) true source destination)
    (left right : Word) (flags : BitVec 32)
    (sourceKnown : lookup state source = some right)
    (destinationKnown : lookup state destination = some left)
    (flagsKnown : state.regs.get? .rflags = some flags)
    (quiet : state.regs.get? .log_register_writes = some false) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (do Functions.x86_fetch_decode_execute (); Functions.jcc_cmovcc_setcc_spec (0x84#8)).run state =
      .ok (decide ((left &&& right).toNat = 0)) after ∧
      X86Execution.RegisterFrame {.rflags, .rip} state after := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨after, executed, _, zero, frame⟩ := X86Comparison.fetched_test_observes other vector state
    source destination window left right flags sourceKnown destinationKnown flagsKnown quiet
  refine ⟨after, ?_, frame⟩
  simp only [run_bind, executed]
  rw [zero_from_flag after _ zero, zero_sense]

namespace Controls

private def empty : State := ⟨∅, (), ∅, (), 0, #[]⟩
private def before : State := { empty with regs := empty.regs.insert .rflags (0#32) }

theorem above_equal_accepts :
    (Functions.jcc_cmovcc_setcc_spec (0x83#8)).run before = .ok true before :=
  executes .aboveEqual before (0#32) (by simp [before])

theorem altered_condition_refuses_original_answer :
    (Functions.jcc_cmovcc_setcc_spec (0x82#8)).run before ≠ .ok true before := by
  change (Functions.jcc_cmovcc_setcc_spec (opcode .below)).run before ≠ .ok true before
  rw [executes .below before (0#32) (by simp [before])]
  intro wrong
  cases wrong

theorem missing_flags_refused :
    (Functions.jcc_cmovcc_setcc_spec (0x83#8)).run empty = .error .Unreachable empty :=
  missing_flags .aboveEqual empty (by simp [empty])

end Controls
end Mettapedia.Machines.TIsa.X86BranchCondition

#print axioms Mettapedia.Machines.TIsa.X86BranchCondition.compare_then_above_equal
#print axioms Mettapedia.Machines.TIsa.X86BranchCondition.test_then_zero
#print axioms Mettapedia.Machines.TIsa.X86BranchCondition.Controls.altered_condition_refuses_original_answer
