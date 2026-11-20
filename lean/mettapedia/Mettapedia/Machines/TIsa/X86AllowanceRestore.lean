import Mettapedia.Machines.TIsa.X86P1Sub1Exit

/-!
# Restoring six saved registers from a prepared native frame

The allowance epilogue adds the RBP pop to the established five-register
epilogue. The same proof applies at any placement of those exact bytes.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

namespace Mettapedia.Machines.TIsa.X86AllowanceRestore

open _root_.X86Registers X86Execution X86RegisterRefinement
open X86P1Sub1Exit (SavedStack)
local instance : MemoryPrimitives := X86Memory.ordinary

def bytes : List Nat := 0x5d :: X86Epilogue.expected

structure Entry (native : State) extends SavedStack native where
  mode : X86PlainFetch.Facts native
  code : BitVec 48
  codeUpper : code.toInt + 11 < (2^47 : Int)
  rip : native.regs.get? .rip = some (code.signExtend 64)
  loaded : codeLoaded native code.toInt bytes
  visible : Vector (BitVec 16) 6
  controls : Vector (BitVec 64) 17
  flags : BitVec 32
  visibleKnown : native.regs.get? .seg_visibles = some visible
  controlsKnown : native.regs.get? .ctrs = some controls
  flagsKnown : native.regs.get? .rflags = some flags
  quiet : native.regs.get? .log_register_writes = some false

def afterRbp {native : State} (entry : Entry native) : State :=
  X86Stack.popResult native 5 entry.rbp entry.stack (address entry.code.toInt 1)

private theorem code_int {native : State} (entry : Entry native) :
    (address entry.code.toInt 1).toInt = entry.code.toInt + 1 :=
  address_toInt _ (BitVec.le_toInt _) entry.codeUpper _ (by decide)

private def epilogueInput {native : State} (entry : Entry native) : X86Epilogue.Inputs (afterRbp entry) := by
  let frame := X86Stack.pop_frame native 5 entry.rbp entry.stack (address entry.code.toInt 1)
  let mode := entry.mode
  refine {
    stack := entry.stack
    stackUpper := entry.upper
    stackKnown := X86Stack.pop_stack _ _ _ _ _ (by decide)
    saved := entry.saved
    returnAddress := entry.returnAddress
    visible := entry.visible
    controls := entry.controls
    flags := entry.flags
    visibleKnown := (frame.registers .seg_visibles (by decide)).trans entry.visibleKnown
    controlsKnown := (frame.registers .ctrs (by decide)).trans entry.controlsKnown
    flagsKnown := (frame.registers .rflags (by decide)).trans entry.flagsKnown
    quiet := (frame.registers .log_register_writes (by decide)).trans entry.quiet
    aligned := entry.aligned
    present := fun slot byte within => by
      rw [afterRbp, frame.memory]
      exact entry.present slot byte within
    context := { mode with
      status := (frame.registers .ms_reg (by decide)).trans mode.status
      fault := (frame.registers .fault_reg (by decide)).trans mode.fault
      msrs := (frame.registers .msrs (by decide)).trans mode.msrs
      segments := (frame.registers .seg_hidden_attrs (by decide)).trans mode.segments
      application := (frame.registers .app_view (by decide)).trans mode.application }
    code := address entry.code.toInt 1
    codeUpper := by rw [code_int entry]; have := entry.codeUpper; omega
    loaded := ?_
    rip := X86FuelPrefix.pointer_rip _ _ }
  intro index byte present
  rw [afterRbp, frame.memory, code_int entry]
  have shifted : address (entry.code.toInt + 1) index = address entry.code.toInt (index + 1) := by
    simp only [address, Nat.cast_add, Nat.cast_one]
    congr 1
    omega
  rw [shifted]
  exact entry.loaded (index + 1) byte (by simpa only [bytes, List.getElem?_cons_succ] using present)

theorem restores (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (native : State) (entry : Entry native) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 7).run native = .ok () after ∧
      RegisterFrame (insert .rbp X86Epilogue.clobbers) native after ∧
      after.regs.get? .rip = some (entry.returnAddress.signExtend 64) ∧
      lookup after 4 = some ((address entry.stack.toInt 48).signExtend 64) ∧
      lookup after 5 = some entry.rbp ∧
      (∀ index : Fin 5, lookup after (X86Epilogue.target index) = some (entry.saved index)) := by
  let : OtherOpcodeHandlers := X86Stack.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  have first := X86Stack.fetched_pop other vector native 5 entry.mode
    entry.code entry.code (address entry.code.toInt 1) entry.bottom entry.stack entry.rbp
    entry.visible entry.controls entry.flags
    (by simp) (by rw [code_int entry]; rfl) entry.step
    (by have := entry.upper; have := entry.step; omega) entry.rip entry.current
    entry.controlsKnown entry.flagsKnown entry.visibleKnown entry.quiet entry.bottomAligned
    (by intro impossible; exact (impossible (by decide)).elim)
    (by simpa only [address, Nat.cast_zero, Int.add_zero, BitVec.ofInt_toInt,
      show X86Stack.popOpcode (5 : Fin 16) = (93#8) by decide] using entry.loaded 0 93 rfl)
    entry.bottomBytes
  let tail := epilogueInput entry
  let after := X86Epilogue.finished (afterRbp entry) tail
  have later := X86Epilogue.executes other vector (afterRbp entry) tail
  have result := X86Epilogue.finished_result (afterRbp entry) tail
  have frame := (X86Stack.pop_frame native 5 entry.rbp entry.stack (address entry.code.toInt 1)).trans result.frame
  have sameReturn : tail.returnAddress = entry.returnAddress := rfl
  have sameStack : X86Epilogue.stackAt tail 6 = address entry.stack.toInt 48 := rfl
  have sameSaved : tail.saved = entry.saved := rfl
  refine ⟨after, X86FuelPrefix.fetches_cons 6 _ _ _ first later, frame.mono (by decide),
    by simpa only [sameReturn] using result.pointer,
    by simpa only [sameStack] using result.stackPointer, ?_,
    by simpa only [sameSaved] using result.saved⟩
  rw [result.frame.lookup 5 (by decide)]
  exact X86Stack.pop_value native 5 entry.rbp entry.stack (address entry.code.toInt 1)

end Mettapedia.Machines.TIsa.X86AllowanceRestore
