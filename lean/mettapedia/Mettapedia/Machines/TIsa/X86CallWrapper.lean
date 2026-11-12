import Mettapedia.Machines.TIsa.X86Prologue

/-!
# Reusable composition from a fetched body contract to the public ABI

The prologue proves saved-stack provenance. A body contract supplies its actual
fetched run, register/byte frame, flags and epilogue destination. Composition
executes the original five pushes and six epilogue instructions, restores the
caller's callee-saved registers, preserves the body's memory and return value,
and restricts the complete call's register frame to caller-clobbered registers.

The concrete empty-body control exercises the wrapper and rejects losing a saved
register. Bodies with effects, compiled-image placement, source correspondence
and whole-emitter correctness retain their own obligations.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.TIsa.X86CallWrapper
open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

def bodyRegisters : Finset Register :=
  {.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15, .rflags, .rip}
def savedRegisters : Finset Register := {.rbx, .r12, .r13, .r14, .r15}
def callerRegisters : Finset Register :=
  {.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11, .rflags, .rsp, .rip}
def allRegisters : Finset Register := {.rsp, .rip} ∪ bodyRegisters ∪ X86Epilogue.clobbers

theorem all_registers : allRegisters ⊆ callerRegisters ∪ savedRegisters := by decide
theorem saved_enumeration : ∀ register ∈ savedRegisters,
    ∃ index : Fin 5, key (X86Prologue.source index) = register := by decide

structure Inputs (state : State) where
  prologue : X86Prologue.Inputs state
  epilogue : BitVec 48
  epilogueUpper : epilogue.toInt + 10 < (2 ^ 47 : Int)
  epilogueLoaded : codeLoaded state epilogue.toInt X86Epilogue.expected
  epilogueStackApart : ∀ index byte, X86Epilogue.expected[index]? = some byte →
    ((address epilogue.toInt index).signExtend 52).toNat ∉ X86Prologue.writes prologue.bottom

structure BodyExit (state : State) (input : Inputs state) (written : Finset Nat) (after : State) where
  frame : X86StateFrame.Frame bodyRegisters written (X86Prologue.finished state input.prologue) after
  flags : BitVec 32
  flagsKnown : after.regs.get? .rflags = some flags
  stackApart : ∀ slot : Fin 6, ∀ byte < 8,
    X86WriteWords.physicalAddress (X86Prologue.stackAt input.prologue slot.val) byte ∉ written
  epilogueApart : ∀ index byte, X86Epilogue.expected[index]? = some byte →
    ((address input.epilogue.toInt index).signExtend 52).toNat ∉ written
  pointer : after.regs.get? .rip = some (input.epilogue.signExtend 64)

def exitStackFacts (state : State) (input : Inputs state) (written : Finset Nat) (after : State)
    (exit : BodyExit state input written after) : X86Epilogue.FrameFacts after :=
  let saved := X86Prologue.epilogueStackFacts state input.prologue
  { saved with
    stackKnown := (exit.frame.lookup 4 (by decide)).trans saved.stackKnown
    visibleKnown := (exit.frame.registers .seg_visibles (by decide)).trans saved.visibleKnown
    controlsKnown := (exit.frame.registers .ctrs (by decide)).trans saved.controlsKnown
    flags := exit.flags
    flagsKnown := exit.flagsKnown
    quiet := (exit.frame.registers .log_register_writes (by decide)).trans saved.quiet
    present := fun slot byte within => by
      change after.mem.get? (X86WriteWords.physicalAddress (X86Prologue.stackAt input.prologue slot.val) byte) = _
      rw [exit.frame.memory _ (exit.stackApart slot byte within)]
      exact saved.present slot byte within }

def exitContext (state : State) (input : Inputs state) (written : Finset Nat) (after : State)
    (exit : BodyExit state input written after) : X86PlainFetch.Facts after :=
  let baseline : X86PlainFetch.Facts (X86Prologue.finished state input.prologue) :=
    (by simpa only [X86Prologue.stage] using X86Prologue.stageContext state input.prologue (5 : Fin 6))
  { baseline with
    status := (exit.frame.registers .ms_reg (by decide)).trans baseline.status
    fault := (exit.frame.registers .fault_reg (by decide)).trans baseline.fault
    msrs := (exit.frame.registers .msrs (by decide)).trans baseline.msrs
    segments := (exit.frame.registers .seg_hidden_attrs (by decide)).trans baseline.segments
    application := (exit.frame.registers .app_view (by decide)).trans baseline.application }

def epilogueInputs (state : State) (input : Inputs state) (written : Finset Nat) (after : State)
    (exit : BodyExit state input written after) : X86Epilogue.Inputs after where
  toFrameFacts := exitStackFacts state input written after exit
  context := exitContext state input written after exit
  code := input.epilogue
  codeUpper := input.epilogueUpper
  loaded := exit.frame.codeLoaded _ _
    ((X86Prologue.finished_frame state input.prologue).codeLoaded _ _
      input.epilogueLoaded input.epilogueStackApart) exit.epilogueApart
  rip := exit.pointer

theorem lookup_register_equal (before after : State) (index : Fin 16)
    (same : lookup after index = lookup before index) :
    after.regs.get? (key index) = before.regs.get? (key index) := by
  unfold lookup at same
  have mapped := congrArg (Option.map (cast (key_word index).symm)) same
  simpa [Option.map_map, Function.comp_def] using mapped

structure Result (state : State) (input : Inputs state) (written : Finset Nat)
    (body after : State) : Prop where
  pointer : after.regs.get? .rip = some (input.prologue.returnAddress.signExtend 64)
  stackPointer : lookup after 4 = some ((X86Prologue.stackAt input.prologue 6).signExtend 64)
  saved : ∀ index : Fin 5, lookup after (X86Prologue.source index) = some (input.prologue.saved index)
  value : lookup after 0 = lookup body 0
  memory : after.mem = body.mem
  flags : after.regs.get? .rflags = body.regs.get? .rflags
  frame : X86StateFrame.Frame callerRegisters (X86Prologue.writes input.prologue.bottom ∪ written) state after

theorem finished_result (state : State) (input : Inputs state) (written : Finset Nat) (body : State)
    (exit : BodyExit state input written body) :
    Result state input written body
      (X86Epilogue.finished body (epilogueInputs state input written body exit)) := by
  let prepared := epilogueInputs state input written body exit
  let after := X86Epilogue.finished body prepared
  have correct := X86Epilogue.finished_result body prepared
  have saved : ∀ index : Fin 5, lookup after (X86Prologue.source index) = some (input.prologue.saved index) := by
    intro index
    fin_cases index
    · exact correct.saved 4
    · exact correct.saved 3
    · exact correct.saved 2
    · exact correct.saved 1
    · exact correct.saved 0
  have allFrame : X86StateFrame.Frame allRegisters
      (X86Prologue.writes input.prologue.bottom ∪ written) state after := by
    simpa only [allRegisters, Finset.union_empty] using
      ((X86Prologue.finished_frame state input.prologue).trans exit.frame).trans
        (X86StateFrame.registerOnly correct.frame)
  have registersSaved : ∀ register ∈ savedRegisters, after.regs.get? register = state.regs.get? register := by
    intro register member
    obtain ⟨index, rfl⟩ := saved_enumeration register member
    exact lookup_register_equal state after _ ((saved index).trans (input.prologue.savedKnown index).symm)
  have frame : X86StateFrame.Frame callerRegisters
      (X86Prologue.writes input.prologue.bottom ∪ written) state after :=
    { allFrame with
      registers := fun register outside => by
        by_cases kept : register ∈ savedRegisters
        · exact registersSaved register kept
        · apply allFrame.registers register
          intro member
          have shared := all_registers member
          exact (Finset.mem_union.mp shared).elim outside kept }
  exact ⟨correct.pointer, correct.stackPointer, saved, correct.rax, correct.frame.memory,
    correct.frame.registers .rflags (by decide), frame⟩

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (input : Inputs state) (written : Finset Nat) (body : State) (count : Nat)
    (exit : BodyExit state input written body) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches count).run (X86Prologue.finished state input.prologue) = .ok () body →
    ∃ after, (X86FuelPrefix.fetches (5 + count + 6)).run state = .ok () after ∧
      Result state input written body after := by
  let : OtherOpcodeHandlers := X86Stack.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  intro bodyRun
  let prepared := epilogueInputs state input written body exit
  let after := X86Epilogue.finished body prepared
  have first := X86Prologue.executes other vector state input.prologue
  have last : (X86FuelPrefix.fetches 6).run body = .ok () after :=
    X86Epilogue.executes (X86Stack.linkedHandlers other) vector body prepared
  refine ⟨after, X86FuelPrefix.fetches_then (5 + count) 6 state body after ?_ last,
    finished_result state input written body exit⟩
  exact X86FuelPrefix.fetches_then 5 count state _ body first bodyRun


namespace Controls

theorem empty_body_returns (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ state after, (X86FuelPrefix.fetches 11).run state = .ok () after ∧
      after.regs.get? .rip = some (0x3000#64) ∧ lookup after 4 = some (0x2030#64) ∧
      lookup after 15 = some (0xfedcba9876543210#64) ∧ lookup after 0 = some (4#64) := by
  let : OtherOpcodeHandlers := X86Stack.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨state, prepared, upper, loaded, apart, returned, bottom, saved, value⟩ :=
    X86Prologue.Controls.wrapper_fixture
  let input : Inputs state := {
    prologue := prepared, epilogue := X86Prologue.codeAt prepared 9
    epilogueUpper := upper, epilogueLoaded := loaded, epilogueStackApart := apart }
  let body := X86Prologue.finished state prepared
  let exit : BodyExit state input ∅ body := {
    frame := X86StateFrame.Frame.refl _ _ _
    flags := prepared.flags
    flagsKnown := (X86Prologue.finished_result state prepared).flags
    stackApart := by intros; simp
    epilogueApart := by intros; simp
    pointer := (X86Prologue.finished_result state prepared).pointer }
  obtain ⟨after, run, correct⟩ := executes other vector state input ∅ body 0 exit rfl
  refine ⟨state, after, run, ?_, ?_, ?_, ?_⟩
  · simpa [input, returned] using correct.pointer
  · have pointer := correct.stackPointer
    dsimp only [input, X86Prologue.stackAt] at pointer
    rw [bottom] at pointer
    exact pointer
  · simpa [input, X86Prologue.source, saved] using correct.saved 4
  · exact correct.value.trans (((X86Prologue.finished_frame state prepared).lookup 0 (by decide)).trans value)

theorem losing_saved_register_refused (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) :
    letI : OtherOpcodeHandlers := X86Stack.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ state, ∀ after, lookup after 15 = some (0#64) →
      (X86FuelPrefix.fetches 11).run state ≠ .ok () after := by
  let : OtherOpcodeHandlers := X86Stack.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨state, proved, run, _, _, saved, _⟩ := empty_body_returns other vector
  refine ⟨state, ?_⟩
  intro after wrong observed
  have same := (EStateM.Result.ok.inj (run.symm.trans observed)).2
  rw [same, wrong] at saved
  contradiction

end Controls

end Mettapedia.Machines.TIsa.X86CallWrapper

#print axioms Mettapedia.Machines.TIsa.X86CallWrapper.epilogueInputs
#print axioms Mettapedia.Machines.TIsa.X86CallWrapper.lookup_register_equal
#print axioms Mettapedia.Machines.TIsa.X86CallWrapper.finished_result
#print axioms Mettapedia.Machines.TIsa.X86CallWrapper.executes
#print axioms Mettapedia.Machines.TIsa.X86CallWrapper.Controls.empty_body_returns
#print axioms Mettapedia.Machines.TIsa.X86CallWrapper.Controls.losing_saved_register_refused
