import Mettapedia.Machines.TIsa.X86RegisterModel
import Mettapedia.Machines.TIsa.Registers
import Mettapedia.Machines.TIsa.Widths
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-!
# Physical-register correspondence for the Sail x86 fragment

The independent register map below connects native register numbers to the
Sail state. The execution lemmas concern the imported accessors, including
missing-register refusal and preservation of the remaining machine state.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86RegisterRefinement

open _root_.X86Registers
open Sail.ConcurrencyInterfaceV1

abbrev State := SequentialState RegisterType trivialChoiceSource

theorem run_bind {α β : Type} (action : SailM α) (next : α → SailM β) (state : State) :
    (action >>= next).run state =
      match action.run state with
      | .ok value after => (next value).run after
      | .error error after => .error error after := by
  change EStateM.bind action next state = _
  cases result : action state <;> simp only [EStateM.bind, EStateM.run, result]

theorem run_get (state : State) : (get : SailM State).run state = .ok state state := rfl

theorem run_pure {α : Type} (value : α) (state : State) :
    (pure value : SailM α).run state = .ok value state := rfl

theorem run_seqRight {α β : Type} (action : SailM α) (next : Unit → SailM β) (state : State) :
    (SeqRight.seqRight action next : SailM β).run state =
      match action.run state with
      | .ok _ after => (next ()).run after
      | .error error after => .error error after := by
  change EStateM.seqRight action next state = _
  cases result : action state <;> simp only [EStateM.seqRight, EStateM.run, result]

theorem run_cast {α β : Type} (same : α = β) (action : SailM α) (state : State) :
    (cast (congrArg SailM same) action).run state =
      match action.run state with
      | .ok value after => .ok (cast same value) after
      | .error error after => .error error after := by
  cases same
  simp only [cast_eq]
  cases action.run state <;> rfl

def key (index : Fin 16) : Register :=
  match index.val with
  | 0 => .rax | 1 => .rcx | 2 => .rdx | 3 => .rbx
  | 4 => .rsp | 5 => .rbp | 6 => .rsi | 7 => .rdi
  | 8 => .r8 | 9 => .r9 | 10 => .r10 | 11 => .r11
  | 12 => .r12 | 13 => .r13 | 14 => .r14 | _ => .r15

theorem key_word (index : Fin 16) : RegisterType (key index) = Word := by
  fin_cases index <;> rfl

theorem key_injective : Function.Injective key := by decide

theorem key_ne_diagnostic (index : Fin 16) : key index ≠ .log_register_writes := by
  fin_cases index <;> decide

def lookup (state : State) (index : Fin 16) : Option Word :=
  (state.regs.get? (key index)).map (cast (key_word index))

def put (state : State) (index : Fin 16) (value : Word) : State :=
  { state with regs := state.regs.insert (key index) (cast (key_word index).symm value) }

theorem readRegister_exact (state : State) (register : Register) :
    (_root_.X86Registers.readReg register).run state =
      match state.regs.get? register with
      | some value => .ok value state
      | none => .error .Unreachable state := by
  unfold _root_.X86Registers.readReg PreSail.readReg
  rw [run_bind, run_get]
  dsimp only
  cases state.regs.get? register <;> rfl

theorem read_gpr_action (index : Fin 16) :
    Functions.read_gpr index.val =
      cast (congrArg SailM (key_word index)) (_root_.X86Registers.readReg (key index)) := by
  fin_cases index <;> rfl

theorem read_gpr_exact (state : State) (index : Fin 16) :
    (Functions.read_gpr index.val).run state =
      match lookup state index with
      | some value => .ok value state
      | none => .error .Unreachable state := by
  rw [read_gpr_action, run_cast (key_word index), readRegister_exact]
  cases read : state.regs.get? (key index) <;> simp only [lookup, read, Option.map]

theorem lookup_put_same (state : State) (index : Fin 16) (value : Word) :
    lookup (put state index value) index = some value := by
  simp [lookup, put]

theorem lookup_put_other (state : State) (destination observed : Fin 16) (value : Word)
    (apart : destination ≠ observed) :
    lookup (put state destination value) observed = lookup state observed := by
  have separate : key destination ≠ key observed := fun same => apart (key_injective same)
  simp [lookup, put, Std.ExtDHashMap.get?_insert, separate]

theorem diagnostic_put (state : State) (index : Fin 16) (value : Word) :
    (put state index value).regs.get? .log_register_writes =
      state.regs.get? .log_register_writes := by
  simp [put, Std.ExtDHashMap.get?_insert, key_ne_diagnostic]

theorem writeRegister_exact (state : State) (register : Register) (value : RegisterType register) :
    (_root_.X86Registers.writeReg register value).run state =
      .ok PUnit.unit { state with regs := state.regs.insert register value } := rfl

theorem write_gpr_action (index : Fin 16) (value : Word) :
    Functions.write_gpr index.val value = (do
      _root_.X86Registers.writeReg (key index) (cast (key_word index).symm value)
      if ← _root_.X86Registers.readReg .log_register_writes then
        Functions.log_gpr_write index.val
      else pure ()) := by
  fin_cases index <;> rfl

theorem write_gpr_exact (state : State) (index : Fin 16) (value : Word)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.write_gpr index.val value).run state = .ok () (put state index value) := by
  have quietAfter : (put state index value).regs.get? .log_register_writes = some false := by
    rw [diagnostic_put]
    exact quiet
  rw [write_gpr_action, run_bind, writeRegister_exact]
  change (do
    let diagnostic ← _root_.X86Registers.readReg .log_register_writes
    if diagnostic then Functions.log_gpr_write index.val else pure ()).run (put state index value) = _
  rw [run_bind, readRegister_exact, quietAfter]
  rfl

theorem run_assert (condition : Bool) (message : String) (state : State) :
    (_root_.X86Registers.assert condition message).run state =
      if condition then .ok () state else .error (.Assertion message) state := by
  cases condition <;> rfl

theorem write_rgfi_exact (state : State) (index : Fin 16) (value : Word)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.write_rgfi (index.val : Int) value).run state = .ok () (put state index value) := by
  have nonnegative : 0 ≤ (index.val : Int) := Int.natCast_nonneg _
  have below : (index.val : Int) < 16 := by exact_mod_cast index.isLt
  unfold Functions.write_rgfi
  rw [run_bind, run_assert]
  simpa [nonnegative, below, Functions.regval_into_reg] using write_gpr_exact state index value quiet

theorem rgfi_exact (state : State) (index : Fin 16) (value : Word)
    (known : lookup state index = some value) :
    (Functions.rgfi (index.val : Int)).run state = .ok value state := by
  have nonnegative : 0 ≤ (index.val : Int) := Int.natCast_nonneg _
  have below : (index.val : Int) < 16 := by exact_mod_cast index.isLt
  unfold Functions.rgfi
  rw [run_bind, run_assert]
  simp only [nonnegative, below, decide_true, Bool.true_and, ite_true]
  change (do
    let word ← Functions.read_gpr index.val
    pure (Functions.regval_from_reg word)).run state = _
  rw [run_bind, read_gpr_exact, known]
  rfl

theorem wr32_exact (state : State) (index : Fin 16) (value : BitVec 32)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.wr32 (BitVec.ofNat 4 index.val) value).run state =
      .ok () (put state index (value.zeroExtend 64)) := by
  have indexBound : index.val < 2 ^ 4 := index.isLt
  simpa [Functions.wr32, Sail.BitVec.toNatInt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt indexBound,
    Sail.BitVec.zeroExtend] using write_rgfi_exact state index (value.zeroExtend 64) quiet

/-- Register writes preserve every other architectural register, of any type. -/
theorem put_other_register (state : State) (index : Fin 16) (value : Word) (observed : Register)
    (apart : key index ≠ observed) :
    (put state index value).regs.get? observed = state.regs.get? observed := by
  simp [put, Std.ExtDHashMap.get?_insert, apart]

theorem put_flags (state : State) (index : Fin 16) (value : Word) :
    (put state index value).regs.get? .rflags = state.regs.get? .rflags := by
  apply put_other_register
  fin_cases index <;> decide

theorem put_instruction_pointer (state : State) (index : Fin 16) (value : Word) :
    (put state index value).regs.get? .rip = state.regs.get? .rip := by
  apply put_other_register
  fin_cases index <;> decide

theorem put_memory (state : State) (index : Fin 16) (value : Word) :
    (put state index value).mem = state.mem := rfl

theorem put_output (state : State) (index : Fin 16) (value : Word) :
    (put state index value).sailOutput = state.sailOutput := rfl

def placed (placement : Registers.Placement) (valid : placement.admitted .x86_64)
    (slot : Fin 14) : Fin 16 :=
  ⟨placement.resolve slot,
    (valid.2.2.2 _ (placement.resolve_mem .x86_64 valid slot)).1⟩

theorem placed_injective (placement : Registers.Placement) (valid : placement.admitted .x86_64) :
    Function.Injective (placed placement valid) := by
  intro left right same
  exact placement.resolve_injective .x86_64 valid (congrArg Fin.val same)

def RepresentsOn (placement : Registers.Placement) (valid : placement.admitted .x86_64)
    (live : Finset (Fin 12)) (values : Fin 12 → Word) (native : State) : Prop :=
  ∀ register ∈ live,
    lookup native (placed placement valid (Registers.logicalSlot register)) = some (values register)

theorem put_scratch_represents (placement : Registers.Placement) (valid : placement.admitted .x86_64)
    (live : Finset (Fin 12)) (values : Fin 12 → Word) (native : State)
    (represented : RepresentsOn placement valid live values native) (scratch : Fin 2) (value : Word) :
    RepresentsOn placement valid live values
      (put native (placed placement valid (Registers.scratchSlot scratch)) value) := by
  intro register member
  rw [lookup_put_other]
  · exact represented register member
  · intro same
    exact Registers.scratch_apart .x86_64 placement valid scratch register (congrArg Fin.val same)

theorem put_logical_represents (placement : Registers.Placement) (valid : placement.admitted .x86_64)
    (live : Finset (Fin 12)) (values : Fin 12 → Word) (native : State)
    (destination : Fin 12) (value : Word)
    (represented : RepresentsOn placement valid (live.erase destination) values native) :
    RepresentsOn placement valid live (Function.update values destination value)
      (put native (placed placement valid (Registers.logicalSlot destination)) value) := by
  intro register member
  by_cases same : register = destination
  · subst register
    simp [lookup_put_same]
  · rw [lookup_put_other]
    · simpa [Function.update_of_ne same] using
        represented register (Finset.mem_erase.mpr ⟨same, member⟩)
    · intro equal
      exact same (Registers.logicalSlot_injective ((placed_injective placement valid equal).symm))

theorem write_logical_represents (placement : Registers.Placement) (valid : placement.admitted .x86_64)
    (live : Finset (Fin 12)) (values : Fin 12 → Word) (native : State)
    (destination : Fin 12) (value : Word)
    (represented : RepresentsOn placement valid (live.erase destination) values native)
    (quiet : native.regs.get? .log_register_writes = some false) :
    ∃ after,
      (Functions.write_gpr (placed placement valid (Registers.logicalSlot destination)).val value).run native =
        .ok () after ∧
      RepresentsOn placement valid live (Function.update values destination value) after :=
  ⟨_, write_gpr_exact native _ value quiet,
    put_logical_represents placement valid live values native destination value represented⟩

namespace Controls

private def emptyNative : State := ⟨∅, (), ∅, (), 0, #[]⟩
private def quietNative : State :=
  { emptyNative with regs := emptyNative.regs.insert .log_register_writes false }

private theorem quiet : quietNative.regs.get? .log_register_writes = some false := by
  simp [quietNative]

example : (Functions.read_gpr 0).run emptyNative = .error .Unreachable emptyNative := by
  simpa [lookup, emptyNative, key] using read_gpr_exact emptyNative (⟨0, by decide⟩ : Fin 16)

example : (Functions.write_gpr 0 7).run quietNative = .ok () (put quietNative 0 7) :=
  write_gpr_exact quietNative 0 7 quiet

example : ¬∃ after, (Functions.write_gpr 0 7).run quietNative = .ok () after ∧
    lookup after 0 = some 8 := by
  rintro ⟨after, executed, wrong⟩
  have correct := write_gpr_exact quietNative 0 7 quiet
  have same := (EStateM.Result.ok.inj (correct.symm.trans executed)).2
  rw [← same, lookup_put_same] at wrong
  contradiction

example : ∃ after,
    (Functions.wr32 0 (0xffffffff : BitVec 32)).run quietNative = .ok () after ∧
    lookup after 0 = some 0xffffffff := by
  refine ⟨_, wr32_exact quietNative 0 _ quiet, ?_⟩
  rw [lookup_put_same]
  rfl

end Controls

end Mettapedia.Machines.TIsa.X86RegisterRefinement
