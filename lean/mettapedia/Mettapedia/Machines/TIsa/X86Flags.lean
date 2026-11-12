import Mettapedia.Machines.TIsa.X86Alu

/-!
# Architectural flag writes in the pinned Sail model

For a defined flag mask, the original writer updates exactly the six
arithmetic status bits. Other architectural registers and memory are
preserved. Missing input flags fail before any update. Undefined flag
choices remain part of the imported model; they are not silently replaced
by the defined-mask theorem.
-/

set_option autoImplicit false

tisa_model_file% "Mettapedia/Machines/TIsa/Models/X86Registers/FlagFunctions.lean.inc"
  sha256 "50530326564e6c94b5a9fb6e088e4912601ec914ec93fe151b1355aa6945bcdc"
  imports [Sail, X86Registers.Defs, X86Registers.SpecializationV1]

namespace Mettapedia.Machines.TIsa.X86Flags

open _root_.X86Registers X86RegisterRefinement
open Sail.ConcurrencyInterfaceV1

def mergeFlags (original user : BitVec 32) : BitVec 32 :=
  Functions._update_rflagsbits_of
    (Functions._update_rflagsbits_sf
      (Functions._update_rflagsbits_zf
        (Functions._update_rflagsbits_af
          (Functions._update_rflagsbits_pf
            (Functions._update_rflagsbits_cf original (Functions._get_rflagsbits_cf user))
            (Functions._get_rflagsbits_pf user))
          (Functions._get_rflagsbits_af user))
        (Functions._get_rflagsbits_zf user))
      (Functions._get_rflagsbits_sf user))
    (Functions._get_rflagsbits_of user)

def putFlags (state : State) (flags : BitVec 32) : State :=
  { state with regs := state.regs.insert .rflags flags }

theorem overwrite_flags (registers : Std.ExtDHashMap Register RegisterType)
    (before after : BitVec 32) :
    (registers.insert .rflags before).insert .rflags after = registers.insert .rflags after := by
  apply Std.ExtDHashMap.ext_get?
  intro register
  simp only [Std.ExtDHashMap.get?_insert]
  by_cases same : (Register.rflags == register) = true <;> simp [same]

theorem write_defined_flags (state : State) (original user : BitVec 32)
    (present : state.regs.get? .rflags = some original)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.write_user_rflags user (0#32)).run state =
      .ok () (putFlags state (mergeFlags original user)) := by
  unfold Functions.write_user_rflags
  simp only [show Functions._get_rflagsbits_cf (0#32) = (0#1) from rfl,
    show Functions._get_rflagsbits_pf (0#32) = (0#1) from rfl,
    show Functions._get_rflagsbits_af (0#32) = (0#1) from rfl,
    show Functions._get_rflagsbits_zf (0#32) = (0#1) from rfl,
    show Functions._get_rflagsbits_sf (0#32) = (0#1) from rfl,
    show Functions._get_rflagsbits_of (0#32) = (0#1) from rfl,
    show ((0#1) == (1#1)) = false from rfl, Bool.false_eq_true, ite_false]
  rw [run_bind, readRegister_exact, present]
  dsimp only
  simp only [run_bind, _root_.X86Registers.readReg, PreSail.readReg,
    run_get, writeRegister_exact, run_pure, present, quiet,
    Std.ExtDHashMap.get?_insert_self, Std.ExtDHashMap.get?_insert,
    show (Register.rflags == Register.log_register_writes) = false from rfl,
    Bool.false_eq_true, dite_false, ite_false]
  simp only [putFlags, mergeFlags, overwrite_flags]

theorem write_missing_flags (state : State) (user mask : BitVec 32)
    (missing : state.regs.get? .rflags = none) :
    (Functions.write_user_rflags user mask).run state = .error .Unreachable state := by
  unfold Functions.write_user_rflags
  rw [run_bind, readRegister_exact, missing]

theorem putFlags_other (state : State) (flags : BitVec 32) (register : Register)
    (apart : Register.rflags ≠ register) :
    (putFlags state flags).regs.get? register = state.regs.get? register := by
  simp [putFlags, Std.ExtDHashMap.get?_insert, apart]

theorem putFlags_gpr (state : State) (flags : BitVec 32) (register : Fin 16) :
    lookup (putFlags state flags) register = lookup state register := by
  have apart : Register.rflags ≠ key register := by fin_cases register <;> decide
  simp only [lookup, putFlags_other state flags (key register) apart]

theorem putFlags_memory (state : State) (flags : BitVec 32) :
    (putFlags state flags).mem = state.mem := rfl

theorem putFlags_pointer (state : State) (flags : BitVec 32) :
    (putFlags state flags).regs.get? .rip = state.regs.get? .rip :=
  putFlags_other state flags .rip (by decide)

theorem putFlags_represents (placement : Registers.Placement) (valid : placement.admitted .x86_64)
    (live : Finset (Fin 12)) (values : Fin 12 → Word) (state : State) (flags : BitVec 32)
    (represented : RepresentsOn placement valid live values state) :
    RepresentsOn placement valid live values (putFlags state flags) := by
  intro register member
  rw [putFlags_gpr]
  exact represented register member

namespace Controls

private def empty : State := ⟨∅, (), ∅, (), 0, #[]⟩
private def before : State :=
  { empty with regs := (empty.regs.insert .rflags (0x200#32)).insert .log_register_writes false }

theorem status_bits_set : mergeFlags (0#32) (0xffffffff#32) = (0x8d5#32) := by decide
theorem control_bit_preserved : mergeFlags (0x200#32) (0#32) = (0x200#32) := by decide

theorem clear_status_preserves_control :
    (Functions.write_user_rflags (0#32) (0#32)).run before =
      .ok () (putFlags before (0x200#32)) := by
  rw [write_defined_flags before (0x200#32) (0#32)
    (by simp [before, Std.ExtDHashMap.get?_insert])
    (by simp [before])]
  rw [control_bit_preserved]

theorem clearing_control_refused :
    (Functions.write_user_rflags (0#32) (0#32)).run before ≠
      .ok () (putFlags before (0#32)) := by
  rw [clear_status_preserves_control]
  intro wrong
  have same := congrArg (fun state : State => state.regs.get? .rflags)
    (EStateM.Result.ok.inj wrong).2
  simp [putFlags] at same

theorem missing_flags_refused :
    (Functions.write_user_rflags (0#32) (0#32)).run empty = .error .Unreachable empty :=
  write_missing_flags empty _ _ (by simp [empty])

end Controls
end Mettapedia.Machines.TIsa.X86Flags
