import Mettapedia.Machines.TIsa.X86ControlFlags

/-!
# Original flag writes with an arbitrary undefined mask

Each flag update follows the original writer. The executable contract retains
its trivial choice provider, selecting zero for undefined status bits.
The control-mask theorem is independent of these selected status values.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86MaskedFlags
open _root_.X86Registers X86RegisterRefinement X86Execution
open Sail.ConcurrencyInterfaceV1

def selectedFlag (user mask : BitVec 32) (get : BitVec 32 → BitVec 1) : BitVec 1 :=
  if get mask = (1#1) then (0#1) else get user

def merged (original user mask : BitVec 32) : BitVec 32 :=
  Functions._update_rflagsbits_of
    (Functions._update_rflagsbits_sf
      (Functions._update_rflagsbits_zf
        (Functions._update_rflagsbits_af
          (Functions._update_rflagsbits_pf
            (Functions._update_rflagsbits_cf original (selectedFlag user mask Functions._get_rflagsbits_cf))
            (selectedFlag user mask Functions._get_rflagsbits_pf))
          (selectedFlag user mask Functions._get_rflagsbits_af))
        (selectedFlag user mask Functions._get_rflagsbits_zf))
      (selectedFlag user mask Functions._get_rflagsbits_sf))
    (selectedFlag user mask Functions._get_rflagsbits_of)

def writeFlag (get : BitVec 32 → BitVec 1) (update : BitVec 32 → BitVec 1 → BitVec 32)
    (user mask : BitVec 32) : SailM PUnit := do
  if (get mask == (1#1)) then
    let flags ← _root_.X86Registers.readReg .rflags
    let value ← Functions.undef_flg ()
    _root_.X86Registers.writeReg .rflags (update flags value)
  else
    let flags ← _root_.X86Registers.readReg .rflags
    _root_.X86Registers.writeReg .rflags (update flags (get user))

theorem write_flag (state : State) (original user mask : BitVec 32)
    (get : BitVec 32 → BitVec 1) (update : BitVec 32 → BitVec 1 → BitVec 32)
    (present : state.regs.get? .rflags = some original) :
    (writeFlag get update user mask).run state =
      .ok PUnit.unit (X86Flags.putFlags state (update original (selectedFlag user mask get))) := by
  unfold writeFlag selectedFlag
  simp only [beq_iff_eq]
  split_ifs <;>
    simp only [run_bind,_root_.X86Registers.readReg,PreSail.readReg,run_get,writeRegister_exact,
      run_pure,present,X86LogicalFlags.original_undefined_choice,X86Flags.putFlags]

theorem updated_present (state : State) (flags : BitVec 32) :
    (X86Flags.putFlags state flags).regs.get? .rflags = some flags := by simp [X86Flags.putFlags]

theorem updated_quiet (state : State) (flags : BitVec 32)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (X86Flags.putFlags state flags).regs.get? .log_register_writes = some false := by
  rw [X86Flags.putFlags_other _ _ _ (by decide)]
  exact quiet

theorem putFlags_putFlags (state : State) (before after : BitVec 32) :
    X86Flags.putFlags (X86Flags.putFlags state before) after = X86Flags.putFlags state after := by
  simp only [X86Flags.putFlags,X86Flags.overwrite_flags]

theorem conditional_bind (condition : Prop) [Decidable condition]
    (yes no : SailM PUnit) (next : PUnit → SailM Unit) :
    (if condition then yes >>= next else no >>= next) =
      ((if condition then yes else no) >>= next) := by
  by_cases choice : condition <;> simp only [choice,ite_true,ite_false]

theorem write_flags (state : State) (original user mask : BitVec 32)
    (present : state.regs.get? .rflags = some original)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.write_user_rflags user mask).run state =
      .ok () (X86Flags.putFlags state (merged original user mask)) := by
  unfold Functions.write_user_rflags
  rw [run_bind,readRegister_exact,present]
  dsimp only
  simp only [conditional_bind]
  change (do
    writeFlag Functions._get_rflagsbits_cf Functions._update_rflagsbits_cf user mask
    writeFlag Functions._get_rflagsbits_pf Functions._update_rflagsbits_pf user mask
    writeFlag Functions._get_rflagsbits_af Functions._update_rflagsbits_af user mask
    writeFlag Functions._get_rflagsbits_zf Functions._update_rflagsbits_zf user mask
    writeFlag Functions._get_rflagsbits_sf Functions._update_rflagsbits_sf user mask
    writeFlag Functions._get_rflagsbits_of Functions._update_rflagsbits_of user mask
    if (← _root_.X86Registers.readReg .log_register_writes) then Functions.log_rflags_write ()
      else pure ()).run state = _
  rw [run_bind,write_flag state original user mask _ _ present]
  dsimp only
  rw [run_bind,write_flag _ _ user mask _ _ (updated_present _ _),putFlags_putFlags]
  dsimp only
  rw [run_bind,write_flag _ _ user mask _ _ (updated_present _ _),putFlags_putFlags]
  dsimp only
  rw [run_bind,write_flag _ _ user mask _ _ (updated_present _ _),putFlags_putFlags]
  dsimp only
  rw [run_bind,write_flag _ _ user mask _ _ (updated_present _ _),putFlags_putFlags]
  dsimp only
  rw [run_bind,write_flag _ _ user mask _ _ (updated_present _ _),putFlags_putFlags]
  dsimp only
  rw [run_bind,readRegister_exact,updated_quiet _ _ quiet]
  rfl

theorem merged_control (flags output mask : BitVec 32) :
    merged flags output mask &&& X86ControlFlags.controlMask = flags &&& X86ControlFlags.controlMask := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  interval_cases index <;>
    simp [merged,X86ControlFlags.controlMask,Functions._update_rflagsbits_cf,
      Functions._update_rflagsbits_pf,Functions._update_rflagsbits_af,Functions._update_rflagsbits_zf,
      Functions._update_rflagsbits_sf,Functions._update_rflagsbits_of,
      Sail.BitVec.updateSubrange,Sail.BitVec.updateSubrange']

#print axioms write_flags
#print axioms merged_control
end Mettapedia.Machines.TIsa.X86MaskedFlags
