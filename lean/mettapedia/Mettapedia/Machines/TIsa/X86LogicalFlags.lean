import Mettapedia.Machines.TIsa.X86Arithmetic

/-!
# Defined logical-operation flags and the original choice provider

Logical operations define CF and ZF while leaving AF unspecified. The pure
merge laws quantify over every auxiliary flag and show that the defined
bits are independent of that choice. The executable writer theorem uses
the original generated model's trivialChoiceSource, which selects zero;
it does not require hardware to select the same undefined AF value.
Whole-backend refinement must retain the appropriate undefined-bit relation.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace Mettapedia.Machines.TIsa.X86LogicalFlags

open _root_.X86Registers X86RegisterRefinement
open Sail.ConcurrencyInterfaceV1

def merged (original user : BitVec 32) (auxiliary : BitVec 1) : BitVec 32 :=
  Functions._update_rflagsbits_of
    (Functions._update_rflagsbits_sf
      (Functions._update_rflagsbits_zf
        (Functions._update_rflagsbits_af
          (Functions._update_rflagsbits_pf
            (Functions._update_rflagsbits_cf original (Functions._get_rflagsbits_cf user))
            (Functions._get_rflagsbits_pf user)) auxiliary)
        (Functions._get_rflagsbits_zf user))
      (Functions._get_rflagsbits_sf user))
    (Functions._get_rflagsbits_of user)

theorem merged_carry (original user : BitVec 32) (auxiliary : BitVec 1) :
    Functions._get_rflagsbits_cf (merged original user auxiliary) =
      Functions._get_rflagsbits_cf user := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  have : index = 0 := by omega
  subst index
  simp [merged, Functions._get_rflagsbits_cf,
    Functions._update_rflagsbits_cf, Functions._update_rflagsbits_pf,
    Functions._update_rflagsbits_af, Functions._update_rflagsbits_zf,
    Functions._update_rflagsbits_sf, Functions._update_rflagsbits_of,
    Sail.BitVec.extractLsb, BitVec.extractLsb, Sail.BitVec.updateSubrange,
    Sail.BitVec.updateSubrange']

theorem merged_zero (original user : BitVec 32) (auxiliary : BitVec 1) :
    Functions._get_rflagsbits_zf (merged original user auxiliary) =
      Functions._get_rflagsbits_zf user := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  have : index = 0 := by omega
  subst index
  simp [merged, Functions._get_rflagsbits_zf,
    Functions._update_rflagsbits_cf, Functions._update_rflagsbits_pf,
    Functions._update_rflagsbits_af, Functions._update_rflagsbits_zf,
    Functions._update_rflagsbits_sf, Functions._update_rflagsbits_of,
    Sail.BitVec.extractLsb, BitVec.extractLsb, Sail.BitVec.updateSubrange,
    Sail.BitVec.updateSubrange']

theorem original_undefined_choice (state : State) :
    (Functions.undef_flg ()).run state = .ok (0#1) state := by rfl

theorem write_logical_flags (state : State) (original user : BitVec 32)
    (present : state.regs.get? .rflags = some original)
    (quiet : state.regs.get? .log_register_writes = some false) :
    (Functions.write_user_rflags user (16#32)).run state =
      .ok () (X86Flags.putFlags state (merged original user (0#1))) := by
  unfold Functions.write_user_rflags
  simp only [show Functions._get_rflagsbits_cf (16#32) = (0#1) from rfl,
    show Functions._get_rflagsbits_pf (16#32) = (0#1) from rfl,
    show Functions._get_rflagsbits_af (16#32) = (1#1) from rfl,
    show Functions._get_rflagsbits_zf (16#32) = (0#1) from rfl,
    show Functions._get_rflagsbits_sf (16#32) = (0#1) from rfl,
    show Functions._get_rflagsbits_of (16#32) = (0#1) from rfl,
    show ((0#1) == (1#1)) = false from rfl,
    show ((1#1) == (1#1)) = true from rfl,
    Bool.false_eq_true, ite_false, ite_true]
  rw [run_bind, readRegister_exact, present]
  dsimp only
  simp only [run_bind, _root_.X86Registers.readReg, PreSail.readReg,
    run_get, writeRegister_exact, run_pure, present, quiet,
    Std.ExtDHashMap.get?_insert_self, Std.ExtDHashMap.get?_insert,
    show (Register.rflags == Register.log_register_writes) = false from rfl,
    Bool.false_eq_true, dite_false, ite_false, original_undefined_choice]
  simp only [X86Flags.putFlags, merged, X86Flags.overwrite_flags]

theorem and_mask (state : State) (left right : Word) (flags : BitVec 32) :
    ((fun value : Word × BitVec 32 × BitVec 32 => value.2.2) <$>
      Functions.gpr_and_spec_8 left right flags).run state = .ok (16#32) state := by
  unfold Functions.gpr_and_spec_8 Functions.pf_spec64 Functions.logbitp_int
  simp only [map_eq_pure_bind, run_bind, run_pure, run_assert]
  change (EStateM.Result.ok (16#32) state : EStateM.Result (Sail.Error exception) State (BitVec 32)) = _
  rfl

theorem and_executes (state : State) (left right : Word) (flags : BitVec 32) :
    ∃ output, (Functions.gpr_and_spec_8 left right flags).run state =
      .ok (left &&& right, output, 16#32) state := by
  obtain ⟨output, undefined, executed⟩ := X86Alu.project_result_reflects _ state state _
    (X86Alu.and_value state left right flags)
  have mask := and_mask state left right flags
  simp only [map_eq_pure_bind, run_bind, executed, run_pure] at mask
  have same := (EStateM.Result.ok.inj mask).1
  exact ⟨output, by simpa only [same] using executed⟩

theorem and_carry (state : State) (left right : Word) (flags : BitVec 32) :
    ((fun value : Word × BitVec 32 × BitVec 32 => Functions._get_rflagsbits_cf value.2.1) <$>
      Functions.gpr_and_spec_8 left right flags).run state = .ok (0#1) state := by
  unfold Functions.gpr_and_spec_8 Functions.pf_spec64 Functions.logbitp_int
  simp only [map_eq_pure_bind, run_bind, run_pure, run_assert,
    show ((0 : Int) ≥b 0) = true from rfl, ite_true]
  rw [show Functions.bits_of_int 0 1 = (0#1) from rfl]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  have : index = 0 := by omega
  subst index
  simp [Functions._get_rflagsbits_cf,
    Functions._update_rflagsbits_cf, Functions._update_rflagsbits_pf,
    Functions._update_rflagsbits_zf, Functions._update_rflagsbits_sf,
    Functions._update_rflagsbits_of, Sail.BitVec.extractLsb, BitVec.extractLsb,
    Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']

theorem and_zero (state : State) (left right : Word) (flags : BitVec 32) :
    ((fun value : Word × BitVec 32 × BitVec 32 => Functions._get_rflagsbits_zf value.2.1) <$>
      Functions.gpr_and_spec_8 left right flags).run state =
        .ok (Functions.zf_spec (left &&& right).toNat) state := by
  unfold Functions.gpr_and_spec_8 Functions.pf_spec64 Functions.logbitp_int
  simp only [map_eq_pure_bind, run_bind, run_pure, run_assert,
    show ((0 : Int) ≥b 0) = true from rfl, ite_true,
    X86Alu.full_extract, Sail.BitVec.toNatInt]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  have : index = 0 := by omega
  subst index
  simp [Functions._get_rflagsbits_zf,
    Functions._update_rflagsbits_cf, Functions._update_rflagsbits_pf,
    Functions._update_rflagsbits_zf, Functions._update_rflagsbits_sf,
    Functions._update_rflagsbits_of, Sail.BitVec.extractLsb, BitVec.extractLsb,
    Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange']

end Mettapedia.Machines.TIsa.X86LogicalFlags

#print axioms Mettapedia.Machines.TIsa.X86LogicalFlags.write_logical_flags
