import Mettapedia.Machines.TIsa.X86LogicalFlags
import Mettapedia.Machines.TIsa.X86StateFrame
import Mathlib.Tactic.IntervalCases
/-!
# Nonarithmetic flag preservation

The mask protects every RFLAGS bit outside CF, PF, AF, ZF, SF and OF.
Arithmetic and logical writes preserve this masked value, including every
choice of the undefined logical AF bit. The state relation composes and
follows from a frame that retains the whole flags register.

AC readback follows from the masked relation. It can therefore be retained
through administrative branches while arithmetic status flags change.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86ControlFlags
open _root_.X86Registers X86RegisterRefinement
local instance : MemoryPrimitives := X86Memory.ordinary

def controlMask : BitVec 32 := ~~~(0x8d5#32)

def Preserved (before after : State) : Prop :=
  (after.regs.get? .rflags).map (fun flags => flags &&& controlMask) =
    (before.regs.get? .rflags).map (fun flags => flags &&& controlMask)

theorem arithmetic_mask (flags result : BitVec 32) :
    X86Flags.mergeFlags flags result &&& controlMask = flags &&& controlMask := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  interval_cases index <;>
    simp [X86Flags.mergeFlags,controlMask,Functions._update_rflagsbits_cf,
      Functions._update_rflagsbits_pf,Functions._update_rflagsbits_af,Functions._update_rflagsbits_zf,
      Functions._update_rflagsbits_sf,Functions._update_rflagsbits_of,
      Sail.BitVec.updateSubrange,Sail.BitVec.updateSubrange']

theorem logical_mask (flags result : BitVec 32) (auxiliary : BitVec 1) :
    X86LogicalFlags.merged flags result auxiliary &&& controlMask = flags &&& controlMask := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  interval_cases index <;>
    simp [X86LogicalFlags.merged,controlMask,Functions._update_rflagsbits_cf,
      Functions._update_rflagsbits_pf,Functions._update_rflagsbits_af,Functions._update_rflagsbits_zf,
      Functions._update_rflagsbits_sf,Functions._update_rflagsbits_of,
      Sail.BitVec.updateSubrange,Sail.BitVec.updateSubrange']

theorem Preserved.refl (native : State) : Preserved native native := rfl

theorem Preserved.trans {before middle after : State}
    (first : Preserved before middle) (second : Preserved middle after) : Preserved before after :=
  Eq.trans second first

theorem of_register_frame {before after : State} {registers : Finset Register}
    (framed : X86Execution.RegisterFrame registers before after) (outside : Register.rflags ∉ registers) :
    Preserved before after := by
  unfold Preserved
  rw [framed.registers .rflags outside]

theorem flags_present {before after : State} (preserved : Preserved before after)
    (flags : BitVec 32) (known : before.regs.get? .rflags = some flags) :
    ∃ nextFlags : BitVec 32, after.regs.get? .rflags = some nextFlags := by
  cases observed : after.regs.get? .rflags with
  | some nextFlags => exact ⟨nextFlags,rfl⟩
  | none =>
    unfold Preserved at preserved
    simp only [observed,known,Option.map_none,Option.map_some] at preserved
    contradiction

theorem masked_ac (flags : BitVec 32) :
    Functions._get_rflagsbits_ac (flags &&& controlMask) = Functions._get_rflagsbits_ac flags := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  have same : index = 0 := by omega
  subst index
  simp [Functions._get_rflagsbits_ac,Sail.BitVec.extractLsb,BitVec.extractLsb,controlMask]

theorem ac_preserved {before after : State} (preserved : Preserved before after)
    (oldFlags newFlags : BitVec 32)
    (oldKnown : before.regs.get? .rflags = some oldFlags)
    (newKnown : after.regs.get? .rflags = some newFlags) :
    Functions._get_rflagsbits_ac newFlags = Functions._get_rflagsbits_ac oldFlags := by
  unfold Preserved at preserved
  rw [newKnown,oldKnown] at preserved
  have masked : newFlags &&& controlMask = oldFlags &&& controlMask := Option.some.inj preserved
  have read := congrArg Functions._get_rflagsbits_ac masked
  simpa only [masked_ac] using read

namespace Controls

theorem carry_change_allowed : (0x201#32) &&& controlMask = (0x200#32) &&& controlMask := by decide

theorem alignment_change_rejected : (0x40200#32) &&& controlMask ≠ (0x200#32) &&& controlMask := by decide

end Controls

end Mettapedia.Machines.TIsa.X86ControlFlags
