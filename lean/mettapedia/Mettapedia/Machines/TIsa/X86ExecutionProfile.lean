import Mettapedia.Machines.TIsa.X86Alignment
import Mettapedia.Machines.TIsa.X86ControlFlags

/-! Register, segment and alignment facts for native execution. -/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86Readiness

open _root_.X86Registers X86RegisterRefinement X86Execution
local instance : MemoryPrimitives := X86Memory.ordinary

structure Profile where
  controls : Vector (BitVec 64) 17
  visible : Vector (BitVec 16) 6
  ac : BitVec 1

def Profile.Holds (profile : Profile) (native : State) : Prop :=
  native.regs.get? .ctrs = some profile.controls ∧
  native.regs.get? .seg_visibles = some profile.visible ∧
  ∃ flags : BitVec 32, native.regs.get? .rflags = some flags ∧ Functions._get_rflagsbits_ac flags = profile.ac

def Profile.enabled (profile : Profile) : Bool :=
  (Functions._get_cr0bits_am (Functions.Mk_cr0bits (Sail.BitVec.truncate profile.controls[0]! 32)) == (1#1)) &&
    ((Sail.BitVec.zeroExtend profile.ac 2 == (1#2)) &&
      (Functions._get_segment_selectorbits_rpl (Functions.Mk_segment_selectorbits profile.visible[1]!) == (3#2)))

theorem Profile.alignment_exact (profile : Profile) (native : State) (holds : profile.Holds native) :
    (Functions.alignment_checking_enabled_p ()).run native = .ok profile.enabled native := by
  obtain ⟨controls,visible,flags,flagsKnown,ac⟩ := holds
  rw [X86FrameLoad.alignment_exact native profile.controls flags profile.visible controls flagsKnown visible]
  simp only [X86FrameLoad.alignmentEnabled,Profile.enabled,ac]

theorem Profile.after_frame (profile : Profile) (before after : State)
    (registers : Finset Register) (bytes : Finset Nat)
    (frame : X86StateFrame.Frame registers bytes before after)
    (dataOnly : registers ⊆ dataRegisters)
    (flags oldFlags : BitVec 32)
    (oldKnown : before.regs.get? .rflags = some oldFlags)
    (newKnown : after.regs.get? .rflags = some flags)
    (ac : Functions._get_rflagsbits_ac flags = Functions._get_rflagsbits_ac oldFlags)
    (holds : profile.Holds before) : profile.Holds after := by
  obtain ⟨controls,visible,seen,seenKnown,seenAc⟩ := holds
  have same : oldFlags = seen := Option.some.inj (oldKnown.symm.trans seenKnown)
  refine ⟨?_,?_,flags,newKnown,?_⟩
  · exact (frame.registers .ctrs (fun member => (by decide : .ctrs ∉ dataRegisters) (dataOnly member))).trans controls
  · exact (frame.registers .seg_visibles
      (fun member => (by decide : .seg_visibles ∉ dataRegisters) (dataOnly member))).trans visible
  · rw [ac,same]
    exact seenAc

theorem Profile.after_control (profile : Profile) (before after : State)
    (registers : Finset Register) (bytes : Finset Nat)
    (frame : X86StateFrame.Frame registers bytes before after)
    (dataOnly : registers ⊆ dataRegisters) (control : X86ControlFlags.Preserved before after)
    (flagsPresent : ∃ flags : BitVec 32, after.regs.get? .rflags = some flags)
    (holds : profile.Holds before) : profile.Holds after := by
  obtain ⟨oldFlags,oldKnown,_oldAc⟩ := holds.2.2
  obtain ⟨newFlags,newKnown⟩ := flagsPresent
  exact profile.after_frame before after registers bytes frame dataOnly newFlags oldFlags oldKnown newKnown
    (X86ControlFlags.ac_preserved control oldFlags newFlags oldKnown newKnown) holds

end Mettapedia.Machines.TIsa.X86Readiness
