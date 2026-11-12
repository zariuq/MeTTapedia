import Mettapedia.Machines.TIsa.X86FetchMemory

/-!
# Effective-address reads on the Sail instruction-fetch path

The actual rme08 implementation reads segment attributes, resolves the
64-bit code address, checks the access and calls rb. These lemmas compose
those operations, retaining their state requirements and failure behavior.
They provide a byte-fetch component; full instruction fetch/decode remains
a separate composition theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Mettapedia.Machines.TIsa.X86EffectiveFetch

open _root_.X86Registers X86RegisterRefinement X86Move X86FetchMemory

theorem code_linear_address (state : State) (address : BitVec 48) :
    (Functions.ea_to_la .Mode_64bit (address.signExtend 64) 1 1).run state =
      .ok (address.signExtend 64) state := by
  unfold Functions.ea_to_la
  simp only [Functions.in_64bit_mode, ite_true]
  change (do
    let linear ← (pure (address.signExtend 64) : SailM (BitVec 64))
    if !(← Functions.canonical_address_p linear.toInt) then
      Functions.x86_model_error ":NON-CANONICAL-ADDRESS"
    else pure ()
    pure linear : SailM (BitVec 64)).run state = _
  rw [run_bind, run_pure]
  dsimp only
  rw [run_bind]
  have canonical : (Functions.canonical_address_p (address.signExtend 64).toInt).run state =
      .ok true state := by
    simpa only [BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 64)] using canonical48 state address
  rw [canonical]
  rfl

theorem byte_alignment (address : BitVec 48) (pointer : Bool) :
    Functions.address_aligned_p address 1 pointer = (pure true : SailM Bool) := rfl

theorem byte_access_check (mode : proc_mode) (address : BitVec 64) (access : String) :
    Functions.check_linear_memory_access mode 8 1 address none 1 access false false =
      (pure () : SailM Unit) := by
  unfold Functions.check_linear_memory_access
  rw [byte_alignment]
  rfl

theorem effective_read_uses_rb [MemoryPrimitives] (state : State) (address : BitVec 48)
    (attributes : Vector (BitVec 16) 6)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes) :
    (Functions.rme08 .Mode_64bit 8 (address.signExtend 64) none 1 ":X").run state =
      (Functions.rb 1 (address.signExtend 64) ":X").run state := by
  unfold Functions.rme08 Functions.load_bytes_from_ea
  rw [run_bind, readRegister_exact, segments]
  dsimp only
  change (do
    let linear ← Functions.ea_to_la .Mode_64bit (address.signExtend 64) 1 1
    Functions.check_linear_memory_access .Mode_64bit 8 1 linear none 1 ":X" false false
    Functions.rb 1 linear ":X" : SailM (BitVec 8)).run state = _
  rw [run_bind, code_linear_address]
  dsimp only
  rw [byte_access_check]
  rfl

local instance : MemoryPrimitives := X86Memory.ordinary

theorem effective_read_exact (state : State) (address : BitVec 48) (pointer : Word)
    (attributes : Vector (BitVec 16) 6) (byte : BitVec 8)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some pointer)
    (present : state.mem.get? (address.signExtend 52).toNat = some byte) :
    (Functions.rme08 .Mode_64bit 8 (address.signExtend 64) none 1 ":X").run state =
      .ok byte state := by
  rw [effective_read_uses_rb state address attributes segments]
  exact rb_one_exact state pointer address byte ":X" application rip present

theorem effective_read_missing (state : State) (address : BitVec 48)
    (attributes : Vector (BitVec 16) 6)
    (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (missing : state.mem.get? (address.signExtend 52).toNat = none) :
    (Functions.rme08 .Mode_64bit 8 (address.signExtend 64) none 1 ":X").run state =
      .error (.OutOfMemoryRange (address.signExtend 52).toNat) state := by
  rw [effective_read_uses_rb state address attributes segments]
  exact rb_one_missing state address ":X" application missing

namespace Controls

private def attributes : Vector (BitVec 16) 6 := Vector.replicate 6 (0#16)
private def mapped : State :=
  ⟨(((∅ : Std.ExtDHashMap Register RegisterType).insert .app_view true).insert .rip (0x1000#64)).insert
      .seg_hidden_attrs attributes,
    (), (∅ : Std.ExtHashMap Nat (BitVec 8)).insert 4096 (0x89#8), (), 0, #[]⟩

theorem read_opcode : (Functions.rme08 .Mode_64bit 8 (0x1000#64) none 1 ":X").run mapped =
    .ok (0x89#8) mapped := by
  apply effective_read_exact mapped (0x1000#48) (0x1000#64) attributes (0x89#8)
  · simp [mapped]
  · simp [mapped, Std.ExtDHashMap.get?_insert]
  · simp [mapped, Std.ExtDHashMap.get?_insert]
  · simp [mapped]

theorem wrong_opcode_refused :
    (Functions.rme08 .Mode_64bit 8 (0x1000#64) none 1 ":X").run mapped ≠
      .ok (0x88#8) mapped := by
  rw [read_opcode]
  intro wrong
  have bytes := (EStateM.Result.ok.inj wrong).1
  exact (by decide : (0x89#8) ≠ (0x88#8)) bytes

private def unmapped : State := { mapped with mem := ∅ }

theorem missing_opcode :
    (Functions.rme08 .Mode_64bit 8 (0x1000#64) none 1 ":X").run unmapped =
      .error (.OutOfMemoryRange 4096) unmapped := by
  apply effective_read_missing unmapped (0x1000#48) attributes
  · simp [unmapped, mapped]
  · simp [unmapped, mapped, Std.ExtDHashMap.get?_insert]
  · simp [unmapped]

end Controls


end Mettapedia.Machines.TIsa.X86EffectiveFetch
