import Mettapedia.Machines.TIsa.X86RegisterRefinement

/-!
# Ordinary sequential memory for the Sail x86 fragment

Plain reads, instruction reads and plain writes use the pinned support
library's byte map. The separate write-address announcement has no state
effect in this sequential profile, as in sail2_prompt_monad.lem. Other memory
kinds are refused. Atomic and concurrent memory interpretations are separate.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86Memory

open _root_.X86Registers
open Sail.ConcurrencyInterfaceV1 X86RegisterRefinement

@[instance_reducible] def ordinary : MemoryPrimitives where
  read kind _ address count := match kind with
    | .Read_plain | .Read_ifetch => do
        let (value, _) ← PreSail.readBytes count address.toNat
        pure value
    | _ => throw .Unreachable
  writeAddress kind _ _ _ := match kind with
    | .Write_plain => pure ()
    | _ => throw .Unreachable
  writeValue kind _ address _ value := match kind with
    | .Write_plain => PreSail.writeBytes address.toNat value
    | _ => throw .Unreachable

theorem readByte_exact (state : State) (address : Nat) :
    (PreSail.readByte address : SailM (BitVec 8)).run state =
      match state.mem.get? address with
      | some byte => .ok byte state
      | none => .error (.OutOfMemoryRange address) state := by
  unfold PreSail.readByte
  rw [run_bind, run_get]
  dsimp only
  cases state.mem.get? address <;> rfl

theorem read_one (state : State) (address : BitVec 64) (value : BitVec 8)
    (known : state.mem.get? address.toNat = some value) :
    (ordinary.read .Read_plain 64 address 1).run state = .ok value state := by
  change (do
    let (value, _) ← PreSail.readBytes 1 address.toNat
    pure value : SailM (BitVec 8)).run state = _
  rw [run_bind]
  have read : (PreSail.readBytes 1 address.toNat : SailM ((BitVec 8) × Option Bool)).run state =
      .ok (value, none) state := by
    have action : (PreSail.readBytes 1 address.toNat : SailM ((BitVec 8) × Option Bool)) = (do
      let byte ← PreSail.readByte address.toNat
      pure (byte, none)) := rfl
    rw [action, run_bind, readByte_exact, known]
    rfl
  rw [read]
  rfl

namespace Controls

private def memory : State := ⟨∅, (), (∅ : Std.ExtHashMap Nat (BitVec 8)).insert 100 (42#8), (), 0, #[]⟩

example : (ordinary.read .Read_plain 64 (100#64) 1).run memory = .ok (42#8) memory := by
  apply read_one
  simp [memory]

example : (ordinary.writeAddress .Write_plain 64 (100#64) 1).run memory = .ok () memory := rfl

example : (ordinary.read .Read_exclusive 64 (100#64) 1).run memory = .error .Unreachable memory := rfl

end Controls

end Mettapedia.Machines.TIsa.X86Memory
