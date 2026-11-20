import Mettapedia.Machines.TIsa.X86Extend32
import Mettapedia.Machines.TIsa.X86FetchEntry

/-!
# One-instruction normalization of 32-bit carriers

MOV32 zero extension and MOVSXD sign extension use their original fetched
instruction contracts. Each code list has its exact length, without padding.
Only the source value needs a physical readback; the destination may alias it.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86Normalize32
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution X86FetchEntry
local instance : MemoryPrimitives := X86Memory.ordinary

def bytes (signed : Bool) (destination : Fin 16) : List Nat :=
  if signed then [(rex true destination destination).toNat,0x63,(modRM destination destination).toNat]
  else if destination.val < 8 then [0x89,(modRM destination destination).toNat]
  else [(rex false destination destination).toNat,0x89,(modRM destination destination).toNat]

theorem length_bounds (signed : Bool) (destination : Fin 16) :
    2 ≤ (bytes signed destination).length ∧ (bytes signed destination).length ≤ 3 := by
  cases signed <;> simp only [bytes,Bool.false_eq_true,ite_false,ite_true]
  · split <;> simp
  · simp

theorem executes (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (signed : Bool) (state : State) (destination : Fin 16) (value : Word) (origin : Entry state)
    (known : lookup state destination = some value)
    (quiet : state.regs.get? .log_register_writes = some false)
    (upper : origin.address.toInt + (bytes signed destination).length < (2 ^ 47 : Int))
    (loaded : codeLoaded state origin.address.toInt (bytes signed destination)) :
    letI : OtherOpcodeHandlers := X86Extend32.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    (Functions.x86_fetch_decode_execute ()).run state =
      .ok () (X86Move.putPointer (put state destination (extend32 signed (low32 value)))
        (address origin.address.toInt (bytes signed destination).length)) := by
  let : OtherOpcodeHandlers := X86Extend32.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  cases signed with
  | true =>
    have size : (bytes true destination).length = 3 := rfl
    have bound : origin.address.toInt + 3 < (2 ^ 47 : Int) := by simpa [size] using upper
    have present : codeLoaded state origin.address.toInt
        [(rex true destination destination).toNat,0x63,(modRM destination destination).toNat] := by
      simpa only [bytes,ite_true] using loaded
    let window := origin.rexWindow (0x63#8) true destination destination bound present
    have run := X86Extend32.fetched other vector state destination destination value window known quiet
    rw [size]
    exact run
  | false =>
    by_cases low : destination.val < 8
    · have size : (bytes false destination).length = 2 := by simp [bytes,low]
      have bound : origin.address.toInt + 2 < (2 ^ 47 : Int) := by simpa [size] using upper
      have present : codeLoaded state origin.address.toInt [0x89,(modRM destination destination).toNat] := by
        simpa only [bytes,Bool.false_eq_true,ite_false,if_pos low] using loaded
      let window := origin.bareWindow (0x89#8) (modRM destination destination) bound present
      have run := X86Move32.fetched_bare (X86Extend32.linkedHandlers other) vector state destination destination
        value ⟨low,low⟩ window known quiet
      rw [size]
      exact run
    · have size : (bytes false destination).length = 3 := by simp [bytes,low]
      have bound : origin.address.toInt + 3 < (2 ^ 47 : Int) := by simpa [size] using upper
      have present : codeLoaded state origin.address.toInt
          [(rex false destination destination).toNat,0x89,(modRM destination destination).toNat] := by
        simpa only [bytes,Bool.false_eq_true,ite_false,if_neg low] using loaded
      let window := origin.rexWindow (0x89#8) false destination destination bound present
      have run := X86Move32.fetched_rex (X86Extend32.linkedHandlers other) vector state destination destination
        value (fun pair => low pair.1) window known quiet
      rw [size]
      exact run

theorem result_frame (signed : Bool) (state : State) (destination : Fin 16) (value : Word)
    (next : BitVec 48) : RegisterFrame {key destination,.rip} state
      (X86Move.putPointer (put state destination (extend32 signed (low32 value))) next) := by
  exact ((put_frame state destination (extend32 signed (low32 value))).trans
    (pointer_frame _ next)).mono (by simp)

#print axioms executes
#print axioms result_frame
end Mettapedia.Machines.TIsa.X86Normalize32
