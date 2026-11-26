import Mettapedia.Machines.TIsa.StoreInstructions.NativeSymbolicPremise
import Mettapedia.Machines.TIsa.StoreInstructions.NativeRoleEmission
import Mettapedia.Machines.TIsa.StoreInstructions.NativeEquationEmission

/-! # Emitting the symbolic MATCH body and its refusal result -/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeSymbolicEmission

open Derivation (Role)
open X86PlacedScalar (Code)
open NativeSymbolicPremise (Layout)
open MemoryBinding (storeEncoding)
open PackedEquations (Arena Node)

variable {slot candidate : Word} {capacity : ℕ} {arena : Arena}

def rememberAt (layout : Layout slot candidate capacity arena) (role : Role) (start : ℕ) : ℕ :=
  start + 7 + 16 * (layout.uses.forRole role).length

def emit (layout : Layout slot candidate capacity arena) (node : Node) (role : Role)
    (start refused : ℕ) (result : Fin 16) : List ℕ :=
  NativeRoleEmission.emit layout.identity (layout.uses.forRole role) start refused ++
    (storeEncoding.bytes 2 layout.record.offset ++
      (NativeEquationEmission.emit layout.operands layout.destination node ++ X86Immediate32.code result 1))

def refuse (result : Fin 16) : List ℕ := X86Immediate32.code result 0

private theorem remember_size (layout : Layout slot candidate capacity arena) :
    (storeEncoding.bytes 2 layout.record.offset).length = 7 :=
  X86DataStore.code_length true 2 6 layout.record.offset

theorem same_body_for_other_equation (layout : Layout slot candidate capacity arena) (left right : Node)
    (role : Role) (start refused : ℕ) (result : Fin 16) :
    emit layout left role start refused result = emit layout right role start refused result := by
  simp only [emit, NativeEquationEmission.emit, NativeEquationEmission.same_bytes_for_other_node layout.destination left right]

theorem size (layout : Layout slot candidate capacity arena) (node : Node) (role : Role)
    (start refused : ℕ) (result : Fin 16) :
    start + (emit layout node role start refused result).length = layout.finish (rememberAt layout role start) + 6 := by
  simp only [emit, List.length_append, NativeRoleEmission.size, remember_size, NativeEquationEmission.size,
    X86Immediate32.code_length, Layout.finish, rememberAt, Nat.add_assoc]

theorem checked_of_emitted (layout : Layout slot candidate capacity arena) (node : Node) (role : Role)
    (image : NativeImage.View) (start refused : ℕ) (result : Fin 16)
    (bodyRoom : start + (emit layout node role start refused result).length ≤ image.size)
    (refuseRoom : refused + (refuse result).length ≤ image.size) (short : image.size < 2 ^ 31)
    (bodyCode : Code image start (emit layout node role start refused result))
    (refuseCode : Code image refused (refuse result)) :
    layout.Placed node role image start (rememberAt layout role start) refused result := by
  let startMark := rememberAt layout role start
  have gateSize : start + (NativeRoleEmission.emit layout.identity (layout.uses.forRole role) start refused).length =
      startMark := by simp only [NativeRoleEmission.size, startMark, rememberAt, Nat.add_assoc]
  obtain ⟨gateCode, rest⟩ := NativeWords.code_append (show Code image start
    (NativeRoleEmission.emit layout.identity (layout.uses.forRole role) start refused ++
      (storeEncoding.bytes 2 layout.record.offset ++
        (NativeEquationEmission.emit layout.operands layout.destination node ++ X86Immediate32.code result 1))) from bodyCode)
  rw [gateSize] at rest
  obtain ⟨markCode, afterMark⟩ := NativeWords.code_append rest
  rw [remember_size] at afterMark
  obtain ⟨effectCode, successCode⟩ := NativeWords.code_append afterMark
  rw [NativeEquationEmission.size, show startMark + 7 + (layout.operands.width + layout.destination.width) =
      layout.finish startMark by simp only [Layout.finish, Nat.add_assoc]] at successCode
  have finishBound : layout.finish startMark + 6 ≤ image.size := (size layout node role start refused result) ▸ bodyRoom
  have noRoom : refused + 6 ≤ image.size := by simpa only [refuse, X86Immediate32.code_length] using refuseRoom
  have earlier : startMark + 7 + (NativeEquationEmission.emit layout.operands layout.destination node).length ≤ image.size := by
    rw [NativeEquationEmission.size]
    unfold Layout.finish at finishBound
    omega
  obtain ⟨readsPlaced, storesPlaced⟩ := NativeEquationEmission.checked_of_emitted layout.operands
    layout.destination node image (startMark + 7) earlier effectCode
  refine ⟨?_, by omega, markCode, readsPlaced, storesPlaced, finishBound, noRoom, successCode, refuseCode⟩
  exact NativeRoleEmission.checked_of_emitted image start refused layout.identity (layout.uses.forRole role)
    (by rw [gateSize]; unfold Layout.finish at finishBound; omega) (by omega) short gateCode

end Mettapedia.Machines.TIsa.StoreInstructions.NativeSymbolicEmission
