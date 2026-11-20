import Mettapedia.Machines.TIsa.P1WordExecution

/-! # Word slots following an activation's metadata -/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.PreparedFrames

/-- The slot starts after the declared metadata and all earlier slots. -/
def registerByte (metadata frame slot : Nat) : Nat := frame + 8 * (metadata + slot)

theorem registerByte_aligned (metadata slot : Nat) : registerByte metadata 0 slot % 8 = 0 := by
  simp [registerByte]

theorem registerByte_inside (metadata : Nat) {width : Nat} (slot : Fin width) :
    registerByte metadata 0 slot + 8 ≤ 8 * (metadata + width) := by
  have within := slot.isLt
  unfold registerByte
  omega

namespace Controls

theorem metadata_changes_the_first_slot :
    registerByte 0 0 0 = 0 ∧ registerByte 5 0 0 = 40 := by decide +kernel

theorem another_conventions_address_does_not_select_the_same_slot :
    registerByte 2 64 1 ≠ registerByte 5 64 1 := by decide +kernel

end Controls

end Mettapedia.Machines.TIsa.PreparedFrames
