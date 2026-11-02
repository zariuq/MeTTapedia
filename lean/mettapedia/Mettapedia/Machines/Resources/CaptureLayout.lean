import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

namespace Mettapedia.Machines.Resources

/-- A bounded variable-length capture layout. Fixed fields and payload lengths
come from the versioned wire declaration, not the host structure layout. -/
structure CaptureLayout where
  version : Nat
  slots : Nat
  nameBytes : Nat
  headerBytes : Nat
  rowBytes : Nat
  readBytes : Nat

def CaptureLayout.maximum (layout : CaptureLayout) : Nat :=
  layout.headerBytes + layout.slots * (layout.rowBytes + layout.nameBytes)

theorem capture_length_bound (layout : CaptureLayout) (lengths : List Nat)
    (slots : lengths.length ≤ layout.slots)
    (names : ∀ n ∈ lengths, n ≤ layout.nameBytes) :
    layout.headerBytes + (lengths.map (layout.rowBytes + ·)).sum ≤ layout.maximum := by
  have bounded : (lengths.map (layout.rowBytes + ·)).sum ≤
      lengths.length * (layout.rowBytes + layout.nameBytes) := by
    induction lengths with
    | nil => simp
    | cons n rest ih =>
      have head := names n (by simp)
      have tail := ih (by simp only [List.length_cons] at slots; omega)
        (by intro k member; exact names k (by simp [member]))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
  exact Nat.add_le_add_left (Nat.le_trans bounded (Nat.mul_le_mul_right _ slots)) _

end Mettapedia.Machines.Resources
