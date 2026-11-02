import Mettapedia.Machines.Resources.CaptureLayout

namespace Mettapedia.Machines.Resources.LinenCaptureLayout
def layout : CaptureLayout :=
  ⟨1, 16, 24, 14, 11, 7⟩
theorem maximum_frame : layout.maximum = 574 := by decide
theorem header_fits_length : layout.maximum < 2^16 := by decide
theorem chunk_payload_disjoint_from_tag : 8 * layout.readBytes = 56 := by decide
theorem occupied_mask_fits : layout.slots ≤ 16 := by decide
theorem every_frame_length_bound (lengths : List Nat)
    (count : lengths.length ≤ layout.slots)
    (names : ∀ n ∈ lengths, n ≤ layout.nameBytes) :
    layout.headerBytes + (lengths.map (layout.rowBytes + ·)).sum ≤ 574 :=
  capture_length_bound layout lengths count names
end Mettapedia.Machines.Resources.LinenCaptureLayout
