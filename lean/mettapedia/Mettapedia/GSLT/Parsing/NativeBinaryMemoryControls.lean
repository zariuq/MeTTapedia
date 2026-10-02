import Mettapedia.GSLT.Parsing.NativeBinaryMemoryBounds

/-! Positive and negative controls for native memory word decoding. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.NativeBinaryMemoryWord

open LanguageDef.NativeOps

private def base : Address := ⟨1, 0, []⟩
private def empty : SourceMemory := ⟨fun _ _ => none, fun _ => none⟩
private def headerOnly : SourceMemory :=
  ⟨fun storage element => if storage = 1 ∧ element = 0 then some (.byte 255) else none,
    fun _ => none⟩
private def nonShortestZero : SourceMemory :=
  ⟨fun storage element => if storage = 1 ∧ element = 0 then some (.byte 248)
    else if storage = 1 ∧ element = 1 then some (.byte 0) else none, fun _ => none⟩

theorem empty_null_cursor_is_truncated :
    sourceRun ⟨247, 8, false⟩ empty none 0 0 = some (.error .truncatedWord) := by decide +kernel

theorem end_of_buffer_does_not_read_the_header :
    sourceRun ⟨247, 8, false⟩ empty (some base) 1 1 = some (.error .truncatedWord) := by decide +kernel

theorem truncated_payload_is_refused_before_its_cells_are_read :
    sourceRun ⟨247, 8, false⟩ headerOnly (some base) 2 0 = some (.error .truncatedWord) := by decide +kernel

theorem invalid_header_is_refused_before_payload_reads :
    sourceRun ⟨247, 1, false⟩ headerOnly (some base) 9 0 = some (.error .invalidHeader) := by decide +kernel

theorem borrowed_non_shortest_zero_is_accepted :
    sourceRun ⟨247, 8, false⟩ nonShortestZero (some base) 2 0 = some (.ok (0, 2)) := by decide +kernel

theorem valid_length_with_a_missing_payload_cell_is_undefined :
    sourceRun ⟨247, 8, false⟩ headerOnly (some base) 9 0 = none := by decide +kernel

theorem invalid_codec_is_refused_before_the_header :
    sourceRun ⟨247, 0, false⟩ empty (some base) 1 0 = some (.error .invalidRequest) := by decide +kernel

end Mettapedia.GSLT.Parsing.NativeBinaryMemoryWord
