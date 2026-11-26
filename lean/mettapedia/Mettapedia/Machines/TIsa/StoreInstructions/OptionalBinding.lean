import Mettapedia.Machines.TIsa.StoreInstructions.MemoryCompare

/-!
# Binding an optional projected subterm

An absent candidate path exits before loading the offered term.
Its term cell need not be initialized. A present path runs the
same fetched binding gate as any other subterm. A refusal never
changes the selected variable slot.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.OptionalBinding

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Cell Controls Reads CodeApart)
open NativeBinding (View occupancy)
open MemoryBinding (Native gate Known registerWrites)
open X86PlacedPairStore (Cells)
open Mettapedia.Logic.LP
local instance : MemoryPrimitives := X86Memory.ordinary

def markerLayout : MemoryCompare.Layout :=
  ⟨MemoryBinding.termWire, MemoryBinding.bitWire, by decide, by decide⟩

structure Checked (image : NativeImage.View) (start occupied accepted refused : ℕ)
    (valueDisp bitDisp termDisp : BitVec 32) {candidate slot : Word}
    (markerDisp : BitVec 32) (marker : Cell candidate markerDisp) : Prop where
  mark : MemoryCompare.Checked markerLayout image start refused .equal
    (.copy markerDisp marker) (.literal 1 : NativeWords.Source slot)
  bind : MemoryBinding.Checked image (start + 26) occupied accepted refused valueDisp bitDisp termDisp

theorem reads_optional {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (codes : PackedOccurrences.Codes (GroundTerm σ)) (table : BindingSlots.Table σ)
    (name : σ.vars) (candidateTerm : Option (GroundTerm σ))
    (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {before : Native} {start occupied accepted refused : ℕ} {image : NativeImage.View} {base : BitVec 48}
    (point : At image before base start) (controls : Controls before)
    {valueDisp bitDisp termDisp markerDisp : BitVec 32} {slot candidate : Word}
    (marker : Cell candidate markerDisp)
    (checked : Checked image start occupied accepted refused valueDisp bitDisp termDisp (slot := slot) markerDisp marker)
    (known : Known before slot candidate)
    (cells : Cells (gate (start + 26) occupied accepted refused valueDisp bitDisp).writes slot)
    (subterm : Cell candidate termDisp) (held : Word)
    (view : View codes before cells.second.address cells.first.address (table name) held)
    (marked : Reads before marker.address (occupancy candidateTerm))
    (ifPresent : ∀ term, candidateTerm = some term →
      ∃ offered, codes.encode term = some offered ∧ Reads before subterm.address offered)
    (safeCode : CodeApart image base cells.writes) :
    letI : OtherOpcodeHandlers := MemoryBinding.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps words,
      (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame registerWrites words before after ∧
      words ⊆ cells.writes ∧
      match candidateTerm.bind (BindingSlots.bind table name) with
      | none => words = ∅ ∧ View codes after cells.second.address cells.first.address (table name) held ∧
          Nonempty (At image after base refused)
      | some following => ∃ result, View codes after cells.second.address cells.first.address (following name) result ∧
          Nonempty (At image after base accepted) := by
  let : OtherOpcodeHandlers := MemoryBinding.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨tested, testedRun, testedFrame, ⟨afterMarker⟩⟩ := MemoryCompare.loaded_comparison other extra vector
    markerLayout (.copy markerDisp marker) (.literal 1 : NativeWords.Source slot) .equal point controls checked.mark
    known.candidate known.slot (occupancy candidateTerm) 1 marked rfl
  have frame : X86StateFrame.Frame registerWrites ∅ before tested := testedFrame.mono (by decide) (by simp)
  have heldView : View codes tested cells.second.address cells.first.address (table name) held :=
    ⟨view.bit.preserved frame (by simp), view.value.preserved frame (by simp), view.code⟩
  cases candidateTerm with
  | none =>
    have refusedPoint : At image tested base refused := by
      simpa [occupancy, Comparison.evaluate] using afterMarker
    exact ⟨tested, 4, ∅, testedRun, frame, by simp, rfl, heldView, ⟨refusedPoint⟩⟩
  | some term =>
    have boundPoint : At image tested base (start + 26) := by
      simpa [occupancy, Comparison.evaluate, NativeWords.Source.width, Nat.add_assoc] using afterMarker
    obtain ⟨offered, encoded, readable⟩ := ifPresent term rfl
    have bases : Known tested slot candidate :=
      ⟨(frame.lookup 6 (by decide)).trans known.slot, (frame.lookup 7 (by decide)).trans known.candidate,
        (frame.lookup 8 (by decide)).trans known.zero, (frame.lookup 9 (by decide)).trans known.one⟩
    obtain ⟨after, cost, words, ran, updated, writes, result⟩ := MemoryBinding.bind_from_memory
      codes table name term offered encoded other extra vector boundPoint
      (controls.transport frame (by decide)) checked.bind bases cells subterm held heldView
      (readable.preserved frame (by simp)) safeCode
    exact ⟨after, 4 + (3 + cost), words, X86FuelPrefix.fetches_then 4 _ before tested after testedRun ran,
      (frame.trans updated).mono (by simp) (by simp), writes, result⟩

end Mettapedia.Machines.TIsa.StoreInstructions.OptionalBinding
