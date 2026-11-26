import Mettapedia.Machines.TIsa.StoreInstructions.NativeBinding
import Mettapedia.Machines.TIsa.StoreInstructions.NativeWords

/-!
# Binding a term loaded from native memory

The binding gate has no precomputed compare operands. Its prefix
loads the occupancy and held term from the private slot, and the
offered term from the candidate bank. The fixed register allocation
keeps both base registers and the two occupancy constants live.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.MemoryBinding

open Mettapedia.Logic.LP
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Cell Controls Reads CodeApart Encoding)
open X86PlacedScalar (Code)
open NativeBinding (View occupancy)
open X86PlacedPairStore (Cells)
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Native := X86RegisterRefinement.State

def storeEncoding : Encoding := .direct 6 (by decide) (by decide)

def gate (start occupied accepted refused : ℕ) (value bit : BitVec 32) : NativeBinding.Layout :=
  ⟨start + 21, occupied, accepted, refused, storeEncoding, 0, 1, 2, 8, 9, value, bit⟩

def bitWire : NativeWords.Wiring := ⟨6, by decide, by decide, storeEncoding, 0, by decide, by decide⟩
def heldWire : NativeWords.Wiring := ⟨6, by decide, by decide, storeEncoding, 1, by decide, by decide⟩
def termWire : NativeWords.Wiring := ⟨7, by decide, by decide, storeEncoding, 2, by decide, by decide⟩

structure Checked (image : NativeImage.View) (start occupied accepted refused : ℕ)
    (value bit term : BitVec 32) : Prop where
  extent : start + 21 ≤ image.size
  loadBit : Code image start (X86DataLoad.code true 0 6 bit)
  loadValue : Code image (start + 7) (X86DataLoad.code true 1 6 value)
  loadTerm : Code image (start + 14) (X86DataLoad.code true 2 7 term)
  bind : (gate start occupied accepted refused value bit).Checked image

noncomputable abbrev handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :=
  X86PlacedScalar.handlers (X86FrameLoad.linkedHandlers other) extra

structure Known (before : Native) (slot candidate : Word) : Prop where
  slot : lookup before 6 = some slot
  candidate : lookup before 7 = some candidate
  zero : lookup before 8 = some 0
  one : lookup before 9 = some 1

abbrev registerWrites : Finset Register := {.rax, .rcx, .rdx, .rflags, .rip}

theorem load_words (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {before : Native} {start occupied accepted refused : ℕ} {image : NativeImage.View} {base : BitVec 48}
    (point : At image before base start) (controls : Controls before)
    {value bit term : BitVec 32} (checked : Checked image start occupied accepted refused value bit term)
    {slot candidate : Word} (known : Known before slot candidate)
    (cells : Cells (gate start occupied accepted refused value bit).writes slot) (subterm : Cell candidate term)
    (bitWord heldWord offeredWord : Word)
    (bitReady : Reads before cells.second.address bitWord)
    (heldReady : Reads before cells.first.address heldWord)
    (termReady : Reads before subterm.address offeredWord) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ next, (X86FuelPrefix.fetches 3).run before = .ok () next ∧
      X86StateFrame.Frame registerWrites ∅ before next ∧
      (∀ a, next.mem.get? a = before.mem.get? a) ∧
      NativeBinding.Inputs (gate start occupied accepted refused value bit) next slot bitWord heldWord offeredWord ∧
      Nonempty (At image next base (start + 21)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let readBit : NativeWords.Source slot := .copy bit cells.second
  let readHeld : NativeWords.Source slot := .copy value cells.first
  let readTerm : NativeWords.Source candidate := .copy term subterm
  obtain ⟨first, bitRun, bitFrame, bitRead, ⟨atHeld⟩⟩ :=
    NativeWords.Source.fetch (handlers other extra) vector bitWire readBit bitWord point controls known.slot bitReady
      (show start + 7 ≤ image.size by have := checked.extent; omega) checked.loadBit
  obtain ⟨second, heldRun, heldFrame, heldRead, ⟨atTerm⟩⟩ :=
    NativeWords.Source.fetch (handlers other extra) vector heldWire readHeld heldWord atHeld
      (controls.transport bitFrame (X86Immediate32.writes_data _))
      ((bitFrame.lookup 6 (by decide)).trans known.slot)
      (heldReady.preserved bitFrame (by simp))
      (show start + 7 + 7 ≤ image.size by have := checked.extent; omega) checked.loadValue
  have firstTwo := bitFrame.trans heldFrame
  obtain ⟨third, termRun, termFrame, termRead, follow⟩ :=
    NativeWords.Source.fetch (handlers other extra) vector termWire readTerm offeredWord atTerm
      ((controls.transport bitFrame (X86Immediate32.writes_data _)).transport heldFrame (X86Immediate32.writes_data _))
      ((firstTwo.lookup 7 (by decide)).trans known.candidate)
      (termReady.preserved firstTwo (by simp))
      (show start + 7 + 7 + 7 ≤ image.size by simpa only [Nat.add_assoc] using checked.extent) checked.loadTerm
  have all := firstTwo.trans termFrame
  have sequence := X86FuelPrefix.fetches_then 1 1 before first second bitRun heldRun
  have runs := X86FuelPrefix.fetches_then 2 1 before second third sequence termRun
  have same (r : Fin 16) (kept : key r ∉ (NativeWords.touched bitWire ∪ NativeWords.touched heldWire) ∪
      NativeWords.touched termWire) : lookup third r = lookup before r := all.lookup _ kept
  refine ⟨third, runs, all.mono (by decide) (by simp), fun a => all.memory a (by simp), ?_, ?_⟩
  · exact ⟨(same 6 (by decide)).trans known.slot,
      ((termFrame.lookup 0 (by decide)).trans (heldFrame.lookup 0 (by decide))).trans bitRead,
      (termFrame.lookup 1 (by decide)).trans heldRead, termRead,
      (same 8 (by decide)).trans known.zero, (same 9 (by decide)).trans known.one⟩
  · simpa only [readBit, readHeld, readTerm, NativeWords.Source.width, Nat.add_assoc] using follow

/-- From initialized arrays, the fetched prefix and gate realize a
single semantic slot binding. No loaded compare result is assumed. -/
theorem bind_from_memory {σ : LPSignature}
    [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    (codes : PackedOccurrences.Codes (GroundTerm σ)) (table : BindingSlots.Table σ)
    (name : σ.vars) (value : GroundTerm σ) (offered : Word) (encoded : codes.encode value = some offered)
    (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {before : Native} {start occupied accepted refused : ℕ} {image : NativeImage.View} {base : BitVec 48}
    (point : At image before base start) (controls : Controls before)
    {valueDisp bitDisp termDisp : BitVec 32} (checked : Checked image start occupied accepted refused valueDisp bitDisp termDisp)
    {slot candidate : Word} (known : Known before slot candidate)
    (cells : Cells (gate start occupied accepted refused valueDisp bitDisp).writes slot) (subterm : Cell candidate termDisp)
    (held : Word) (view : View codes before cells.second.address cells.first.address (table name) held)
    (termReady : Reads before subterm.address offered) (safeCode : CodeApart image base cells.writes) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps words,
      (X86FuelPrefix.fetches (3 + steps)).run before = .ok () after ∧
      X86StateFrame.Frame registerWrites words before after ∧
      words ⊆ cells.writes ∧
      match BindingSlots.bind table name value with
      | none => words = ∅ ∧ View codes after cells.second.address cells.first.address (table name) held ∧
          Nonempty (At image after base refused)
      | some following => ∃ result, View codes after cells.second.address cells.first.address (following name) result ∧
          Nonempty (At image after base accepted) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨loaded, ran, prefixFrame, _, input, ⟨atGate⟩⟩ := load_words other extra vector point controls checked known
    cells subterm (occupancy (table name)) held offered view.bit view.value termReady
  have retained : View codes loaded cells.second.address cells.first.address (table name) held :=
    ⟨view.bit.preserved prefixFrame (by simp), view.value.preserved prefixFrame (by simp), view.code⟩
  obtain ⟨after, cost, words, fired, frame, writes, result⟩ := NativeBinding.fetched_binding codes table name value offered
    encoded (X86FrameLoad.linkedHandlers other) extra vector _ checked.bind atGate
    (controls.transport prefixFrame (by decide)) slot held cells safeCode retained input
  exact ⟨after, cost, words, X86FuelPrefix.fetches_then 3 cost before loaded after ran fired,
    (prefixFrame.trans frame).mono (by decide) (by simp), writes, result⟩

end Mettapedia.Machines.TIsa.StoreInstructions.MemoryBinding
