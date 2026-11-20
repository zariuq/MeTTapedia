import Mettapedia.Machines.TIsa.X86RowTableStore
import Mettapedia.Algebra.FiniteCoordinateBuffer

/-!
# Publishing one prepared shaped buffer through the shared row interface

One published row is a contiguous word-buffer payload. Shape belongs to the
declared interface, and the decoder checks its complete length. Unpublished,
unavailable and malformed observations remain different outcomes. Preparation
and the final native count store reuse the checker-table publication laws.

This verifies exposure of already prepared word data. It does not prove native
tensor arithmetic, floating-point algebra or ownership of foreign buffers.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.BufferPublication
open _root_.X86Registers X86RegisterRefinement X86Execution X86MemoryView
open Mettapedia.Algebra.FiniteCoordinateBuffer
local instance : MemoryPrimitives := X86Memory.ordinary

inductive Observation where
  | unavailable
  | unpublished
  | wrongCount (actual : Nat)
  | wrongShape (actual expected : Nat)
  | ready (buffer : Dense Word)
  deriving DecidableEq, Repr

def decode (rows columns : Nat) : Option (List (List Word)) → Observation
  | none => .unavailable
  | some [] => .unpublished
  | some [entries] =>
      if entries.length = rows * columns then .ready ⟨rows,columns,entries⟩
      else .wrongShape entries.length (rows * columns)
  | some entries => .wrongCount entries.length

theorem decode_single (rows columns : Nat) (entries : List Word) (shape : entries.length = rows * columns) :
    decode rows columns (some [entries]) = .ready ⟨rows,columns,entries⟩ := by
  simp [decode,shape]

theorem ready_valid (rows columns : Nat) (table : Option (List (List Word))) (buffer : Dense Word)
    (ready : decode rows columns table = .ready buffer) :
    buffer.rows = rows ∧ buffer.columns = columns ∧ buffer.Valid := by
  cases table with
  | none => contradiction
  | some records =>
    cases records with
    | nil => contradiction
    | cons entries rest =>
      cases rest with
      | cons other remaining => contradiction
      | nil =>
        change (if entries.length = rows * columns then .ready ⟨rows,columns,entries⟩
          else Observation.wrongShape entries.length (rows * columns)) = Observation.ready buffer at ready
        split at ready
        next shape =>
          have same := Observation.ready.inj ready
          subst buffer
          exact ⟨rfl,rfl,shape⟩
        next bad => contradiction

theorem source_exposes_buffer (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (program : P1Capture.Program) (span : P1Capture.Span) (instruction : X86BoundedStore.Instruction)
    (native : State) (call : X86RowTableStore.StoreCall program span instruction native)
    (layout : RowTableView.Layout) (rows columns : Nat) (entries : List Word)
    (wide : instruction.wide = true) (atCount : call.address = layout.count)
    (payload : call.values (.register instruction.source) = (1#64))
    (countRead : RowTableView.word (X86RowTableStore.logicalBytes native) layout.count = some (0#64))
    (prepared : RowTableView.row layout (X86RowTableStore.logicalBytes native) 0 = some entries)
    (shape : entries.length = rows * columns) (apart : layout.countApart 1) :
    letI : OtherOpcodeHandlers := X86BoundedStore.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches (X86BoundedStore.count instruction)).run native = .ok () after ∧
      X86StateFrame.Frame X86Bounds.writes (X86DataStore.writes true (X86MemoryStore.target layout.count)) native after ∧
      represents call.view call.following after ∧
      decode rows columns (RowTableView.observe layout (X86RowTableStore.logicalBytes after)) = .ready ⟨rows,columns,entries⟩ ∧
      after.regs.get? .rip = some ((address call.entry.base (span.offset + span.length)).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ call.entry.profile.Holds after ∧
      X86P1LoadCapture.Loaded program after call.entry.base ∧
      ∀ prefixCount < X86BoundedStore.count instruction, ∀ seen,
        (X86FuelPrefix.fetches prefixCount).run native = .ok () seen →
          decode rows columns (RowTableView.observe layout (X86RowTableStore.logicalBytes seen)) = .unpublished := by
  let : OtherOpcodeHandlers := X86BoundedStore.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,nextFlags,run,frame,represented,published,rip,flagsRead,holds,image,prefixes⟩ :=
    X86RowTableStore.source_publishes other extra vector program span instruction native call layout 0 wide atCount
      payload countRead (by decide) apart
  have old : RowTableView.observe layout (X86RowTableStore.logicalBytes native) = some [] := by
    simp [RowTableView.observe,countRead,RowTableView.rowsBefore]
  change RowTableView.observe layout (X86RowTableStore.logicalBytes after) =
    (RowTableView.observe layout (X86RowTableStore.logicalBytes native)).bind
      (fun earlier => (RowTableView.row layout (X86RowTableStore.logicalBytes native) 0).map
        (fun last => earlier ++ [last])) at published
  rw [old,prepared] at published
  refine ⟨after,nextFlags,run,frame,represented,?_,rip,flagsRead,holds,image,?_⟩
  · change RowTableView.observe layout (X86RowTableStore.logicalBytes after) = some [entries] at published
    rw [published]
    exact decode_single rows columns entries shape
  · intro prefixCount within seen executed
    rw [prefixes prefixCount within seen executed,old]
    rfl

namespace Controls
theorem full_payload : decode 1 2 (some [[7,11]]) = .ready ⟨1,2,[7,11]⟩ := by decide
theorem missing_is_not_unpublished : decode 1 2 none ≠ decode 1 2 (some []) := by decide
theorem no_shape_truncation : decode 2 2 (some [[7,11]]) = .wrongShape 2 4 := by decide
theorem empty_shape_is_ready : decode 0 7 (some [[]]) = .ready ⟨0,7,[]⟩ := by decide
theorem multiple_payloads_are_not_one_buffer : decode 1 2 (some [[7],[11]]) = .wrongCount 2 := by decide
theorem dimensions_remain_explicit : decode 1 2 (some [[7,11]]) ≠ decode 2 1 (some [[7,11]]) := by decide
end Controls

#print axioms ready_valid
#print axioms source_exposes_buffer
#print axioms Controls.missing_is_not_unpublished
#print axioms Controls.no_shape_truncation
#print axioms Controls.dimensions_remain_explicit
end Mettapedia.Machines.TIsa.BufferPublication
