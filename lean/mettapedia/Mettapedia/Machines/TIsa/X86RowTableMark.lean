import Mettapedia.Machines.TIsa.X86RowTableStore
import Mettapedia.Machines.TIsa.RowTableInitialization

/-!
# Published mark updates through actual native stores

A mark is a one-word row. Updating an existing row preserves the count,
every other mark and the zero unpublished tail. The native result reuses
the captured store bank, original source firing, exact execution count,
frames and image endpoint. Published rows stay unchanged until the final
store instruction. Custody and concurrent publication remain separate.

The logical index guard is explicit: a physically allocated unpublished
slot is outside the domain of a mark update.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86RowTableMark
open _root_.X86Registers X86RegisterRefinement X86Execution X86MemoryView
open X86RowTableStore
local instance : MemoryPrimitives := X86Memory.ordinary

theorem mark_frame (layout : RowTableView.Layout) (before after : State)
    (registers : Finset Register) (index capacity : Nat) (count value : Word)
    (oneWord : layout.width = 1) (inside : index < count.toNat) (capacityBound : count.toNat ≤ capacity)
    (countRead : RowTableView.word (logicalBytes before) layout.count = some count)
    (apart : layout.countApart capacity)
    (zero : RowTableView.zeroTail layout (logicalBytes before) count.toNat capacity)
    (addressBound : layout.address index 0 < 2 ^ 64)
    (area : X86CanonicalSpan.Area (BitVec.ofNat 64 (layout.address index 0)) 8)
    (frame : X86StateFrame.Frame registers
      (X86DataStore.writes true (X86MemoryStore.target (layout.address index 0))) before after)
    (stored : ∀ offset < 8,
      after.mem.get? (X86WriteWords.physicalAddress (X86MemoryStore.target (layout.address index 0)) offset) =
        some (value.extractLsb' (8 * offset) 8)) :
    RowTableView.word (logicalBytes after) (layout.address index 0) = some value ∧
    RowTableView.word (logicalBytes after) layout.count = some count ∧
    RowTableView.zeroTail layout (logicalBytes after) count.toNat capacity ∧
    ∀ other, other ≠ index →
      RowTableView.word (logicalBytes after) (layout.address other 0) =
        RowTableView.word (logicalBytes before) (layout.address other 0) := by
  have position : layout.address index 0 = layout.rows + 8 * index := by
    simp [RowTableView.Layout.address,oneWord]
  have countOutside : layout.address index 0 + 8 ≤ layout.count ∨ layout.count + 8 ≤ layout.address index 0 := by
    rcases apart with left | right
    · exact Or.inr (by omega)
    · simp only [oneWord,Nat.mul_one] at right
      exact Or.inl (by omega)
  have countSame := word_framed true before after registers (layout.address index 0) layout.count
    addressBound area frame countOutside
  have endsBefore : layout.address index 0 + 8 ≤ layout.rows + 8 * (count.toNat * layout.width) := by
    simp only [oneWord,Nat.mul_one]
    omega
  refine ⟨word_written after _ value addressBound area stored,countSame.trans countRead,
    zeroTail_before_frame layout true before after registers _ count.toNat capacity
      addressBound area frame zero endsBefore,?_⟩
  intro other different
  apply word_framed true before after registers _ _ addressBound area frame
  simp only [RowTableView.Layout.address,oneWord,Nat.mul_one,Nat.add_zero,X86DataStore.byteCount,if_true]
  omega

theorem source_marks (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (program : P1Capture.Program) (span : P1Capture.Span) (instruction : X86BoundedStore.Instruction)
    (native : State) (call : StoreCall program span instruction native)
    (layout : RowTableView.Layout) (index capacity : Nat) (count : Word)
    (wide : instruction.wide = true) (oneWord : layout.width = 1)
    (atMark : call.address = layout.address index 0)
    (inside : index < count.toNat) (capacityBound : count.toNat ≤ capacity)
    (countRead : RowTableView.word (logicalBytes native) layout.count = some count)
    (apart : layout.countApart capacity)
    (zero : RowTableView.zeroTail layout (logicalBytes native) count.toNat capacity) :
    letI : OtherOpcodeHandlers := X86BoundedStore.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags,
      (X86FuelPrefix.fetches (X86BoundedStore.count instruction)).run native = .ok () after ∧
      X86StateFrame.Frame X86Bounds.writes
        (X86DataStore.writes true (X86MemoryStore.target (layout.address index 0))) native after ∧
      represents call.view call.following after ∧
      RowTableView.word (logicalBytes after) (layout.address index 0) =
        some (call.values (.register instruction.source)) ∧
      RowTableView.word (logicalBytes after) layout.count = some count ∧
      RowTableView.zeroTail layout (logicalBytes after) count.toNat capacity ∧
      (∀ selected, selected ≠ index →
        RowTableView.word (logicalBytes after) (layout.address selected 0) =
          RowTableView.word (logicalBytes native) (layout.address selected 0)) ∧
      after.regs.get? .rip = some ((address call.entry.base (span.offset + span.length)).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ call.entry.profile.Holds after ∧
      X86P1LoadCapture.Loaded program after call.entry.base ∧
      ∀ prefixCount < X86BoundedStore.count instruction, ∀ seen,
        (X86FuelPrefix.fetches prefixCount).run native = .ok () seen →
          RowTableView.observe layout (logicalBytes seen) = RowTableView.observe layout (logicalBytes native) := by
  let : OtherOpcodeHandlers := X86BoundedStore.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨_source,after,nextFlags,run,frame,represented,stored,rip,flagsRead,_quiet,_control,holds,image,_prefixes⟩ :=
    X86BoundedStoreSites.source_executes other extra vector program span instruction call.member call.decoded
      call.view call.values native call.entry call.address call.following call.safe call.source call.descriptors call.codeApart
  obtain ⟨addressBound,area⟩ := call.target_geometry
  rw [wide,atMark] at frame stored area
  have updated := mark_frame layout native after X86Bounds.writes index capacity count _ oneWord inside capacityBound
    countRead apart zero (atMark ▸ addressBound) area frame stored
  refine ⟨after,nextFlags,run,frame,represented,updated.1,updated.2.1,updated.2.2.1,
    updated.2.2.2,rip,flagsRead,holds,image,?_⟩
  intro prefixCount within seen executed
  exact readonly_hidden layout native seen X86Bounds.writes
    (call.before_store other extra vector prefixCount within seen executed)

namespace Controls

def layout : RowTableView.Layout := ⟨16,0,1⟩
def empty : ByteMemory := fun _ => none
def published : ByteMemory := writeBytes
  (RowTableInitialization.initializeTable layout empty 3) layout.count (unpackBytes 8 2)
def marked : ByteMemory := writeBytes published (layout.address 1 0) (unpackBytes 8 1)
def unchecked : ByteMemory := writeBytes published (layout.address 2 0) (unpackBytes 8 1)

theorem published_mark_changes :
    RowTableView.observe layout published = some [[0],[0]] ∧
    RowTableView.observe layout marked = some [[0],[1]] ∧
    RowTableView.word marked layout.count = some 2 := by decide

theorem preserves_unpublished_tail : RowTableView.zeroTail layout marked 2 3 := by
  intro index lower upper column columnInside
  have same : index = 2 := by omega
  have col : column = 0 := by change column < 1 at columnInside;omega
  subst index
  subst column
  decide

theorem unchecked_tail_write_breaks_invariant :
    RowTableView.observe layout unchecked = RowTableView.observe layout published ∧
    ¬RowTableView.zeroTail layout unchecked 2 3 := by
  refine ⟨by decide,?_⟩
  intro claimed
  have wrong := claimed 2 (by decide) (by decide) 0 (by decide)
  have actual : RowTableView.word unchecked (layout.address 2 0) = some 1 := by decide
  rw [actual] at wrong
  exact (by decide : (some (1 : Word)) ≠ some 0) wrong

end Controls

#print axioms mark_frame
#print axioms source_marks
#print axioms Controls.published_mark_changes
#print axioms Controls.preserves_unpublished_tail
#print axioms Controls.unchecked_tail_write_breaks_invariant
end Mettapedia.Machines.TIsa.X86RowTableMark
