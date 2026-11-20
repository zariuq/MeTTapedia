import Mettapedia.Machines.TIsa.RowTableView

/-!
# Initializing unpublished word tables

Initialization writes the count first, then clears the entire row capacity.
It needs no prior contents, including for bytes that were unavailable. The
result has an empty published view and a zero tail, with an exact byte frame.

This is an entry-phase operation. Native range validation, exclusive custody
and the connection to a particular machine-code initializer remain obligations
of the caller and its refinement theorem.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.RowTableInitialization
open RowTableView

def initializeTable (layout : Layout) (memory : ByteMemory) (capacity : Nat) : ByteMemory :=
  writeWords (writeBytes memory layout.count (unpackBytes 8 0)) layout.rows
    (List.replicate (capacity * layout.width) 0)

theorem initialize_count (layout : Layout) (memory : ByteMemory) (capacity : Nat)
    (apart : layout.countApart capacity) :
    word (initializeTable layout memory capacity) layout.count = some 0 := by
  have kept : word (initializeTable layout memory capacity) layout.count =
      word (writeBytes memory layout.count (unpackBytes 8 0)) layout.count := by
    apply word_congr
    intro offset within
    apply writeWords_outside
    rcases apart with before | after
    · exact Or.inl (by omega)
    · exact Or.inr (by simpa only [List.length_replicate] using
        (show layout.rows + 8 * (capacity * layout.width) ≤ layout.count + offset by omega))
  exact kept.trans (word_read_after_write memory layout.count 0)

theorem initialize_observe (layout : Layout) (memory : ByteMemory) (capacity : Nat)
    (apart : layout.countApart capacity) :
    observe layout (initializeTable layout memory capacity) = some [] := by
  simp [observe,initialize_count layout memory capacity apart,rowsBefore]

theorem initialize_zeroTail (layout : Layout) (memory : ByteMemory) (capacity : Nat) :
    zeroTail layout (initializeTable layout memory capacity) 0 capacity := by
  intro index _ within column columnWithin
  have product := Nat.mul_le_mul_right layout.width (show index + 1 ≤ capacity by omega)
  rw [Nat.add_mul] at product
  have position : index * layout.width + column < capacity * layout.width := by omega
  have seen := written_word (writeBytes memory layout.count (unpackBytes 8 0)) layout.rows
    (List.replicate (capacity * layout.width) (0 : Word)) ⟨index * layout.width + column,by simpa using position⟩
  simpa [initializeTable,Layout.address,List.get_eq_getElem] using seen

theorem initialize_outside (layout : Layout) (memory : ByteMemory) (capacity address : Nat)
    (outsideCount : address < layout.count ∨ layout.count + 8 ≤ address)
    (outsideRows : address < layout.rows ∨ layout.rows + 8 * (capacity * layout.width) ≤ address) :
    initializeTable layout memory capacity address = memory address := by
  unfold initializeTable
  rw [writeWords_outside _ _ _ _ (by simpa only [List.length_replicate] using outsideRows)]
  exact word_write_preserves_outside memory layout.count 0 address outsideCount

theorem initialize_ready (layout : Layout) (memory : ByteMemory) (capacity : Nat)
    (apart : layout.countApart capacity) :
    word (initializeTable layout memory capacity) layout.count = some 0 ∧
    observe layout (initializeTable layout memory capacity) = some [] ∧
    zeroTail layout (initializeTable layout memory capacity) 0 capacity :=
  ⟨initialize_count layout memory capacity apart,
   initialize_observe layout memory capacity apart,
   initialize_zeroTail layout memory capacity⟩

namespace Controls

def layout : Layout := ⟨16,0,2⟩
def unavailable : ByteMemory := fun _ => none

theorem initializes_unavailable :
    observe layout (initializeTable layout unavailable 2) = some [] ∧
    zeroTail layout (initializeTable layout unavailable 2) 0 2 := by
  exact (initialize_ready layout unavailable 2 (by decide)).2

theorem clears_all_columns :
    word (initializeTable layout unavailable 2) 16 = some 0 ∧
    word (initializeTable layout unavailable 2) 24 = some 0 ∧
    word (initializeTable layout unavailable 2) 32 = some 0 ∧
    word (initializeTable layout unavailable 2) 40 = some 0 := by decide

theorem outside_remains_unavailable :
    initializeTable layout unavailable 2 8 = none ∧
    initializeTable layout unavailable 2 48 = none := by decide

theorem empty_view_does_not_establish_zero_tail :
    let counted := writeBytes unavailable layout.count (unpackBytes 8 0)
    observe layout counted = some [] ∧ ¬zeroTail layout counted 0 2 := by
  dsimp
  constructor
  · have countRead : word (writeBytes unavailable layout.count (unpackBytes 8 0)) layout.count = some 0 :=
      word_read_after_write unavailable layout.count 0
    change observe layout (writeBytes unavailable layout.count (unpackBytes 8 (0 : Word))) = some []
    rw [observe,countRead]
    rfl
  · intro zero
    have seen := zero 0 (by decide) (by decide) 0 (by decide)
    change word (writeBytes unavailable 0 (unpackBytes 8 0)) 16 = some 0 at seen
    have missing : word (writeBytes unavailable 0 (unpackBytes 8 0)) 16 = none := by decide
    rw [missing] at seen
    contradiction

theorem shortened_clear_is_incomplete :
    ¬zeroTail layout (initializeTable layout unavailable 1) 0 2 := by
  intro zero
  have seen := zero 1 (by decide) (by decide) 0 (by decide)
  change word (initializeTable layout unavailable 1) 32 = some 0 at seen
  have missing : word (initializeTable layout unavailable 1) 32 = none := by decide
  rw [missing] at seen
  contradiction

end Controls

#print axioms initialize_count
#print axioms initialize_observe
#print axioms initialize_zeroTail
#print axioms initialize_outside
#print axioms initialize_ready
#print axioms Controls.initializes_unavailable
#print axioms Controls.clears_all_columns
#print axioms Controls.outside_remains_unavailable
#print axioms Controls.empty_view_does_not_establish_zero_tail
#print axioms Controls.shortened_clear_is_incomplete
end Mettapedia.Machines.TIsa.RowTableInitialization
