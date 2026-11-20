import Mettapedia.Machines.TIsa.X86PlacedMemory

/-! # Adjacent qword stores through a shared base register -/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86PlacedPairStore

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code)
open X86PlacedMemory (Encoding Cell Controls Reads CodeApart footprint)
local instance : MemoryPrimitives := X86Memory.ordinary

structure Layout where
  start : Nat
  encoding : Encoding
  firstSource : Fin 16
  secondSource : Fin 16
  firstOffset : BitVec 32
  secondOffset : BitVec 32

def Layout.second (layout : Layout) : Nat := layout.start + layout.encoding.length
def Layout.finish (layout : Layout) : Nat := layout.second + layout.encoding.length

def Layout.Checked (layout : Layout) (image : NativeImage.View) : Prop :=
  layout.finish ≤ image.size ∧
  Code image layout.start (layout.encoding.bytes layout.firstSource layout.firstOffset) ∧
  Code image layout.second (layout.encoding.bytes layout.secondSource layout.secondOffset)

instance (layout : Layout) (image : NativeImage.View) : Decidable (layout.Checked image) :=
  inferInstanceAs (Decidable (_ ∧ _))

structure Cells (layout : Layout) (baseValue : Word) where
  first : Cell baseValue layout.firstOffset
  second : Cell baseValue layout.secondOffset
  apart : Disjoint (footprint first.address) (footprint second.address)

abbrev Cells.writes {layout : Layout} {baseValue : Word} (cells : Cells layout baseValue) : Finset Nat :=
  footprint cells.first.address ∪ footprint cells.second.address

private theorem outside_rip : ∀ register : Fin 16, key register ∉ ({.rip} : Finset Register) := by decide

theorem stores (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {state : State} {base : BitVec 48} {layout : Layout}
    (point : At image state base layout.start) (known : Controls state)
    (checked : layout.Checked image) (baseValue firstValue secondValue : Word)
    (cells : Cells layout baseValue) (apart : CodeApart image base cells.writes)
    (baseKnown : lookup state layout.encoding.base = some baseValue)
    (firstKnown : lookup state layout.firstSource = some firstValue)
    (secondKnown : lookup state layout.secondSource = some secondValue) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run state = .ok () after ∧
      X86StateFrame.Frame {.rip} cells.writes state after ∧
      Reads after cells.first.address firstValue ∧ Reads after cells.second.address secondValue ∧
      Nonempty (At image after base layout.finish) := by
  let : OtherOpcodeHandlers := other
  let : VectorOpcodeHandlers := vector
  obtain ⟨inside, firstCode, secondCode⟩ := checked
  have firstInside : layout.start + layout.encoding.length ≤ image.size := by
    unfold Layout.finish Layout.second at inside
    omega
  obtain ⟨middle, first, written, value, ⟨next⟩⟩ := X86PlacedMemory.stores other vector point known
    layout.encoding layout.firstSource layout.firstOffset baseValue firstValue cells.first baseKnown firstKnown
    firstInside firstCode (apart.mono Finset.subset_union_left)
  obtain ⟨after, second, writtenAgain, otherValue, reached⟩ := X86PlacedMemory.stores other vector next
    (known.transport written (by decide)) layout.encoding layout.secondSource layout.secondOffset baseValue secondValue cells.second
    ((written.lookup _ (outside_rip _)).trans baseKnown) ((written.lookup _ (outside_rip _)).trans secondKnown)
    inside secondCode (apart.mono Finset.subset_union_right)
  exact ⟨after, @X86FuelPrefix.fetches_then other vector 1 1 state middle after first second,
    (written.trans writtenAgain).mono (by simp) (Finset.Subset.refl _),
    value.preserved writtenAgain cells.apart, otherValue, reached⟩

end Mettapedia.Machines.TIsa.X86PlacedPairStore
