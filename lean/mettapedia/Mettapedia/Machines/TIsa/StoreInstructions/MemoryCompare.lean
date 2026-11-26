import Mettapedia.Machines.TIsa.StoreInstructions.MatchPlan
import Mettapedia.Machines.TIsa.StoreInstructions.MemoryBinding

/-!
# Native comparison of a loaded constructor

Constructor keys have an encoding independent of subterm handles.
The absence of a path is encoded too, and is never the expected key
of a constructor test. The observed key is read from the candidate
array; only the expected key is a literal in the emitted code.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.MemoryCompare

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Cell Reads)
open X86PlacedScalar (Code CompareBranch)
open NativeWords (Wiring touched outside_scratch)
open Mettapedia.Logic.LP
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Native := X86RegisterRefinement.State

structure Layout where
  left : Wiring
  right : Wiring
  distinct : left.scratch ≠ right.scratch
  rightBasePreserved : right.readBase ≠ left.scratch

variable {firstBase secondBase : Word}

structure Checked (layout : Layout) (image : NativeImage.View) (start refused : ℕ)
    (condition : Comparison) (left : NativeWords.Source firstBase) (right : NativeWords.Source secondBase) : Prop where
  prefixFits : start + left.width + right.width ≤ image.size
  loadLeft : Code image start (left.bytes layout.left)
  loadRight : Code image (start + left.width) (right.bytes layout.right)
  compare : CompareBranch image (start + left.width + right.width) refused
    condition layout.left.scratch layout.right.scratch

abbrev Layout.touched (layout : Layout) : Finset Register :=
  (NativeWords.touched layout.left ∪ NativeWords.touched layout.right) ∪ {.rflags, .rip}

theorem loaded_comparison (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (layout : Layout) (left : NativeWords.Source firstBase) (right : NativeWords.Source secondBase)
    (condition : Comparison) {before : Native} {image : NativeImage.View} {base : BitVec 48} {start refused : ℕ}
    (point : At image before base start) (controls : Controls before)
    (checked : Checked layout image start refused condition left right)
    (leftBase : lookup before layout.left.readBase = some firstBase)
    (rightBase : lookup before layout.right.readBase = some secondBase)
    (leftWord rightWord : Word) (leftReady : left.Ready before leftWord) (rightReady : right.Ready before rightWord) :
    letI : OtherOpcodeHandlers := MemoryBinding.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 4).run before = .ok () after ∧
      X86StateFrame.Frame layout.touched ∅ before after ∧
      Nonempty (At image after base (if condition.evaluate leftWord rightWord
        then start + left.width + right.width + 9 else refused)) := by
  let : OtherOpcodeHandlers := MemoryBinding.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨first, gotLeft, leftFrame, leftKnown, ⟨next⟩⟩ := left.fetch (MemoryBinding.handlers other extra)
    vector layout.left leftWord point controls leftBase leftReady
    (by have := checked.prefixFits; omega) checked.loadLeft
  obtain ⟨second, gotRight, rightFrame, rightKnown, ⟨atCompare⟩⟩ := right.fetch (MemoryBinding.handlers other extra)
    vector layout.right rightWord next (controls.transport leftFrame (X86Immediate32.writes_data _))
    ((leftFrame.lookup _ (outside_scratch layout.left _ layout.rightBasePreserved)).trans rightBase)
    (right.ready_preserved rightReady leftFrame (by simp)) checked.prefixFits checked.loadRight
  have leftOperand := (rightFrame.lookup _ (outside_scratch layout.right _ layout.distinct)).trans leftKnown
  obtain ⟨after, compared, comparedFrame, follow⟩ := X86PlacedScalar.compare_branch
    (X86FrameLoad.linkedHandlers other) extra vector atCompare condition
    layout.left.scratch layout.right.scratch checked.compare leftWord rightWord leftOperand rightKnown
  have loaded := X86FuelPrefix.fetches_then 1 1 before first second gotLeft gotRight
  exact ⟨after, X86FuelPrefix.fetches_then 2 2 before second after loaded compared,
    ((leftFrame.trans rightFrame).trans (X86StateFrame.registerOnly comparedFrame)).mono (by rfl) (by simp),
    follow⟩

variable {σ : LPSignature} [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

/-- The same memory compare tests a constructor at every observed
path, including an absent path. -/
theorem constructor_test (codes : PackedOccurrences.Codes (Option (MatchPlan.Symbol σ)))
    (read : MatchPlan.Observation σ) (path : MatchPlan.Path) (expected : MatchPlan.Symbol σ)
    (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (layout : Layout) (displacement : BitVec 32) (cell : Cell firstBase displacement)
    (observed target : Word)
    (represented : codes.encode ((read path).map MatchPlan.symbol) = some observed)
    (encoded : codes.encode (some expected) = some target)
    {before : Native} {image : NativeImage.View} {base : BitVec 48} {start refused : ℕ}
    (point : At image before base start) (controls : Controls before)
    (checked : Checked layout image start refused .equal (.copy displacement cell)
      (.literal target : NativeWords.Source secondBase))
    (leftBase : lookup before layout.left.readBase = some firstBase)
    (rightBase : lookup before layout.right.readBase = some secondBase)
    (loaded : Reads before cell.address observed) :
    letI : OtherOpcodeHandlers := MemoryBinding.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 4).run before = .ok () after ∧
      X86StateFrame.Frame layout.touched ∅ before after ∧
      Nonempty (At image after base (if MatchPlan.shapePasses read path expected then start + 26 else refused)) := by
  obtain ⟨after, fetched, framed, follow⟩ := loaded_comparison other extra vector layout (.copy displacement cell)
    (.literal target) .equal point controls checked leftBase rightBase observed target loaded rfl
  have equality : Comparison.equal.evaluate observed target = MatchPlan.shapePasses read path expected := by
    apply Bool.eq_iff_iff.mpr
    have code := WordTests.code_equality codes represented encoded
    change (observed == target) = true ↔ _
    rw [beq_iff_eq, code]
    cases value : read path <;> simp [MatchPlan.shapePasses, value]
  rw [equality] at follow
  exact ⟨after, fetched, framed, by simpa only [NativeWords.Source.width, Nat.add_assoc] using follow⟩

end Mettapedia.Machines.TIsa.StoreInstructions.MemoryCompare
