import Mettapedia.Machines.TIsa.StoreInstructions.NativeMarkTable
import Mettapedia.Machines.TIsa.StoreInstructions.NativeTermArena
import Mettapedia.Machines.TIsa.X86PlacedArithmetic

/-!
# A fetched, data-dependent disjunction over child marks

The loop reads an edge handle from the original child arena,
checks that it names an earlier term, and only then reads the
mark. It can stop on the first set bit. Unlike an inlined list
of reads, these bytes are independent of the arity and edges.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeChildMarkLoop

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads)
open X86PlacedScalar (Code CompareBranch Jump registerCode jumpDelta)
open X86IndexedAddress (Base)
open X86PreparedLea (Index)
open NativeArenaGeometry (Region)
open NativeOccurs (word)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def edgeBase : Base := ⟨6, by decide⟩
def markBase : Base := ⟨7, by decide⟩
def edgeIndex : Index := ⟨2, by decide⟩
def childIndex : Index := ⟨0, by decide⟩
def decreaseCode : List ℕ := registerCode (X86Arithmetic.opcode .sub) 13 2
def clearCode : List ℕ := registerCode 0x89 12 0

def emit (start malformed : ℕ) : List ℕ :=
  NativeDecisions.compareBytes .lessUnsigned 12 2 start (start + 57) ++
    (decreaseCode ++ (NativeIndexedWord.loadCode edgeBase edgeIndex ++
      (NativeDecisions.compareBytes .lessUnsigned 0 1 (start + 23) malformed ++
        (NativeIndexedWord.loadCode markBase childIndex ++
          (NativeDecisions.compareBytes .notEqual 0 13 (start + 43) (start + 60) ++
            (X86UnconditionalJump.Block.code (jumpDelta (start + 52) start) ++ clearCode))))))

theorem emit_size (start malformed : ℕ) : (emit start malformed).length = 60 := by
  simp only [emit, List.length_append, NativeDecisions.compare_size, NativeIndexedWord.load_size,
    X86UnconditionalJump.Block.code_length, show decreaseCode.length = 3 from rfl, show clearCode.length = 3 from rfl]

structure Placed (image : NativeImage.View) (start malformed : ℕ) : Prop where
  extent : start + 60 ≤ image.size
  more : CompareBranch image start (start + 57) .lessUnsigned 12 2
  decrease : Code image (start + 9) decreaseCode
  edge : Code image (start + 12) (NativeIndexedWord.loadCode edgeBase edgeIndex)
  earlier : CompareBranch image (start + 23) malformed .lessUnsigned 0 1
  bit : Code image (start + 32) (NativeIndexedWord.loadCode markBase childIndex)
  check : CompareBranch image (start + 43) (start + 60) .notEqual 0 13
  again : Jump image (start + 52) start
  clear : Code image (start + 57) clearCode

theorem placed_of_emitted (image : NativeImage.View) (start malformed : ℕ) (size : start + 60 ≤ image.size)
    (target : malformed ≤ image.size) (short : image.size < 2 ^ 31)
    (bytes : Code image start (emit start malformed)) : Placed image start malformed := by
  obtain ⟨more, rest⟩ := NativeWords.code_append (show Code image start
    (NativeDecisions.compareBytes .lessUnsigned 12 2 start (start + 57) ++ _) from bytes)
  rw [NativeDecisions.compare_size] at rest
  obtain ⟨decrease, rest⟩ := NativeWords.code_append rest
  change Code image (start + 12) _ at rest
  obtain ⟨edge, rest⟩ := NativeWords.code_append rest
  rw [NativeIndexedWord.load_size] at rest
  obtain ⟨earlier, rest⟩ := NativeWords.code_append rest
  rw [NativeDecisions.compare_size] at rest
  obtain ⟨bit, rest⟩ := NativeWords.code_append rest
  rw [NativeIndexedWord.load_size] at rest
  obtain ⟨check, rest⟩ := NativeWords.code_append rest
  rw [NativeDecisions.compare_size] at rest
  obtain ⟨again, clear⟩ := NativeWords.code_append rest
  refine ⟨size, NativeDecisions.compare_placed image _ _ _ _ _ (by omega) (by omega) short more,
    decrease, edge, NativeDecisions.compare_placed image _ _ _ _ _ (by omega) target short earlier, bit,
    NativeDecisions.compare_placed image _ _ _ _ _ (by omega) size short check,
    ⟨by omega, by omega, ?_, again⟩, clear⟩
  unfold jumpDelta
  rw [BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)]
  omega

noncomputable abbrev handlers := X86IndexedAddress.handlers

abbrev clobbers : Finset Register := {.rax, .rdx, .r10, .rflags, .rip}

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

variable {nodeCapacity edgeCapacity markCapacity : ℕ}
variable {layout : NativeTermArena.Layout nodeCapacity edgeCapacity} {arena : PackedTerms.Arena}
variable {table : Region markCapacity} {marks : Array Bool} {node : PackedTerms.Node}

structure Input (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (arena : PackedTerms.Arena)
    (table : Region markCapacity) (marks : Array Bool) (node : PackedTerms.Node) (remaining : ℕ) (before : Native) : Prop where
  source : NativeTermArena.Ready layout arena before
  marked : NativeMarkTable.Ready table marks before
  span : lookup before 6 = some (layout.edges.atWord node.childrenAt.toNat)
  tableBase : lookup before 7 = some (table.atWord 0)
  parent : lookup before 1 = some (BitVec.ofNat 64 marks.size)
  count : lookup before 2 = some (BitVec.ofNat 64 remaining)
  zero : lookup before 12 = some 0
  one : lookup before 13 = some 1

private theorem count_exact (table : Region markCapacity) (n : ℕ) (fits : n ≤ markCapacity) :
    (BitVec.ofNat 64 n).toNat = n := by
  have below : n < 2 ^ 64 := by
    by_cases empty : markCapacity = 0
    · omega
    · have cap := table.positive_room (by omega : 0 < markCapacity)
      omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt below]

private theorem physical_counter {children : Array Word} (segment : PackedTerms.segment arena.children node = some children)
    (remaining : ℕ) (bound : remaining ≤ children.size) :
    (BitVec.ofNat 64 remaining).toNat = remaining := by
  have size := (PackedTerms.segment_width arena.children node children segment).1
  have limit := node.childrenCount.isLt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem minus_one (n : ℕ) : BitVec.ofNat 64 (n + 1) - 1 = BitVec.ofNat 64 n := by
  rw [BitVec.ofNat_add, show BitVec.ofNat 64 1 = (1 : Word) from rfl]
  exact BitVec.add_sub_cancel _ _

/-- The fetched loop has a complete run and returns the source
disjunction for the requested prefix. It never reads a mark
from an uninitialized slot, and writes no memory. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start malformed : ℕ}
    (placed : Placed image start malformed) (children : Array Word) (bits : List Bool)
    (segment : PackedTerms.segment arena.children node = some children)
    (ordered : PackedOccurs.childrenBits marks children = some bits)
    (remaining : ℕ) (bound : remaining ≤ children.size)
    {before : Native} (point : At image before base start) (controls : Controls before)
    (input : Input layout arena table marks node remaining before) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧ steps ≤ 12 * remaining + 3 ∧
      X86StateFrame.Frame clobbers ∅ before after ∧
      lookup after 0 = some (word ((bits.take remaining).any id)) ∧ Nonempty (At image after base (start + 60)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  obtain ⟨size, follows⟩ := PackedOccursPrefix.child_coordinates marks children bits ordered
  induction remaining generalizing before with
  | zero =>
    obtain ⟨a, checked, registerFrame, ⟨endpoint⟩⟩ := X86PlacedScalar.compare_branch
      (X86PlacedFrameAddress.nativeBase other) extra vector point .lessUnsigned 12 2 placed.more 0 0 input.zero input.count
    have atClear : At image a base (start + 57) := endpoint
    obtain ⟨after, moved, movedFrame, actual, finish⟩ := X86PlacedRegisterMove.executes
      (handlers other extra) vector atClear (by omega) 12 0 0 ((registerFrame.lookup 12 (by decide)).trans input.zero) placed.clear
    exact ⟨after, 3, X86FuelPrefix.fetches_then 2 1 before a after checked moved, by omega,
      (X86StateFrame.registerOnly (registerFrame.trans movedFrame)).mono (by decide) (by simp), actual, finish⟩
  | succ n ih =>
    obtain ⟨a, checked, checkedFrame, ⟨proceed⟩⟩ := X86PlacedScalar.compare_branch
      (X86PlacedFrameAddress.nativeBase other) extra vector point .lessUnsigned 12 2 placed.more 0 _ input.zero input.count
    change At image a base (if decide (0 < (BitVec.ofNat 64 (n + 1)).toNat) then start + 9
      else start + 57) at proceed
    rw [physical_counter segment _ bound] at proceed
    simp only [show 0 < n + 1 by omega, decide_true, if_true] at proceed
    obtain ⟨b, decreased, decreaseFrame, index, ⟨atRead⟩⟩ := X86PlacedArithmetic.executes
      (handlers other extra) vector proceed (by omega) .sub 13 2 _ 1
      ((checkedFrame.lookup 13 (by decide)).trans input.one) ((checkedFrame.lookup 2 (by decide)).trans input.count)
      placed.decrease
    have link : X86Arithmetic.linkedHandlers (handlers other extra) = handlers other extra := rfl
    rw [link] at decreased
    change lookup b 2 = some (BitVec.ofNat 64 (n + 1) - 1) at index
    rw [minus_one] at index
    let i : Fin children.size := ⟨n, by omega⟩
    let handle := children[i]
    have ordinal := physical_counter segment n (by omega)
    have available := (PackedTerms.segment_width arena.children node children segment).2
    let edge : Fin arena.children.size := ⟨node.childrenAt.toNat + n, by omega⟩
    have edgeWord : arena.children[edge] = handle := by
      have read := PackedTerms.segment_at arena.children node children i segment
      change arena.children[edge.val]? = some handle at read
      rw [Array.getElem?_eq_getElem edge.isLt] at read
      exact Option.some.inj read
    have prelude := X86StateFrame.registerOnly (checkedFrame.trans decreaseFrame)
    have knownEdge := (input.source.child edge).preserved prelude (by simp)
    rw [edgeWord] at knownEdge
    have physicalEdge : node.childrenAt.toNat + (BitVec.ofNat 64 n).toNat < edgeCapacity := by
      rw [ordinal]
      exact edge.isLt.trans_le input.source.edgesFit
    have addressEdge' : (⟨node.childrenAt.toNat + (BitVec.ofNat 64 n).toNat, physicalEdge⟩ : Fin edgeCapacity) =
        ⟨edge.val, edge.isLt.trans_le input.source.edgesFit⟩ := by
      apply Fin.ext
      exact congrArg (node.childrenAt.toNat + ·) ordinal
    have atWord : Reads b
        ((layout.edges.wordCell ⟨node.childrenAt.toNat + (BitVec.ofNat 64 n).toNat, physicalEdge⟩).cell 0).address handle := by
      rw [addressEdge']
      exact knownEdge
    obtain ⟨c, edgeLoaded, edgeFrame, actualHandle, ⟨atEarlier⟩⟩ := NativeIndexedWord.fetched_load other extra vector
      (show At image b base (start + 12) from atRead) (controls.transport prelude (by decide)) (by omega)
      edgeBase edgeIndex layout.edges node.childrenAt.toNat (BitVec.ofNat 64 n) handle physicalEdge
      ((prelude.lookup 6 (by decide)).trans input.span) index atWord placed.edge
    have throughEdge := prelude.trans edgeFrame
    let bit := bits[n]'(by omega)
    have actualBit : marks[handle.toNat]? = some bit := by
      have read := follows i
      rw [List.getElem?_eq_getElem (by change n < bits.length; omega)] at read
      exact read
    obtain ⟨inside, knownBit⟩ := input.marked.at_word handle actualBit
    obtain ⟨d, guarded, guardFrame, ⟨atBit⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
      extra vector (show At image c base (start + 23) from atEarlier) .lessUnsigned 0 1 placed.earlier handle _
      actualHandle ((throughEdge.lookup 1 (by decide)).trans input.parent)
    change At image d base (if decide (handle.toNat < (BitVec.ofNat 64 marks.size).toNat) then start + 23 + 9
      else malformed) at atBit
    rw [count_exact table _ input.marked.fits] at atBit
    simp only [inside, decide_true, if_true] at atBit
    have eligible := throughEdge.trans (X86StateFrame.registerOnly guardFrame)
    have physicalBit : 0 + handle.toNat < markCapacity := by simpa using inside.trans_le input.marked.fits
    have addressBit' : (⟨0 + handle.toNat, physicalBit⟩ : Fin markCapacity) =
        ⟨handle.toNat, inside.trans_le input.marked.fits⟩ := Fin.ext (Nat.zero_add _)
    have atMark : Reads d ((table.wordCell ⟨0 + handle.toNat, physicalBit⟩).cell 0).address (word bit) := by
      rw [addressBit']
      exact knownBit.preserved eligible (by simp)
    obtain ⟨e, bitLoaded, bitFrame, materialized, ⟨atCheck⟩⟩ := NativeIndexedWord.fetched_load other extra vector
      (show At image d base (start + 32) from atBit) (controls.transport eligible (by decide)) (by omega)
      markBase childIndex table 0 handle (word bit) physicalBit
      ((eligible.lookup 7 (by decide)).trans input.tableBase) ((guardFrame.lookup 0 (by decide)).trans actualHandle) atMark placed.bit
    have afterBit := eligible.trans bitFrame
    obtain ⟨f, tested, testFrame, ⟨position⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
      extra vector (show At image e base (start + 43) from atCheck) .notEqual 0 13 placed.check (word bit) 1
      materialized ((afterBit.lookup 13 (by decide)).trans input.one)
    have ranThree := X86FuelPrefix.fetches_then 2 1 before a b checked decreased
    have ranFive := X86FuelPrefix.fetches_then 3 2 before b c ranThree edgeLoaded
    have ranSeven := X86FuelPrefix.fetches_then 5 2 before c d ranFive guarded
    have ranNine := X86FuelPrefix.fetches_then 7 2 before d e ranSeven bitLoaded
    have ranEleven := X86FuelPrefix.fetches_then 9 2 before e f ranNine tested
    have testedFrame := afterBit.trans (X86StateFrame.registerOnly testFrame)
    have nextBits : bits.take (n + 1) = bits.take n ++ [bit] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
      rfl
    cases active : bit with
    | true =>
      have check : Comparison.notEqual.evaluate (word true) 1 = false := by decide +kernel
      have endAt : At image f base (start + 60) := by
        simpa only [active, check, Bool.false_eq_true, if_false] using position
      have answer : ((bits.take (n + 1)).any id) = true := by simp [nextBits, List.any_append, active]
      exact ⟨f, 11, ranEleven, by omega, testedFrame.mono (by decide) (by simp),
        (testFrame.lookup 0 (by decide)).trans (by rw [answer]; simpa only [active] using materialized), ⟨endAt⟩⟩
    | false =>
      have check : Comparison.notEqual.evaluate (word false) 1 = true := by decide +kernel
      have atJump : At image f base (start + 52) := by simpa only [active, check, if_true] using position
      obtain ⟨g, jumped, jumpFrame, ⟨back⟩⟩ := X86PlacedScalar.jump (X86PlacedFrameAddress.nativeBase other)
        extra vector atJump placed.again
      have frame : X86StateFrame.Frame clobbers ∅ before g :=
        (testedFrame.trans (X86StateFrame.registerOnly jumpFrame)).mono (by decide) (by simp)
      have remainingFrame := ((((edgeFrame.trans (X86StateFrame.registerOnly guardFrame)).trans bitFrame).trans
        (X86StateFrame.registerOnly testFrame)).trans (X86StateFrame.registerOnly jumpFrame))
      have next : Input layout arena table marks node n g :=
        ⟨input.source.preserved frame, input.marked.preserved frame, (frame.lookup 6 (by decide)).trans input.span,
          (frame.lookup 7 (by decide)).trans input.tableBase, (frame.lookup 1 (by decide)).trans input.parent,
          (remainingFrame.lookup 2 (by decide)).trans index, (frame.lookup 12 (by decide)).trans input.zero,
          (frame.lookup 13 (by decide)).trans input.one⟩
      obtain ⟨after, steps, ran, cost, laterFrame, value, finish⟩ := ih (by omega) back
        (controls.transport frame clobbers_data) next
      have complete := X86FuelPrefix.fetches_then 12 steps before g after
        (X86FuelPrefix.fetches_then 11 1 before f g ranEleven jumped) ran
      exact ⟨after, 12 + steps, complete, by omega, (frame.trans laterFrame).mono (by simp) (by simp),
        by simpa [nextBits, List.any_append, active] using value, finish⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeChildMarkLoop
