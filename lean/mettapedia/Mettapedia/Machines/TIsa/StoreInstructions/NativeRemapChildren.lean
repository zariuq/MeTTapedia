import Mettapedia.Machines.TIsa.StoreInstructions.NativeSubstLeaf

/-!
# Checking for a changed compound before reserving a copy

The fixed byte stream compares each old child handle with its
word in the initialized remap prefix. It can leave at the first
difference. If they all agree, the application can keep its
old handle without reconstructing either the node or its edges.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeRemapChildren

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads)
open X86PlacedScalar (Code CompareBranch Jump registerCode jumpDelta)
open NativeArenaGeometry (Region)
open NativeSubstLeaf (MapReady)
open NativeChildMarkLoop (edgeBase edgeIndex childIndex markBase decreaseCode)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def mapRead : List ℕ := NativeIndexedWord.loadToCode markBase childIndex 14

def visitCode (start stop malformed : ℕ) : List ℕ :=
  NativeDecisions.compareBytes .lessUnsigned 12 2 start stop ++
    (decreaseCode ++ (NativeIndexedWord.loadCode edgeBase edgeIndex ++
      (NativeDecisions.compareBytes .lessUnsigned 0 1 (start + 23) malformed ++ mapRead)))

def emit (start unchanged changed malformed : ℕ) : List ℕ :=
  visitCode start unchanged malformed ++ (NativeDecisions.compareBytes .equal 0 14 (start + 43) changed ++
    X86UnconditionalJump.Block.code (jumpDelta (start + 52) start))

theorem visit_size (start stop malformed : ℕ) : (visitCode start stop malformed).length = 43 := by
  simp only [visitCode, List.length_append, NativeDecisions.compare_size, NativeIndexedWord.load_size,
    show decreaseCode.length = 3 from rfl, show mapRead.length = 11 from rfl]

theorem emit_size (start unchanged changed malformed : ℕ) :
    (emit start unchanged changed malformed).length = 57 := by
  simp only [emit, List.length_append, visit_size, NativeDecisions.compare_size, X86UnconditionalJump.Block.code_length]

structure VisitPlaced (image : NativeImage.View) (start stop malformed : ℕ) : Prop where
  extent : start + 43 ≤ image.size
  more : CompareBranch image start stop .lessUnsigned 12 2
  decrease : Code image (start + 9) decreaseCode
  edge : Code image (start + 12) (NativeIndexedWord.loadCode edgeBase edgeIndex)
  earlier : CompareBranch image (start + 23) malformed .lessUnsigned 0 1
  mapped : Code image (start + 32) mapRead

theorem visit_placed (image : NativeImage.View) (start stop malformed : ℕ)
    (size : start + 43 ≤ image.size) (finished : stop ≤ image.size) (bad : malformed ≤ image.size)
    (short : image.size < 2 ^ 31) (bytes : Code image start (visitCode start stop malformed)) :
    VisitPlaced image start stop malformed := by
  obtain ⟨more, rest⟩ := NativeWords.code_append (show Code image start
    (NativeDecisions.compareBytes .lessUnsigned 12 2 start stop ++ _) from bytes)
  rw [NativeDecisions.compare_size] at rest
  obtain ⟨decrease, rest⟩ := NativeWords.code_append rest
  change Code image (start + 12) _ at rest
  obtain ⟨edge, rest⟩ := NativeWords.code_append rest
  rw [NativeIndexedWord.load_size] at rest
  obtain ⟨earlier, mapped⟩ := NativeWords.code_append rest
  rw [NativeDecisions.compare_size] at mapped
  exact ⟨size, NativeDecisions.compare_placed image _ _ _ _ _ (by omega) finished short more,
    decrease, edge, NativeDecisions.compare_placed image _ _ _ _ _ (by omega) bad short earlier, mapped⟩

structure Placed (image : NativeImage.View) (start unchanged changed malformed : ℕ) : Prop where
  extent : start + 57 ≤ image.size
  visit : VisitPlaced image start unchanged malformed
  compare : CompareBranch image (start + 43) changed .equal 0 14
  again : Jump image (start + 52) start

theorem placed_of_emitted (image : NativeImage.View) (start unchanged changed malformed : ℕ)
    (size : start + 57 ≤ image.size) (same : unchanged ≤ image.size) (different : changed ≤ image.size)
    (bad : malformed ≤ image.size) (short : image.size < 2 ^ 31)
    (bytes : Code image start (emit start unchanged changed malformed)) :
    Placed image start unchanged changed malformed := by
  obtain ⟨visited, rest⟩ := NativeWords.code_append (show Code image start (visitCode start unchanged malformed ++ _) from bytes)
  rw [visit_size] at rest
  obtain ⟨compare, again⟩ := NativeWords.code_append rest
  rw [NativeDecisions.compare_size] at again
  refine ⟨size, visit_placed image start unchanged malformed (by omega) same bad short visited,
    NativeDecisions.compare_placed image _ _ _ _ _ (by omega) different short compare, ⟨by omega, by omega, ?_, again⟩⟩
  unfold jumpDelta
  rw [BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)]
  omega

noncomputable abbrev handlers := X86IndexedAddress.handlers

abbrev clobbers : Finset Register := {.rax, .rdx, .r10, .r14, .rflags, .rip}

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

variable {nodeCapacity edgeCapacity mapCapacity : ℕ}
variable {layout : NativeTermArena.Layout nodeCapacity edgeCapacity} {arena : PackedTerms.Arena}
variable {table : Region mapCapacity} {mapping : Array Word} {node : PackedTerms.Node}

structure Input (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (arena : PackedTerms.Arena)
    (table : Region mapCapacity) (mapping : Array Word) (node : PackedTerms.Node) (remaining : ℕ) (before : Native) : Prop where
  source : NativeTermArena.Ready layout arena before
  mapped : MapReady table mapping before
  span : lookup before 6 = some (layout.edges.atWord node.childrenAt.toNat)
  tableBase : lookup before 7 = some (table.atWord 0)
  parent : lookup before 1 = some (BitVec.ofNat 64 mapping.size)
  count : lookup before 2 = some (BitVec.ofNat 64 remaining)
  zero : lookup before 12 = some 0
  one : lookup before 13 = some 1

private theorem word_count (table : Region mapCapacity) (n : ℕ) (fits : n ≤ mapCapacity) :
    (BitVec.ofNat 64 n).toNat = n := by
  by_cases empty : mapCapacity = 0
  · have zero : n = 0 := by omega
    rw [zero]; rfl
  · have cap := table.positive_room (by omega : 0 < mapCapacity)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem child_count {children : Array Word} (segment : PackedTerms.segment arena.children node = some children)
    (n : ℕ) (fits : n ≤ children.size) : (BitVec.ofNat 64 n).toNat = n := by
  have size := (PackedTerms.segment_width arena.children node children segment).1
  have limit := node.childrenCount.isLt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem minus_one (n : ℕ) : BitVec.ofNat 64 (n + 1) - 1 = BitVec.ofNat 64 n := by
  rw [BitVec.ofNat_add, show BitVec.ofNat 64 1 = (1 : Word) from rfl]
  exact BitVec.add_sub_cancel _ _

/-- The common nonempty visit reads both actual words, decrements
the cursor, and leaves the array and remap untouched. -/
theorem fetched_visit (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start stop malformed : ℕ}
    (placed : VisitPlaced image start stop malformed) (children newer : Array Word)
    (segment : PackedTerms.segment arena.children node = some children)
    (translated : PackedSubstitution.translate mapping children = some newer)
    (n : ℕ) (bound : n + 1 ≤ children.size)
    {before : Native} (point : At image before base start) (controls : Controls before)
    (input : Input layout arena table mapping node (n + 1) before) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 9).run before = .ok () after ∧ X86StateFrame.Frame clobbers ∅ before after ∧
      lookup after 0 = children[n]? ∧ lookup after 14 = newer[n]? ∧
      lookup after 2 = some (BitVec.ofNat 64 n) ∧ Nonempty (At image after base (start + 43)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have space := placed.extent
  obtain ⟨width, coordinates⟩ := PackedRemapCoordinates.coordinates mapping children newer translated
  obtain ⟨a, tested, testFrame, ⟨nonempty⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
    extra vector point .lessUnsigned 12 2 placed.more 0 _ input.zero input.count
  change At image a base (if decide (0 < (BitVec.ofNat 64 (n + 1)).toNat) then start + 9 else stop) at nonempty
  rw [child_count segment _ bound] at nonempty
  simp only [show 0 < n + 1 by omega, decide_true, if_true] at nonempty
  obtain ⟨b, decreased, decFrame, newIndex, ⟨atEdge⟩⟩ := X86PlacedArithmetic.executes
    (handlers other extra) vector nonempty (by omega) .sub 13 2 _ 1
    ((testFrame.lookup 13 (by decide)).trans input.one) ((testFrame.lookup 2 (by decide)).trans input.count) placed.decrease
  have ordinary : X86Arithmetic.linkedHandlers (handlers other extra) = handlers other extra := rfl
  rw [ordinary] at decreased
  change lookup b 2 = some (BitVec.ofNat 64 (n + 1) - 1) at newIndex
  rw [minus_one] at newIndex
  let i : Fin children.size := ⟨n, by omega⟩
  let original := children[i]
  let moved := newer[n]'(by omega)
  have ordinal := child_count segment n (by omega)
  have available := (PackedTerms.segment_width arena.children node children segment).2
  let edge : Fin arena.children.size := ⟨node.childrenAt.toNat + n, by omega⟩
  have edgeWord : arena.children[edge] = original := by
    have read := PackedTerms.segment_at arena.children node children i segment
    change arena.children[edge.val]? = some original at read
    rw [Array.getElem?_eq_getElem edge.isLt] at read
    exact Option.some.inj read
  have prefixFrame := X86StateFrame.registerOnly (testFrame.trans decFrame)
  have edgeRead := (input.source.child edge).preserved prefixFrame (by simp)
  rw [edgeWord] at edgeRead
  have physicalEdge : node.childrenAt.toNat + (BitVec.ofNat 64 n).toNat < edgeCapacity := by
    rw [ordinal]
    exact edge.isLt.trans_le input.source.edgesFit
  have sameEdge : (⟨node.childrenAt.toNat + (BitVec.ofNat 64 n).toNat, physicalEdge⟩ : Fin edgeCapacity) =
      ⟨edge.val, edge.isLt.trans_le input.source.edgesFit⟩ := Fin.ext (congrArg (node.childrenAt.toNat + ·) ordinal)
  have nativeEdge : Reads b
      ((layout.edges.wordCell ⟨node.childrenAt.toNat + (BitVec.ofNat 64 n).toNat, physicalEdge⟩).cell 0).address original := by
    rw [sameEdge]
    exact edgeRead
  obtain ⟨c, loaded, edgeFrame, old, ⟨atRange⟩⟩ := NativeIndexedWord.fetched_load other extra vector
    (show At image b base (start + 12) from atEdge) (controls.transport prefixFrame (by decide)) (by omega)
    edgeBase edgeIndex layout.edges node.childrenAt.toNat (BitVec.ofNat 64 n) original physicalEdge
    ((prefixFrame.lookup 6 (by decide)).trans input.span) newIndex nativeEdge placed.edge
  have throughEdge := prefixFrame.trans edgeFrame
  have atMapping : mapping[original.toNat]? = some moved := by
    have value := coordinates i
    exact value.trans (Array.getElem?_eq_getElem (by omega : n < newer.size))
  obtain ⟨mappedInside, mappedRead⟩ := input.mapped.at_word original atMapping
  obtain ⟨d, eligible, rangeFrame, ⟨atMap⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
    extra vector (show At image c base (start + 23) from atRange) .lessUnsigned 0 1 placed.earlier original _
    old ((throughEdge.lookup 1 (by decide)).trans input.parent)
  change At image d base
    (if decide (original.toNat < (BitVec.ofNat 64 mapping.size).toNat) then start + 23 + 9 else malformed) at atMap
  rw [word_count table _ input.mapped.fits] at atMap
  simp only [mappedInside, decide_true, if_true] at atMap
  have beforeMap := throughEdge.trans (X86StateFrame.registerOnly rangeFrame)
  have slot : 0 + original.toNat < mapCapacity := by simpa using mappedInside.trans_le input.mapped.fits
  have sameSlot : (⟨0 + original.toNat, slot⟩ : Fin mapCapacity) =
      ⟨original.toNat, mappedInside.trans_le input.mapped.fits⟩ := Fin.ext (Nat.zero_add _)
  have nativeMapped : Reads d ((table.wordCell ⟨0 + original.toNat, slot⟩).cell 0).address moved := by
    rw [sameSlot]
    exact mappedRead.preserved beforeMap (by simp)
  obtain ⟨e, readMapped, mapFrame, translatedWord, ⟨atCompare⟩⟩ := NativeIndexedWord.fetched_load_to other extra vector
    (show At image d base (start + 32) from atMap) (controls.transport beforeMap (by decide)) (by omega)
    markBase childIndex 14 (by decide) table 0 original moved slot ((beforeMap.lookup 7 (by decide)).trans input.tableBase)
    ((rangeFrame.lookup 0 (by decide)).trans old) nativeMapped placed.mapped
  have throughMap := beforeMap.trans mapFrame
  have three := X86FuelPrefix.fetches_then 2 1 before a b tested decreased
  have five := X86FuelPrefix.fetches_then 3 2 before b c three loaded
  have seven := X86FuelPrefix.fetches_then 5 2 before c d five eligible
  have nine := X86FuelPrefix.fetches_then 7 2 before d e seven readMapped
  have sourceWord : lookup e 0 = children[n]? := by
    rw [Array.getElem?_eq_getElem i.isLt]
    exact (mapFrame.lookup 0 (by decide)).trans ((rangeFrame.lookup 0 (by decide)).trans old)
  have targetWord : lookup e 14 = newer[n]? := by
    rw [Array.getElem?_eq_getElem (by omega : n < newer.size)]
    exact translatedWord
  have remains := ((edgeFrame.trans (X86StateFrame.registerOnly rangeFrame)).trans mapFrame)
  exact ⟨e, nine, throughMap.mono (by decide) (by simp), sourceWord, targetWord,
    (remains.lookup 2 (by decide)).trans newIndex, ⟨atCompare⟩⟩

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start unchanged changed malformed : ℕ}
    (placed : Placed image start unchanged changed malformed) (children newer : Array Word)
    (segment : PackedTerms.segment arena.children node = some children)
    (translated : PackedSubstitution.translate mapping children = some newer)
    (remaining : ℕ) (bound : remaining ≤ children.size)
    {before : Native} (point : At image before base start) (controls : Controls before)
    (input : Input layout arena table mapping node remaining before) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧ steps ≤ 12 * remaining + 2 ∧
      X86StateFrame.Frame clobbers ∅ before after ∧
      Nonempty (At image after base
        (if children.toList.take remaining = newer.toList.take remaining then unchanged else changed)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have width := (PackedRemapCoordinates.coordinates mapping children newer translated).1
  induction remaining generalizing before with
  | zero =>
    obtain ⟨after, ran, frame, endpoint⟩ := X86PlacedScalar.compare_branch
      (X86PlacedFrameAddress.nativeBase other) extra vector point .lessUnsigned 12 2 placed.visit.more 0 0 input.zero input.count
    exact ⟨after, 2, ran, by omega, (X86StateFrame.registerOnly frame).mono (by decide) (by simp), endpoint⟩
  | succ n ih =>
    let i : Fin children.size := ⟨n, by omega⟩
    let original := children[i]
    let moved := newer[n]'(by omega)
    obtain ⟨e, visited, throughMap, old, relocated, index, ⟨atCompare⟩⟩ :=
      fetched_visit other extra vector placed.visit children newer segment translated n bound point controls input
    rw [Array.getElem?_eq_getElem i.isLt] at old
    rw [Array.getElem?_eq_getElem (by omega : n < newer.size)] at relocated
    obtain ⟨f, compared, cmpFrame, ⟨destination⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
      extra vector atCompare .equal 0 14 placed.compare original moved old relocated
    simp only [Comparison.evaluate, beq_iff_eq] at destination
    have eleven := X86FuelPrefix.fetches_then 9 2 before e f visited compared
    have inspected := throughMap.trans (X86StateFrame.registerOnly cmpFrame)
    have equivalence :
        children.toList.take (n + 1) = newer.toList.take (n + 1) ↔
          children.toList.take n = newer.toList.take n ∧ original = moved := by
      have relation := PackedRemapCoordinates.take_next_same children.toList newer.toList n
        (by rw [Array.length_toList]; omega) (by rw [Array.length_toList]; omega)
      change _ ↔ _ ∧ children[n]'(by omega) = newer[n]'(by omega)
      simpa only [Array.getElem_toList] using relation
    by_cases same : original = moved
    · simp only [if_pos same] at destination
      obtain ⟨g, jumped, jumpFrame, ⟨back⟩⟩ := X86PlacedScalar.jump (X86PlacedFrameAddress.nativeBase other)
        extra vector destination placed.again
      have advanced : X86StateFrame.Frame clobbers ∅ before g :=
        (inspected.trans (X86StateFrame.registerOnly jumpFrame)).mono (by decide) (by simp)
      have remainingFrame := X86StateFrame.registerOnly (cmpFrame.trans jumpFrame)
      have next : Input layout arena table mapping node n g :=
        ⟨input.source.preserved advanced, input.mapped.preserved advanced, (advanced.lookup 6 (by decide)).trans input.span,
          (advanced.lookup 7 (by decide)).trans input.tableBase, (advanced.lookup 1 (by decide)).trans input.parent,
          (remainingFrame.lookup 2 (by decide)).trans index, (advanced.lookup 12 (by decide)).trans input.zero,
          (advanced.lookup 13 (by decide)).trans input.one⟩
      obtain ⟨after, steps, ran, cost, frame, endpoint⟩ := ih (by omega) back
        (controls.transport advanced clobbers_data) next
      exact ⟨after, 12 + steps, X86FuelPrefix.fetches_then 12 steps before g after
        (X86FuelPrefix.fetches_then 11 1 before f g eleven jumped) ran, by omega,
        (advanced.trans frame).mono (by simp) (by simp), by simpa only [equivalence, same, and_true] using endpoint⟩
    · simp only [if_neg same] at destination
      have disagree : children.toList.take (n + 1) ≠ newer.toList.take (n + 1) := fun h => same (equivalence.mp h).2
      exact ⟨f, 11, eleven, by omega, inspected.mono (by decide) (by simp), by simpa only [if_neg disagree] using ⟨destination⟩⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeRemapChildren
