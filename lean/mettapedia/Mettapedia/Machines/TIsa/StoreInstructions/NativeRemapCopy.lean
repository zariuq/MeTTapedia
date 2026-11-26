import Mettapedia.Machines.TIsa.StoreInstructions.NativeRemapChildren

/-!
# Copying a changed application's translated edges

The shared visit reads the actual old handle and its remap.
This loop stores the remapped word at the same ordinal in the
reserved destination span. It neither changes the old term
graph nor publishes a new term record.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeRemapCopy

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads CodeApart footprint)
open X86PlacedScalar (Code Jump registerCode jumpDelta)
open NativeArenaGeometry (Region)
open NativeSubstLeaf (MapReady)
open NativeMarkTable (Within)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def destinationBase : X86IndexedAddress.Base := ⟨3, by decide⟩
def copyCode : List ℕ := registerCode 0x89 14 0
def storeCode : List ℕ := NativeIndexedWord.storeCode destinationBase NativeChildMarkLoop.edgeIndex

def emit (start finished malformed : ℕ) : List ℕ :=
  NativeRemapChildren.visitCode start finished malformed ++ (copyCode ++ (storeCode ++
    X86UnconditionalJump.Block.code (jumpDelta (start + 57) start)))

theorem emit_size (start finished malformed : ℕ) : (emit start finished malformed).length = 62 := by
  simp only [emit, List.length_append, NativeRemapChildren.visit_size, X86UnconditionalJump.Block.code_length,
    show copyCode.length = 3 from rfl, show storeCode.length = 11 from rfl]

structure Placed (image : NativeImage.View) (start finished malformed : ℕ) : Prop where
  extent : start + 62 ≤ image.size
  visit : NativeRemapChildren.VisitPlaced image start finished malformed
  copy : Code image (start + 43) copyCode
  store : Code image (start + 46) storeCode
  again : Jump image (start + 57) start

theorem placed_of_emitted (image : NativeImage.View) (start finished malformed : ℕ)
    (extent : start + 62 ≤ image.size) (finish : finished ≤ image.size) (bad : malformed ≤ image.size)
    (short : image.size < 2 ^ 31) (installed : Code image start (emit start finished malformed)) :
    Placed image start finished malformed := by
  obtain ⟨visit, rest⟩ := NativeWords.code_append (show Code image start
    (NativeRemapChildren.visitCode start finished malformed ++ _) from installed)
  rw [NativeRemapChildren.visit_size] at rest
  obtain ⟨copy, rest⟩ := NativeWords.code_append rest
  obtain ⟨store, again⟩ := NativeWords.code_append rest
  refine ⟨extent, NativeRemapChildren.visit_placed image _ _ _ (by omega) finish bad short visit, copy,
    store, ⟨by omega, by omega, ?_, again⟩⟩
  unfold jumpDelta
  rw [BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)]
  omega

noncomputable abbrev handlers := X86IndexedAddress.handlers

abbrev clobbers : Finset Register := NativeRemapChildren.clobbers

variable {nodeCapacity edgeCapacity mapCapacity : ℕ}
variable {layout : NativeTermArena.Layout nodeCapacity edgeCapacity} {arena : PackedTerms.Arena}
variable {table : Region mapCapacity} {mapping : Array Word} {node : PackedTerms.Node}

structure Geometry (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (table : Region mapCapacity)
    (image : NativeImage.View) (base : BitVec 48) : Prop where
  code : ∀ i : Fin edgeCapacity, CodeApart image base (footprint ((layout.edges.wordCell i).cell 0).address)
  nodes : ∀ (i : Fin nodeCapacity) (j : Fin 4) (fresh : Fin edgeCapacity),
    Disjoint (footprint ((layout.record i).cell j).address) (footprint ((layout.edges.wordCell fresh).cell 0).address)
  remap : ∀ (i : Fin mapCapacity) (fresh : Fin edgeCapacity),
    Disjoint (footprint ((table.wordCell i).cell 0).address) (footprint ((layout.edges.wordCell fresh).cell 0).address)

structure Input (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (arena : PackedTerms.Arena)
    (table : Region mapCapacity) (mapping : Array Word) (node : PackedTerms.Node)
    (destination remaining : ℕ) (before : Native) : Prop where
  words : NativeRemapChildren.Input layout arena table mapping node remaining before
  output : lookup before 3 = some (layout.edges.atWord destination)

def Stored (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (destination count : ℕ)
    (newer : Array Word) (fits : destination + count ≤ edgeCapacity) (width : count ≤ newer.size) (native : Native) : Prop :=
  ∀ i : Fin count, Reads native
    ((layout.edges.wordCell ⟨destination + i.val, by have present := i.isLt; omega⟩).cell 0).address
    (newer[i.val]'(i.isLt.trans_le width))

private theorem coordinate_word {children : Array Word} (segment : PackedTerms.segment arena.children node = some children)
    (n : ℕ) (fits : n ≤ children.size) : (BitVec.ofNat 64 n).toNat = n := by
  have width := (PackedTerms.segment_width arena.children node children segment).1
  have bound := node.childrenCount.isLt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- A complete fetched copy realizes exactly the physical words
of the translated child array. Writes are confined to the
chosen fresh span, regardless of duplicates or child aliases. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start finished malformed : ℕ}
    (placed : Placed image start finished malformed) (geometry : Geometry layout table image base)
    (children newer : Array Word) (segment : PackedTerms.segment arena.children node = some children)
    (translated : PackedSubstitution.translate mapping children = some newer)
    (destination remaining : ℕ) (bound : remaining ≤ children.size) (width : remaining ≤ newer.size)
    (afterSource : arena.children.size ≤ destination) (fits : destination + remaining ≤ edgeCapacity)
    {before : Native} (point : At image before base start) (controls : Controls before)
    (input : Input layout arena table mapping node destination remaining before) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after bytes, (X86FuelPrefix.fetches (13 * remaining + 2)).run before = .ok () after ∧
      X86StateFrame.Frame clobbers bytes before after ∧ Within layout.edges destination (destination + remaining) bytes ∧
      Stored layout destination remaining newer fits width after ∧ Nonempty (At image after base finished) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  induction remaining generalizing before with
  | zero =>
    obtain ⟨after, run, regs, endpoint⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
      extra vector point .lessUnsigned 12 2 placed.visit.more 0 0 input.words.zero input.words.count
    exact ⟨after, ∅, run, (X86StateFrame.registerOnly regs).mono (by decide) (by simp),
      by simp [Within], fun i => Fin.elim0 i, endpoint⟩
  | succ n ih =>
    obtain ⟨a, visited, visitFrame, _, mapped, index, ⟨atCopy⟩⟩ := NativeRemapChildren.fetched_visit other extra vector
      placed.visit children newer segment translated n bound point controls input.words
    let value := newer[n]'(by omega)
    have available : lookup a 14 = some value := mapped.trans (Array.getElem?_eq_getElem (by omega : n < newer.size))
    obtain ⟨b, copied, copyFrame, register, ⟨atStore⟩⟩ := X86PlacedRegisterMove.executes (handlers other extra)
      vector atCopy (by omega) 14 0 value available placed.copy
    have beforeStore := visitFrame.trans (X86StateFrame.registerOnly copyFrame)
    let slot : Fin edgeCapacity := ⟨destination + n, by omega⟩
    have coord := coordinate_word segment n (by omega)
    have existsSlot : destination + (BitVec.ofNat 64 n).toNat < edgeCapacity := by rw [coord]; exact slot.isLt
    have sameSlot : (⟨destination + (BitVec.ofNat 64 n).toNat, existsSlot⟩ : Fin edgeCapacity) = slot :=
      Fin.ext (congrArg (destination + ·) coord)
    have placedStore : CodeApart image base
        (footprint ((layout.edges.wordCell ⟨destination + (BitVec.ofNat 64 n).toNat, existsSlot⟩).cell 0).address) := by
      rw [sameSlot]
      exact geometry.code slot
    obtain ⟨c, stored, storeFrame, written, ⟨atJump⟩⟩ := NativeIndexedWord.fetched_store other extra vector
      (show At image b base (start + 46) from atStore) (controls.transport beforeStore (by decide)) (by omega)
      destinationBase NativeChildMarkLoop.edgeIndex layout.edges destination (BitVec.ofNat 64 n) value existsSlot
      ((beforeStore.lookup 3 (by decide)).trans input.output) ((copyFrame.lookup 2 (by decide)).trans index)
      register placed.store placedStore
    rw [sameSlot] at storeFrame written
    obtain ⟨d, jumped, jumpFrame, ⟨again⟩⟩ := X86PlacedScalar.jump (X86PlacedFrameAddress.nativeBase other)
      extra vector (show At image c base (start + 57) from atJump) placed.again
    let just := footprint ((layout.edges.wordCell slot).cell 0).address
    have frame : X86StateFrame.Frame clobbers just before d :=
      ((beforeStore.trans storeFrame).trans (X86StateFrame.registerOnly jumpFrame)).mono (by decide) (by simp [just])
    have nodeReady : NativeTermArena.Ready layout arena d :=
      ⟨input.words.source.nodesFit, input.words.source.edgesFit,
        fun i j => (input.words.source.node i j).preserved frame (geometry.nodes _ j slot),
        fun i => (input.words.source.child i).preserved frame (layout.edges.wordCells_disjoint (by
          intro eq
          have equal := congrArg Fin.val eq
          change i.val = destination + n at equal
          have inside := i.isLt
          omega))⟩
    have earlier := ((X86StateFrame.registerOnly copyFrame).trans storeFrame).trans (X86StateFrame.registerOnly jumpFrame)
    have next : Input layout arena table mapping node destination n d :=
      ⟨⟨nodeReady, input.words.mapped.kept frame (fun i => geometry.remap i slot),
        (frame.lookup 6 (by decide)).trans input.words.span, (frame.lookup 7 (by decide)).trans input.words.tableBase,
        (frame.lookup 1 (by decide)).trans input.words.parent, (earlier.lookup 2 (by decide)).trans index,
        (frame.lookup 12 (by decide)).trans input.words.zero, (frame.lookup 13 (by decide)).trans input.words.one⟩,
        (frame.lookup 3 (by decide)).trans input.output⟩
    obtain ⟨after, bytes, ran, laterFrame, confined, values, endpoint⟩ :=
      ih (by omega) (by omega) (by omega) again (controls.transport frame NativeRemapChildren.clobbers_data) next
    have total : X86StateFrame.Frame clobbers (just ∪ bytes) before after :=
      (frame.trans laterFrame).mono (by simp) (Finset.Subset.refl _)
    have touched : Within layout.edges destination (destination + (n + 1)) (just ∪ bytes) := by
      intro key modified
      rcases Finset.mem_union.mp modified with first | later
      · exact ⟨slot, by change destination ≤ destination + n; omega,
          by change destination + n < destination + (n + 1); omega, first⟩
      · obtain ⟨i, lower, upper, changed⟩ := confined key later
        exact ⟨i, lower, by omega, changed⟩
    have finishedWords : Stored layout destination (n + 1) newer fits width after := by
      intro i
      by_cases last : i.val = n
      · have same : (⟨destination + i.val, by have present := i.isLt; omega⟩ : Fin edgeCapacity) = slot :=
          Fin.ext (congrArg (destination + ·) last)
        rw [same]
        have bytesPreserved : Disjoint just bytes :=
          confined.apart_interval just (fun j _ prior => layout.edges.wordCells_disjoint (fun equal => by
            have same := congrArg Fin.val equal
            change destination + n = j.val at same
            omega))
        have exactWord := (written.preserved (X86StateFrame.registerOnly jumpFrame) (by simp)).preserved laterFrame bytesPreserved
        simpa only [last, value] using exactWord
      · exact values ⟨i.val, by have present := i.isLt; omega⟩
    have first := X86FuelPrefix.fetches_then 9 1 before a b visited copied
    have middle := X86FuelPrefix.fetches_then 10 2 before b c first stored
    have one := X86FuelPrefix.fetches_then 12 1 before c d middle jumped
    have all := X86FuelPrefix.fetches_then 13 (13 * n + 2) before d after one ran
    rw [show 13 + (13 * n + 2) = 13 * (n + 1) + 2 by omega] at all
    exact ⟨after, just ∪ bytes, all, total, touched, finishedWords, endpoint⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeRemapCopy
