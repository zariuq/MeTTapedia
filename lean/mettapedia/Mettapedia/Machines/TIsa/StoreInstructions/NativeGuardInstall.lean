import Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardRegion
import Mettapedia.Machines.TIsa.StoreInstructions.NativeRootSlices

/-!
# Attaching a guard to an already normalized root vector

The guard takes one selected pattern and a borrowed window
of occurrence handles. Attaching writes the five descriptor
words the guard needs. It copies neither term records nor
occurrence slots, including in the empty-window case.
-/

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardInstall

open _root_.X86Registers X86Execution X86RegisterRefinement
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads CodeApart footprint)
open X86PlacedScalar (Code registerCode)
open NativeArenaGeometry (Region)
open NativeBindingSelection (Separated)
open NativeLiveRootEntry (Descriptor Held)
open NativeBindingRootMemory (Covered)
open NativeGuardWorkspace (Frame)
open NativeRootSlices (View)
open NativeSubstLeaf (MapReady)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

def guardFrame (d : Descriptor) : Frame :=
  d.region.slice 0 16 (by decide) (by decide) (by decide)

theorem guard_pointer (d : Descriptor) : (guardFrame d).pointer = d.pointer := BitVec.add_zero _

theorem guard_field (d : Descriptor) (slot : Fin 16) :
    ((guardFrame d).cell slot).address = (d.cell ⟨slot.val, slot.isLt.trans (by decide)⟩).address := by
  rw [guardFrame, Region.slice_address, Nat.zero_add]
  rfl

theorem root_solver (d : Descriptor) : d.solver = (guardFrame d).solver := by
  have pointer := (NativeLiveRootEntry.Descriptor.solver_pointer d).trans
    (((guardFrame d).solver_pointer.trans (guard_pointer d)).symm)
  cases root : d.solver
  cases base : (guardFrame d).solver
  have same := pointer
  rw [root, base] at same
  cases same
  rfl

def rootsBase : X86IndexedAddress.Base := ⟨2, by decide⟩
def indexReg : X86PreparedLea.Index := ⟨1, by decide⟩
def stackCode : List ℕ := registerCode 0x89 4 6
def rootCode : List ℕ := X86DataLoad.code true 2 6 128
def patternCode : List ℕ := NativeIndexedWord.loadCode rootsBase indexReg
def locationCode : List ℕ := X86IndexedAddress.addressCode 0 indexReg 3 rootsBase
def encoding : X86PlacedMemory.Encoding := .direct 6 (by decide) (by decide)
def patternStore : List ℕ := encoding.bytes 0 88
def windowStore : List ℕ := encoding.bytes 0 96

private def rootWire : NativeWords.Wiring := ⟨6, by decide, by decide, encoding, 2, by decide, by decide⟩
private def indexWire : NativeWords.Wiring := ⟨6, by decide, by decide, encoding, 1, by decide, by decide⟩
private def copyWire : NativeWords.Wiring := ⟨6, by decide, by decide, encoding, 0, by decide, by decide⟩

def copies (frame : Frame) (graph : PackedTerms.Arena) (count : ℕ) :
    List (NativeWords.Move frame.pointer frame.pointer) :=
  [⟨NativeAgendaRead.fieldSource frame 3, BitVec.ofNat 64 graph.nodes.size, 64, frame.cell 8⟩,
   ⟨NativeAgendaRead.fieldSource frame 4, BitVec.ofNat 64 graph.children.size, 72, frame.cell 9⟩,
   ⟨.literal (BitVec.ofNat 64 count), BitVec.ofNat 64 count, 104, frame.cell 13⟩]

def copyBytes (count : ℕ) : List ℕ :=
  X86DataLoad.code true 0 6 24 ++ (encoding.bytes 0 64 ++
    (X86DataLoad.code true 0 6 32 ++ (encoding.bytes 0 72 ++
      (X86PlacedWideImmediate.bytes 0 (BitVec.ofNat 64 count) ++ encoding.bytes 0 104))))

theorem copy_code (frame : Frame) (graph : PackedTerms.Arena) (count : ℕ) :
    NativeWords.emitted copyWire (copies frame graph count) = copyBytes count := by rfl

theorem copy_size (frame : Frame) (graph : PackedTerms.Arena) (count : ℕ) :
    NativeWords.size copyWire (copies frame graph count) = 45 := rfl

def rootDestination (right : Bool) : Fin 16 := if right then 2 else 0

def rootLoad (right : Bool) : List ℕ :=
  NativeIndexedWord.loadToCode rootsBase indexReg (rootDestination right)

def emitRoot (right : Bool) (pattern : ℕ) : List ℕ :=
  stackCode ++ (rootCode ++ (X86PlacedWideImmediate.bytes 1 (BitVec.ofNat 64 pattern) ++
    rootLoad right))

theorem emitRoot_size (right : Bool) (pattern : ℕ) : (emitRoot right pattern).length = 31 := by
  cases right <;> rfl

def emitNeedle (pattern : ℕ) : List ℕ := emitRoot false pattern ++ patternStore

theorem emitNeedle_size (pattern : ℕ) : (emitNeedle pattern).length = 38 := rfl

def emit (pattern offset count : ℕ) : List ℕ :=
  emitNeedle pattern ++ (X86PlacedWideImmediate.bytes 1 (BitVec.ofNat 64 offset) ++
    (locationCode ++ (windowStore ++ copyBytes count)))

theorem emit_size (pattern offset count : ℕ) : (emit pattern offset count).length = 104 := rfl

structure RootPlaced (image : NativeImage.View) (right : Bool) (start pattern : ℕ) : Prop where
  extent : start + 31 ≤ image.size
  stack : Code image start stackCode
  roots : Code image (start + 3) rootCode
  index : Code image (start + 10) (X86PlacedWideImmediate.bytes 1 (BitVec.ofNat 64 pattern))
  load : Code image (start + 20) (rootLoad right)

theorem root_placed (image : NativeImage.View) (right : Bool) (start pattern : ℕ)
    (extent : start + 31 ≤ image.size) (code : Code image start (emitRoot right pattern)) :
    RootPlaced image right start pattern := by
  obtain ⟨stack, rest⟩ := NativeWords.code_append (show Code image start (stackCode ++ _) from code)
  obtain ⟨roots, rest⟩ := NativeWords.code_append rest
  obtain ⟨index, load⟩ := NativeWords.code_append rest
  exact ⟨extent, stack, roots, index, load⟩

structure NeedlePlaced (image : NativeImage.View) (start pattern : ℕ) : Prop where
  extent : start + 38 ≤ image.size
  root : RootPlaced image false start pattern
  savePattern : Code image (start + 31) patternStore

theorem needle_placed (image : NativeImage.View) (start pattern : ℕ)
    (extent : start + 38 ≤ image.size) (code : Code image start (emitNeedle pattern)) :
    NeedlePlaced image start pattern := by
  obtain ⟨read, save⟩ := NativeWords.code_append (show Code image start (emitRoot false pattern ++ _) from code)
  rw [emitRoot_size] at save
  exact ⟨extent, root_placed image false start pattern (by omega) read, save⟩

structure Placed (image : NativeImage.View) (start pattern offset count : ℕ) : Prop where
  extent : start + 104 ≤ image.size
  pattern : NeedlePlaced image start pattern
  offsetWord : Code image (start + 38) (X86PlacedWideImmediate.bytes 1 (BitVec.ofNat 64 offset))
  address : Code image (start + 48) locationCode
  savePointer : Code image (start + 52) windowStore
  copies : Code image (start + 59) (copyBytes count)

theorem placed_of_emitted (image : NativeImage.View) (start pattern offset count : ℕ)
    (extent : start + 104 ≤ image.size) (code : Code image start (emit pattern offset count)) : Placed image start pattern offset count := by
  obtain ⟨needle, rest⟩ := NativeWords.code_append (show Code image start (emitNeedle pattern ++ _) from code)
  rw [emitNeedle_size] at rest
  obtain ⟨offsetWord, rest⟩ := NativeWords.code_append rest
  obtain ⟨address, rest⟩ := NativeWords.code_append rest
  obtain ⟨savePointer, copies⟩ := NativeWords.code_append rest
  exact ⟨extent, needle_placed image _ _ (by omega) needle, offsetWord, address, savePointer, copies⟩

def slotBytes (frame : Frame) (i : Fin 16) : Finset ℕ := footprint (frame.cell i).address

def descriptorBytes (frame : Frame) : Finset ℕ :=
  (slotBytes frame 11 ∪ slotBytes frame 12) ∪ (slotBytes frame 8 ∪ (slotBytes frame 9 ∪ slotBytes frame 13))

theorem slots_cover (frame : Frame) (i : Fin 16) : Covered frame.region (slotBytes frame i) := by
  unfold slotBytes
  rw [← frame.as_slice]
  exact Covered.cell frame.region 0 16 (by decide) (by decide) (by decide) i

theorem descriptor_covered (frame : Frame) : Covered frame.region (descriptorBytes frame) :=
  ((slots_cover frame 11).union (slots_cover frame 12)).union
    ((slots_cover frame 8).union ((slots_cover frame 9).union (slots_cover frame 13)))

theorem other_slot (frame : Frame) (i : Fin 16) (diff : i ≠ 11 ∧ i ≠ 12 ∧ i ≠ 8 ∧ i ≠ 9 ∧ i ≠ 13) :
    Disjoint (slotBytes frame i) (descriptorBytes frame) :=
  Finset.disjoint_union_right.mpr ⟨Finset.disjoint_union_right.mpr ⟨frame.separate_words diff.1, frame.separate_words diff.2.1⟩,
    Finset.disjoint_union_right.mpr ⟨frame.separate_words diff.2.2.1,
      Finset.disjoint_union_right.mpr ⟨frame.separate_words diff.2.2.2.1, frame.separate_words diff.2.2.2.2⟩⟩⟩

theorem root_metadata_apart (d : Descriptor) (frame : Frame) (same : frame = guardFrame d)
    (slot : Fin 18) (separate : 16 ≤ slot.val) :
    Disjoint (footprint (d.cell slot).address) (descriptorBytes frame) := by
  have field (i : Fin 16) : Disjoint (footprint (d.cell slot).address) (slotBytes frame i) := by
    rw [slotBytes, same, guard_field]
    apply d.separate_words
    intro equal
    have clash := congrArg Fin.val equal
    have inside := i.isLt
    change slot.val = i.val at clash
    omega
  exact Finset.disjoint_union_right.mpr ⟨Finset.disjoint_union_right.mpr ⟨field 11, field 12⟩,
    Finset.disjoint_union_right.mpr ⟨field 8, Finset.disjoint_union_right.mpr ⟨field 9, field 13⟩⟩⟩

abbrev clobbers : Finset Register := {.rax, .rcx, .rdx, .rsi, .r10, .rip}
theorem clobbers_data : clobbers ⊆ dataRegisters := by decide
noncomputable abbrev handlers := X86IndexedAddress.handlers

variable {rc : ℕ} {rootRegion : Region rc} {all : Array Word} {d : Descriptor} {frame : Frame}
variable {image : NativeImage.View} {base : BitVec 48}

theorem fetched_root (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {start : ℕ} {before : Native} (right : Bool) (coordinate : Fin all.size)
    (code : RootPlaced image right start coordinate.val)
    (point : At image before base start) (controls : Controls before)
    (sameFrame : frame = guardFrame d) (held : Held d rootRegion all before) (stack : lookup before 4 = some frame.pointer) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 5).run before = .ok () after ∧ X86StateFrame.Frame clobbers ∅ before after ∧
      lookup after 6 = some frame.pointer ∧ lookup after (rootDestination right) = some all[coordinate] ∧
      (right = false → lookup after 2 = some (rootRegion.atWord 0)) ∧ Nonempty (At image after base (start + 31)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := code.extent
  let index : Word := BitVec.ofNat 64 coordinate.val
  have indexNat : index.toNat = coordinate.val :=
    NativeSubstitutionReserve.word_of_region rootRegion _ (coordinate.isLt.le.trans held.words.fits)
  obtain ⟨a, opened, stackFrame, stack, ⟨atBase⟩⟩ := X86PlacedRegisterMove.executes
    (handlers other extra) vector point (by omega) 4 6 frame.pointer stack code.stack
  have openedFrame := X86StateFrame.registerOnly stackFrame
  have samePointer : frame.pointer = d.pointer := by rw [sameFrame, guard_pointer]
  obtain ⟨b, loaded, rootFrame, baseWord, ⟨atIndex⟩⟩ := (NativeAgendaRead.fieldSource d 16).fetch
    (handlers other extra) vector rootWire (rootRegion.atWord 0) atBase
    (controls.transport openedFrame (by decide)) (samePointer ▸ stack) (held.descriptor.pointer.preserved openedFrame (by simp))
    (show start + 10 ≤ image.size by omega) code.roots
  have linked : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
  rw [linked] at loaded
  have openedRoots := openedFrame.trans rootFrame
  obtain ⟨c, indexed, indexFrame, ordinal, ⟨atNeedle⟩⟩ := (NativeWords.Source.literal (oldBase := frame.pointer) index).fetch
    (handlers other extra) vector indexWire index (show At image b base (start + 10) from atIndex)
    (controls.transport openedRoots (by decide)) ((rootFrame.lookup 6 (by decide)).trans stack) rfl
    (show start + 20 ≤ image.size by omega) code.index
  rw [linked] at indexed
  have ordinalFrame := openedRoots.trans indexFrame
  have fits : 0 + index.toNat < rc := by rw [Nat.zero_add, indexNat]; exact coordinate.isLt.trans_le held.words.fits
  have sameSlot : (⟨0 + index.toNat, fits⟩ : Fin rc) = ⟨coordinate.val, coordinate.isLt.trans_le held.words.fits⟩ :=
    Fin.ext ((Nat.zero_add _).trans indexNat)
  have patternRead := (held.words.read coordinate).preserved ordinalFrame (by simp)
  obtain ⟨e, inspected, inspectFrame, word, endpoint⟩ := NativeIndexedWord.fetched_load_to other extra vector
    (show At image c base (start + 20) from atNeedle) (controls.transport ordinalFrame (by decide)) (by omega)
    rootsBase indexReg (rootDestination right) (by cases right <;> decide) rootRegion 0 index all[coordinate] fits
    ((indexFrame.lookup 2 (by decide)).trans baseWord) ordinal (by rw [sameSlot]; exact patternRead) code.load
  have readable := (indexFrame.trans inspectFrame).lookup 6 (by cases right <;> decide)
  have registers : X86StateFrame.Frame clobbers ∅ before e :=
    (ordinalFrame.trans inspectFrame).mono (by cases right <;> decide) (by simp)
  have first := X86FuelPrefix.fetches_then 2 1 before b c
    (X86FuelPrefix.fetches_then 1 1 before a b opened loaded) indexed
  exact ⟨e, X86FuelPrefix.fetches_then 3 2 before c e first inspected, registers,
    (readable.trans ((rootFrame.lookup 6 (by decide)).trans stack)), word,
    fun selected => ((inspectFrame.lookup 2 (by rw [selected]; decide)).trans
      ((indexFrame.lookup 2 (by decide)).trans baseWord)), endpoint⟩

theorem fetched_needle (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {start : ℕ} {before : Native} (view : View all) (code : NeedlePlaced image start view.pattern.val)
    (point : At image before base start) (controls : Controls before)
    (sameFrame : frame = guardFrame d) (held : Held d rootRegion all before) (stack : lookup before 4 = some frame.pointer)
    (safe : CodeApart image base (slotBytes frame 11)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 6).run before = .ok () after ∧
      X86StateFrame.Frame clobbers (slotBytes frame 11) before after ∧
      lookup after 6 = some frame.pointer ∧ lookup after 2 = some (rootRegion.atWord 0) ∧
      Reads after (frame.cell 11).address view.needle ∧ Nonempty (At image after base (start + 38)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨e, read, readFrame, frameBase, word, rootBase, ⟨atPattern⟩⟩ :=
    fetched_root other extra vector false view.pattern code.root point controls sameFrame held stack
  obtain ⟨f, wrotePattern, patternFrame, patternRead, ⟨atOffset⟩⟩ := X86PlacedMemory.stores (handlers other extra) vector
    atPattern (controls.transport readFrame clobbers_data)
    encoding 0 88 frame.pointer view.needle (frame.cell 11)
    frameBase word code.extent code.savePattern safe
  have patternKept : X86StateFrame.Frame clobbers (slotBytes frame 11) before f :=
    (readFrame.trans patternFrame).mono (by decide) (by simp [slotBytes])
  exact ⟨f, X86FuelPrefix.fetches_then 5 1 before e f read wrotePattern, patternKept,
    (patternFrame.lookup 6 (by decide)).trans frameBase, (patternFrame.lookup 2 (by decide)).trans (rootBase rfl),
    patternRead, ⟨atOffset⟩⟩

private theorem prefix_fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {start : ℕ} {before : Native} (view : View all) (code : Placed image start view.pattern.val view.offset view.count)
    (point : At image before base start) (controls : Controls before)
    (sameFrame : frame = guardFrame d) (held : Held d rootRegion all before) (stack : lookup before 4 = some frame.pointer)
    (safe : CodeApart image base (descriptorBytes frame)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 9).run before = .ok () after ∧
      X86StateFrame.Frame clobbers (slotBytes frame 11 ∪ slotBytes frame 12) before after ∧
      lookup after 6 = some frame.pointer ∧
      Reads after (frame.cell 11).address view.needle ∧
      Reads after (frame.cell 12).address ((view.region rootRegion held.words.fits).atWord 0) ∧
      Nonempty (At image after base (start + 59)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := code.extent
  have available : view.offset ≤ rc := (Nat.le_add_right _ _).trans (view.fits.trans held.words.fits)
  let offset : Word := BitVec.ofNat 64 view.offset
  have offsetNat : offset.toNat = view.offset := NativeSubstitutionReserve.word_of_region rootRegion _ available
  have address : rootRegion.atWord 0 + offset * 8 = (view.region rootRegion held.words.fits).atWord 0 := by
    rw [← NativeArenaGeometry.word_scale8, offsetNat]
    simp [Region.atWord, View.region, NativeRootSlices.window]
  obtain ⟨f, throughPlace, patternKept, frameBase, baseWord, patternRead, ⟨atOffset⟩⟩ :=
    fetched_needle other extra vector view code.pattern point controls sameFrame held stack
      (safe.mono (Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left))
  obtain ⟨g, loadedOffset, offsetFrame, position, ⟨atAddress⟩⟩ := (NativeWords.Source.literal (oldBase := frame.pointer) offset).fetch
    (handlers other extra) vector indexWire offset (show At image f base (start + 38) from atOffset)
    (controls.transport patternKept clobbers_data) frameBase rfl
    (show start + 48 ≤ image.size by omega) code.offsetWord
  have linked : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
  rw [linked] at loadedOffset
  have throughOffset := patternKept.trans offsetFrame
  obtain ⟨h, addressed, addressFrame, pointer, ⟨atWindow⟩⟩ := X86IndexedAddress.forms_address other extra vector
    (show At image g base (start + 48) from atAddress) (by omega) 0 indexReg 3 rootsBase code.address
    (rootRegion.atWord 0) offset ((offsetFrame.lookup 2 (by decide)).trans baseWord)
    position
  have throughAddress := throughOffset.trans (X86StateFrame.registerOnly addressFrame)
  have keepRsi := offsetFrame.trans (X86StateFrame.registerOnly addressFrame)
  have framePointer : lookup h 6 = some frame.pointer := (keepRsi.lookup 6 (by decide)).trans frameBase
  obtain ⟨after, storedWindow, windowFrame, readWindow, done⟩ := X86PlacedMemory.stores (handlers other extra) vector
    (show At image h base (start + 52) from atWindow) (controls.transport throughAddress (by decide)) encoding 0 96
    frame.pointer (view.region rootRegion held.words.fits |>.atWord 0) (frame.cell 12)
    framePointer
    (by simpa only [show (BitVec.ofNat 64 (2 ^ (3 : Fin 4).val)) = 8 from rfl, address] using pointer)
    (show start + 59 ≤ image.size by omega) code.savePointer
    (safe.mono (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left))
  have all : X86StateFrame.Frame clobbers (slotBytes frame 11 ∪ slotBytes frame 12) before after :=
    (throughAddress.trans windowFrame).mono (by decide) (by simp [slotBytes])
  have pattern := (patternRead.preserved (offsetFrame.trans (X86StateFrame.registerOnly addressFrame)) (by simp)).preserved
    windowFrame (frame.separate_words (by decide : (11 : Fin 16) ≠ 12))
  have throughWindow := X86FuelPrefix.fetches_then 8 1 before h after
    (X86FuelPrefix.fetches_then 7 1 before g h
      (X86FuelPrefix.fetches_then 6 1 before f g throughPlace loadedOffset) addressed) storedWindow
  exact ⟨after, throughWindow, all, (windowFrame.lookup 6 (by decide)).trans framePointer, pattern, readWindow, done⟩

variable {nc ec mc ac tc : ℕ}
variable {term : NativeTermArena.Layout nc ec} {map : Region mc}
variable {agenda : NativeAgendaRecords.Layout ac} {trail : NativeAgendaRecords.Layout tc}

structure Input (term : NativeTermArena.Layout nc ec) (map : Region mc) (frame : Frame)
    (agenda : NativeAgendaRecords.Layout ac) (trail : NativeAgendaRecords.Layout tc) (d : Descriptor) (rootRegion : Region rc)
    (graph : PackedTerms.Arena) (all : Array Word) (native : Native) : Prop where
  sameFrame : frame = guardFrame d
  graphReady : NativeTermArena.Ready term graph native
  roots : Held d rootRegion all native
  staging : NativeSubstitutionFrame.Ready term map d.solver.substitution graph native
  aux : NativeBindingStep.Aux term d.solver agenda trail native
  savedAgenda : Reads native (frame.cell 10).address agenda.words.pointer
  zero : lookup native 12 = some 0
  one : lookup native 13 = some 1

private theorem copy_writes (frame : Frame) (graph : PackedTerms.Arena) (count : ℕ) :
    NativeWords.written (copies frame graph count) = slotBytes frame 8 ∪ (slotBytes frame 9 ∪ slotBytes frame 13) := by
  simp only [NativeWords.written, copies, slotBytes, Finset.union_empty]

private theorem copies_separate (frame : Frame) (graph : PackedTerms.Arena) (count : ℕ) :
    NativeWords.Separate (copies frame graph count) := by
  unfold NativeWords.Separate copies
  repeat' first | apply List.Pairwise.nil | apply List.Pairwise.cons
  all_goals
    intro m selected
    simp only [List.mem_cons, List.not_mem_nil, or_false] at selected
    try
      rcases selected with rfl | rfl <;> exact frame.separate_words (by decide)

private theorem copies_source (frame : Frame) (graph : PackedTerms.Arena) (count : ℕ)
    (m : NativeWords.Move frame.pointer frame.pointer) (member : m ∈ copies frame graph count) :
    Disjoint m.source.uses (NativeWords.written (copies frame graph count)) := by
  rw [copy_writes]
  simp only [copies, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact (other_slot frame 3 (by decide)).mono_right Finset.subset_union_right
  · exact (other_slot frame 4 (by decide)).mono_right Finset.subset_union_right
  · simp [NativeWords.Source.uses]

private theorem static_source {before after : Native} {regs : Finset Register}
    {graph : PackedTerms.Arena} (stage : NativeSubstitutionFrame.Ready term map frame.solver.substitution graph before)
    (run : X86StateFrame.Frame regs (descriptorBytes frame) before after) (i : Fin 7) :
    Reads after (frame.cell ⟨i.val, i.isLt.trans (by decide)⟩).address (NativeSubstitutionFrame.values term map graph i) := by
  have hold := stage.word i
  rw [frame.staged_cell] at hold
  have outside (slot : Fin 16) (lower : 7 ≤ slot.val) : (⟨i.val, i.isLt.trans (by decide)⟩ : Fin 16) ≠ slot := by
    intro same
    exact (Nat.not_lt_of_ge lower) ((congrArg Fin.val same) ▸ i.isLt)
  exact hold.preserved run (other_slot frame _ ⟨outside 11 (by decide), outside 12 (by decide),
    outside 8 (by decide), outside 9 (by decide), outside 13 (by decide)⟩)

/-- No copied array is introduced by attaching a view of the
resolved graph. Only the five descriptor cells are written. -/
theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {start : ℕ} {before : Native} (view : View all) (code : Placed image start view.pattern.val view.offset view.count)
    (point : At image before base start) (controls : Controls before) (graph : PackedTerms.Arena)
    (input : Input term map frame agenda trail d rootRegion graph all before)
    (guardSpace : NativeGuardState.Geometry term map frame agenda trail (view.region rootRegion input.roots.words.fits) image base)
    (rootApart : Separated rootRegion frame.region) (safe : CodeApart image base (descriptorBytes frame)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 15).run before = .ok () after ∧
      X86StateFrame.Frame clobbers (descriptorBytes frame) before after ∧
      NativeGuardState.Stable term map frame agenda trail (view.region rootRegion input.roots.words.fits)
        graph view.needle view.occurrences after ∧ Held d rootRegion all after ∧
      Nonempty (At image after base (start + 104)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have same : d.solver = frame.solver := by rw [input.sameFrame]; exact root_solver d
  have stage : NativeSubstitutionFrame.Ready term map frame.solver.substitution graph before := same ▸ input.staging
  have stack : lookup before 4 = some frame.pointer :=
    ((NativeTrailReserve.Descriptor.substitution_pointer frame.solver).trans frame.solver_pointer) ▸ stage.pointer
  obtain ⟨a, prefixRun, prefixFrame, address, needle, directory, ⟨atCopies⟩⟩ :=
    prefix_fetched other extra vector view code point controls input.sameFrame input.roots stack safe
  let moves := copies frame graph view.count
  have limit := code.extent
  have coded : NativeWords.Checked copyWire image (start + 59) moves := by
    apply NativeWords.checked_of_emitted
    · rw [show moves = copies frame graph view.count from rfl, copy_code]
      exact limit
    · rw [show moves = copies frame graph view.count from rfl, copy_code]
      exact code.copies
  have preserved (i : Fin 7) :=
    static_source stage (prefixFrame.mono (Finset.Subset.refl _) (show _ ⊆ descriptorBytes frame from Finset.subset_union_left)) i
  have values : ∀ m ∈ moves, NativeWords.Source.Ready a m.source m.value := by
    intro m member
    simp only [moves, copies, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact preserved 3
    · exact preserved 4
    · rfl
  have safeCopies : CodeApart image base (NativeWords.written moves) := by
    rw [show moves = copies frame graph view.count from rfl, copy_writes]
    exact safe.mono Finset.subset_union_right
  obtain ⟨after, installed, copiesFrame, stored, endpoint⟩ := NativeWords.fetch_all (handlers other extra) vector copyWire moves atCopies
    (controls.transport prefixFrame clobbers_data) coded address address values
    (copies_source frame graph view.count) (copies_separate frame graph view.count) safeCopies
  have linked : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
  rw [linked] at installed
  have whole : X86StateFrame.Frame clobbers (descriptorBytes frame) before after :=
    (prefixFrame.trans copiesFrame).mono (by decide)
      (by simpa only [moves, copy_writes, descriptorBytes] using Finset.Subset.refl (descriptorBytes frame))
  have savedNodes : Reads after (frame.cell 8).address (BitVec.ofNat 64 graph.nodes.size) :=
    stored (moves[0]'(show 0 < 3 by decide)) (by simp [moves, copies])
  have savedEdges : Reads after (frame.cell 9).address (BitVec.ofNat 64 graph.children.size) :=
    stored (moves[1]'(show 1 < 3 by decide)) (by simp [moves, copies])
  have size : Reads after (frame.cell 13).address (BitVec.ofNat 64 view.occurrences.size) := by
    rw [view.size]
    exact stored (moves[2]'(show 2 < 3 by decide)) (by simp [moves, copies])
  have untouched (i : Fin 16) (different : i ≠ 8 ∧ i ≠ 9 ∧ i ≠ 13) :
      Disjoint (slotBytes frame i) (NativeWords.written moves) := by
    rw [show moves = copies frame graph view.count from rfl, copy_writes]
    exact Finset.disjoint_union_right.mpr ⟨frame.separate_words different.1,
      Finset.disjoint_union_right.mpr ⟨frame.separate_words different.2.1, frame.separate_words different.2.2⟩⟩
  have covered := descriptor_covered frame
  have geometry := guardSpace.workspace
  have validTerms := input.graphReady.kept whole
    (fun i j => Covered.separate geometry.frameNode.symm (Covered.node term i j) covered)
    (fun i => Covered.separate geometry.frameEdge.symm (Covered.edge term i) covered)
  have rootWords := input.roots.words.kept whole (fun i => Covered.separate rootApart (Covered.word rootRegion i) covered)
  have static (i : Fin 11) (notNodes : i ≠ 3) (notEdges : i ≠ 4) :
      Reads after (frame.cell ⟨i.val, i.isLt.trans (by decide)⟩).address
        (NativeGuardWorkspace.values term map agenda trail graph i) := by
    fin_cases i
    · exact static_source stage whole 0
    · exact static_source stage whole 1
    · exact static_source stage whole 2
    · exact (notNodes rfl).elim
    · exact (notEdges rfl).elim
    · exact static_source stage whole 5
    · exact static_source stage whole 6
    · have read := input.aux.trailPtr
      rw [same, frame.solver_cell] at read
      exact read.preserved whole (other_slot frame 7 (by decide))
    · exact savedNodes
    · exact savedEdges
    · exact input.savedAgenda.preserved whole (other_slot frame 10 (by decide))
  have scratch : NativeGuardWorkspace.Ready term map frame agenda trail graph after :=
    ⟨validTerms, (whole.lookup 4 (by decide)).trans stack, static,
      input.aux.pool.preserved whole (Covered.separate geometry.frameAgenda.symm (Covered.metadata agenda 1) covered),
      input.aux.agendaLimit.preserved whole (Covered.separate geometry.frameAgenda.symm (Covered.metadata agenda 2) covered),
      input.aux.trailLimit.preserved whole (Covered.separate geometry.frameTrail.symm (Covered.metadata trail 2) covered),
      (whole.lookup 12 (by decide)).trans input.zero, (whole.lookup 13 (by decide)).trans input.one⟩
  have final : NativeGuardOperands.Directory (view.region rootRegion input.roots.words.fits) frame view.needle view.occurrences after :=
    ⟨needle.preserved copiesFrame (untouched 11 (by decide)), directory.preserved copiesFrame (untouched 12 (by decide)), size,
      view.resident rootRegion rootWords⟩
  have original : Held d rootRegion all after :=
    ⟨input.roots.descriptor.kept whole (root_metadata_apart d frame input.sameFrame 16 (by decide))
      (root_metadata_apart d frame input.sameFrame 17 (by decide)), rootWords⟩
  exact ⟨after, X86FuelPrefix.fetches_then 9 6 before a after prefixRun installed, whole, ⟨scratch, final⟩, original,
    by rw [show moves = copies frame graph view.count from rfl, copy_size] at endpoint; exact endpoint⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeGuardInstall
