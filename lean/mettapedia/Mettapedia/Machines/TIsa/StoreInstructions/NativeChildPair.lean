import Mettapedia.Machines.TIsa.StoreInstructions.NativeTermArena

/-!
# Reading corresponding packed children at a runtime index

After the spans have been prepared, the loop checks the unscaled
index, forms one address into each span, and loads the actual
handles. The operands remain ordered, even when the spans overlap
or when several positions hold the same handle.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeChildPair

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls)
open X86PlacedScalar (Code CompareBranch)
open X86IndexedAddress (Base addressCode)
open X86PreparedLea (Index)
open PackedTerms (Arena Node)
open NativeWords (Wiring)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

structure Spans (arena : Arena) (left right : Node) where
  leftWords : Array Word
  rightWords : Array Word
  left : PackedTerms.segment arena.children left = some leftWords
  right : PackedTerms.segment arena.children right = some rightWords
  width : leftWords.size = rightWords.size

def Spans.pairs {arena : Arena} {left right : Node} (spans : Spans arena left right) : List (Word × Word) :=
  spans.leftWords.toList.zip spans.rightWords.toList

theorem Spans.length {arena : Arena} {left right : Node} (spans : Spans arena left right) :
    spans.pairs.length = spans.leftWords.size := by
  simp only [Spans.pairs, List.length_zip, Array.length_toList, spans.width, min_self]

theorem Spans.get {arena : Arena} {left right : Node} (spans : Spans arena left right)
    (index : ℕ) (inside : index < spans.leftWords.size) :
    spans.pairs[index]? = some (spans.leftWords[index], spans.rightWords[index]'(spans.width ▸ inside)) := by
  have zipped : index < spans.pairs.length := spans.length.symm ▸ inside
  rw [List.getElem?_eq_getElem zipped]
  simp only [Spans.pairs, List.getElem_zip, Array.getElem_toList]

def spanPointer {nodeCapacity edgeCapacity : ℕ} (layout : NativeTermArena.Layout nodeCapacity edgeCapacity)
    (node : Node) : Word :=
  layout.edges.pointer + node.childrenAt * 8

inductive Side | left | right

def Side.base : Side → Base
  | .left => ⟨6, by decide⟩
  | .right => ⟨7, by decide⟩

def Side.destination : Side → Fin 16
  | .left => 9
  | .right => 10

def Side.wire (side : Side) : Wiring :=
  ⟨0, by decide, by decide, MemoryBinding.storeEncoding, side.destination,
    by cases side <;> decide, by cases side <;> decide⟩

def indexRegister : Index := ⟨1, by decide⟩

def selectCode (side : Side) : List ℕ :=
  addressCode 0 indexRegister 3 side.base ++ X86DataLoad.code true side.destination 0 0

theorem select_size (side : Side) : (selectCode side).length = 11 := rfl

def emit (start outside : ℕ) : List ℕ :=
  NativeDecisions.compareBytes .lessUnsigned 1 8 start outside ++ (selectCode .left ++ selectCode .right)

theorem emit_size (start outside : ℕ) : (emit start outside).length = 31 := rfl

structure Placed (image : NativeImage.View) (start outside : ℕ) : Prop where
  extent : start + 31 ≤ image.size
  check : CompareBranch image start outside .lessUnsigned 1 8
  left : Code image (start + 9) (selectCode .left)
  right : Code image (start + 20) (selectCode .right)

theorem placed_of_emitted (image : NativeImage.View) (start outside : ℕ)
    (extent : start + 31 ≤ image.size) (target : outside ≤ image.size) (short : image.size < 2 ^ 31)
    (code : Code image start (emit start outside)) :
    Placed image start outside := by
  obtain ⟨check, body⟩ := NativeWords.code_append (show Code image start
    (NativeDecisions.compareBytes .lessUnsigned 1 8 start outside ++ _) from code)
  rw [NativeDecisions.compare_size] at body
  obtain ⟨left, right⟩ := NativeWords.code_append body
  rw [select_size] at right
  exact ⟨extent, NativeDecisions.compare_placed image _ _ _ _ _ (by omega) target short check, left, right⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers

abbrev clobbers : Finset Register := {.rax, .r9, .r10, .rflags, .rip}

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

private theorem sizeWord {arena : Arena} (node : Node) (words : Array Word)
    (found : PackedTerms.segment arena.children node = some words) :
    (BitVec.ofNat 64 words.size).toNat = words.size := by
  have count := (PackedTerms.segment_width arena.children node words found).1
  have fits := node.childrenCount.isLt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

private theorem select_fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {base : BitVec 48} {start : ℕ}
    {before : Native} (point : At image before base start) (controls : Controls before)
    {nodeCapacity edgeCapacity : ℕ} {layout : NativeTermArena.Layout nodeCapacity edgeCapacity} {arena : Arena}
    (resident : NativeTermArena.Ready layout arena before) (side : Side) (node : Node) (words : Array Word)
    (found : PackedTerms.segment arena.children node = some words)
    (index : Word) (inside : index.toNat < words.size) (knownIndex : lookup before 1 = some index)
    (knownSpan : lookup before side.base.register = some (spanPointer layout node))
    (extent : start + 11 ≤ image.size) (code : Code image start (selectCode side)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run before = .ok () after ∧
      X86StateFrame.Frame {.rax, key side.destination, .rip} ∅ before after ∧
      lookup after side.destination = some words[index.toNat] ∧ Nonempty (At image after base (start + 11)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have span := (PackedTerms.segment_width arena.children node words found).2
  let q : Fin arena.children.size := ⟨node.childrenAt.toNat + index.toNat, by omega⟩
  let backing : WordRegion.Region 1 := layout.child ⟨q.val, q.isLt.trans_le resident.edgesFit⟩
  have pointer : backing.pointer = spanPointer layout node + index * 8 := by
    change layout.edges.atWord (node.childrenAt.toNat + index.toNat) = _
    rw [← layout.edges.atWord_next node.childrenAt.toNat index.toNat]
    unfold NativeArenaGeometry.Region.atWord spanPointer
    rw [NativeArenaGeometry.word_scale8, NativeArenaGeometry.word_scale8]
  have value : arena.children[q] = words[index.toNat] := by
    have selected := PackedTerms.segment_at arena.children node words ⟨index.toNat, inside⟩ found
    change arena.children[q.val]? = some words[index.toNat] at selected
    rw [Array.getElem?_eq_getElem q.isLt] at selected
    exact Option.some.inj selected
  obtain ⟨addressBytes, loadBytes⟩ := NativeWords.code_append (show Code image start
    (addressCode 0 indexRegister 3 side.base ++ X86DataLoad.code true side.destination 0 0) from code)
  change Code image (start + 4) (X86DataLoad.code true side.destination 0 0) at loadBytes
  obtain ⟨selected, calculated, locateFrame, located, ⟨atRead⟩⟩ := X86IndexedAddress.forms_address other extra vector
    point (by omega) 0 indexRegister 3 side.base addressBytes (spanPointer layout node) index knownSpan knownIndex
  have read := (resident.child q).preserved (X86StateFrame.registerOnly locateFrame) (by simp)
  change X86PlacedMemory.Reads selected (backing.cell 0).address arena.children[q] at read
  rw [value] at read
  let source : NativeWords.Source backing.pointer := .copy 0 (backing.cell 0)
  obtain ⟨after, loaded, loadFrame, exactValue, endpoint⟩ := source.fetch (handlers other extra) vector side.wire _
    atRead (controls.transport (X86StateFrame.registerOnly locateFrame) (by decide))
    (pointer.symm ▸ located) read (show start + 11 ≤ image.size from extent) loadBytes
  have noHandlerChange : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
  rw [noHandlerChange] at loaded
  exact ⟨after, X86FuelPrefix.fetches_then 1 1 before selected after calculated loaded,
    ((X86StateFrame.registerOnly locateFrame).trans loadFrame).mono (by cases side <;> decide) (by simp),
    exactValue, endpoint⟩

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start outside : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : Placed image start outside)
    {nodeCapacity edgeCapacity : ℕ} {layout : NativeTermArena.Layout nodeCapacity edgeCapacity} {arena : Arena}
    (resident : NativeTermArena.Ready layout arena before) (left right : Node) (spans : Spans arena left right)
    (index : Word) (knownIndex : lookup before 1 = some index) (knownCount : lookup before 8 = some (.ofNat 64 spans.leftWords.size))
    (leftSpan : lookup before 6 = some (spanPointer layout left))
    (rightSpan : lookup before 7 = some (spanPointer layout right)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame clobbers ∅ before after ∧
      if index.toNat < spans.leftWords.size then
        ∃ pair, steps = 6 ∧ spans.pairs[index.toNat]? = some pair ∧ lookup after 9 = some pair.1 ∧
          lookup after 10 = some pair.2 ∧ Nonempty (At image after base (start + 31))
      else steps = 2 ∧ Nonempty (At image after base outside) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨checked, ran, checkFrame, ⟨atIndex⟩⟩ := X86PlacedScalar.compare_branch
    (X86PlacedFrameAddress.nativeBase other) extra vector point .lessUnsigned 1 8 placed.check
    index _ knownIndex knownCount
  change At image checked base (if decide (index.toNat < (BitVec.ofNat 64 spans.leftWords.size).toNat)
    then start + 9 else outside) at atIndex
  rw [sizeWord left spans.leftWords spans.left] at atIndex
  have prelude := X86StateFrame.registerOnly checkFrame
  have extent := placed.extent
  by_cases within : index.toNat < spans.leftWords.size
  · simp only [within, decide_true, if_true] at atIndex
    obtain ⟨leftLoaded, loadLeft, frameLeft, leftValue, ⟨atRight⟩⟩ := select_fetched other extra vector atIndex
      (controls.transport prelude (by decide)) (resident.preserved prelude) .left left spans.leftWords spans.left
      index within ((prelude.lookup 1 (by decide)).trans knownIndex) ((prelude.lookup 6 (by decide)).trans leftSpan)
      (by omega) placed.left
    have throughLeft := prelude.trans frameLeft
    obtain ⟨after, loadRight, frameRight, rightValue, endpoint⟩ := select_fetched other extra vector
      (show At image leftLoaded base (start + 20) from atRight) (controls.transport throughLeft (by decide))
      (resident.preserved throughLeft) .right right spans.rightWords spans.right index (spans.width ▸ within)
      ((throughLeft.lookup 1 (by decide)).trans knownIndex) ((throughLeft.lookup 7 (by decide)).trans rightSpan)
      (by omega) placed.right
    have done := X86FuelPrefix.fetches_then 2 2 before checked leftLoaded ran loadLeft
    refine ⟨after, 6, X86FuelPrefix.fetches_then 4 2 before leftLoaded after done loadRight,
      (throughLeft.trans frameRight).mono (by decide) (by simp), ?_⟩
    rw [if_pos within]
    exact ⟨_, rfl, spans.get index.toNat within, (frameRight.lookup 9 (by decide)).trans leftValue,
      rightValue, endpoint⟩
  · simp only [within, decide_false] at atIndex
    refine ⟨checked, 2, ran, prelude.mono (by decide) (by simp), ?_⟩
    rw [if_neg within]
    exact ⟨rfl, ⟨atIndex⟩⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeChildPair
