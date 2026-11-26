import Mettapedia.Machines.TIsa.StoreInstructions.NativeRemapCopy

/-!
# Appending the record for copied application edges

The original initialized arena stays present. The new ordinal
selects one reserved record in the same array, and four fetched
stores fill it only after the corresponding edge words have
been prepared. This block has no publication of a live length.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeTermAppend

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads CodeApart Encoding footprint)
open X86PlacedScalar (Code registerCode)
open NativeTermArena (field)
open PackedTerms (Arena Node)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

structure Registers where
  side : NativeTermSelection.Side
  field : Fin 4 → Fin 16
  kept : ∀ i, field i ≠ 0 ∧ field i ≠ side.output.register

def Registers.encoding (abi : Registers) : Encoding :=
  .direct abi.side.output.register (by cases abi.side <;> decide) (by cases abi.side <;> decide)

def remapRegisters : Registers :=
  ⟨.right, fun i => match i.val with | 0 => 14 | 1 => 10 | 2 => 13 | _ => 6, by decide +kernel⟩

def zeroCode : List ℕ := registerCode 0x89 12 0

def storeBytes (abi : Registers) : List ℕ :=
  (List.finRange 4).flatMap (fun j => abi.encoding.bytes (abi.field j) (BitVec.ofNat 32 (WordRegion.offset j)))

theorem store_size (abi : Registers) : (storeBytes abi).length = 28 := by
  cases abi with | mk side field kept =>
    cases side <;> rfl

def emit (abi : Registers) : List ℕ := zeroCode ++ (NativeTermSelection.scaleCode abi.side ++ storeBytes abi)

theorem emit_size (abi : Registers) : (emit abi).length = 39 := by
  simp only [emit, List.length_append, NativeTermSelection.scale_size, store_size,
    show zeroCode.length = 3 from rfl]

structure Placed (abi : Registers) (image : NativeImage.View) (start : ℕ) : Prop where
  extent : start + 39 ≤ image.size
  zero : Code image start zeroCode
  scale : Code image (start + 3) (NativeTermSelection.scaleCode abi.side)
  stores : Code image (start + 11) (storeBytes abi)

theorem placed_of_emitted (abi : Registers) (image : NativeImage.View) (start : ℕ)
    (extent : start + 39 ≤ image.size) (bytes : Code image start (emit abi)) : Placed abi image start := by
  obtain ⟨zero, rest⟩ := NativeWords.code_append (show Code image start (zeroCode ++ _) from bytes)
  obtain ⟨scale, stores⟩ := NativeWords.code_append rest
  rw [NativeTermSelection.scale_size] at stores
  exact ⟨extent, zero, scale, stores⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers

def clobbers (abi : Registers) : Finset Register := {.rax, key abi.side.output.register, .rip}

theorem clobbers_data (abi : Registers) : clobbers abi ⊆ dataRegisters := by
  intro reg member
  simp only [clobbers, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl
  · decide
  · exact data_key _
  · decide

private theorem prelude_subset (abi : Registers) :
    ({key 0, .rip} ∪ {key abi.side.output.register, .rip} : Finset Register) ⊆ clobbers abi := by
  intro reg member
  simp only [clobbers, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, show key 0 = .rax from rfl] at member ⊢
  tauto

def writeAt (abi : Registers) (record : WordRegion.Region 4) (node : Node) (j : Fin 4) : NativeStores.Write record.pointer :=
  ⟨abi.field j, _, record.cell j, field node j⟩

def writes (abi : Registers) (record : WordRegion.Region 4) (node : Node) : List (NativeStores.Write record.pointer) :=
  (List.finRange 4).map (writeAt abi record node)

theorem store_bytes (abi : Registers) (record : WordRegion.Region 4) (node : Node) :
    NativeStores.emitted abi.encoding (writes abi record node) = storeBytes abi := by
  unfold NativeStores.emitted writes storeBytes
  rw [List.flatMap_map]
  rfl

theorem field_members {abi : Registers} {record : WordRegion.Region 4} {node : Node}
    {write : NativeStores.Write record.pointer} (found : write ∈ writes abi record node) :
    ∃ i : Fin 4, write = writeAt abi record node i := by
  obtain ⟨i, _, eq⟩ := List.mem_map.mp found
  exact ⟨i, eq.symm⟩

theorem separate (abi : Registers) (record : WordRegion.Region 4) (node : Node) : NativeStores.Separate (writes abi record node) := by
  have disjoint : (List.finRange 4).Pairwise (fun i j => i ≠ j) := by decide +kernel
  exact disjoint.map (writeAt abi record node) (fun _ _ different => record.separate_words different)

variable {nodeCapacity edgeCapacity : ℕ}
variable {layout : NativeTermArena.Layout nodeCapacity edgeCapacity} {arena : Arena}

structure Input (abi : Registers) (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (arena : Arena) (node : Node)
    (before : Native) : Prop where
  source : NativeTermArena.Ready layout arena before
  pointer : lookup before 3 = some layout.nodes.pointer
  ordinal : lookup before abi.side.input.register = some (PackedTerms.root arena)
  zero : lookup before 12 = some 0
  fields : ∀ j : Fin 4, lookup before (abi.field j) = some (field node j)

def bytesOf (abi : Registers) (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (arena : Arena)
    (room : arena.nodes.size < nodeCapacity) (node : Node) : Finset ℕ :=
  NativeStores.written (writes abi (layout.record ⟨arena.nodes.size, room⟩) node)

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (abi : Registers) (placed : Placed abi image start)
    (header : UnifierHeaders.Header) (children : Array Word)
    (room : arena.nodes.size < nodeCapacity) (fits : arena.children.size + children.size ≤ edgeCapacity)
    (input : Input abi layout arena (PackedTerms.newNode arena header children) before)
    (copied : NativeRemapCopy.Stored layout arena.children.size children.size children fits (Nat.le_refl _) before)
    (code : CodeApart image base (bytesOf abi layout arena room (PackedTerms.newNode arena header children)))
    (apart : ∀ (i : Fin edgeCapacity) (j : Fin 4),
      Disjoint (footprint ((layout.child i).cell 0).address)
        (footprint ((layout.record ⟨arena.nodes.size, room⟩).cell j).address)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 7).run before = .ok () after ∧
      X86StateFrame.Frame (clobbers abi) (bytesOf abi layout arena room (PackedTerms.newNode arena header children)) before after ∧
      NativeTermArena.Ready layout (PackedTerms.place arena header children) after ∧
      PackedTerms.append arena header children = some (PackedTerms.place arena header children, PackedTerms.root arena) ∧
      lookup after abi.side.input.register = some (PackedTerms.root arena) ∧ Nonempty (At image after base (start + 39)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  let index : Fin nodeCapacity := ⟨arena.nodes.size, room⟩
  let record := layout.record index
  let node := PackedTerms.newNode arena header children
  let ordinal := PackedTerms.root arena
  have exactOrdinal : ordinal.toNat = arena.nodes.size := input.source.count_word
  have landed : record.pointer = layout.nodes.pointer + ordinal * 32 := by
    have inRange : ordinal.toNat < nodeCapacity := exactOrdinal ▸ room
    have loc := layout.record_word ordinal inRange
    rw [show (⟨ordinal.toNat, inRange⟩ : Fin nodeCapacity) = index from Fin.ext exactOrdinal] at loc
    exact loc
  obtain ⟨a, cleared, clearFrame, zero, ⟨atScale⟩⟩ := X86PlacedRegisterMove.executes (handlers other extra)
    vector point (by omega) 12 0 0 input.zero placed.zero
  obtain ⟨b, scaled, scaleFrame, pointer, ⟨atStore⟩⟩ := NativeTermSelection.scale_fetched other extra vector atScale
    (by omega) abi.side layout.nodes.pointer ordinal ((clearFrame.lookup 3 (by decide)).trans input.pointer)
    zero ((clearFrame.lookup abi.side.input.register (by cases abi.side <;> decide)).trans input.ordinal) placed.scale
  have beforeStore := (X86StateFrame.registerOnly clearFrame).trans scaleFrame
  have established : lookup b abi.side.output.register = some record.pointer := landed.symm ▸ pointer
  have codeFits : start + 11 + (NativeStores.emitted abi.encoding (writes abi record node)).length ≤ image.size := by
    rw [store_bytes, store_size]
    omega
  have storePlaced : Code image (start + 11) (NativeStores.emitted abi.encoding (writes abi record node)) := by
    rw [store_bytes]
    exact placed.stores
  have ready (w : NativeStores.Write record.pointer) (access : w ∈ writes abi record node) :
      lookup b w.source = some w.value := by
    obtain ⟨i, rfl⟩ := field_members access
    have noPointer : ∀ r : Fin 16, key r ≠ .rip := by decide +kernel
    have held : key (abi.field i) ∉ ({key 0, .rip} ∪ {key abi.side.output.register, .rip} : Finset Register) := by
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨⟨fun equal => (abi.kept i).1 (key_injective equal), noPointer _⟩,
        ⟨fun equal => (abi.kept i).2 (key_injective equal), noPointer _⟩⟩
    exact (beforeStore.lookup _ held).trans (input.fields i)
  obtain ⟨after, done, storeFrame, written, endpoint⟩ := NativeStores.fetched (handlers other extra) vector
    abi.encoding (writes abi record node) (show At image b base (start + 11) from atStore)
    (controls.transport beforeStore ((prelude_subset abi).trans (clobbers_data abi)))
    (NativeStores.checked_of_emitted _ _ _ _ codeFits storePlaced)
    established ready (separate abi record node) code
  have frame : X86StateFrame.Frame (clobbers abi) (bytesOf abi layout arena room node) before after :=
    (beforeStore.trans storeFrame).mono (Finset.union_subset (prelude_subset abi) (by simp [clobbers])) (by
      simp only [Finset.empty_union, bytesOf, record, index]
      exact Finset.Subset.refl _)
  have nodeExtent : arena.nodes.size < 2 ^ 64 := by
    have bound := (BitVec.ofNat 64 arena.nodes.size).isLt
    rwa [input.source.count_word] at bound
  have edgeExtent : arena.children.size + children.size < 2 ^ 64 := by
    by_cases empty : edgeCapacity = 0
    · omega
    · have bound := layout.edges.positive_room (by omega : 0 < edgeCapacity)
      omega
  have appended : PackedTerms.append arena header children =
      some (PackedTerms.place arena header children, ordinal) := if_pos ⟨nodeExtent, edgeExtent⟩
  have fitsNodes : (PackedTerms.place arena header children).nodes.size ≤ nodeCapacity := by
    simp only [PackedTerms.place, Array.size_push]
    omega
  have fitsEdges : (PackedTerms.place arena header children).children.size ≤ edgeCapacity := by
    simpa only [PackedTerms.place, Array.size_append] using fits
  have visible : NativeTermArena.Ready layout (PackedTerms.place arena header children) after := by
    refine ⟨fitsNodes, fitsEdges, ?_, ?_⟩
    · intro i j
      by_cases latest : i.val = arena.nodes.size
      · have same : (⟨i.val, i.isLt.trans_le fitsNodes⟩ : Fin nodeCapacity) = index := Fin.ext latest
        have isNode : (PackedTerms.place arena header children).nodes[i] = node := by
          change (arena.nodes.push node)[i.val] = node
          simp [Array.getElem_push, latest]
        rw [same, isNode]
        exact written (writeAt abi record node j) (by simp [writes])
      · have older : i.val < arena.nodes.size := by
          have before := i.isLt
          simp only [PackedTerms.place, Array.size_push] at before
          omega
        let k : Fin arena.nodes.size := ⟨i.val, older⟩
        have oldNode : (PackedTerms.place arena header children).nodes[i] = arena.nodes[k] := by
          change (arena.nodes.push node)[i.val] = arena.nodes[i.val]
          simp [Array.getElem_push, older]
        rw [oldNode]
        apply (input.source.node k j).preserved frame
        apply NativeStores.apart_written
        intro item member
        obtain ⟨col, rfl⟩ := field_members member
        exact layout.separate_records ⟨k.val, k.isLt.trans_le input.source.nodesFit⟩ index older j col
    · intro i
      have protect : Disjoint (footprint ((layout.child ⟨i.val, i.isLt.trans_le fitsEdges⟩).cell 0).address)
          (bytesOf abi layout arena room node) := by
        apply NativeStores.apart_written
        intro item member
        obtain ⟨j, rfl⟩ := field_members member
        exact apart _ j
      have content : Reads before ((layout.child ⟨i.val, i.isLt.trans_le fitsEdges⟩).cell 0).address
          (PackedTerms.place arena header children).children[i] := by
        by_cases prior : i.val < arena.children.size
        · let k : Fin arena.children.size := ⟨i.val, prior⟩
          have word : (PackedTerms.place arena header children).children[i] = arena.children[k] := by
            change (arena.children ++ children)[i.val] = arena.children[i.val]
            exact Array.getElem_append_left prior
          rw [word]
          exact input.source.child k
        · have bound := i.isLt
          simp only [PackedTerms.place, Array.size_append] at bound
          let k : Fin children.size := ⟨i.val - arena.children.size, by omega⟩
          have word : (PackedTerms.place arena header children).children[i] = children[k] := by
            change (arena.children ++ children)[i.val] = children[k.val]
            exact Array.getElem_append_right (Nat.le_of_not_gt prior)
          have position : (⟨arena.children.size + k.val, by have inside := k.isLt; omega⟩ : Fin edgeCapacity)
              = ⟨i.val, i.isLt.trans_le fitsEdges⟩ := Fin.ext (by change arena.children.size + (i.val - arena.children.size) = i.val; omega)
          rw [word]
          have found := copied k
          rw [position] at found
          exact found
      exact content.preserved frame protect
  exact ⟨after, X86FuelPrefix.fetches_then 3 4 before b after
    (X86FuelPrefix.fetches_then 1 2 before a b cleared scaled) done, frame, visible, appended,
    (frame.lookup abi.side.input.register (by unfold clobbers; cases abi.side <;> decide)).trans input.ordinal, endpoint⟩

/-- On a changed application, the record written by the fetched
block and the already copied edge span are precisely the packed
substitution's new term. No source term is unfolded. -/
theorem fetched_rewrite (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (abi : Registers) (placed : Placed abi image start)
    (source : Arena) (original query replacement : Word) (mapped : Array Word)
    (node : Node) (selected : source.nodes[original.toNat]? = some node) (application : node.header.tag = 2)
    (children newer : Array Word) (span : PackedTerms.segment source.children node = some children)
    (translated : PackedSubstitution.translate mapped children = some newer) (changed : newer ≠ children)
    (room : arena.nodes.size < nodeCapacity) (fits : arena.children.size + newer.size ≤ edgeCapacity)
    (input : Input abi layout arena (PackedTerms.newNode arena node.header newer) before)
    (copied : NativeRemapCopy.Stored layout arena.children.size newer.size newer fits (Nat.le_refl _) before)
    (code : CodeApart image base (bytesOf abi layout arena room (PackedTerms.newNode arena node.header newer)))
    (apart : ∀ (i : Fin edgeCapacity) (j : Fin 4),
      Disjoint (footprint ((layout.child i).cell 0).address)
        (footprint ((layout.record ⟨arena.nodes.size, room⟩).cell j).address)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 7).run before = .ok () after ∧
      X86StateFrame.Frame (clobbers abi) (bytesOf abi layout arena room (PackedTerms.newNode arena node.header newer)) before after ∧
      NativeTermArena.Ready layout (PackedTerms.place arena node.header newer) after ∧
      PackedSubstitution.rewrite source arena mapped query replacement original =
        some (PackedTerms.place arena node.header newer, PackedTerms.root arena) ∧
      lookup after abi.side.input.register = some (PackedTerms.root arena) ∧ Nonempty (At image after base (start + 39)) := by
  obtain ⟨after, executed, frame, contents, appended, ordinal, endpoint⟩ := fetched other extra vector point controls abi placed
    node.header newer room fits input copied code apart
  have notVar : node.header.tag ≠ 0 := by rw [application]; decide
  have notConst : node.header.tag ≠ 1 := by rw [application]; decide
  exact ⟨after, executed, frame, contents, by
    simp only [PackedSubstitution.rewrite, selected, bind, Option.bind_some, if_neg notVar, if_neg notConst,
      if_pos application, span, translated, if_neg changed]
    exact appended, ordinal, endpoint⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeTermAppend
