import Mettapedia.Languages.Micromath.Kernel
import Mettapedia.Machines.TIsa.ImportedP1
import Mettapedia.Machines.TIsa.X86P1Sub1Entry
import Mettapedia.Machines.TIsa.X86MemoryBounds

/-!
# Micromath substitution through its native entry

The captured loads read the four premise rows in the published word layout.
Their comparisons and the published output refine `Micromath.substitute1?`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option Elab.async false

namespace Mettapedia.Machines.TIsa.X86P1Sub1Rule

open _root_.X86Registers X86RegisterRefinement X86Execution
open Mettapedia.Languages.Micromath (Claim Derives Substitute1Guard substitute1?)
open X86P1Sub1Entry
open X86P1Sub1Guards.PremiseGuards (leftLoad rightLoad prefixWrites)
open X86P1Sub1Guards.OperandLoads (instructionAt)
open X86P1Sub1Output (loadIndex outputWrites)
open X86P1Sub1Exit (handlers tailRegisters)

theorem live_export_identity :
    ImportedP1.programs[11]'(by rw [ImportedP1.exact_count.2]; decide) = X86P1Sub1Allowance.sub1 := by
  kernel_reflexivity

private def operand (site : Fin 18) : Fin 4 × Fin 4 :=
  ![(1, 1), (0, 2), (2, 1), (0, 3), (2, 2), (1, 2), (2, 3), (1, 3),
    (3, 1), (0, 0), (3, 2), (1, 2), (3, 3), (1, 3), (3, 0), (0, 1), (1, 0), (2, 0)] site

private def rowRegister (row : Fin 4) : Fin 12 := ⟨row.val + 1, by have := row.isLt; omega⟩

theorem load_layout (site : Fin 18) :
    (instructionAt site).wide = true ∧
    (instructionAt site).region.val = (operand site).1.val ∧
    (instructionAt site).base = rowRegister (operand site).1 ∧
    (instructionAt site).offset.val = 8 * (operand site).2.val ∧
    (X86BoundedLoad.displacement (instructionAt site)).signExtend 64 =
      BitVec.ofNat 64 (8 * (operand site).2.val) := by
  have checked : (List.finRange 18).all (fun i => decide (
    (instructionAt i).wide = true ∧ (instructionAt i).region.val = (operand i).1.val ∧
    (instructionAt i).base = rowRegister (operand i).1 ∧
    (instructionAt i).offset.val = 8 * (operand i).2.val ∧
    (X86BoundedLoad.displacement (instructionAt i)).signExtend 64 =
      BitVec.ofNat 64 (8 * (operand i).2.val))) = true := by
    kernel_reflexivity
  exact of_decide_eq_true (List.all_eq_true.mp checked site (List.mem_finRange site))

structure InputRows (state : State) where
  base : Fin 4 → Word
  words : Fin 4 → Fin 4 → Word
  pointers : ∀ row, lookup state (X86BoundedLoad.physical (rowRegister row)) = some (base row)
  bytes : ∀ row field, X86MemoryView.wordAt? (X86MemoryView.memory state)
    (base row + BitVec.ofNat 64 (8 * field.val)) = some (words row field)

structure InputFrame {state : State} (rows : InputRows state) where
  frame : Word
  frameKnown : lookup state 7 = some frame
  frameArea : X86CanonicalSpan.Area frame frameLayout.size
  frameAligned : frame.toNat % 8 = 0
  length : Fin 4 → Word
  baseRead : ∀ row, X86MemoryView.wordAt? (X86MemoryView.memory state)
    (frame + BitVec.ofNat 64 (16 * row.val)) = some (rows.base row)
  lengthRead : ∀ row, X86MemoryView.wordAt? (X86MemoryView.memory state)
    (frame + BitVec.ofNat 64 (16 * row.val + 8)) = some (length row)
  room : ∀ row, 32 ≤ (length row).toNat
  rowArea : ∀ row, X86CanonicalSpan.Area (rows.base row) 32
  rowAligned : ∀ row, (rows.base row).toNat % 8 = 0

noncomputable def InputFrame.loadRequest {state : State} {rows : InputRows state} (input : InputFrame rows)
    (profile : X86Readiness.Profile) (flags : BitVec 32) (holds : profile.Holds state)
    (flagsKnown : state.regs.get? .rflags = some flags) (quiet : state.regs.get? .log_register_writes = some false)
    (site : Fin 18) : X86P1Sub1Guards.OperandLoads.Request (instructionAt site) state := by
  have shape := load_layout site
  have wide := shape.1
  have region := shape.2.1
  have pointerRegister := shape.2.2.1
  have offset := shape.2.2.2.1
  have displacement := shape.2.2.2.2
  let row := (operand site).1
  let field := (operand site).2
  let layout := X86BoundedLoad.layout (instructionAt site)
  have rowSlot : layout.region.val = row.val := region
  have pointerKnown : lookup state layout.pointer = some (rows.base row) := by
    simpa only [layout, X86BoundedLoad.layout, pointerRegister, row] using rows.pointers row
  let facts := X86MemoryBounds.facts_at state layout profile flags input.frame
    (rows.base row) (rows.base row) (input.length row) input.frameKnown pointerKnown
    (by rw [rowSlot]; exact input.baseRead row) (by rw [rowSlot]; exact input.lengthRead row)
    input.frameArea input.frameAligned holds flagsKnown quiet
  let source := rows.base row + BitVec.ofNat 64 (8 * field.val)
  let location := X86CanonicalSpan.narrow source
  have bytes := X86MemoryReadback.wordAt?_narrow_bytes state source (rows.words row field) (rows.bytes row field)
  refine {
    toFacts := facts
    within := ?_
    value := rows.words row field
    dataAddress := location
    dataUpper := ?_
    effective := ?_
    alignment := ?_
    dataBytes := ?_ }
  · change (rows.base row - rows.base row).toNat + (instructionAt site).offset.val +
        (X86BoundedLoad.layout (instructionAt site)).count.val ≤ (input.length row).toNat
    rw [BitVec.sub_self]
    simp [X86BoundedLoad.layout, offset, wide]
    have := (operand site).2.isLt
    have := input.room row
    omega
  · simpa [wide, X86DataLoad.byteCount, location] using bytes.2.1
  · change rows.base row + (X86BoundedLoad.displacement (instructionAt site)).signExtend 64 = location.signExtend 64
    rw [displacement]
    exact bytes.1
  · apply Or.inr
    simp only [wide, X86DataLoad.byteCount, ite_true]
    change location &&& (7#48) = 0#48
    have within : 8 * field.val < 32 := by have := field.isLt; omega
    dsimp only [location, source]
    rw [X86CanonicalSpan.narrow_offset _ 32 _ (by decide) (input.rowArea row) within]
    exact X86CanonicalSpan.offset_aligned _ 32 _ (by decide) (input.rowArea row) within
      (input.rowAligned row) (by omega)
  · intro byte inside
    rw [wide, X86DataLoad.byteCount, if_pos rfl] at inside
    exact bytes.2.2 byte inside

def InputRows.claim {state : State} (rows : InputRows state) (row : Fin 4) : Claim :=
  ⟨(rows.words row 0).toNat, (rows.words row 1).toNat, (rows.words row 2).toNat, (rows.words row 3).toNat⟩

private theorem word_of_equal_bytes (a b : Word)
    (same : ∀ byte < 8, a.extractLsb' (8 * byte) 8 = b.extractLsb' (8 * byte) 8) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  have byte : bit / 8 < 8 := by omega
  have within : bit % 8 < 8 := Nat.mod_lt _ (by decide)
  have coord : 8 * (bit / 8) + bit % 8 = bit := by omega
  have read := congrArg (fun w : BitVec 8 => w.getLsbD (bit % 8)) (same _ byte)
  simpa only [BitVec.getLsbD_extractLsb', within, decide_true, Bool.true_and, coord] using read

theorem InputRows.load_word {state : State} (rows : InputRows state) (args : Arguments state) (site : Fin 18) :
    (args.loads site).value = rows.words (operand site).1 (operand site).2 := by
  obtain ⟨wide, _, baseRegister, _, offset⟩ := load_layout site
  let request := args.loads site
  have lookupBase : lookup state (X86BoundedLoad.physical (rowRegister (operand site).1)) =
      some request.pointer := by
    simpa only [request, X86BoundedLoad.layout, baseRegister] using request.pointerKnown
  have pointer := Option.some.inj (lookupBase.symm.trans (rows.pointers (operand site).1))
  obtain ⟨location, found, _, read⟩ :=
    X86MemoryReadback.wordAt?_native_bytes state _ _ (rows.bytes (operand site).1 (operand site).2)
  have sameAddress : request.dataAddress = location := by
    apply BitVec.eq_of_toInt_eq
    have signed := congrArg BitVec.toInt (request.effective.symm.trans (by simpa only [pointer, offset] using found))
    simpa only [BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 64)] using signed
  apply word_of_equal_bytes
  intro byte inside
  have physical := request.dataBytes byte (by simpa only [wide, X86DataLoad.byteCount, ite_true] using inside)
  rw [sameAddress] at physical
  exact Option.some.inj (physical.symm.trans (read byte inside))

theorem InputRows.guard_iff {state : State} (rows : InputRows state) (args : Arguments state) :
    (∀ i, (args.loads (leftLoad i)).value = (args.loads (rightLoad i)).value) ↔
      Substitute1Guard (rows.claim 0) (rows.claim 1) (rows.claim 2) (rows.claim 3) := by
  constructor
  · intro agrees
    have atIndex (i : Fin 7) := congrArg BitVec.toNat
      ((rows.load_word args (leftLoad i)).symm.trans ((agrees i).trans (rows.load_word args (rightLoad i))))
    exact ⟨atIndex 0, atIndex 1, atIndex 2, atIndex 3, atIndex 4, atIndex 5, atIndex 6⟩
  · rintro ⟨first, second, third, fourth, fifth, sixth, seventh⟩ index
    rw [rows.load_word args (leftLoad index), rows.load_word args (rightLoad index)]
    apply BitVec.eq_of_toNat_eq
    fin_cases index <;> assumption

def InputRows.conclusion {state : State} (rows : InputRows state) : Claim :=
  ⟨(rows.claim 3).out, (rows.claim 0).f, (rows.claim 1).out, (rows.claim 2).out⟩

def claimField (claim : Claim) : Fin 4 → Nat := ![claim.out, claim.f, claim.x, claim.y]

theorem InputRows.output_word {state : State} (rows : InputRows state) (args : Arguments state) (field : Fin 4) :
    (args.loads (loadIndex field)).value = BitVec.ofNat 64 (claimField rows.conclusion field) := by
  rw [rows.load_word args (loadIndex field)]
  fin_cases field <;>
    simp [operand, loadIndex, InputRows.conclusion, InputRows.claim, claimField, BitVec.ofNat_toNat]

structure OutputRow (state : State) where
  base : Word
  pointer : lookup state (X86BoundedStore.physical 5) = some base
  extent : X86CanonicalSpan.Area base 32

abbrev OutputRow.bytes {state : State} (row : OutputRow state) : Finset Nat :=
  X86WriteWords.written (X86CanonicalSpan.narrow row.base) (List.range 32)

private theorem store_offset (field : Fin 4) :
    (X86BoundedStore.displacement (X86P1Sub1Output.Stores.instructionAt field)).signExtend 64 =
      BitVec.ofNat 64 (8 * field.val) := by
  fin_cases field <;> kernel_reflexivity

private def capacityOffset (limit : Bool) : Nat := if limit then 184 else 176

def InputFrame.capacityInputs {state : State} {rows : InputRows state} (input : InputFrame rows)
    (profile : X86Readiness.Profile) (flags : BitVec 32) (holds : profile.Holds state)
    (flagsKnown : state.regs.get? .rflags = some flags) (quiet : state.regs.get? .log_register_writes = some false)
    (value : Bool → Word) (known : ∀ limit, X86MemoryView.wordAt? (X86MemoryView.memory state)
      (input.frame + BitVec.ofNat 64 (capacityOffset limit)) = some (value limit)) :
    X86P1Sub1Guards.Capacity.Inputs state := by
  let data := fun limit => X86CanonicalSpan.narrow (input.frame + BitVec.ofNat 64 (capacityOffset limit))
  have bytes := fun limit => X86MemoryReadback.wordAt?_narrow_bytes state _ _ (known limit)
  refine {
    frame := input.frame
    frameKnown := input.frameKnown
    controls := profile.controls
    controlsKnown := holds.1
    visible := profile.visible
    visibleKnown := holds.2.1
    flags := flags
    flagsKnown := flagsKnown
    quiet := quiet
    data := data
    value := value
    upper := fun limit => (bytes limit).2.1
    effective := ?_
    aligned := ?_
    present := fun limit index within => (bytes limit).2.2 index within }
  · intro limit
    cases limit
    · exact (bytes false).1
    · exact (bytes true).1
  · intro limit
    have within : capacityOffset limit < frameLayout.size := by cases limit <;> decide
    have stride : capacityOffset limit % 8 = 0 := by cases limit <;> decide
    dsimp only [data]
    rw [X86CanonicalSpan.narrow_offset _ frameLayout.size _ (by decide) input.frameArea within]
    exact X86CanonicalSpan.offset_aligned _ frameLayout.size _ (by decide) input.frameArea within
      input.frameAligned stride

structure OutputFrame {state : State} {rows : InputRows state} (input : InputFrame rows)
    (output : OutputRow state) where
  length : Word
  baseRead : X86MemoryView.wordAt? (X86MemoryView.memory state) (input.frame + 64) = some output.base
  lengthRead : X86MemoryView.wordAt? (X86MemoryView.memory state) (input.frame + 72) = some length
  room : 32 ≤ length.toNat
  aligned : output.base.toNat % 8 = 0

noncomputable def OutputFrame.destination {state : State} {rows : InputRows state} {input : InputFrame rows}
    {output : OutputRow state} (frame : OutputFrame input output)
    (profile : X86Readiness.Profile) (flags : BitVec 32) (holds : profile.Holds state)
    (flagsKnown : state.regs.get? .rflags = some flags) (quiet : state.regs.get? .log_register_writes = some false)
    (field : Fin 4) : X86P1Sub1Output.Stores.Destination (X86P1Sub1Output.Stores.instructionAt field) state := by
  have shape := X86P1Sub1Output.Stores.source_fields field
  have wide := shape.1
  have region := shape.2.1
  have pointer := shape.2.2.1
  have offset := shape.2.2.2.1
  let layout := X86BoundedStore.layout (X86P1Sub1Output.Stores.instructionAt field)
  have slot : layout.region.val = 4 := congrArg Fin.val region
  have pointerKnown : lookup state layout.pointer = some output.base := by
    simpa only [layout, X86BoundedStore.layout, pointer] using output.pointer
  let facts := X86MemoryBounds.facts_at state layout profile flags input.frame output.base output.base frame.length
    input.frameKnown pointerKnown (by rw [slot]; exact frame.baseRead) (by rw [slot]; exact frame.lengthRead)
    input.frameArea input.frameAligned holds flagsKnown quiet
  let destination := output.base + BitVec.ofNat 64 (8 * field.val)
  let data := X86CanonicalSpan.narrow destination
  have within : 8 * field.val < 32 := by have := field.isLt; omega
  have canonical := output.extent.2 (8 * field.val) within
  refine {
    toFacts := facts
    within := ?_
    data := data
    dataUpper := ?_
    effective := ?_
    alignment := ?_ }
  · change (output.base - output.base).toNat + (X86P1Sub1Output.Stores.instructionAt field).offset.val +
      (X86BoundedStore.layout (X86P1Sub1Output.Stores.instructionAt field)).count.val ≤ frame.length.toNat
    rw [BitVec.sub_self]
    simp [X86BoundedStore.layout, offset, wide]
    have := frame.room
    have := field.isLt
    omega
  · simp only [wide, X86DataStore.byteCount]
    change (X86CanonicalSpan.narrow destination).toInt + 8 ≤ (2 ^ 47 : Int)
    rw [X86CanonicalSpan.narrow_toInt destination canonical, X86CanonicalSpan.offset_signed _ 32 _ (by decide)
      output.extent within]
    have := X86CanonicalSpan.area_signed_upper output.base 32 (by decide) output.extent
    have := field.isLt
    omega
  · change output.base + (X86BoundedStore.displacement
      (X86P1Sub1Output.Stores.instructionAt field)).signExtend 64 = data.signExtend 64
    rw [store_offset]
    exact (X86CanonicalSpan.narrow_representation destination canonical).symm
  · apply Or.inr
    simp only [wide, X86DataStore.byteCount]
    change data &&& (7#48) = 0#48
    dsimp only [destination, data]
    rw [X86CanonicalSpan.narrow_offset _ 32 _ (by decide) output.extent within]
    exact X86CanonicalSpan.offset_aligned _ 32 _ (by decide) output.extent within frame.aligned (by omega)

noncomputable def InputFrame.arguments {state : State} {rows : InputRows state} {output : OutputRow state}
    (input : InputFrame rows) (out : OutputFrame input output)
    (profile : X86Readiness.Profile) (flags : BitVec 32) (holds : profile.Holds state)
    (flagsKnown : state.regs.get? .rflags = some flags) (quiet : state.regs.get? .log_register_writes = some false)
    (value : Bool → Word) (known : ∀ limit, X86MemoryView.wordAt? (X86MemoryView.memory state)
      (input.frame + BitVec.ofNat 64 (capacityOffset limit)) = some (value limit)) : Arguments state :=
  ⟨input.loadRequest profile flags holds flagsKnown quiet,
    input.capacityInputs profile flags holds flagsKnown quiet value known,
    out.destination profile flags holds flagsKnown quiet⟩

private theorem inside_span (base : Word) (size offset byte : Nat)
    (area : X86CanonicalSpan.Area base size) (within : offset + byte < size) :
    X86WriteWords.physicalAddress (X86CanonicalSpan.narrow (base + BitVec.ofNat 64 offset)) byte ∈
      X86WriteWords.written (X86CanonicalSpan.narrow base) (List.range size) := by
  have positive : 0 < size := by omega
  have first : offset < size := by omega
  rw [X86CanonicalSpan.narrow_offset _ _ _ positive area first,
    X86CanonicalSpan.physicalAddress_nested _ _ _ _ positive area within,
    X86CanonicalSpan.physicalKey_offset _ _ _ positive area within]
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨offset + byte, List.mem_range.mpr within, rfl⟩)

theorem InputFrame.arguments_apart {state : State} {rows : InputRows state} {output : OutputRow state}
    (input : InputFrame rows) (out : OutputFrame input output)
    (profile : X86Readiness.Profile) (flags : BitVec 32) (holds : profile.Holds state)
    (flagsKnown : state.regs.get? .rflags = some flags) (quiet : state.regs.get? .log_register_writes = some false)
    (value : Bool → Word) (known : ∀ limit, X86MemoryView.wordAt? (X86MemoryView.memory state)
      (input.frame + BitVec.ofNat 64 (capacityOffset limit)) = some (value limit))
    (spills : Finset Nat)
    (frameApart : Disjoint (X86WriteWords.written (X86CanonicalSpan.narrow input.frame)
      (List.range frameLayout.size)) spills)
    (rowsApart : ∀ row, Disjoint (X86WriteWords.written (X86CanonicalSpan.narrow (rows.base row))
      (List.range 32)) spills) :
    (input.arguments out profile flags holds flagsKnown quiet value known).Apart spills := by
  have frameByte (offset index : Nat) (inside : offset + index < frameLayout.size) :
      X86WriteWords.physicalAddress (X86CanonicalSpan.narrow (input.frame + BitVec.ofNat 64 offset)) index
        ∉ spills := (Finset.disjoint_left.mp frameApart) (inside_span _ _ _ _ input.frameArea inside)
  constructor
  · intro site index inside
    let slot := (X86BoundedLoad.layout (instructionAt site)).region
    change X86WriteWords.physicalAddress
      (X86CanonicalSpan.narrow (input.frame + BitVec.ofNat 64 (16 * slot.val))) index ∉ spills
    apply frameByte
    change 16 * slot.val + index < 192
    have := slot.isLt
    omega
  · intro site index inside
    let slot := (X86BoundedLoad.layout (instructionAt site)).region
    change X86WriteWords.physicalAddress
      (X86CanonicalSpan.narrow (input.frame + BitVec.ofNat 64 (16 * slot.val + 8))) index ∉ spills
    apply frameByte
    change 16 * slot.val + 8 + index < 192
    have := slot.isLt
    omega
  · intro site index inside
    let row := (operand site).1
    let field := (operand site).2
    change X86WriteWords.physicalAddress
      (X86CanonicalSpan.narrow (rows.base row + BitVec.ofNat 64 (8 * field.val))) index ∉ spills
    have insideWord : index < 8 := by simpa [X86DataLoad.byteCount, (load_layout site).1] using inside
    apply (Finset.disjoint_left.mp (rowsApart row))
    apply inside_span _ _ _ _ (input.rowArea row)
    have := field.isLt
    omega
  · intro limit index inside
    apply frameByte
    cases limit
    · change 176 + index < 192
      omega
    · change 184 + index < 192
      omega
  · intro field index inside
    let slot := (X86BoundedStore.layout (X86P1Sub1Output.Stores.instructionAt field)).region
    change X86WriteWords.physicalAddress
      (X86CanonicalSpan.narrow (input.frame + BitVec.ofNat 64 (16 * slot.val))) index ∉ spills
    apply frameByte
    change 16 * slot.val + index < 192
    have := slot.isLt
    omega
  · intro field index inside
    let slot := (X86BoundedStore.layout (X86P1Sub1Output.Stores.instructionAt field)).region
    change X86WriteWords.physicalAddress
      (X86CanonicalSpan.narrow (input.frame + BitVec.ofNat 64 (16 * slot.val + 8))) index ∉ spills
    apply frameByte
    change 16 * slot.val + 8 + index < 192
    have := slot.isLt
    omega

theorem OutputFrame.write_spans {state : State} {rows : InputRows state} {input : InputFrame rows}
    {output : OutputRow state} (out : OutputFrame input output)
    (profile : X86Readiness.Profile) (flags : BitVec 32) (holds : profile.Holds state)
    (flagsKnown : state.regs.get? .rflags = some flags) (quiet : state.regs.get? .log_register_writes = some false) :
    let addresses := fun i => (out.destination profile flags holds flagsKnown quiet i).data
    X86P1Sub1Output.Stores.rowWrites addresses =
      X86WriteWords.written (X86CanonicalSpan.narrow output.base) (List.range 32) ∧
    Pairwise (fun i j => Disjoint (X86P1Sub1Output.Stores.fieldWrites addresses i)
      (X86P1Sub1Output.Stores.fieldWrites addresses j)) := by
  dsimp only
  let dest := fun i => (out.destination profile flags holds flagsKnown quiet i).data
  let span := X86WriteWords.written (X86CanonicalSpan.narrow output.base) (List.range 32)
  have coordinate (i : Fin 4) (n : Nat) (within : n < 8) :
      X86WriteWords.physicalAddress (dest i) n =
        X86WriteWords.physicalAddress (X86CanonicalSpan.narrow output.base) (8 * i.val + n) := by
    have inside : 8 * i.val + n < 32 := by have := i.isLt; omega
    have start : 8 * i.val < 32 := by omega
    change X86WriteWords.physicalAddress
      (X86CanonicalSpan.narrow (output.base + BitVec.ofNat 64 (8 * i.val))) n = _
    rw [X86CanonicalSpan.narrow_offset _ 32 _ (by decide) output.extent start,
      X86CanonicalSpan.physicalAddress_nested _ 32 _ _ (by decide) output.extent inside,
      X86CanonicalSpan.physicalKey_offset _ 32 _ (by decide) output.extent inside]
  have unpack (i : Fin 4) (key : Nat) (present : key ∈ X86P1Sub1Output.Stores.fieldWrites dest i) :
      ∃ n < 8, X86WriteWords.physicalAddress (X86CanonicalSpan.narrow output.base) (8 * i.val + n) = key := by
    unfold X86P1Sub1Output.Stores.fieldWrites X86DataStore.writes X86WriteWords.written at present
    obtain ⟨byte, bound, atKey⟩ := List.mem_map.mp (List.mem_toFinset.mp present)
    have within : byte < 8 := by simpa [X86DataStore.byteCount] using bound
    exact ⟨byte, within, (coordinate i byte within).symm.trans atKey⟩
  change X86P1Sub1Output.Stores.rowWrites dest = span ∧ _
  constructor
  · ext key
    constructor
    · intro present
      obtain ⟨i, _, field⟩ := Finset.mem_biUnion.mp present
      obtain ⟨byte, within, same⟩ := unpack i key field
      have inside : 8 * i.val + byte < 32 := by have := i.isLt; omega
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, List.mem_range.mpr inside, same⟩)
    · intro present
      obtain ⟨offset, bound, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp present)
      have inside := List.mem_range.mp bound
      let i : Fin 4 := ⟨offset / 8, by omega⟩
      have within : offset % 8 < 8 := Nat.mod_lt _ (by decide)
      have split : 8 * i.val + offset % 8 = offset := by dsimp [i]; omega
      rw [← split, ← coordinate i _ within]
      exact X86P1Sub1Output.Stores.byte_in_row dest i _ within
  · intro i j different
    apply Finset.disjoint_left.mpr
    intro key left right
    obtain ⟨a, ha, first⟩ := unpack i key left
    obtain ⟨b, hb, second⟩ := unpack j key right
    have upper := X86CanonicalSpan.area_narrow_upper output.base 32 (by decide) output.extent
    have equal := X86WriteWords.physicalAddress_injective 32 (X86CanonicalSpan.narrow output.base)
      upper _ _ (by have := i.isLt; omega) (by have := j.isLt; omega) (first.trans second.symm)
    exact different (Fin.ext (by omega))

theorem OutputFrame.output_apart {state : State} {rows : InputRows state} {input : InputFrame rows}
    {output : OutputRow state} (out : OutputFrame input output)
    (caller : CallerInputs state) (ret : ReturnInputs caller)
    (profile : X86Readiness.Profile) (flags : BitVec 32) (holds : profile.Holds state)
    (flagsKnown : state.regs.get? .rflags = some flags) (quiet : state.regs.get? .log_register_writes = some false)
    (capacity : Bool → Word) (known : ∀ limit, X86MemoryView.wordAt? (X86MemoryView.memory state)
      (input.frame + BitVec.ofNat 64 (capacityOffset limit)) = some (capacity limit))
    (frameApart : Disjoint (X86WriteWords.written (X86CanonicalSpan.narrow input.frame)
      (List.range frameLayout.size)) output.bytes)
    (codeApart : Disjoint (X86WriteWords.written caller.prologue.code
      (List.range X86P1Sub1Allowance.sub1.size)) output.bytes)
    (budgetApart : Disjoint (receiptBytes caller.fuel.budgetAddress) output.bytes)
    (stackApart : Disjoint (X86WriteWords.written caller.bottom (List.range 56)) output.bytes)
    (retain : Disjoint output.bytes ret.writes) :
    OutputApart (input.arguments out profile flags holds flagsKnown quiet capacity known) ret := by
  let args := input.arguments out profile flags holds flagsKnown quiet capacity known
  have writes := out.write_spans profile flags holds flagsKnown quiet
  have footprint : args.outputBytes = output.bytes := writes.1
  have excludesFrame (offset n : Nat) (inside : offset + n < frameLayout.size) :
      X86WriteWords.physicalAddress (X86CanonicalSpan.narrow (input.frame + BitVec.ofNat 64 offset)) n
        ∉ args.outputBytes := by
    rw [footprint]
    exact (Finset.disjoint_left.mp frameApart) (inside_span _ _ _ _ input.frameArea inside)
  change OutputApart args ret
  refine ⟨writes.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i n within
    let slot := (X86BoundedStore.layout (X86P1Sub1Output.Stores.instructionAt i)).region
    change X86WriteWords.physicalAddress
      (X86CanonicalSpan.narrow (input.frame + BitVec.ofNat 64 (16 * slot.val))) n ∉ args.outputBytes
    apply excludesFrame
    change 16 * slot.val + n < 192
    have := slot.isLt
    omega
  · intro i n within
    let slot := (X86BoundedStore.layout (X86P1Sub1Output.Stores.instructionAt i)).region
    change X86WriteWords.physicalAddress
      (X86CanonicalSpan.narrow (input.frame + BitVec.ofNat 64 (16 * slot.val + 8))) n ∉ args.outputBytes
    apply excludesFrame
    change 16 * slot.val + 8 + n < 192
    have := slot.isLt
    omega
  · intro offset byte present
    have within : offset < X86P1Sub1Allowance.sub1.size := by
      by_contra beyond
      simp [P1Capture.Program.view, beyond] at present
    rw [footprint]
    exact (Finset.disjoint_left.mp codeApart)
      (List.mem_toFinset.mpr (List.mem_map.mpr ⟨offset, List.mem_range.mpr within, rfl⟩))
  · intro n within
    rw [footprint]
    exact (Finset.disjoint_left.mp budgetApart)
      (List.mem_toFinset.mpr (List.mem_map.mpr ⟨n, List.mem_range.mpr within, rfl⟩))
  · intro n within
    rw [footprint]
    have inside : n < 56 := by omega
    exact (Finset.disjoint_left.mp stackApart)
      (List.mem_toFinset.mpr (List.mem_map.mpr ⟨n, List.mem_range.mpr inside, rfl⟩))
  · intro slot n within
    have point : (address caller.prologue.bottom.toInt (8 * slot.val)).toInt =
        caller.prologue.bottom.toInt + 8 * slot.val :=
      X86Prologue.stack_int caller.prologue slot.val (by have := slot.isLt; omega)
    have coordinate : X86WriteWords.physicalAddress (address caller.prologue.bottom.toInt (8 * slot.val)) n =
        X86WriteWords.physicalAddress caller.bottom (8 + 8 * slot.val + n) := by
      unfold X86WriteWords.physicalAddress
      rw [point, ← caller.step]
      simp only [address, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.add_assoc]
    rw [footprint, coordinate]
    have inside : 8 + 8 * slot.val + n < 56 := by have := slot.isLt; omega
    exact (Finset.disjoint_left.mp stackApart)
      (List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, List.mem_range.mpr inside, rfl⟩))
  · rw [footprint]
    exact retain

theorem OutputRow.store_address {state : State} (row : OutputRow state) (args : Arguments state) (field : Fin 4) :
    (args.stores field).data = address (X86CanonicalSpan.narrow row.base).toInt (8 * field.val) := by
  let store := args.stores field
  have base := (X86P1Sub1Output.Stores.source_fields field).2.2.1
  have known : lookup state (X86BoundedStore.physical 5) = some store.pointer := by
    simpa only [store, X86BoundedStore.layout, base] using store.pointerKnown
  have pointer := Option.some.inj (known.symm.trans row.pointer)
  have inside : 8 * field.val < 32 := by have := field.isLt; omega
  have represented := X86CanonicalSpan.offset_representation row.base 32 (8 * field.val) (by decide)
    row.extent inside
  have effective := store.effective
  rw [pointer, store_offset] at effective
  apply BitVec.eq_of_toInt_eq
  have signed := congrArg BitVec.toInt (effective.symm.trans represented.symm)
  simpa only [BitVec.toInt_signExtend_of_le (by decide : 48 ≤ 64)] using signed

def InputRows.ruleResult {state : State} (rows : InputRows state) (used limit : Word) : ExitStatus × Option Claim :=
  match substitute1? (rows.claim 0) (rows.claim 1) (rows.claim 2) (rows.claim 3) with
  | none => (.refused, none)
  | some claim => if used.toNat < limit.toNat then (.completed, some claim) else (.unsupported, none)

theorem InputRows.ruleResult_status {state : State} (rows : InputRows state) (args : Arguments state) :
    args.expectedExit = (rows.ruleResult (args.capacity.value false) (args.capacity.value true)).1 := by
  by_cases guard : Substitute1Guard (rows.claim 0) (rows.claim 1) (rows.claim 2) (rows.claim 3)
  · have compares := (rows.guard_iff args).mpr guard
    by_cases room : (args.capacity.value false).toNat < (args.capacity.value true).toNat <;>
      simp [Arguments.expectedExit, InputRows.ruleResult, substitute1?, compares, guard, room]
  · have compares := mt (rows.guard_iff args).mp guard
    simp [Arguments.expectedExit, InputRows.ruleResult, substitute1?, compares, guard]

theorem InputRows.ruleResult_publishes {state : State} (rows : InputRows state) (used limit : Word)
    (claim : Claim) (publication : (rows.ruleResult used limit).2 = some claim) :
    (rows.ruleResult used limit).1 = .completed ∧ claim = rows.conclusion ∧
      substitute1? (rows.claim 0) (rows.claim 1) (rows.claim 2) (rows.claim 3) = some claim := by
  by_cases guard : Substitute1Guard (rows.claim 0) (rows.claim 1) (rows.claim 2) (rows.claim 3)
  · by_cases room : used.toNat < limit.toNat
    · have same : rows.conclusion = claim := by
        simpa [InputRows.ruleResult, InputRows.conclusion, substitute1?, guard, room] using publication
      subst claim
      simp [InputRows.ruleResult, InputRows.conclusion, substitute1?, guard, room]
    · simp [InputRows.ruleResult, substitute1?, guard, room] at publication
  · simp [InputRows.ruleResult, substitute1?, guard] at publication

private theorem InputRows.no_publication {state : State} (rows : InputRows state) (used limit : Word)
    (unpublished : (rows.ruleResult used limit).2 = none) :
    (rows.ruleResult used limit).1 ≠ .completed := by
  cases proposal : substitute1? (rows.claim 0) (rows.claim 1) (rows.claim 2) (rows.claim 3) with
  | none => simp [InputRows.ruleResult, proposal]
  | some claim =>
    by_cases room : used.toNat < limit.toNat <;> simp [InputRows.ruleResult, proposal, room] at unpublished ⊢

private theorem output_outside_spills {state : State} {caller : CallerInputs state}
    {args : Arguments state} {ret : ReturnInputs caller} (apart : OutputApart args ret) :
    Disjoint args.outputBytes (spillBytes caller.prologue.bottom caller.bottom) := by
  refine Finset.disjoint_left.mpr ?_
  intro key output saved
  rcases Finset.mem_union.mp saved with five | last
  · unfold X86Prologue.writes X86WriteWords.written at five
    obtain ⟨i, range, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp five)
    have inside := List.mem_range.mp range
    let slot : Fin 6 := ⟨i / 8, by omega⟩
    have within : i % 8 < 8 := Nat.mod_lt _ (by decide)
    have lower : -(2 ^ 47 : Int) ≤ caller.prologue.bottom.toInt := by
      simpa using BitVec.le_toInt caller.prologue.bottom
    have atSlot := address_toInt caller.prologue.bottom.toInt lower caller.prologue.stackUpper
      (8 * slot.val) (by dsimp [slot]; omega)
    have physical : X86WriteWords.physicalAddress (address caller.prologue.bottom.toInt (8 * slot.val)) (i % 8) =
        X86WriteWords.physicalAddress caller.prologue.bottom i := by
      unfold X86WriteWords.physicalAddress
      rw [atSlot, address, address, Int.add_assoc, ← Int.natCast_add]
      have index : 8 * slot.val + i % 8 = i := by dsimp [slot]; omega
      rw [index]
    exact apart.saved slot (i % 8) within (physical ▸ output)
  · unfold X86WriteWords.written at last
    obtain ⟨i, range, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp last)
    exact apart.bottom i (List.mem_range.mp range) output

theorem refines_substitute1 (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (caller : CallerInputs state)
    (args : Arguments state) (apart : args.Apart (spillBytes caller.prologue.bottom caller.bottom))
    (ret : ReturnInputs caller) (outputApart : OutputApart args ret) (inputs : InputRows state)
    (output : OutputRow state) :
    let result := inputs.ruleResult (args.capacity.value false) (args.capacity.value true)
    ∃ steps after,
      (@X86FuelPrefix.fetches (handlers other extra) vector steps).run state = .ok () after ∧
      ReturnObservation ret
        ((if result.1 = .completed then outputWrites else prefixWrites) ∪ tailRegisters)
        (if result.1 = .completed then args.outputBytes ∪ ret.writes else ret.writes) result.1 after ∧
      (result.2 = none → ∀ field : Fin 4, ∀ byte < 8,
        after.mem.get? (X86CanonicalSpan.physicalKey (output.base + BitVec.ofNat 64 (8 * field.val + byte))) =
          state.mem.get? (X86CanonicalSpan.physicalKey (output.base + BitVec.ofNat 64 (8 * field.val + byte)))) ∧
      ∀ claim, result.2 = some claim → ∀ field : Fin 4, ∀ byte < 8,
        after.mem.get? (X86CanonicalSpan.physicalKey (output.base + BitVec.ofNat 64 (8 * field.val + byte))) =
          some ((BitVec.ofNat 64 (claimField claim field)).extractLsb' (8 * byte) 8) := by
  dsimp only
  obtain ⟨steps, after, executed, returned, written⟩ :=
    returns_from_caller other extra vector state caller args apart ret outputApart
  have outcome := inputs.ruleResult_status args
  rw [outcome] at returned
  refine ⟨steps, after, executed, returned, ?_, ?_⟩
  · intro no field byte inside
    have stopped := inputs.no_publication _ _ no
    have bound : 8 * field.val + byte < 32 := by have := field.isLt; omega
    have physical := X86CanonicalSpan.physicalAddress_nested output.base 32 (8 * field.val) byte
      (by decide) output.extent bound
    rw [← physical, ← output.store_address args field]
    have belongs := X86P1Sub1Output.Stores.byte_in_row (fun i => (args.stores i).data) field byte inside
    apply returned.frame.memory
    rw [if_neg stopped, Finset.mem_union]
    exact not_or_intro ((Finset.disjoint_left.mp (output_outside_spills outputApart)) belongs)
      ((Finset.disjoint_left.mp outputApart.retain) belongs)
  · intro claim yes field byte inside
    obtain ⟨completed, rfl, _⟩ := inputs.ruleResult_publishes _ _ claim yes
    have bound : 8 * field.val + byte < 32 := by have := field.isLt; omega
    have physical := X86CanonicalSpan.physicalAddress_nested output.base 32 (8 * field.val) byte
      (by decide) output.extent bound
    rw [← physical, ← output.store_address args field, ← inputs.output_word args field]
    exact written (outcome.trans completed) field byte inside

theorem refines_substitute1_from_frame (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (caller : CallerInputs state) (ret : ReturnInputs caller)
    (inputs : InputRows state) (input : InputFrame inputs) (output : OutputRow state) (out : OutputFrame input output)
    (profile : X86Readiness.Profile) (flags : BitVec 32) (holds : profile.Holds state)
    (flagsKnown : state.regs.get? .rflags = some flags) (quiet : state.regs.get? .log_register_writes = some false)
    (capacity : Bool → Word) (known : ∀ limit, X86MemoryView.wordAt? (X86MemoryView.memory state)
      (input.frame + BitVec.ofNat 64 (capacityOffset limit)) = some (capacity limit)) :
    let args := input.arguments out profile flags holds flagsKnown quiet capacity known
    let result := inputs.ruleResult (capacity false) (capacity true)
    args.Apart (spillBytes caller.prologue.bottom caller.bottom) → OutputApart args ret →
    ∃ steps after,
      (@X86FuelPrefix.fetches (handlers other extra) vector steps).run state = .ok () after ∧
      ReturnObservation ret
        ((if result.1 = .completed then outputWrites else prefixWrites) ∪ tailRegisters)
        (if result.1 = .completed then args.outputBytes ∪ ret.writes else ret.writes) result.1 after ∧
      (result.2 = none → ∀ field : Fin 4, ∀ byte < 8,
        after.mem.get? (X86CanonicalSpan.physicalKey (output.base + BitVec.ofNat 64 (8 * field.val + byte))) =
          state.mem.get? (X86CanonicalSpan.physicalKey (output.base + BitVec.ofNat 64 (8 * field.val + byte)))) ∧
      ∀ claim, result.2 = some claim → ∀ field : Fin 4, ∀ byte < 8,
        after.mem.get? (X86CanonicalSpan.physicalKey (output.base + BitVec.ofNat 64 (8 * field.val + byte))) =
          some ((BitVec.ofNat 64 (claimField claim field)).extractLsb' (8 * byte) 8) := by
  intro args result apart outputApart
  exact refines_substitute1 other extra vector state caller args apart ret outputApart inputs output

theorem InputRows.publication_derivable {state : State} (rows : InputRows state) (used limit : Word)
    {axioms : Set Claim} {claim : Claim} (publication : (rows.ruleResult used limit).2 = some claim)
    (premises : ∀ row, Derives axioms (rows.claim row)) : Derives axioms claim :=
  Derives.substitute1 (premises 0) (premises 1) (premises 2) (premises 3)
    (rows.ruleResult_publishes used limit claim publication).2.2

structure CallSpans {state : State} {rows : InputRows state} (input : InputFrame rows)
    (output : OutputRow state) {caller : CallerInputs state} (ret : ReturnInputs caller) : Prop where
  frameSpills : Disjoint (X86WriteWords.written (X86CanonicalSpan.narrow input.frame)
    (List.range frameLayout.size)) (spillBytes caller.prologue.bottom caller.bottom)
  rowsSpills : ∀ row, Disjoint (X86WriteWords.written (X86CanonicalSpan.narrow (rows.base row))
    (List.range 32)) (spillBytes caller.prologue.bottom caller.bottom)
  frameOutput : Disjoint (X86WriteWords.written (X86CanonicalSpan.narrow input.frame)
    (List.range frameLayout.size)) output.bytes
  codeOutput : Disjoint (X86WriteWords.written caller.prologue.code
    (List.range X86P1Sub1Allowance.sub1.size)) output.bytes
  budgetOutput : Disjoint (receiptBytes caller.fuel.budgetAddress) output.bytes
  stackOutput : Disjoint (X86WriteWords.written caller.bottom (List.range 56)) output.bytes
  outputReceipt : Disjoint output.bytes ret.writes

theorem refines_substitute1_from_spans (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (caller : CallerInputs state) (ret : ReturnInputs caller)
    (inputs : InputRows state) (input : InputFrame inputs) (output : OutputRow state) (out : OutputFrame input output)
    (profile : X86Readiness.Profile) (flags : BitVec 32) (holds : profile.Holds state)
    (flagsKnown : state.regs.get? .rflags = some flags) (quiet : state.regs.get? .log_register_writes = some false)
    (capacity : Bool → Word) (known : ∀ limit, X86MemoryView.wordAt? (X86MemoryView.memory state)
      (input.frame + BitVec.ofNat 64 (capacityOffset limit)) = some (capacity limit))
    (apart : CallSpans input output ret) :
    let result := inputs.ruleResult (capacity false) (capacity true)
    let fieldAddress := fun field : Fin 4 => output.base + BitVec.ofNat 64 (8 * field.val)
    ∃ steps after,
      (@X86FuelPrefix.fetches (handlers other extra) vector steps).run state = .ok () after ∧
      ReturnObservation ret
        ((if result.1 = .completed then outputWrites else prefixWrites) ∪ tailRegisters)
        (if result.1 = .completed then output.bytes ∪ ret.writes else ret.writes) result.1 after ∧
      (result.2 = none → ∀ field,
        X86MemoryView.wordAt? (X86MemoryView.memory after) (fieldAddress field) =
          X86MemoryView.wordAt? (X86MemoryView.memory state) (fieldAddress field)) ∧
      ∀ claim, result.2 = some claim →
        (∀ field, X86MemoryView.wordAt? (X86MemoryView.memory after) (fieldAddress field) =
          some (BitVec.ofNat 64 (claimField claim field))) ∧
        ∀ axioms, (∀ row, Derives axioms (inputs.claim row)) → Derives axioms claim := by
  intro result fieldAddress
  have argsApart := input.arguments_apart out profile flags holds flagsKnown quiet capacity known _
    apart.frameSpills apart.rowsSpills
  have outApart := out.output_apart caller ret profile flags holds flagsKnown quiet capacity known
    apart.frameOutput apart.codeOutput apart.budgetOutput apart.stackOutput apart.outputReceipt
  obtain ⟨steps, after, executed, returned, unchanged, written⟩ :=
    refines_substitute1_from_frame other extra vector state caller ret inputs input output out profile flags
      holds flagsKnown quiet capacity known argsApart outApart
  have footprint : (input.arguments out profile flags holds flagsKnown quiet capacity known).outputBytes =
      output.bytes := (out.write_spans profile flags holds flagsKnown quiet).1
  rw [footprint] at returned
  have coordinate (field : Fin 4) (offset : Nat) :
      fieldAddress field + BitVec.ofNat 64 offset = output.base + BitVec.ofNat 64 (8 * field.val + offset) := by
    simp only [fieldAddress, BitVec.add_assoc, ← BitVec.ofNat_add]
  refine ⟨steps, after, executed, returned, ?_, ?_⟩
  · intro none field
    apply X86MemoryView.wordAt?_congr
    intro address member
    obtain ⟨offset, bound, rfl⟩ := Finset.mem_image.mp member
    simp only [X86MemoryView.memory, coordinate]
    exact unchanged none field offset (Finset.mem_range.mp bound)
  · intro claim published
    refine ⟨?_, fun axioms premises => inputs.publication_derivable _ _ published premises⟩
    intro field
    apply (X86MemoryReadback.wordAt?_eq_some_iff _ _ _).mpr
    have offset : output.base.toNat + 8 * field.val < 2 ^ 64 := by
      have := output.extent.1
      have := field.isLt
      omega
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change (output.base + BitVec.ofNat 64 (8 * field.val)).toNat + 8 ≤ 2 ^ 64
      rw [X86CanonicalSpan.add_toNat _ _ offset]
      have := output.extent.1
      have := field.isLt
      omega
    · intro index
      rw [coordinate]
      exact output.extent.2 _ (by have := field.isLt; have := index.isLt; omega)
    · intro index
      simp only [X86MemoryView.memory, coordinate]
      exact written claim published field index.val index.isLt

end Mettapedia.Machines.TIsa.X86P1Sub1Rule

#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Rule.live_export_identity
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Rule.load_layout
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Rule.InputFrame.loadRequest
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Rule.InputRows.load_word
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Rule.InputRows.guard_iff
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Rule.InputRows.output_word
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Rule.OutputRow.store_address
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Rule.refines_substitute1
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Rule.refines_substitute1_from_frame
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Rule.InputFrame.arguments_apart
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Rule.OutputFrame.write_spans
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Rule.OutputFrame.output_apart
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Rule.InputRows.publication_derivable
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Rule.refines_substitute1_from_spans
