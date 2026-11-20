import Mettapedia.Machines.TIsa.X86P1Sub1Guards
import Mettapedia.Machines.TIsa.X86BoundedStore

/-!
# Output construction in the allowance-bearing Micromath sub1 image

The output fields are read by the four captured load spans after the
capacity branch. The checked stores use those four registers as sources.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option Elab.async false

namespace Mettapedia.Machines.TIsa.X86P1Sub1Output

open _root_.X86Registers X86Execution X86RegisterRefinement X86P1Sub1Guards
open X86P1Sub1Allowance (sub1)
open OperandLoads (instructionAt spanAt Request)
open X86BoundedLoad (count physical writes)
local instance : MemoryPrimitives := X86Memory.ordinary

def loadIndex (i : Fin 4) : Fin 18 := ⟨14 + i.val, by have := i.isLt; omega⟩

noncomputable def outputRegister (i : Fin 4) : Fin 16 :=
  physical (instructionAt (loadIndex i)).destination

noncomputable def outputEntry (n : Nat) : Nat :=
  if valid : n < 4 then (spanAt (loadIndex ⟨n, valid⟩)).offset else 1066

noncomputable def outputLoadCount (n : Nat) : Nat :=
  if valid : n < 4 then count (instructionAt (loadIndex ⟨n, valid⟩)) else 0

noncomputable def outputPrefixCount : Nat → Nat
  | 0 => 0
  | n + 1 => outputPrefixCount n + outputLoadCount n

abbrev outputWrites : Finset Register := insert .rbx (insert .r11 PremiseGuards.prefixWrites)

theorem load_routes (i : Fin 4) :
    (spanAt (loadIndex i)).offset + (spanAt (loadIndex i)).length = outputEntry (i.val + 1) ∧
    (instructionAt (loadIndex i)).wide = true := by
  fin_cases i <;> constructor <;> kernel_reflexivity

theorem load_writes (i : Fin 4) :
    writes (instructionAt (loadIndex i)) ⊆ outputWrites ∧
    key (physical (instructionAt (loadIndex i)).base) ∉ outputWrites := by
  fin_cases i <;> exact of_decide_eq_true (by kernel_reflexivity)

theorem other_field_preserved (i j : Fin 4) (different : i ≠ j) :
    key (outputRegister i) ∉ writes (instructionAt (loadIndex j)) := by
  fin_cases i <;> fin_cases j <;>
    first | exact (different rfl).elim | exact of_decide_eq_true (by kernel_reflexivity)

theorem entry_offset : outputEntry 0 = 881 := by kernel_reflexivity

theorem end_offset : outputEntry 4 = 1066 := by kernel_reflexivity

set_option maxHeartbeats 4000000 in
theorem loads_prefix (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (state : State) (base : BitVec 48) (upper : base.toInt + sub1.size < (2 ^ 47 : Int))
    (placed : X86CodePlacement.Placed state base.toInt sub1.view) (mode : X86PlainFetch.Facts state)
    (rip : state.regs.get? .rip = some ((address base.toInt (outputEntry 0)).signExtend 64))
    (request : ∀ i, Request (instructionAt (loadIndex i)) state) (n : Nat) (within : n ≤ 4) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches (outputPrefixCount n)).run state = .ok () after ∧
      after.regs.get? .rip = some ((address base.toInt (outputEntry n)).signExtend 64) ∧
      RegisterFrame outputWrites state after ∧ after.regs.get? .rflags = some flags ∧
      X86ControlFlags.Preserved state after ∧
      ∀ i : Fin 4, i.val < n → lookup after (outputRegister i) = some (request i).value := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  induction n with
  | zero =>
    exact ⟨state, (request 0).flags, X86FuelPrefix.fetches_zero state, rip,
      RegisterFrame.refl _ _, (request 0).flagsKnown, X86ControlFlags.Preserved.refl _, fun _ h => (Nat.not_lt_zero _ h).elim⟩
  | succ n ih =>
    obtain ⟨middle, flags, earlier, atNext, frame, known, control, results⟩ := ih (by omega)
    let i : Fin 4 := ⟨n, by omega⟩
    have dataOnly : outputWrites ⊆ dataRegisters := by decide
    let current := (request i).transport frame (load_writes i).2 (by decide) dataOnly control flags known
    have code := X86CodePlacement.Placed.preserved _ _ placed (X86StateFrame.registerOnly frame) (by simp)
    obtain ⟨after, nextFlags, read, written, value, next, flagsKnown, controlStep⟩ :=
      OperandLoads.executes other extra vector (loadIndex i) middle base upper code
        (PremiseGuards.modeAfter mode frame dataOnly)
        (by simpa only [outputEntry, dif_pos i.isLt, i] using atNext) current
    have stepCount : outputLoadCount n = count (instructionAt (loadIndex i)) := by
      simp only [outputLoadCount, dif_pos i.isLt, i]
    have joined : RegisterFrame outputWrites state after :=
      (frame.trans written).mono (Finset.union_subset (Finset.Subset.refl _) (load_writes i).1)
    refine ⟨after, nextFlags, X86FuelPrefix.fetches_then _ _ state middle after earlier
      (by rw [stepCount]; exact read), ?_, joined, flagsKnown, control.trans controlStep, ?_⟩
    · simpa only [(load_routes i).1, i] using next
    · intro j before
      by_cases same : j = i
      · subst j
        simpa only [outputRegister, (load_routes i).2, X86DataLoad.value, ite_true,
          current, Request.transport] using value
      · have earlierField : j.val < n := by
          have different : j.val ≠ n := fun h => same (Fin.ext h)
          omega
        exact (written.lookup _ (other_field_preserved j i same)).trans (results j earlierField)

open PremiseGuards (leftLoad rightLoad entryOffset prefixCount prefixWrites)

theorem loads_after_checks (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : BitVec 48)
    (upper : base.toInt + sub1.size < (2 ^ 47 : Int))
    (placed : X86CodePlacement.Placed state base.toInt sub1.view) (mode : X86PlainFetch.Facts state)
    (rip : state.regs.get? .rip = some ((address base.toInt (entryOffset 0)).signExtend 64))
    (left : ∀ i, Request (instructionAt (leftLoad i)) state)
    (right : ∀ i, Request (instructionAt (rightLoad i)) state)
    (agrees : ∀ i : Fin 7, (left i).value == (right i).value)
    (capacity : Capacity.Inputs state) (room : (capacity.value false).toNat < (capacity.value true).toNat)
    (request : ∀ i, Request (instructionAt (loadIndex i)) state) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches (prefixCount 7 + 4 + outputPrefixCount 4)).run state = .ok () after ∧
      after.regs.get? .rip = some ((address base.toInt 1066).signExtend 64) ∧
      RegisterFrame outputWrites state after ∧ lookup after 5 = lookup state 5 ∧
      after.regs.get? .rflags = some flags ∧ X86ControlFlags.Preserved state after ∧
      ∀ i : Fin 4, lookup after (outputRegister i) = some (request i).value := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle, flags, checks, pc, frame, _, known, control⟩ :=
    Capacity.executes_after_matches other extra vector state base upper placed mode rip left right agrees capacity
  have dataOnly : prefixWrites ⊆ dataRegisters := by decide
  have included : prefixWrites ⊆ outputWrites := by decide
  let current (i : Fin 4) := (request i).transport frame
    (fun h => (load_writes i).2 (included h)) (by decide) dataOnly control flags known
  have code := X86CodePlacement.Placed.preserved _ _ placed (X86StateFrame.registerOnly frame) (by simp)
  obtain ⟨after, nextFlags, load, atStore, written, flagsKnown, controlStep, fields⟩ :=
    loads_prefix other extra vector middle base upper code (PremiseGuards.modeAfter mode frame dataOnly)
      (by simpa only [entry_offset, if_pos room] using pc) current 4 (by decide)
  have joined : RegisterFrame outputWrites state after :=
    (frame.trans written).mono (Finset.union_subset included (Finset.Subset.refl _))
  exact ⟨after, nextFlags, X86FuelPrefix.fetches_then _ _ state middle after checks load,
    by simpa only [end_offset] using atStore, joined, joined.lookup 5 (by decide),
    flagsKnown, control.trans controlStep, fun i => fields i i.isLt⟩

namespace Stores

open X86P1Sub1Allowance (code_int)

noncomputable def spans : List P1Capture.Span :=
  sub1.spans.filter (fun span => span.kind == "STORE")

theorem span_count : spans.length = 4 := by kernel_reflexivity

noncomputable def spanAt (i : Fin 4) : P1Capture.Span := spans[i.val]'(by rw [span_count]; exact i.isLt)

noncomputable def decode? (i : Fin 4) : Option X86BoundedStore.Instruction := do
  let span := spanAt i
  let reject ← OperandLoads.rejection
  let .instruction (.store .word64 region base offset source) ← sub1.source.body.atPath (← span.path) | none
  if valid : span.offset ≤ reject ∧ (physical base).val % 8 ≠ 4 ∧
      (physical base).val % 8 ≠ 5 ∧ offset.toNat < 2 ^ 31 then
    some ⟨true, source, base, region, ⟨offset.toNat, valid.2.2.2⟩, reject - span.offset, valid.2.1, valid.2.2.1⟩
  else none

theorem decoded (i : Fin 4) : (decode? i).isSome := by
  fin_cases i <;> exact of_decide_eq_true (by kernel_reflexivity)

noncomputable def instructionAt (i : Fin 4) : X86BoundedStore.Instruction :=
  (decode? i).get (decoded i)

open X86BoundedStore (layout bytes displacement)

theorem source_fields (i : Fin 4) :
    (instructionAt i).wide = true ∧ (instructionAt i).region = 4 ∧ (instructionAt i).base = 5 ∧
    (instructionAt i).offset.val = 8 * i.val ∧
    physical (instructionAt i).source = outputRegister i := by
  fin_cases i <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> kernel_reflexivity

noncomputable def entry (n : Nat) : Nat :=
  if valid : n < 4 then (spanAt ⟨n, valid⟩).offset else 1277

theorem starts : entry 0 = 1066 := by kernel_reflexivity

theorem routes (i : Fin 4) : (spanAt i).offset + (spanAt i).length = entry (i.val + 1) := by
  fin_cases i <;> kernel_reflexivity

theorem exact_bytes (i : Fin 4) :
    NativeImage.readRange? sub1.view (spanAt i).offset (bytes (instructionAt i)).length =
      some ((bytes (instructionAt i)).map (BitVec.ofNat 8)) := by
  fin_cases i <;> kernel_reflexivity

theorem changed_store_opcode :
    NativeImage.readRange? (X86P1Sub1Allowance.Controls.patch sub1.view 1103) (spanAt 0).offset
      (bytes (instructionAt 0)).length ≠ some ((bytes (instructionAt 0)).map (BitVec.ofNat 8)) :=
  of_decide_eq_true (by kernel_reflexivity)

theorem geometry (i : Fin 4) :
    let instruction := instructionAt i
    let span := spanAt i
    let bounds := layout instruction
    span.offset + span.length + 3 ≤ sub1.size ∧ span.length = (bytes instruction).length ∧
    span.offset + instruction.reject = 1539 ∧
    (X86Bounds.branchDelta bounds 23).toInt = (instruction.reject : Int) - 23 ∧
    (X86Bounds.branchDelta bounds (X86Bounds.compareAt bounds)).toInt =
      (instruction.reject : Int) - X86Bounds.compareAt bounds ∧
    (X86Bounds.branchDelta bounds (X86Bounds.exitAt bounds)).toInt =
      (instruction.reject : Int) - X86Bounds.exitAt bounds := by
  fin_cases i <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | kernel_reflexivity | exact of_decide_eq_true (by kernel_reflexivity)

structure Destination (instruction : X86BoundedStore.Instruction) (state : State)
    extends X86Bounds.Facts (layout instruction) state where
  within : (pointer - base).toNat + instruction.offset.val + (layout instruction).count.val ≤ length.toNat
  data : BitVec 48
  dataUpper : data.toInt + X86DataStore.byteCount instruction.wide ≤ (2 ^ 47 : Int)
  effective : pointer + (displacement instruction).signExtend 64 = data.signExtend 64
  alignment : X86FrameLoad.alignmentEnabled controls flags visible = false ∨
    data &&& BitVec.ofNat 48 (X86DataStore.byteCount instruction.wide - 1) = (0#48)

theorem executes (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (i : Fin 4) (state : State) (base : BitVec 48) (upper : base.toInt + sub1.size < (2 ^ 47 : Int))
    (placed : X86CodePlacement.Placed state base.toInt sub1.view) (mode : X86PlainFetch.Facts state)
    (rip : state.regs.get? .rip = some ((address base.toInt (spanAt i).offset).signExtend 64))
    (dest : Destination (instructionAt i) state) (value : Word)
    (source : lookup state (outputRegister i) = some value) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches (X86BoundedStore.count (instructionAt i))).run state = .ok () after ∧
      X86StateFrame.Frame X86Bounds.writes (X86DataStore.writes true dest.data) state after ∧
      (∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress dest.data index) =
        some (value.extractLsb' (8 * index) 8)) ∧
      after.regs.get? .rip = some ((address base.toInt (entry (i.val + 1))).signExtend 64) ∧
      after.regs.get? .rflags = some flags ∧ X86ControlFlags.Preserved state after := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  let span := spanAt i
  let instruction := instructionAt i
  obtain ⟨fits, length, target, overflow, short, range⟩ := geometry i
  have inside : span.offset + 3 ≤ sub1.size := by
    change (spanAt i).offset + 3 ≤ sub1.size
    omega
  let origin := X86P1Sub1Fuel.basis base span.offset upper inside mode rip
  have located : origin.address.toInt = base.toInt + span.offset := code_int base upper _ (by omega)
  have upperBound : origin.address.toInt + (sub1.size - span.offset : Nat) < (2 ^ 47 : Int) := by
    rw [located, Nat.cast_sub (by omega)]
    omega
  have bytesFit : X86Bounds.exitAt (layout instruction) + 10 ≤ sub1.size - span.offset := by
    rw [X86BoundedStore.bytes_length] at length
    change X86Bounds.exitAt (layout (instructionAt i)) + 10 ≤ sub1.size - (spanAt i).offset
    omega
  let bounds : X86Bounds.Context (layout instruction) origin.address :=
    { extent := sub1.size - span.offset
      upper := upperBound
      codeWithin := by omega
      rejectWithin := by
        have size := X86P1Sub1Allowance.exported_identity.2.2
        change (instructionAt i).reject ≤ sub1.size - (spanAt i).offset
        omega
      overflowDelta := overflow
      shortDelta := short
      rangeDelta := range }
  let input : X86BoundedStore.Inputs instruction state origin :=
    { toFacts := dest.toFacts
      geometry := bounds
      tailWithin := bytesFit
      loaded := X86CodePlacement.code_of_read_range _ _ _ _ _ _ located placed (exact_bytes i) }
  let writable : X86BoundedStore.Writable input :=
    { value := value
      sourceKnown := by simpa only [instruction, (source_fields i).2.2.2.2] using source
      dataAddress := dest.data
      upper := dest.dataUpper
      effective := dest.effective
      safe := dest.alignment }
  obtain ⟨after, flags, run, frame, written, next, known, _, control, _⟩ :=
    X86BoundedStore.succeeds other extra vector instruction state origin input dest.within writable
  refine ⟨after, flags, run, ?_, ?_, ?_, known, control⟩
  · simpa only [instruction, writable, (source_fields i).1] using frame
  · have qword (wide : Bool) (exactWidth : wide = true)
        (stored : ∀ index < X86DataStore.byteCount wide,
          after.mem.get? (X86WriteWords.physicalAddress dest.data index) =
            some ((X86DataStore.payload wide value).extractLsb' (8 * index) 8)) :
        ∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress dest.data index) =
          some (value.extractLsb' (8 * index) 8) := by
      subst wide
      exact stored
    exact qword _ (source_fields i).1 written
  · rw [located, ← length] at next
    simpa only [address, Int.natCast_add, Int.add_assoc, span, ← routes i] using next

def Destination.transport {instruction : X86BoundedStore.Instruction} {before after : State}
    {registerWrites : Finset Register} {byteWrites : Finset Nat} (dest : Destination instruction before)
    (frame : X86StateFrame.Frame registerWrites byteWrites before after)
    (dataOnly : registerWrites ⊆ dataRegisters)
    (frameFixed : key 7 ∉ registerWrites) (pointerFixed : key (layout instruction).pointer ∉ registerWrites)
    (outsideBase : ∀ index < 8, X86WriteWords.physicalAddress dest.baseAddress index ∉ byteWrites)
    (outsideLength : ∀ index < 8, X86WriteWords.physicalAddress dest.lengthAddress index ∉ byteWrites)
    (control : X86ControlFlags.Preserved before after) (flags : BitVec 32)
    (flagsKnown : after.regs.get? .rflags = some flags) : Destination instruction after :=
  let preserves (r : Register) (outside : r ∉ dataRegisters) :=
    frame.registers r (fun member => outside (dataOnly member))
  let ac := X86ControlFlags.ac_preserved control dest.flags flags dest.flagsKnown flagsKnown
  { dest with
    frameKnown := (frame.lookup 7 frameFixed).trans dest.frameKnown
    pointerKnown := (frame.lookup _ pointerFixed).trans dest.pointerKnown
    controlKnown := (preserves .ctrs (by decide)).trans dest.controlKnown
    visibleKnown := (preserves .seg_visibles (by decide)).trans dest.visibleKnown
    quiet := (preserves .log_register_writes (by decide)).trans dest.quiet
    flags := flags
    flagsKnown := flagsKnown
    baseBytes := fun i h => (frame.memory _ (outsideBase i h)).trans (dest.baseBytes i h)
    lengthBytes := fun i h => (frame.memory _ (outsideLength i h)).trans (dest.lengthBytes i h)
    alignment := by simpa only [X86FrameLoad.alignmentEnabled, ac] using dest.alignment }

def fieldWrites (addresses : Fin 4 → BitVec 48) (i : Fin 4) : Finset Nat :=
  X86DataStore.writes true (addresses i)

def rowWrites (addresses : Fin 4 → BitVec 48) : Finset Nat :=
  Finset.univ.biUnion (fieldWrites addresses)

private theorem field_subset (addresses : Fin 4 → BitVec 48) (i : Fin 4) :
    fieldWrites addresses i ⊆ rowWrites addresses := by
  intro byte present
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, present⟩

private theorem within_field (addresses : Fin 4 → BitVec 48) (i : Fin 4) (index : Nat) (inside : index < 8) :
    X86WriteWords.physicalAddress (addresses i) index ∈ fieldWrites addresses i := by
  unfold fieldWrites X86DataStore.writes X86WriteWords.written
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨index, by
    simpa only [X86DataStore.byteCount, ite_true, List.mem_range] using inside, rfl⟩)

theorem byte_in_row (addresses : Fin 4 → BitVec 48) (i : Fin 4) (index : Nat) (inside : index < 8) :
    X86WriteWords.physicalAddress (addresses i) index ∈ rowWrites addresses :=
  field_subset addresses i (within_field addresses i index inside)

private theorem source_fixed (i : Fin 4) : key (outputRegister i) ∉ X86Bounds.writes :=
  X86BoundedLoad.logical_outside (OperandLoads.instructionAt (loadIndex i)).destination

private theorem pointer_fixed (i : Fin 4) : key (layout (instructionAt i)).pointer ∉ outputWrites := by
  fin_cases i <;> exact of_decide_eq_true (by kernel_reflexivity)

noncomputable def storeCount (n : Nat) : Nat :=
  if valid : n < 4 then X86BoundedStore.count (instructionAt ⟨n, valid⟩) else 0

noncomputable def prefixStoreCount : Nat → Nat
  | 0 => 0
  | n + 1 => prefixStoreCount n + storeCount n

set_option maxHeartbeats 5000000 in
theorem executes_prefix (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : BitVec 48)
    (upper : base.toInt + sub1.size < (2 ^ 47 : Int))
    (placed : X86CodePlacement.Placed state base.toInt sub1.view) (mode : X86PlainFetch.Facts state)
    (rip : state.regs.get? .rip = some ((address base.toInt (entry 0)).signExtend 64))
    (dest : ∀ i, Destination (instructionAt i) state)
    (values : Fin 4 → Word) (source : ∀ i, lookup state (outputRegister i) = some (values i))
    (separate : Pairwise fun i j =>
      Disjoint (fieldWrites (fun i => (dest i).data) i) (fieldWrites (fun i => (dest i).data) j))
    (BaseSafe : ∀ i index, index < 8 → X86WriteWords.physicalAddress (dest i).baseAddress index ∉
      rowWrites (fun i => (dest i).data))
    (LengthSafe : ∀ i index, index < 8 → X86WriteWords.physicalAddress (dest i).lengthAddress index ∉
      rowWrites (fun i => (dest i).data))
    (CodeSafe : ∀ index byte, sub1.view.read index = some byte →
      ((address base.toInt index).signExtend 52).toNat ∉ rowWrites (fun i => (dest i).data))
    (n : Nat) (within : n ≤ 4) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags, (X86FuelPrefix.fetches (prefixStoreCount n)).run state = .ok () after ∧
      after.regs.get? .rip = some ((address base.toInt (entry n)).signExtend 64) ∧
      X86StateFrame.Frame X86Bounds.writes (rowWrites (fun i => (dest i).data)) state after ∧
      after.regs.get? .rflags = some flags ∧ X86ControlFlags.Preserved state after ∧
      ∀ i : Fin 4, i.val < n → ∀ index < 8,
        after.mem.get? (X86WriteWords.physicalAddress (dest i).data index) =
          some ((values i).extractLsb' (8 * index) 8) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  induction n with
  | zero =>
    exact ⟨state, (dest 0).flags, X86FuelPrefix.fetches_zero state, rip, X86StateFrame.Frame.refl _ _ _,
      (dest 0).flagsKnown, X86ControlFlags.Preserved.refl _, fun _ h => (Nat.not_lt_zero _ h).elim⟩
  | succ n ih =>
    obtain ⟨middle, flags, previous, atNext, frame, known, control, results⟩ := ih (by omega)
    let i : Fin 4 := ⟨n, by omega⟩
    have included : X86Bounds.writes ⊆ outputWrites := by decide
    let current := (dest i).transport frame X86Bounds.writes_data (by decide)
      (fun h => pointer_fixed i (included h)) (BaseSafe i) (LengthSafe i) control flags known
    have code := X86CodePlacement.Placed.preserved _ _ placed frame CodeSafe
    have modeNow := PremiseGuards.modeAfterRegisters mode
      (fun r outside => frame.registers r (fun h => outside (X86Bounds.writes_data h)))
    obtain ⟨after, nextFlags, write, written, stored, next, flagsKnown, controlStep⟩ :=
      executes other extra vector i middle base upper code modeNow
        (by simpa only [entry, dif_pos i.isLt, i] using atNext) current (values i)
        ((frame.lookup _ (source_fixed i)).trans (source i))
    have count : storeCount n = X86BoundedStore.count (instructionAt i) := by
      simp only [storeCount, dif_pos i.isLt, i]
    have subset : X86DataStore.writes true current.data ⊆ rowWrites (fun j => (dest j).data) :=
      field_subset (fun j => (dest j).data) i
    have joined : X86StateFrame.Frame X86Bounds.writes (rowWrites (fun i => (dest i).data)) state after :=
      (frame.trans written).mono (Finset.union_subset (Finset.Subset.refl _) (Finset.Subset.refl _))
        (Finset.union_subset (Finset.Subset.refl _) subset)
    refine ⟨after, nextFlags, X86FuelPrefix.fetches_then _ _ state middle after previous
      (by rw [count]; exact write), by simpa only [i] using next, joined, flagsKnown, control.trans controlStep, ?_⟩
    intro j before offset inside
    by_cases same : j = i
    · subst j
      exact stored offset inside
    · have prior : j.val < n := by
        have unequal : j.val ≠ n := fun h => same (Fin.ext h)
        omega
      have elsewhere : X86WriteWords.physicalAddress (dest j).data offset ∉
          X86DataStore.writes true current.data := fun overlap =>
        Finset.disjoint_left.mp (separate same) (within_field _ j offset inside) overlap
      exact (written.memory _ elsewhere).trans (results j prior offset inside)

theorem stores_after_checks (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (state : State) (base : BitVec 48)
    (upper : base.toInt + sub1.size < (2 ^ 47 : Int))
    (placed : X86CodePlacement.Placed state base.toInt sub1.view) (mode : X86PlainFetch.Facts state)
    (rip : state.regs.get? .rip = some ((address base.toInt (entryOffset 0)).signExtend 64))
    (left : ∀ i, Request (OperandLoads.instructionAt (leftLoad i)) state)
    (right : ∀ i, Request (OperandLoads.instructionAt (rightLoad i)) state)
    (agrees : ∀ i : Fin 7, (left i).value == (right i).value)
    (capacity : Capacity.Inputs state) (room : (capacity.value false).toNat < (capacity.value true).toNat)
    (request : ∀ i, Request (OperandLoads.instructionAt (loadIndex i)) state)
    (dest : ∀ i, Destination (instructionAt i) state)
    (separate : Pairwise fun i j =>
      Disjoint (fieldWrites (fun i => (dest i).data) i) (fieldWrites (fun i => (dest i).data) j))
    (baseSafe : ∀ i index, index < 8 → X86WriteWords.physicalAddress (dest i).baseAddress index ∉
      rowWrites (fun i => (dest i).data))
    (lengthSafe : ∀ i index, index < 8 → X86WriteWords.physicalAddress (dest i).lengthAddress index ∉
      rowWrites (fun i => (dest i).data))
    (codeSafe : ∀ index byte, sub1.view.read index = some byte →
      ((address base.toInt index).signExtend 52).toNat ∉ rowWrites (fun i => (dest i).data)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after flags,
      (X86FuelPrefix.fetches (prefixCount 7 + 4 + outputPrefixCount 4 + prefixStoreCount 4)).run state = .ok () after ∧
      after.regs.get? .rip = some ((address base.toInt 1277).signExtend 64) ∧
      X86StateFrame.Frame outputWrites (rowWrites (fun i => (dest i).data)) state after ∧
      lookup after 5 = lookup state 5 ∧ after.regs.get? .rflags = some flags ∧
      X86ControlFlags.Preserved state after ∧
      ∀ i : Fin 4, ∀ index < 8, after.mem.get? (X86WriteWords.physicalAddress (dest i).data index) =
        some ((request i).value.extractLsb' (8 * index) 8) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle, flags, loads, started, frame, _, known, control, values⟩ :=
    loads_after_checks other extra vector state base upper placed mode rip left right agrees capacity room request
  have dataOnly : outputWrites ⊆ dataRegisters := by decide
  have inOutput : X86Bounds.writes ⊆ outputWrites := by decide
  have memory := X86StateFrame.registerOnly frame
  let current (i : Fin 4) := (dest i).transport memory dataOnly (by decide) (pointer_fixed i)
    (fun _ _ => Finset.notMem_empty _) (fun _ _ => Finset.notMem_empty _) control flags known
  have code := X86CodePlacement.Placed.preserved _ _ placed memory (by simp)
  obtain ⟨after, nextFlags, stores, returned, written, flagsKnown, controlStep, contents⟩ :=
    executes_prefix other extra vector middle base upper code (PremiseGuards.modeAfter mode frame dataOnly)
      (by simpa only [starts] using started) current (fun i => (request i).value) values
      separate baseSafe lengthSafe codeSafe 4 (by decide)
  have joined : X86StateFrame.Frame outputWrites (rowWrites (fun i => (dest i).data)) state after :=
    (memory.trans written).mono (Finset.union_subset (Finset.Subset.refl _) inOutput)
      (Finset.union_subset (Finset.empty_subset _) (Finset.Subset.refl _))
  exact ⟨after, nextFlags, X86FuelPrefix.fetches_then _ _ state middle after loads stores, returned,
    joined, joined.lookup 5 (by decide), flagsKnown, control.trans controlStep, fun i => contents i i.isLt⟩

end Stores

end Mettapedia.Machines.TIsa.X86P1Sub1Output

#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Output.load_routes
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Output.load_writes
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Output.other_field_preserved
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Output.loads_prefix
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Output.loads_after_checks
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Output.Stores.source_fields
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Output.Stores.exact_bytes
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Output.Stores.changed_store_opcode
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Output.Stores.executes
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Output.Stores.executes_prefix
#print axioms Mettapedia.Machines.TIsa.X86P1Sub1Output.Stores.stores_after_checks
