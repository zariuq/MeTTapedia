import Mettapedia.Machines.TIsa.X86AssemblerExecution
import Mettapedia.Machines.TIsa.X86BranchGate

/-!
# Source continuation branches lowered through the checked assembler

Logical control words remain source names. The assembler places their labels;
the native TEST/JZ template keeps its original instruction semantics. Prefix
and continuation chunks share one label environment, including backward links.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.X86BranchCompiler
open _root_.X86Registers X86RegisterRefinement X86RegisterEncoding X86Execution X86Assembler
local instance : MemoryPrimitives := X86Memory.ordinary
universe u
variable {Key : Type u}

def testBytes (register : Fin 16) : List Byte :=
  [rex true register register,0x85,modRM register register]

def body (branch : Control.Branch Key) (register : Fin 16) : List Chunk :=
  [.bytes (testBytes register),.branch (some 4) branch.no.toNat]

def lower (branch : Control.Branch Key) (register : Fin 16) : List Chunk :=
  .label branch.point.toNat :: (body branch register ++ [.label branch.yes.toNat])

theorem body_width (branch : Control.Branch Key) (register : Fin 16) : width (body branch register) = 9 := rfl

theorem lower_width (branch : Control.Branch Key) (register : Fin 16) : width (lower branch register) = 9 := rfl

theorem lower_markers (cursor : Nat) (branch : Control.Branch Key) (register : Fin 16) (tail : List Chunk) :
    markersAt cursor (lower branch register ++ tail) =
      (branch.point.toNat,cursor) :: (branch.yes.toNat,cursor + 9) :: markersAt (cursor + 9) tail := by
  simp [lower,body,markersAt,testBytes,Chunk.width,prefixLength,Nat.add_assoc]

theorem gate_code_bytes (register : Fin 16) (word : BitVec 32) :
    (X86BranchGate.code register word).map (BitVec.ofNat 8) =
      testBytes register ++ (opcodeBytes (some 4) ++ RelativeBranch.encode32 word) := by
  rw [X86AssemblerExecution.encode32_list]
  simp only [X86BranchGate.code,List.map_append,List.map_cons,List.map_nil,List.map_map,
    Function.comp_def,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  rfl

theorem lower_emitted (labels : Labels) (cursor : Nat) (branch : Control.Branch Key) (register : Fin 16)
    (tail : List Chunk) (emission : Emission) (emitted : emitAt labels cursor (lower branch register ++ tail) = some emission) :
    ∃ target operand remaining,
      lookup labels branch.no.toNat = some target ∧ RelativeBranch.encodeNear? (cursor + 5) target = some operand ∧
      emitAt labels (cursor + 9) tail = some remaining ∧
      emission.bytes = testBytes register ++ ((opcodeBytes (some 4) ++ operand) ++ remaining.bytes) ∧
      emission.fixups = ⟨cursor + 3,some 4,branch.no.toNat,target⟩ :: remaining.fixups := by
  change ((lookup labels branch.no.toNat).bind (fun target =>
    (RelativeBranch.encodeNear? (cursor + 5) target).bind (fun operand =>
      (emitAt labels (cursor + 9) tail).bind (fun remaining => some (Emission.mk
        ((opcodeBytes (some 4) ++ operand) ++ remaining.bytes)
        (Fixup.mk (cursor + 3) (some 4) branch.no.toNat target :: remaining.fixups)))))).bind
    (fun later => some (Emission.mk (testBytes register ++ later.bytes) later.fixups)) = some emission at emitted
  simp only [Option.bind_assoc,Option.bind_some] at emitted
  cases found : lookup labels branch.no.toNat with
  | none => simp [found] at emitted
  | some target =>
    rw [found] at emitted
    change (RelativeBranch.encodeNear? (cursor + 5) target).bind (fun operand =>
      (emitAt labels (cursor + 9) tail).bind (fun remaining => some (Emission.mk
        (testBytes register ++ ((opcodeBytes (some 4) ++ operand) ++ remaining.bytes))
        (Fixup.mk (cursor + 3) (some 4) branch.no.toNat target :: remaining.fixups)))) = some emission at emitted
    cases encoded : RelativeBranch.encodeNear? (cursor + 5) target with
    | none => simp [encoded] at emitted
    | some operand =>
      rw [encoded] at emitted
      change (emitAt labels (cursor + 9) tail).bind (fun remaining => some (Emission.mk
        (testBytes register ++ ((opcodeBytes (some 4) ++ operand) ++ remaining.bytes))
        (Fixup.mk (cursor + 3) (some 4) branch.no.toNat target :: remaining.fixups))) = some emission at emitted
      cases later : emitAt labels (cursor + 9) tail with
      | none => simp [later] at emitted
      | some remaining =>
        rw [later] at emitted
        change some (Emission.mk
          (testBytes register ++ ((opcodeBytes (some 4) ++ operand) ++ remaining.bytes))
          (Fixup.mk (cursor + 3) (some 4) branch.no.toNat target :: remaining.fixups)) = some emission at emitted
        have same := Option.some.inj emitted
        cases same
        exact ⟨target,operand,remaining,rfl,encoded,rfl,rfl,rfl⟩

structure Compilation (branch : Control.Branch Key) (register : Fin 16)
    (first tail : List Chunk) (emission : Emission) where
  labels : Labels
  resolved : labelsAt 0 (first ++ (lower branch register ++ tail)) = some labels
  point : lookup labels branch.point.toNat = some (width first)
  yes : lookup labels branch.yes.toNat = some (width first + 9)
  target : Nat
  no : lookup labels branch.no.toNat = some target
  targetInside : target ≤ emission.bytes.length
  word : BitVec 32
  signed : word.toInt = (target : Int) - (width first : Int) - 9
  leading : List Byte
  remaining : List Byte
  leadingLength : leading.length = width first
  bytes : emission.bytes = leading ++
    ((X86BranchGate.code register word).map (BitVec.ofNat 8) ++ remaining)

theorem ofAssembly (branch : Control.Branch Key) (register : Fin 16) (first tail : List Chunk) (emission : Emission)
    (assembled : assemble (first ++ (lower branch register ++ tail)) = some emission) :
    Nonempty (Compilation branch register first tail emission) := by
  unfold assemble at assembled
  cases resolved : labelsAt 0 (first ++ (lower branch register ++ tail)) with
  | none => simp [resolved] at assembled
  | some labels =>
    rw [resolved] at assembled
    change emitAt labels 0 (first ++ (lower branch register ++ tail)) = some emission at assembled
    obtain ⟨left,right,firstEmitted,rightEmitted,whole⟩ :=
      emitAt_split labels 0 first (lower branch register ++ tail) emission assembled
    have initialLength := (emitAt_correct labels 0 first left firstEmitted).1
    have rightRun : emitAt labels (width first) (lower branch register ++ tail) = some right := by
      simpa only [Nat.zero_add] using rightEmitted
    obtain ⟨target,operand,remaining,found,encoded,later,headBytes,_fixups⟩ :=
      lower_emitted labels (width first) branch register tail right rightRun
    obtain ⟨fits,operandEq⟩ := (RelativeBranch.encodeNear?_iff _ _ _).mp encoded
    let word := BitVec.ofInt 32 (RelativeBranch.displacement (width first + 5) target)
    have wordValue : word.toInt = RelativeBranch.displacement (width first + 5) target :=
      BitVec.toInt_ofInt_eq_self (by decide) fits.1 fits.2
    have pointMarker : (branch.point.toNat,width first) ∈
        markersAt 0 (first ++ (lower branch register ++ tail)) := by
      rw [markersAt_append,Nat.zero_add,lower_markers]
      exact List.mem_append_right _ List.mem_cons_self
    have yesMarker : (branch.yes.toNat,width first + 9) ∈
        markersAt 0 (first ++ (lower branch register ++ tail)) := by
      rw [markersAt_append,Nat.zero_add,lower_markers]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have targetRange := labels_inside 0 (first ++ (lower branch register ++ tail)) labels resolved
      (branch.no.toNat,target) (lookup_member labels branch.no.toNat target found)
    have length := (emitAt_correct labels 0 (first ++ (lower branch register ++ tail)) emission assembled).1
    refine ⟨{
      labels := labels
      resolved := resolved
      point := label_lookup 0 _ labels resolved branch.point.toNat (width first) pointMarker
      yes := label_lookup 0 _ labels resolved branch.yes.toNat (width first + 9) yesMarker
      target := target
      no := found
      targetInside := by rw [length]; simpa only [Nat.zero_add] using targetRange.2
      word := word
      signed := by rw [wordValue]; unfold RelativeBranch.displacement; omega
      leading := left.bytes
      remaining := remaining.bytes
      leadingLength := initialLength
      bytes := ?_ }⟩
    rw [whole]
    change left.bytes ++ right.bytes = _
    rw [headBytes,gate_code_bytes]
    rw [operandEq]
    simp only [word,List.append_assoc]

theorem Compilation.header_inside {branch : Control.Branch Key} {register : Fin 16}
    {first tail : List Chunk} {emission : Emission} (compiled : Compilation branch register first tail emission) :
    width first + 9 ≤ emission.bytes.length := by
  rw [compiled.bytes,List.length_append,List.length_append,List.length_map,X86BranchGate.code_length,
    compiled.leadingLength]
  omega

theorem Compilation.window {branch : Control.Branch Key} {register : Fin 16}
    {first tail : List Chunk} {emission : Emission} (compiled : Compilation branch register first tail emission)
    (index byte : Nat) (present : (X86BranchGate.code register compiled.word)[index]? = some byte) :
    emission.bytes[width first + index]? = some (BitVec.ofNat 8 byte) := by
  have within : index < 9 := by
    have bound := (List.getElem?_eq_some_iff.mp present).1
    simpa only [X86BranchGate.code_length] using bound
  rw [compiled.bytes,List.getElem?_append_right (by rw [compiled.leadingLength]; omega),compiled.leadingLength,
    Nat.add_sub_cancel_left,List.getElem?_append_left (by rw [List.length_map,X86BranchGate.code_length]; exact within),
    List.getElem?_map,present]
  rfl

def nativeInput (branch : Control.Branch Key) (register : Fin 16) (first tail : List Chunk) (emission : Emission)
    (compiled : Compilation branch register first tail emission) (native : State) (base : Int)
    (origin : X86LegacyFetch.Basis native) (lowerBound : -(2 ^ 47 : Int) ≤ base)
    (upper : base + emission.bytes.length + 3 < (2 ^ 47 : Int))
    (location : origin.address.toInt = base + width first)
    (loaded : X86CodePlacement.Placed native base (X86Assembler.view emission.bytes))
    (value : Word) (known : X86RegisterRefinement.lookup native register = some value)
    (flags : BitVec 32) (flagsKnown : native.regs.get? .rflags = some flags)
    (quiet : native.regs.get? .log_register_writes = some false) : X86BranchGate.Inputs native register := by
  refine {
    toBasis := origin
    value := value
    flags := flags
    valueKnown := known
    flagsKnown := flagsKnown
    quiet := quiet
    upper := by rw [location]; have := compiled.header_inside; omega
    displacement := compiled.word
    target := address base compiled.target
    jump := ?_
    loaded := ?_ }
  · rw [address_toInt base lowerBound (by omega : base + emission.bytes.length < (2 ^ 47 : Int))
      compiled.target compiled.targetInside,location,compiled.signed]
    omega
  · intro index byte present
    have observed := loaded (width first + index) (BitVec.ofNat 8 byte) (compiled.window index byte present)
    have shifted : address base (width first + index) = address origin.address.toInt index := by
      unfold address
      rw [location]
      congr 1
      omega
    simpa only [shifted] using observed

structure Entry (register : Fin 16) (start : Nat) (emission : Emission) (native : State) where
  base : Int
  origin : X86LegacyFetch.Basis native
  lower : -(2 ^ 47 : Int) ≤ base
  upper : base + emission.bytes.length + 3 < (2 ^ 47 : Int)
  location : origin.address.toInt = base + start
  loaded : X86CodePlacement.Placed native base (X86Assembler.view emission.bytes)
  value : Word
  known : X86RegisterRefinement.lookup native register = some value
  flags : BitVec 32
  flagsKnown : native.regs.get? .rflags = some flags
  quiet : native.regs.get? .log_register_writes = some false

def chosen (branch : Control.Branch Key) (value : Word) : Word := if value = (0#64) then branch.no else branch.yes

def chosenOffset {branch : Control.Branch Key} {register : Fin 16} {first tail : List Chunk} {emission : Emission}
    (compiled : Compilation branch register first tail emission) (value : Word) : Nat :=
  if value = (0#64) then compiled.target else width first + 9

section Execution
variable [OtherOpcodeHandlers] [VectorOpcodeHandlers]
variable {branch : Control.Branch Key} {register : Fin 16} {first tail : List Chunk} {emission : Emission} {native : State}

structure Result [DecidableEq Key] (compiled : Compilation branch register first tail emission)
    (entry : Entry register (width first) emission native) (keys : Finset (Control.Location Key))
    (before : Control.Location Key → Word) (after : State) : Prop where
  source : ∃ invocation : CellEffects.Invocation branch.recipe,
    CellEffects.system.Enables (Cells.encode keys before) invocation ∧
      CellEffects.system.fire (Cells.encode keys before) invocation =
        Cells.encode keys (Function.update before (.inl branch.activation) (chosen branch entry.value))
  sourceStep : (CellEffects.profile [branch.recipe]).theory.rewrites (Cells.encode keys before)
    (Cells.encode keys (Function.update before (.inl branch.activation) (chosen branch entry.value)))
  inputLabel : lookup compiled.labels (before (.inl branch.activation)).toNat = some (width first)
  outputLabel : lookup compiled.labels (chosen branch entry.value).toNat = some (chosenOffset compiled entry.value)
  run : (X86FuelPrefix.fetches 2).run native = .ok () after
  frame : RegisterFrame X86BranchGate.writes native after
  pointer : after.regs.get? .rip = some ((address entry.base (chosenOffset compiled entry.value)).signExtend 64)
  condition : X86RegisterRefinement.lookup after register = some entry.value
  flags : ∃ flags : BitVec 32, after.regs.get? .rflags = some flags
  control : X86ControlFlags.Preserved native after
  image : X86CodePlacement.Placed after entry.base (X86Assembler.view emission.bytes)
  prefixes : ∀ count ≤ 2, ∀ observed, (X86FuelPrefix.fetches count).run native = .ok () observed →
    RegisterFrame X86BranchGate.writes native observed

end Execution

theorem Result.next_entry [DecidableEq Key] [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    {branch : Control.Branch Key} {register : Fin 16} {first tail : List Chunk} {emission : Emission}
    {native after : State} {compiled : Compilation branch register first tail emission}
    {entry : Entry register (width first) emission native} {keys : Finset (Control.Location Key)}
    {before : Control.Location Key → Word} (correct : Result compiled entry keys before after)
    (nextRegister : Fin 16) (value : Word) (known : X86RegisterRefinement.lookup native nextRegister = some value) :
    ∃ next : Entry nextRegister (chosenOffset compiled entry.value) emission after,
      next.base = entry.base ∧ next.value = value := by
  have inside : chosenOffset compiled entry.value ≤ emission.bytes.length := by
    unfold chosenOffset
    split
    · exact compiled.targetInside
    · exact compiled.header_inside
  let target := address entry.base (chosenOffset compiled entry.value)
  have position : target.toInt = entry.base + (chosenOffset compiled entry.value : Nat) :=
    address_toInt entry.base entry.lower (by have := entry.upper; omega) _ inside
  have targetUpper : target.toInt + 3 < (2 ^ 47 : Int) := by rw [position]; have := entry.upper; omega
  let nextOrigin := X86StateFrame.basisAt native after entry.origin
    (X86StateFrame.registerOnly correct.frame) X86BranchGate.writes_data target targetUpper correct.pointer
  obtain ⟨flags,flagsKnown⟩ := correct.flags
  refine ⟨{
    base := entry.base
    origin := nextOrigin
    lower := entry.lower
    upper := entry.upper
    location := position
    loaded := correct.image
    value := value
    known := ?_
    flags := flags
    flagsKnown := flagsKnown
    quiet := ?_ },rfl,rfl⟩
  · exact (correct.frame.lookup nextRegister (by fin_cases nextRegister <;> decide)).trans known
  · exact (correct.frame.registers .log_register_writes (by decide)).trans entry.quiet

theorem realizes_compiled [DecidableEq Key] (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (branch : Control.Branch Key) (register : Fin 16) (first tail : List Chunk)
    (emission : Emission) (compiled : Compilation branch register first tail emission)
    (native : State) (entry : Entry register (width first) emission native)
    (keys : Finset (Control.Location Key)) (before : Control.Location Key → Word)
    (included : branch.recipe.support ⊆ keys) (current : before (.inl branch.activation) = branch.point)
    (reads : before (.inr branch.condition) = entry.value) (canonical : entry.value = 0 ∨ entry.value = 1) :
    letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, Result compiled entry keys before after := by
  let : OtherOpcodeHandlers := X86BranchGate.handlers other extra
  let : VectorOpcodeHandlers := vector
  let input := nativeInput branch register first tail emission compiled native entry.base entry.origin
    entry.lower entry.upper entry.location entry.loaded entry.value entry.known entry.flags entry.flagsKnown entry.quiet
  have selected : branch.target? (before (.inr branch.condition)) = some (chosen branch entry.value) := by
    rw [reads,branch.target?_iff]
    rcases canonical with zero | one
    · exact Or.inl ⟨zero,by simp [chosen,zero]⟩
    · exact Or.inr ⟨one,by simp [chosen,one]⟩
  obtain ⟨invocation,enabled,fired⟩ := branch.realized keys before (chosen branch entry.value) included current selected
  obtain ⟨after,flags,executed,framed,retained,knownFlags,pointer,control⟩ :=
    X86BranchGate.executes_control other extra vector native register input
  have fallthrough : address entry.origin.address.toInt 9 = address entry.base (width first + 9) := by
    unfold address
    rw [entry.location]
    congr 1
    omega
  refine ⟨after,{
    source := ⟨invocation,enabled,fired⟩
    sourceStep := ⟨ULift.up ⟨0,by simp⟩,invocation,enabled,fired.symm⟩
    inputLabel := by rw [current]; exact compiled.point
    outputLabel := ?_
    run := executed
    frame := framed
    pointer := ?_
    condition := retained
    flags := ⟨flags,knownFlags⟩
    control := control
    image := ?_
    prefixes := ?_ }⟩
  · by_cases zero : entry.value = (0#64)
    · simpa only [chosen,chosenOffset,if_pos zero] using compiled.no
    · simpa only [chosen,chosenOffset,if_neg zero] using compiled.yes
  · change after.regs.get? .rip = some
      ((if entry.value = (0#64) then address entry.base compiled.target else address entry.origin.address.toInt 9).signExtend 64) at pointer
    by_cases zero : entry.value = (0#64)
    · simpa only [chosenOffset,if_pos zero] using pointer
    · simpa only [chosenOffset,if_neg zero,fallthrough] using pointer
  · intro index byte present
    rw [framed.memory]
    exact entry.loaded index byte present
  · intro count within observed candidate
    obtain ⟨proved,executedPrefix,prefixFrame⟩ := X86BranchGate.prefix_frame other extra vector native register input count within
    have same := X86FuelPrefix.fetches_deterministic count native proved observed executedPrefix candidate
    subst observed
    exact prefixFrame

theorem realizes [DecidableEq Key] (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (branch : Control.Branch Key) (register : Fin 16) (first tail : List Chunk)
    (emission : Emission) (assembled : assemble (first ++ (lower branch register ++ tail)) = some emission)
    (native : State) (entry : Entry register (width first) emission native)
    (keys : Finset (Control.Location Key)) (before : Control.Location Key → Word)
    (included : branch.recipe.support ⊆ keys) (current : before (.inl branch.activation) = branch.point)
    (reads : before (.inr branch.condition) = entry.value) (canonical : entry.value = 0 ∨ entry.value = 1) :
    letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ compiled : Compilation branch register first tail emission, ∃ after, Result compiled entry keys before after := by
  obtain ⟨compiled⟩ := ofAssembly branch register first tail emission assembled
  obtain ⟨after,correct⟩ := realizes_compiled other extra vector branch register first tail emission compiled native entry
    keys before included current reads canonical
  exact ⟨compiled,after,correct⟩

theorem reflects [DecidableEq Key] (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) (branch : Control.Branch Key) (register : Fin 16) (first tail : List Chunk)
    (emission : Emission) (assembled : assemble (first ++ (lower branch register ++ tail)) = some emission)
    (native : State) (entry : Entry register (width first) emission native)
    (keys : Finset (Control.Location Key)) (before : Control.Location Key → Word)
    (included : branch.recipe.support ⊆ keys) (current : before (.inl branch.activation) = branch.point)
    (reads : before (.inr branch.condition) = entry.value) (canonical : entry.value = 0 ∨ entry.value = 1)
    (after : State) :
    letI : OtherOpcodeHandlers := X86BranchGate.handlers other extra
    letI : VectorOpcodeHandlers := vector
    (X86FuelPrefix.fetches 2).run native = .ok () after →
      ∃ compiled : Compilation branch register first tail emission, Result compiled entry keys before after := by
  let : OtherOpcodeHandlers := X86BranchGate.handlers other extra
  let : VectorOpcodeHandlers := vector
  intro observed
  obtain ⟨compiled,proved,correct⟩ := realizes other extra vector branch register first tail emission assembled native entry
    keys before included current reads canonical
  have same := X86FuelPrefix.fetches_deterministic 2 native proved after correct.run observed
  subst after
  exact ⟨compiled,correct⟩

end Mettapedia.Machines.TIsa.X86BranchCompiler
