import Mettapedia.Machines.TIsa.X86DataStore
import Mettapedia.Machines.TIsa.X86BoundedLoad

/-!
# Complete checked stores with explicit byte effects

The existing bounds checker and original MOV store compose for both widths.
Only a successful bounds path requires the source-register and data-address
observations. Rejection reads no source payload and changes no memory.
Every fetched prefix preserves the declared register and byte frame.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.X86BoundedStore
open _root_.X86Registers X86RegisterRefinement X86Execution X86FetchEntry
local instance : MemoryPrimitives := X86Memory.ordinary
abbrev physical := X86BoundedLoad.physical

structure Instruction where
  wide : Bool
  source : Fin 12
  base : Fin 12
  region : Fin 9
  offset : X86BoundsArithmetic.Offset
  reject : Nat
  noSib : (physical base).val % 8 ≠ 4
  noStack : (physical base).val % 8 ≠ 5

def layout (instruction : Instruction) : X86Bounds.Layout :=
  ⟨physical instruction.base,instruction.region,instruction.offset,if instruction.wide then 8 else 4,instruction.reject⟩
def displacement (instruction : Instruction) : BitVec 32 := X86PositiveImmediate.immediate32 instruction.offset
def tail (instruction : Instruction) : List Nat :=
  X86DataStore.code instruction.wide (physical instruction.source) (physical instruction.base) (displacement instruction)
def bytes (instruction : Instruction) : List Nat := X86Bounds.code (layout instruction) ++ tail instruction
def count (instruction : Instruction) : Nat := X86Bounds.offsetSteps (layout instruction) + 6
noncomputable abbrev handlers := X86Bounds.handlers

theorem bytes_length (instruction : Instruction) : (bytes instruction).length = X86Bounds.exitAt (layout instruction) + 7 := by
  simp [bytes,tail,X86Bounds.code_length,X86DataStore.code_length]

structure Inputs (instruction : Instruction) (state : State) (origin : X86LegacyFetch.Basis state)
    extends X86Bounds.Facts (layout instruction) state where
  geometry : X86Bounds.Context (layout instruction) origin.address
  tailWithin : X86Bounds.exitAt (layout instruction) + 10 ≤ geometry.extent
  loaded : codeLoaded state origin.address.toInt (bytes instruction)

def Inputs.bounds {instruction : Instruction} {state : State} {origin : X86LegacyFetch.Basis state}
    (input : Inputs instruction state origin) : X86Bounds.Inputs (layout instruction) state origin :=
  { toFacts := input.toFacts
    geometry := input.geometry
    loaded := codeLoaded_left state origin.address.toInt _ _ input.loaded }

def Fits {instruction : Instruction} {state : State} {origin : X86LegacyFetch.Basis state}
    (input : Inputs instruction state origin) : Prop :=
  (input.pointer - input.base).toNat + instruction.offset.val + (layout instruction).count.val ≤ input.length.toNat
instance {instruction : Instruction} {state : State} {origin : X86LegacyFetch.Basis state}
    (input : Inputs instruction state origin) : Decidable (Fits input) := inferInstanceAs (Decidable (_ ≤ _))

structure Writable {instruction : Instruction} {state : State} {origin : X86LegacyFetch.Basis state}
    (input : Inputs instruction state origin) where
  value : Word
  sourceKnown : lookup state (physical instruction.source) = some value
  dataAddress : BitVec 48
  upper : dataAddress.toInt + X86DataStore.byteCount instruction.wide ≤ (2 ^ 47 : Int)
  effective : input.pointer + (displacement instruction).signExtend 64 = dataAddress.signExtend 64
  safe : X86FrameLoad.alignmentEnabled input.controls input.flags input.visible = false ∨
    dataAddress &&& BitVec.ofNat 48 (X86DataStore.byteCount instruction.wide - 1) = (0#48)

theorem succeeds (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (instruction : Instruction) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs instruction state origin) (fits : Fits input) (data : Writable input) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches (count instruction)).run state = .ok () after ∧
      X86StateFrame.Frame X86Bounds.writes (X86DataStore.writes instruction.wide data.dataAddress) state after ∧
      (∀ index < X86DataStore.byteCount instruction.wide,
        after.mem.get? (X86WriteWords.physicalAddress data.dataAddress index) =
          some ((X86DataStore.payload instruction.wide data.value).extractLsb' (8 * index) 8)) ∧
      after.regs.get? .rip = some ((address origin.address.toInt (bytes instruction).length).signExtend 64) ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .log_register_writes = some false ∧
      X86ControlFlags.Preserved state after ∧
      ∀ prefixCount ≤ count instruction, ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run state = .ok () observed →
          X86StateFrame.Frame X86Bounds.writes (X86DataStore.writes instruction.wide data.dataAddress) state observed := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨middle,nextFlags,first,firstFrame,nextKnown,nextRip,control⟩ :=
    X86Bounds.succeeds_control other extra vector (layout instruction) state origin input.bounds fits
  let nextOrigin := rebase state middle origin (firstFrame.mono X86Bounds.writes_data)
    input.geometry.upper (X86Bounds.exitAt (layout instruction)) (by have := input.tailWithin;omega) nextRip
  have located : nextOrigin.address.toInt = origin.address.toInt + X86Bounds.exitAt (layout instruction) := by
    change (address origin.address.toInt (X86Bounds.exitAt (layout instruction))).toInt = _
    exact X86Bounds.position_exact _ _ input.geometry _ (by have := input.tailWithin;omega)
  have tailLoaded : codeLoaded middle nextOrigin.address.toInt (tail instruction) := by
    have loaded := firstFrame.code_preserved origin.address.toInt (bytes instruction) input.loaded
    have right := codeLoaded_right middle origin.address.toInt (X86Bounds.code (layout instruction)) (tail instruction) loaded
    simpa only [located,X86Bounds.code_length] using right
  have ac := X86ControlFlags.ac_preserved control input.flags nextFlags input.flagsKnown nextKnown
  have alignment : X86FrameLoad.alignmentEnabled input.controls nextFlags input.visible =
      X86FrameLoad.alignmentEnabled input.controls input.flags input.visible := by
    simp only [X86FrameLoad.alignmentEnabled,ac]
  let storeInput : X86DataStore.CheckedInputs middle instruction.wide (physical instruction.source)
      (physical instruction.base) (displacement instruction) := {
    nextOrigin with
    noSib := instruction.noSib
    noStack := instruction.noStack
    visible := input.visible
    controls := input.controls
    baseValue := input.pointer
    value := data.value
    flags := nextFlags
    dataAddress := data.dataAddress
    baseKnown := (firstFrame.lookup _ (X86BoundedLoad.logical_outside instruction.base)).trans input.pointerKnown
    sourceKnown := (firstFrame.lookup _ (X86BoundedLoad.logical_outside instruction.source)).trans data.sourceKnown
    controlKnown := (firstFrame.registers .ctrs (by decide)).trans input.controlKnown
    flagsKnown := nextKnown
    visibleKnown := (firstFrame.registers .seg_visibles (by decide)).trans input.visibleKnown
    quiet := (firstFrame.registers .log_register_writes (by decide)).trans input.quiet
    upper := by rw [located];have := input.geometry.upper;have := input.tailWithin;omega
    dataUpper := data.upper
    effective := data.effective
    safe := by rw [alignment];exact data.safe
    loaded := tailLoaded }
  obtain ⟨second,lastFrame⟩ := X86DataStore.executes_checked (handlers other extra) vector middle instruction.wide
    (physical instruction.source) (physical instruction.base) (displacement instruction) storeInput
  let after := X86DataStore.result instruction.wide middle data.dataAddress (address nextOrigin.address.toInt 7) data.value
  have last : X86StateFrame.Frame X86Bounds.writes (X86DataStore.writes instruction.wide data.dataAddress) middle after :=
    lastFrame.mono (by simp [X86Bounds.writes]) (Finset.Subset.refl _)
  have firstWhole : X86StateFrame.Frame X86Bounds.writes (X86DataStore.writes instruction.wide data.dataAddress) state middle :=
    (X86StateFrame.registerOnly firstFrame).mono (Finset.Subset.refl _) (Finset.empty_subset _)
  have combined : X86StateFrame.Frame X86Bounds.writes (X86DataStore.writes instruction.wide data.dataAddress) state after :=
    (firstWhole.trans last).mono (by simp) (by simp)
  have endAt : address nextOrigin.address.toInt 7 = address origin.address.toInt (bytes instruction).length := by
    rw [located,bytes_length]
    simp only [address,Int.natCast_add,Int.add_assoc]
  have lastControl : X86ControlFlags.Preserved middle after := by
    unfold X86ControlFlags.Preserved
    rw [lastFrame.registers .rflags (by decide)]
  refine ⟨after,nextFlags,?_,combined,?_,?_,?_,?_,control.trans lastControl,?_⟩
  · simpa only [count,Nat.add_assoc] using X86FuelPrefix.fetches_then
      (X86Bounds.offsetSteps (layout instruction) + 5) 1 state middle after first second
  · exact X86DataStore.byte_readback middle instruction.wide data.dataAddress _ data.value data.upper
  · change (X86Move.putPointer _ (address nextOrigin.address.toInt 7)).regs.get? .rip = _
    simp only [X86Move.putPointer,Std.ExtDHashMap.get?_insert_self,endAt]
  · exact (lastFrame.registers .rflags (by decide)).trans nextKnown
  · exact (lastFrame.registers .log_register_writes (by decide)).trans
      ((firstFrame.registers .log_register_writes (by decide)).trans input.quiet)
  · have prefixFirst : ∀ count ≤ X86Bounds.offsetSteps (layout instruction) + 5, ∀ reached,
        (X86FuelPrefix.fetches count).run state = .ok () reached →
          X86StateFrame.Frame X86Bounds.writes (X86DataStore.writes instruction.wide data.dataAddress) state reached := by
      intro count within reached run
      exact (X86StateFrame.registerOnly (X86Bounds.success_prefix_frame other extra vector _ state origin input.bounds fits count within reached run)).mono
        (Finset.Subset.refl _) (Finset.empty_subset _)
    have prefixLast : ∀ count ≤ 1, ∀ reached,
        (X86FuelPrefix.fetches count).run middle = .ok () reached →
          X86StateFrame.Frame X86Bounds.writes (X86DataStore.writes instruction.wide data.dataAddress) middle reached := by
      intro count within reached run
      interval_cases count
      · have same := X86FuelPrefix.fetches_deterministic 0 middle middle reached (X86FuelPrefix.fetches_zero middle) run
        subst reached
        exact X86StateFrame.Frame.refl _ _ middle
      · have same := X86FuelPrefix.fetches_deterministic 1 middle after reached second run
        subst reached
        exact last
    simpa only [count,Nat.add_assoc] using X86PrefixComposition.append_frame X86Bounds.writes
      (X86DataStore.writes instruction.wide data.dataAddress) (X86Bounds.offsetSteps (layout instruction) + 5) 1
      state middle first firstWhole prefixFirst prefixLast

theorem rejects (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    (instruction : Instruction) (state : State) (origin : X86LegacyFetch.Basis state)
    (input : Inputs instruction state origin) (refused : ¬ Fits input) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (X86Bounds.boundsSteps (layout instruction) input.base input.pointer input.length)).run state = .ok () after ∧
      RegisterFrame X86Bounds.writes state after ∧
      after.regs.get? .rip = some ((address origin.address.toInt instruction.reject).signExtend 64) ∧
      X86ControlFlags.Preserved state after ∧
      ∀ prefixCount ≤ X86Bounds.boundsSteps (layout instruction) input.base input.pointer input.length, ∀ observed,
        (X86FuelPrefix.fetches prefixCount).run state = .ok () observed → RegisterFrame X86Bounds.writes state observed := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨after,run,frame,rip,control⟩ := X86Bounds.classifies_control other extra vector _ state origin input.bounds
  have notFits : ¬ (input.bounds.pointer - input.bounds.base).toNat +
      (layout instruction).offset.val + (layout instruction).count.val ≤ input.bounds.length.toNat := refused
  rw [if_neg notFits] at rip
  exact ⟨after,run,frame,rip,control,X86Bounds.execution_prefix_frame other extra vector _ state origin input.bounds⟩

#print axioms succeeds
#print axioms rejects
end Mettapedia.Machines.TIsa.X86BoundedStore
