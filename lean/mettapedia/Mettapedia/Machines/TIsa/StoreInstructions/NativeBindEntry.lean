import Mettapedia.Machines.TIsa.StoreInstructions.NativeOccursLoop

/-!
# Shared checked entry for left and right native bindings

Only the first two register moves depend on the side of the
variable. The shared block reads the scratch pointer and capacity
from the frame, checks the unscaled target, and initializes an
empty mark prefix. A capacity refusal touches no memory.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeBindEntry

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads)
open X86PlacedScalar (Code CompareBranch Jump registerCode jumpDelta)
open NativeArenaGeometry (Region)
open NativeAgendaRead (fieldSource)
open NativeWords (Wiring)
open MemoryBinding (Native)
local instance : MemoryPrimitives := X86Memory.ordinary

inductive Side | left | right
  deriving DecidableEq, Repr

def Side.nameSource : Side → Fin 16
  | .left => 10
  | .right => 0

def Side.termSource : Side → Fin 16
  | .left => 2
  | .right => 1

def Side.exiting : Side → UnifierHeaders.Exit
  | .left => .bindLeft
  | .right => .bindRight

def Side.variableHandle : Side → Word → Word → Word
  | .left, l, _ => l
  | .right, _, r => r

def Side.replacement : Side → Word → Word → Word
  | .left, _, r => r
  | .right, l, _ => l

def entryCode (side : Side) (start shared : ℕ) : List ℕ :=
  registerCode 0x89 side.nameSource 8 ++ (registerCode 0x89 side.termSource 9 ++
    X86UnconditionalJump.Block.code (jumpDelta (start + 6) shared))

theorem entry_size (side : Side) (start shared : ℕ) : (entryCode side start shared).length = 11 := rfl

structure EntryPlaced (image : NativeImage.View) (side : Side) (start shared : ℕ) : Prop where
  extent : start + 11 ≤ image.size
  name : Code image start (registerCode 0x89 side.nameSource 8)
  term : Code image (start + 3) (registerCode 0x89 side.termSource 9)
  jump : Jump image (start + 6) shared

theorem entry_placed (image : NativeImage.View) (side : Side) (start shared : ℕ)
    (extent : start + 11 ≤ image.size) (target : shared ≤ image.size) (short : image.size < 2 ^ 31)
    (installed : Code image start (entryCode side start shared)) : EntryPlaced image side start shared := by
  obtain ⟨name, rest⟩ := NativeWords.code_append (show Code image start
    (registerCode 0x89 side.nameSource 8 ++ _) from installed)
  obtain ⟨term, jump⟩ := NativeWords.code_append rest
  refine ⟨extent, name, term, ⟨by omega, target, ?_, jump⟩⟩
  unfold jumpDelta
  rw [BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)]
  omega

noncomputable abbrev handlers := X86IndexedAddress.handlers

abbrev entryClobbers : Finset Register := {.r8, .r9, .rip}

theorem entry_clobbers_data : entryClobbers ⊆ dataRegisters := by decide

theorem fetched_entry (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start shared : ℕ} {before : Native}
    (point : At image before base start) (side : Side) (placed : EntryPlaced image side start shared)
    (query target : Word) (name : lookup before side.nameSource = some query)
    (term : lookup before side.termSource = some target) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 3).run before = .ok () after ∧ X86StateFrame.Frame entryClobbers ∅ before after ∧
      lookup after 8 = some query ∧ lookup after 9 = some target ∧ Nonempty (At image after base shared) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  obtain ⟨a, movedName, nameFrame, keptName, ⟨atTerm⟩⟩ := X86PlacedRegisterMove.executes (handlers other extra)
    vector point (by omega) side.nameSource 8 query name placed.name
  obtain ⟨b, movedTerm, termFrame, keptTerm, ⟨atJump⟩⟩ := X86PlacedRegisterMove.executes (handlers other extra)
    vector atTerm (by omega) side.termSource 9 target ((nameFrame.lookup _ (by cases side <;> decide)).trans term) placed.term
  obtain ⟨after, jumped, jumpFrame, endpoint⟩ := X86PlacedScalar.jump (X86PlacedFrameAddress.nativeBase other)
    extra vector (show At image b base (start + 6) from atJump) placed.jump
  refine ⟨after, X86FuelPrefix.fetches_then 2 1 before b after
    (X86FuelPrefix.fetches_then 1 1 before a b movedName movedTerm) jumped,
    (X86StateFrame.registerOnly ((nameFrame.trans termFrame).trans jumpFrame)).mono (by decide) (by simp),
    ((termFrame.trans jumpFrame).lookup 8 (by decide)).trans keptName, (jumpFrame.lookup 9 (by decide)).trans keptTerm,
    endpoint⟩

def frameCode : List ℕ := registerCode 0x89 4 6
def tableCode : List ℕ := X86DataLoad.code true 7 6 0
def capacityCode : List ℕ := X86DataLoad.code true 2 6 8
def zeroCode : List ℕ := registerCode 0x89 12 1

def setupCode (start loop exhausted : ℕ) : List ℕ :=
  frameCode ++ (tableCode ++ (capacityCode ++ (NativeDecisions.compareBytes .lessUnsigned 9 2 (start + 17) exhausted ++
    (zeroCode ++ X86UnconditionalJump.Block.code (jumpDelta (start + 29) loop)))))

theorem setup_size (start loop exhausted : ℕ) : (setupCode start loop exhausted).length = 34 := rfl

structure SetupPlaced (image : NativeImage.View) (start loop exhausted : ℕ) : Prop where
  extent : start + 34 ≤ image.size
  context : Code image start frameCode
  table : Code image (start + 3) tableCode
  capacity : Code image (start + 10) capacityCode
  reserve : CompareBranch image (start + 17) exhausted .lessUnsigned 9 2
  zero : Code image (start + 26) zeroCode
  jump : Jump image (start + 29) loop

theorem setup_placed (image : NativeImage.View) (start loop exhausted : ℕ)
    (extent : start + 34 ≤ image.size) (loopFits : loop ≤ image.size) (lack : exhausted ≤ image.size)
    (short : image.size < 2 ^ 31) (installed : Code image start (setupCode start loop exhausted)) :
    SetupPlaced image start loop exhausted := by
  obtain ⟨context, tail⟩ := NativeWords.code_append (show Code image start (frameCode ++ _) from installed)
  obtain ⟨table, tail⟩ := NativeWords.code_append tail
  obtain ⟨capacity, tail⟩ := NativeWords.code_append tail
  change Code image (start + 17) _ at tail
  obtain ⟨reserve, tail⟩ := NativeWords.code_append tail
  rw [NativeDecisions.compare_size] at tail
  obtain ⟨zero, jump⟩ := NativeWords.code_append tail
  refine ⟨extent, context, table, capacity, NativeDecisions.compare_placed image _ _ _ _ _ (by omega) lack short reserve,
    zero, ⟨by omega, loopFits, ?_, jump⟩⟩
  unfold jumpDelta
  rw [BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)]
  omega

abbrev setupClobbers : Finset Register := {.rcx, .rdx, .rsi, .rdi, .rflags, .rip}

theorem setup_clobbers_data : setupClobbers ⊆ dataRegisters := by decide

def tableWire : Wiring := ⟨6, by decide, by decide, MemoryBinding.storeEncoding, 7, by decide, by decide⟩
def capacityWire : Wiring := ⟨6, by decide, by decide, MemoryBinding.storeEncoding, 2, by decide, by decide⟩

variable {nodeCapacity edgeCapacity markCapacity agendaCapacity : ℕ}
variable {layout : NativeTermArena.Layout nodeCapacity edgeCapacity} {arena : PackedTerms.Arena}
variable {agendaLayout : NativeAgendaRecords.Layout agendaCapacity} {table : Region markCapacity}

structure Environment (layout : NativeTermArena.Layout nodeCapacity edgeCapacity) (arena : PackedTerms.Arena)
    (agendaLayout : NativeAgendaRecords.Layout agendaCapacity) (table : Region markCapacity)
    (descriptor : WordRegion.Region 2) (native : Native) : Prop where
  source : NativeTermArena.Ready layout arena native
  terms : lookup native 3 = some layout.nodes.pointer
  work : lookup native 5 = some agendaLayout.words.pointer
  pool : Reads native (agendaLayout.metadata.cell 1).address layout.edges.pointer
  stack : lookup native 4 = some descriptor.pointer
  markTable : Reads native (descriptor.cell 0).address (table.atWord 0)
  capacity : Reads native (descriptor.cell 1).address (BitVec.ofNat 64 markCapacity)
  zero : lookup native 12 = some 0
  one : lookup native 13 = some 1
  two : lookup native 14 = some 2

theorem Environment.preserved {descriptor : WordRegion.Region 2} {before after : Native} {regs : Finset Register}
    (input : Environment layout arena agendaLayout table descriptor before) (frame : X86StateFrame.Frame regs ∅ before after)
    (abi : ∀ r ∈ ({3, 4, 5, 12, 13, 14} : Finset (Fin 16)), key r ∉ regs) :
    Environment layout arena agendaLayout table descriptor after :=
  ⟨input.source.preserved frame, (frame.lookup 3 (abi _ (by decide))).trans input.terms,
    (frame.lookup 5 (abi _ (by decide))).trans input.work, input.pool.preserved frame (by simp),
    (frame.lookup 4 (abi _ (by decide))).trans input.stack, input.markTable.preserved frame (by simp),
    input.capacity.preserved frame (by simp), (frame.lookup 12 (abi _ (by decide))).trans input.zero,
    (frame.lookup 13 (abi _ (by decide))).trans input.one, (frame.lookup 14 (abi _ (by decide))).trans input.two⟩

private theorem capacity_nat (table : Region markCapacity) :
    (BitVec.ofNat 64 markCapacity).toNat = markCapacity := by
  by_cases pos : 0 < markCapacity
  · have bound := table.positive_room pos
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rw [show markCapacity = 0 by omega]
    rfl

theorem fetched_setup (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start loop exhausted : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before) (placed : SetupPlaced image start loop exhausted)
    (descriptor : WordRegion.Region 2) (input : Environment layout arena agendaLayout table descriptor before)
    (query target : Word) (name : lookup before 8 = some query) (root : lookup before 9 = some target) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame setupClobbers ∅ before after ∧
      if target.toNat < markCapacity then
        steps = 7 ∧ NativeOccursLoop.Input layout arena agendaLayout table #[] query target after ∧
          Nonempty (At image after base loop)
      else steps = 5 ∧ Nonempty (At image after base exhausted) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent := placed.extent
  have linked : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
  obtain ⟨a, loaded, regFrame, context, ⟨atTable⟩⟩ := X86PlacedRegisterMove.executes (handlers other extra)
    vector point (by omega) 4 6 descriptor.pointer input.stack placed.context
  have initial := X86StateFrame.registerOnly regFrame
  obtain ⟨b, loadedTable, tableFrame, tableBase, ⟨atSize⟩⟩ := (fieldSource descriptor 0).fetch
    (handlers other extra) vector tableWire (table.atWord 0) atTable (controls.transport initial (by decide))
    context (input.markTable.preserved initial (by simp)) (show start + 10 ≤ image.size by omega) placed.table
  have withTable := initial.trans tableFrame
  obtain ⟨c, loadedCapacity, capFrame, cap, ⟨atCheck⟩⟩ := (fieldSource descriptor 1).fetch
    (handlers other extra) vector capacityWire (BitVec.ofNat 64 markCapacity)
    (show At image b base (start + 10) from atSize) (controls.transport withTable (by decide))
    ((tableFrame.lookup 6 (by decide)).trans context) (input.capacity.preserved withTable (by simp))
    (show start + 17 ≤ image.size by omega) placed.capacity
  rw [linked] at loadedTable loadedCapacity
  have checkedInput := withTable.trans capFrame
  obtain ⟨d, guarded, guardFrame, ⟨cursor⟩⟩ := X86PlacedScalar.compare_branch (X86PlacedFrameAddress.nativeBase other)
    extra vector (show At image c base (start + 17) from atCheck) .lessUnsigned 9 2 placed.reserve target _
    ((checkedInput.lookup 9 (by decide)).trans root) cap
  change At image d base
    (if decide (target.toNat < (BitVec.ofNat 64 markCapacity).toNat) then start + 17 + 9 else exhausted) at cursor
  rw [capacity_nat table] at cursor
  have checked := checkedInput.trans (X86StateFrame.registerOnly guardFrame)
  have firstTwo := X86FuelPrefix.fetches_then 1 1 before a b loaded loadedTable
  have firstThree := X86FuelPrefix.fetches_then 2 1 before b c firstTwo loadedCapacity
  have firstFive := X86FuelPrefix.fetches_then 3 2 before c d firstThree guarded
  by_cases room : target.toNat < markCapacity
  · simp only [room, decide_true, if_true] at cursor
    obtain ⟨e, zeroed, zeroFrame, index, ⟨atJump⟩⟩ := X86PlacedRegisterMove.executes (handlers other extra)
      vector (show At image d base (start + 26) from cursor) (by omega) 12 1 0
      ((checked.lookup 12 (by decide)).trans input.zero) placed.zero
    obtain ⟨after, jumped, jumpFrame, endpoint⟩ := X86PlacedScalar.jump (X86PlacedFrameAddress.nativeBase other)
      extra vector (show At image e base (start + 29) from atJump) placed.jump
    have all : X86StateFrame.Frame setupClobbers ∅ before after :=
      (checked.trans (X86StateFrame.registerOnly (zeroFrame.trans jumpFrame))).mono (by decide) (by simp)
    have tableKept := ((((capFrame.trans (X86StateFrame.registerOnly guardFrame)).trans
      (X86StateFrame.registerOnly zeroFrame)).trans (X86StateFrame.registerOnly jumpFrame)).lookup 7 (by decide)).trans tableBase
    have staged : NativeOccursLoop.Input layout arena agendaLayout table #[] query target after :=
      ⟨⟨input.source.preserved all, NativeMarkTable.Ready.empty _ _, (all.lookup 3 (by decide)).trans input.terms,
        (all.lookup 5 (by decide)).trans input.work, input.pool.preserved all (by simp), tableKept,
        (jumpFrame.lookup 1 (by decide)).trans index, (all.lookup 8 (by decide)).trans name,
        (all.lookup 12 (by decide)).trans input.zero, (all.lookup 13 (by decide)).trans input.one,
        (all.lookup 14 (by decide)).trans input.two⟩, (all.lookup 9 (by decide)).trans root⟩
    refine ⟨after, 7, X86FuelPrefix.fetches_then 6 1 before e after
      (X86FuelPrefix.fetches_then 5 1 before d e firstFive zeroed) jumped, all, ?_⟩
    rw [if_pos room]
    exact ⟨rfl, staged, endpoint⟩
  · simp only [room, decide_false] at cursor
    refine ⟨d, 5, firstFive, checked.mono (by decide) (by simp), ?_⟩
    rw [if_neg room]
    exact ⟨rfl, ⟨cursor⟩⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeBindEntry
