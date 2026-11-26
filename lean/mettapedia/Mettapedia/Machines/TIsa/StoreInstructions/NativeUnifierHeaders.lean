import Mettapedia.Machines.TIsa.StoreInstructions.UnifierHeaders
import Mettapedia.Machines.TIsa.StoreInstructions.NativeDecisions
import Mettapedia.Machines.TIsa.StoreInstructions.NativePackedOccurrence

/-!
# Fetched dispatch on two finite-term headers

Each selected header provides its tag and symbol in memory.
The same emitted bytes handle every pair of headers. The result
selects the next solver action, not an already computed answer.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeUnifierHeaders

open Mettapedia.Logic.LP
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls Reads)
open X86PlacedScalar (Code)
open NativeDecisions (Tree)
open UnifierHeaders (Header dispatch)
open NativePackedOccurrence (Bank wordAt)
open NativeWords (Wiring)
open MemoryBinding (Native handlers storeEncoding)
local instance : MemoryPrimitives := X86Memory.ordinary

private def bad : Tree := .leaf UnifierHeaders.Exit.malformed.word
private def dropEquation : Tree := .leaf UnifierHeaders.Exit.discard.word
private def leftVariable : Tree := .leaf UnifierHeaders.Exit.bindLeft.word
private def rightVariable : Tree := .leaf UnifierHeaders.Exit.bindRight.word
private def children : Tree := .leaf UnifierHeaders.Exit.expand.word
private def conflict : Tree := .leaf UnifierHeaders.Exit.clash.word

def tree : Tree :=
  .test .lessEqualUnsigned 8 14
    (.test .lessEqualUnsigned 9 14
      (.test .equal 8 12
        (.test .equal 9 12 (.test .equal 10 0 dropEquation leftVariable) leftVariable)
        (.test .equal 9 12 rightVariable
          (.test .equal 8 9
            (.test .equal 10 0 (.test .equal 8 13 dropEquation children) conflict)
            conflict)))
      bad)
    bad

def registers (left right : Header) (r : Fin 16) : Word :=
  match r.val with
  | 8 => left.tag
  | 9 => right.tag
  | 10 => left.symbol
  | 0 => right.symbol
  | 13 => 1
  | 14 => 2
  | _ => 0

theorem inputs : tree.reads = ({8, 9, 10, 0, 12, 13, 14} : Finset (Fin 16)) := by decide +kernel

theorem decision (left right : Header) :
    tree.answer (registers left right) = (dispatch left right).word := by
  simp [tree, Tree.answer, registers, dispatch, Comparison.evaluate]
  split_ifs <;> rfl

def wireLeftTag : Wiring := ⟨6, by decide, by decide, storeEncoding, 8, by decide, by decide⟩
def wireRightTag : Wiring := ⟨7, by decide, by decide, storeEncoding, 9, by decide, by decide⟩
def wireLeftSymbol : Wiring := ⟨6, by decide, by decide, storeEncoding, 10, by decide, by decide⟩
def wireRightSymbol : Wiring := ⟨7, by decide, by decide, storeEncoding, 0, by decide, by decide⟩

abbrev loadClobbers : Finset Register := {.r8, .r9, .r10, .rax, .rip}

structure Resident (left right : Bank) (l r : Header) (state : Native) : Prop where
  leftBase : lookup state 6 = some left.pointer
  rightBase : lookup state 7 = some right.pointer
  leftTag : Reads state (wordAt left 0).cell.address l.tag
  rightTag : Reads state (wordAt right 0).cell.address r.tag
  leftSymbol : Reads state (wordAt left 1).cell.address l.symbol
  rightSymbol : Reads state (wordAt right 1).cell.address r.symbol
  zero : lookup state 12 = some 0
  one : lookup state 13 = some 1
  two : lookup state 14 = some 2

structure Loads (left right : Bank) (image : NativeImage.View) (start : ℕ) : Prop where
  extent : start + 28 ≤ image.size
  leftTag : Code image start ((wordAt left 0).source.bytes wireLeftTag)
  rightTag : Code image (start + 7) ((wordAt right 0).source.bytes wireRightTag)
  leftSymbol : Code image (start + 14) ((wordAt left 1).source.bytes wireLeftSymbol)
  rightSymbol : Code image (start + 21) ((wordAt right 1).source.bytes wireRightSymbol)

def loadBytes (left right : Bank) : List ℕ :=
  (wordAt left 0).source.bytes wireLeftTag ++
    ((wordAt right 0).source.bytes wireRightTag ++
      ((wordAt left 1).source.bytes wireLeftSymbol ++ (wordAt right 1).source.bytes wireRightSymbol))

def headerLoads : List ℕ :=
  X86DataLoad.code true 8 6 0 ++
    (X86DataLoad.code true 9 7 0 ++ (X86DataLoad.code true 10 6 8 ++ X86DataLoad.code true 0 7 8))

theorem loads_independent (left right : Bank) : loadBytes left right = headerLoads := rfl

theorem header_load_size : headerLoads.length = 28 := rfl

theorem load_size (left right : Bank) : (loadBytes left right).length = 28 := by
  simp only [loadBytes, List.length_append, NativeWords.Source.bytes_length, NativeRoleGate.WordAt.source,
    NativeWords.Source.width]

theorem checked_loads (left right : Bank) (image : NativeImage.View) (start : ℕ)
    (inside : start + 28 ≤ image.size) (installed : Code image start (loadBytes left right)) :
    Loads left right image start := by
  obtain ⟨a, rest⟩ := NativeWords.code_append (show Code image start
    ((wordAt left 0).source.bytes wireLeftTag ++ _) from installed)
  rw [NativeWords.Source.bytes_length] at rest
  obtain ⟨b, rest⟩ := NativeWords.code_append rest
  rw [NativeWords.Source.bytes_length] at rest
  obtain ⟨c, d⟩ := NativeWords.code_append rest
  rw [NativeWords.Source.bytes_length] at d
  exact ⟨inside, a, b, c, d⟩

theorem fetched_loads (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {base : BitVec 48} {start : ℕ}
    {before : Native} (point : At image before base start) (controls : Controls before)
    (left right : Bank) (l r : Header) (resident : Resident left right l r before)
    (ready : Loads left right image start) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 4).run before = .ok () after ∧
      X86StateFrame.Frame loadClobbers ∅ before after ∧
      (∀ reg ∈ tree.reads, lookup after reg = some (registers l r reg)) ∧
      Nonempty (At image after base (start + 28)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have inside := ready.extent
  obtain ⟨a, fetchedA, frameA, leftTag, ⟨atB⟩⟩ :=
    (wordAt left 0).source.fetch (handlers other extra) vector wireLeftTag l.tag point controls resident.leftBase
      resident.leftTag (by change start + 7 ≤ image.size; omega) ready.leftTag
  obtain ⟨b, fetchedB, frameB, rightTag, ⟨atC⟩⟩ :=
    (wordAt right 0).source.fetch (handlers other extra) vector wireRightTag r.tag atB
      (controls.transport frameA (by decide)) ((frameA.lookup 7 (by decide)).trans resident.rightBase)
      (resident.rightTag.preserved frameA (by simp)) (by change start + 14 ≤ image.size; omega) ready.rightTag
  have first := frameA.trans frameB
  obtain ⟨c, fetchedC, frameC, leftSymbol, ⟨atD⟩⟩ :=
    (wordAt left 1).source.fetch (handlers other extra) vector wireLeftSymbol l.symbol atC
      (controls.transport first (by decide)) ((first.lookup 6 (by decide)).trans resident.leftBase)
      (resident.leftSymbol.preserved first (by simp)) (by change start + 21 ≤ image.size; omega) ready.leftSymbol
  have earlier := first.trans frameC
  obtain ⟨after, fetchedD, frameD, rightSymbol, endpoint⟩ :=
    (wordAt right 1).source.fetch (handlers other extra) vector wireRightSymbol r.symbol atD
      (controls.transport earlier (by decide)) ((earlier.lookup 7 (by decide)).trans resident.rightBase)
      (resident.rightSymbol.preserved earlier (by simp)) inside ready.rightSymbol
  have all : X86StateFrame.Frame loadClobbers ∅ before after :=
    (earlier.trans frameD).mono (by decide) (by simp)
  have firstTwo := X86FuelPrefix.fetches_then 1 1 before a b fetchedA fetchedB
  have three := X86FuelPrefix.fetches_then 2 1 before b c firstTwo fetchedC
  refine ⟨after, X86FuelPrefix.fetches_then 3 1 before c after three fetchedD, all, ?_, endpoint⟩
  intro reg read
  simp only [inputs, Finset.mem_insert, Finset.mem_singleton] at read
  rcases read with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (((frameB.trans frameC).trans frameD).lookup 8 (by decide)).trans leftTag
  · exact ((frameC.trans frameD).lookup 9 (by decide)).trans rightTag
  · exact (frameD.lookup 10 (by decide)).trans leftSymbol
  · exact rightSymbol
  · exact (all.lookup 12 (by decide)).trans resident.zero
  · exact (all.lookup 13 (by decide)).trans resident.one
  · exact (all.lookup 14 (by decide)).trans resident.two

def emit (left right : Bank) (start exit : ℕ) (result : Fin 16) : List ℕ :=
  loadBytes left right ++ NativeDecisions.emit result exit tree (start + 28)

theorem clobbers_data : loadClobbers ⊆ dataRegisters := by decide

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers) {image : NativeImage.View} {base : BitVec 48} {start exit : ℕ}
    {before : Native} (point : At image before base start) (controls : Controls before)
    (left right : Bank) (l r : Header) (resident : Resident left right l r before) (result : Fin 16)
    (inside : start + (emit left right start exit result).length ≤ image.size)
    (exitFits : exit ≤ image.size) (short : image.size < 2 ^ 31)
    (installed : Code image start (emit left right start exit result)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches (4 + tree.cost (registers l r))).run before = .ok () after ∧
      X86StateFrame.Frame (loadClobbers ∪ NativeDecisions.clobbers result) ∅ before after ∧
      lookup after result = some ((dispatch l r).word.zeroExtend 64) ∧
      Nonempty (At image after base exit) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨loads, code⟩ := NativeWords.code_append (show Code image start
    (loadBytes left right ++ NativeDecisions.emit result exit tree (start + 28)) from installed)
  rw [load_size] at code
  simp only [emit, List.length_append, load_size, NativeDecisions.size] at inside
  have placed := NativeDecisions.placed_of_emitted image result exit tree (start + 28) (by omega) exitFits short code
  obtain ⟨loaded, read, loadFrame, inputs, ⟨atDecision⟩⟩ := fetched_loads other extra vector point controls
    left right l r resident (checked_loads left right image start (by omega) loads)
  obtain ⟨after, decided, tailFrame, value, endpoint⟩ := NativeDecisions.fetched
    (X86FrameLoad.linkedHandlers other) extra vector result tree (registers l r) atDecision placed inputs
  exact ⟨after, X86FuelPrefix.fetches_then 4 _ before loaded after read decided,
    (loadFrame.trans tailFrame).mono (Finset.Subset.refl _) (by simp),
    decision l r ▸ value, endpoint⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeUnifierHeaders
