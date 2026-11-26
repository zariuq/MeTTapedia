import Mettapedia.Machines.TIsa.StoreInstructions.IndexedGuard
import Mettapedia.Machines.TIsa.StoreInstructions.SnapshotPlacement
import Mettapedia.Machines.TIsa.StoreInstructions.NativeCandidateLookup

/-!
# Fetched presence, absence and exact count from a packed snapshot

For an instantiated value and an exact bucket, the native TEST
loads the bucket's length at execution time and compares it with
the encoded target. It reads no posting and changes no snapshot
or binding word. The value-to-key selection and the snapshot's
placement are the calling context.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeIndexedGuard

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Controls)
open X86PlacedScalar (Code)
open Derivation (Matcher)
open IndexedGuard (Query ExactBucket countOf)
open PrivateArrayPlan (Slot)
open NativePreparation (AddressMap Represents)
local instance : MemoryPrimitives := X86Memory.ordinary

def targetWire : NativeWords.Wiring :=
  ⟨7, by decide, by decide, MemoryBinding.storeEncoding, 15, by decide, by decide⟩

structure Placed (image : NativeImage.View) (start refused finish : ℕ) (disp : BitVec 32)
    (query : Query) (result : Fin 16) : Prop where
  extent : start + 17 ≤ image.size
  loadCount : Code image start (X86DataLoad.code true 14 7 disp)
  loadTarget : Code image (start + 7) (X86PlacedWideImmediate.bytes 15 (BitVec.ofNat 64 query.target))
  test : WordTests.Block image (start + 17) refused finish 14 15 result query.condition

def clobbers (dst : Fin 16) : Finset Register :=
  insert (key dst) {.r14, .r15, .rflags, .rip}

private theorem compare_writes (dst : Fin 16) :
    (({.rflags, .rip} : Finset Register) ∪ X86Immediate32.writes dst ∪ {.rip}) ⊆ clobbers dst := by
  intro register member
  simp only [clobbers, X86Immediate32.writes, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at member ⊢
  tauto

private theorem load_handlers (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) :
    NativeWords.handlers (MemoryBinding.handlers other extra) = MemoryBinding.handlers other extra := rfl

universe u v w
variable {T : Type u} {V : Type v} {B : Type w} [DecidableEq V] {keys : ℕ}

theorem fetched (M : Matcher T V B) (codes : PackedOccurrences.Codes V)
    (st : StoreInstructions.State V B) (classify : V → Fin keys)
    {snapshot : StorePublication.Snapshot} (packed : StorePublication.encode codes classify st.store = some snapshot)
    (value : V) (exactBucket : ExactBucket classify st.store value)
    (level : ℕ) (dst : P1Source.Reg) (query : Query) (targetFits : query.target < 2 ^ 64)
    (pattern : T) (instantiated : M.instantiate (st.levels level).bindings pattern = some value)
    (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start refused finish : ℕ}
    {before : MemoryBinding.Native} (point : At image before base start) (controls : Controls before)
    (bank : SnapshotPlacement.Bank snapshot) (resident : Represents bank.addressMap before snapshot)
    (arg : lookup before 7 = some bank.pointer)
    (placed : Placed image start refused finish (bank.addressMap.offset (.length (classify value).val))
      query (X86BoundedLoad.physical dst)) :
    letI : OtherOpcodeHandlers := MemoryBinding.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after abstract,
      (X86FuelPrefix.fetches 6).run before = .ok () after ∧
      X86StateFrame.Frame (clobbers (X86BoundedLoad.physical dst)) ∅ before after ∧
      executeInstruction M st (.transform (.test (.check (query.check pattern)) level dst)) = .ok abstract ∧
      lookup after (X86BoundedLoad.physical dst) = some (abstract.machine.registers dst) ∧
      Nonempty (At image after base finish) := by
  let : OtherOpcodeHandlers := MemoryBinding.handlers other extra
  let : VectorOpcodeHandlers := vector
  let field := Slot.length (classify value).val
  let count := BitVec.ofNat 64 (countOf st.store value)
  let target := BitVec.ofNat 64 query.target
  let measure : NativeWords.Source bank.pointer := .copy (bank.addressMap.offset field) (bank.addressMap.cell field)
  have observed : PrivateArrayPlan.read snapshot field = some count :=
    IndexedGuard.lengthWord_exact codes classify packed value exactBucket
  obtain ⟨sized, readCount, countFrame, number, ⟨atTarget⟩⟩ := measure.fetch (MemoryBinding.handlers other extra)
    vector NativeCandidateLookup.countWire count point controls arg (resident field count observed)
    (by have := placed.extent; change start + 7 ≤ image.size; omega) placed.loadCount
  rw [load_handlers] at readCount
  let literal : NativeWords.Source bank.pointer := .literal target
  obtain ⟨withTarget, readTarget, targetFrame, expected, ⟨atCompare⟩⟩ := literal.fetch
    (MemoryBinding.handlers other extra) vector targetWire target atTarget
    (controls.transport countFrame (by decide)) ((countFrame.lookup 7 (by decide)).trans arg) rfl
    placed.extent placed.loadTarget
  rw [load_handlers] at readTarget
  obtain ⟨after, compared, resultFrame, satisfied, done⟩ := WordTests.lower_compare_x86
    (X86FrameLoad.linkedHandlers other) extra vector atCompare placed.test count target
    ((targetFrame.lookup 14 (by decide)).trans number) expected
  have prefixRun := X86FuelPrefix.fetches_then 1 1 before sized withTarget readCount readTarget
  have loaded : X86StateFrame.Frame {.r14, .r15, .rip} ∅ before withTarget :=
    (countFrame.trans targetFrame).mono (by decide) (by simp)
  let dstReg := X86BoundedLoad.physical dst
  have tested : X86StateFrame.Frame (clobbers dstReg) ∅ withTarget after :=
    (X86StateFrame.registerOnly resultFrame).mono (compare_writes dstReg) (Finset.Subset.refl _)
  have clean : X86StateFrame.Frame (clobbers dstReg) ∅ before after := by
    apply (loaded.trans tested).mono
    · intro r membership
      rcases Finset.mem_union.mp membership with prior | rest
      · exact Finset.mem_insert_of_mem ((by decide :
          ({.r14, .r15, .rip} : Finset Register) ⊆ {.r14, .r15, .rflags, .rip}) prior)
      · exact rest
    · simp
  have nativeExact : query.condition.evaluate count target = query.accepts (countOf st.store value) :=
    query.word_decision _ (IndexedGuard.count_in_word codes (StorePublication.encode_views codes classify packed).1 value)
      targetFits
  let abstract := st.write dst (booleanWord (query.accepts (countOf st.store value)))
  refine ⟨after, abstract, X86FuelPrefix.fetches_then 2 4 before withTarget after prefixRun compared,
    clean, IndexedGuard.execute_count_read M st level dst query pattern value instantiated, ?_, done⟩
  rw [nativeExact] at satisfied
  simpa [abstract, StoreInstructions.State.write, P1WordExecution.State.write] using satisfied

end Mettapedia.Machines.TIsa.StoreInstructions.NativeIndexedGuard
