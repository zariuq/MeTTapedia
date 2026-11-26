import Mettapedia.Machines.TIsa.StoreInstructions.NativeWords

/-!
# Placed stores from registers

A preparation can write several disjoint words without reloading
operands. The emitted bytes depend on source registers and
addresses, not on the words being written. Each word remains
readable after the whole preparation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeStores

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Encoding Cell Controls Reads CodeApart footprint)
open X86PlacedScalar (Code)
local instance : MemoryPrimitives := X86Memory.ordinary

abbrev Native := X86RegisterRefinement.State

structure Write (pointer : Word) where
  source : Fin 16
  displacement : BitVec 32
  cell : Cell pointer displacement
  value : Word

variable {pointer : Word}

def Write.bytes (encoding : Encoding) (write : Write pointer) : List ℕ :=
  encoding.bytes write.source write.displacement

def emitted (encoding : Encoding) (writes : List (Write pointer)) : List ℕ :=
  writes.flatMap (Write.bytes encoding ·)

def written : List (Write pointer) → Finset ℕ
  | [] => ∅
  | first :: rest => footprint first.cell.address ∪ written rest

def Checked (encoding : Encoding) (image : NativeImage.View) : ℕ → List (Write pointer) → Prop
  | position, [] => position ≤ image.size
  | position, first :: rest => position + encoding.length ≤ image.size ∧ Code image position (first.bytes encoding) ∧
    Checked encoding image (position + encoding.length) rest

theorem Write.byte_length (encoding : Encoding) (write : Write pointer) :
    (write.bytes encoding).length = encoding.length := by
  cases encoding with
  | direct base noSib noStack => exact X86DataStore.code_length true write.source base write.displacement
  | r12 => exact X86SibQword.code_length .store write.source write.displacement

theorem emitted_size (encoding : Encoding) (writes : List (Write pointer)) :
    (emitted encoding writes).length = writes.length * encoding.length := by
  induction writes with
  | nil => simp [emitted]
  | cons first rest ih =>
    change (first.bytes encoding ++ emitted encoding rest).length = _
    rw [List.length_append, first.byte_length, ih, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem checked_of_emitted (encoding : Encoding) (image : NativeImage.View) (start : ℕ)
    (writes : List (Write pointer)) (extent : start + (emitted encoding writes).length ≤ image.size)
    (installed : Code image start (emitted encoding writes)) : Checked encoding image start writes := by
  induction writes generalizing start with
  | nil => exact extent
  | cons first rest ih =>
    obtain ⟨front, tail⟩ := NativeWords.code_append (show Code image start
      (first.bytes encoding ++ emitted encoding rest) from installed)
    rw [first.byte_length] at tail
    change start + (first.bytes encoding ++ emitted encoding rest).length ≤ image.size at extent
    rw [List.length_append, first.byte_length] at extent
    exact ⟨by omega, front, ih _ (by omega) tail⟩

def Separate (writes : List (Write pointer)) : Prop :=
  writes.Pairwise (fun a b => Disjoint (footprint a.cell.address) (footprint b.cell.address))

theorem apart_written (region : Finset ℕ) (writes : List (Write pointer))
    (every : ∀ write ∈ writes, Disjoint region (footprint write.cell.address)) : Disjoint region (written writes) := by
  induction writes with
  | nil => simp [written]
  | cons first rest ih =>
    exact Finset.disjoint_union_right.mpr
      ⟨every first List.mem_cons_self, ih (fun write found => every write (List.mem_cons_of_mem _ found))⟩

theorem keeps_word (register : Fin 16) : key register ∉ ({.rip} : Finset Register) := by
  revert register
  decide +kernel

theorem fetched (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers) (encoding : Encoding)
    (writes : List (Write pointer)) {image : NativeImage.View} {base : BitVec 48}
    {before : Native} {start : ℕ} (point : At image before base start) (controls : Controls before)
    (checked : Checked encoding image start writes) (address : lookup before encoding.base = some pointer)
    (operands : ∀ write ∈ writes, lookup before write.source = some write.value)
    (separate : Separate writes) (codeApart : CodeApart image base (written writes)) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches writes.length).run before = .ok () after ∧
      X86StateFrame.Frame {.rip} (written writes) before after ∧
      (∀ write ∈ writes, Reads after write.cell.address write.value) ∧
      Nonempty (At image after base (start + writes.length * encoding.length)) := by
  let : OtherOpcodeHandlers := other
  let : VectorOpcodeHandlers := vector
  induction writes generalizing before start with
  | nil => exact ⟨before, X86FuelPrefix.fetches_zero before, X86StateFrame.Frame.refl _ _ _,
      fun _ h => (List.not_mem_nil h).elim, ⟨by simpa using point⟩⟩
  | cons head tail ih =>
    obtain ⟨middle, first, firstFrame, writtenHead, ⟨next⟩⟩ := X86PlacedMemory.stores other vector point controls
      encoding head.source head.displacement pointer head.value head.cell address (operands head List.mem_cons_self)
      checked.1 checked.2.1 (codeApart.mono Finset.subset_union_left)
    have apart := List.pairwise_cons.mp separate
    obtain ⟨after, rest, restFrame, results, finished⟩ := ih next (controls.transport firstFrame (by decide)) checked.2.2
      ((firstFrame.lookup _ (keeps_word _)).trans address)
      (fun write covered => (firstFrame.lookup _ (keeps_word _)).trans (operands write (List.mem_cons_of_mem _ covered)))
      apart.2 (codeApart.mono Finset.subset_union_right)
    refine ⟨after, ?_, (firstFrame.trans restFrame).mono (by simp) (Finset.Subset.refl _), ?_, ?_⟩
    · simpa only [List.length_cons, Nat.add_comm] using
        (X86FuelPrefix.fetches_then 1 tail.length before middle after first rest)
    · intro write member
      rcases List.mem_cons.mp member with rfl | remaining
      · exact writtenHead.preserved restFrame (apart_written _ _ apart.1)
      · exact results write remaining
    · simpa only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using finished

end Mettapedia.Machines.TIsa.StoreInstructions.NativeStores
