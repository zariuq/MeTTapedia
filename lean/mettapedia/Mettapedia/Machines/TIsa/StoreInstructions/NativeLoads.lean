import Mettapedia.Machines.TIsa.StoreInstructions.NativeWords
import Mettapedia.Machines.TIsa.X86IndexedAddress

/-!
# Fetched loads from one resident frame

A batch of displaced qword loads does not change its base or
memory. Distinct destinations retain their observed words.
This packages the same placed loads as the individual store
instruction fragments; the emitter contains only displacements
and register choices, not the observed words.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeLoads

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Cell Controls Reads Encoding)
open X86PlacedScalar (Code)
local instance : MemoryPrimitives := X86Memory.ordinary
abbrev Native := X86RegisterRefinement.State

structure Base where
  register : Fin 16
  noSib : register.val % 8 ≠ 4
  noStack : register.val % 8 ≠ 5

def Base.encoding (base : Base) : Encoding := .direct base.register base.noSib base.noStack

structure Load (base : Base) (pointer : Word) where
  destination : Fin 16
  separate : base.register ≠ destination
  displacement : BitVec 32
  cell : Cell pointer displacement
  value : Word

variable {base : Base} {pointer : Word}

def Load.wiring (load : Load base pointer) : NativeWords.Wiring :=
  ⟨base.register, base.noSib, base.noStack, base.encoding, load.destination, load.separate, load.separate⟩

def Load.bytes (load : Load base pointer) : List ℕ :=
  X86DataLoad.code true load.destination base.register load.displacement

theorem Load.size (load : Load base pointer) : load.bytes.length = 7 := rfl

def emitted (loads : List (Load base pointer)) : List ℕ := loads.flatMap Load.bytes

theorem emitted_size (loads : List (Load base pointer)) : (emitted loads).length = 7 * loads.length := by
  induction loads with
  | nil => rfl
  | cons hd tail ih =>
    change (hd.bytes ++ emitted tail).length = _
    simp only [List.length_append, Load.size, List.length_cons, ih]
    omega

def clobbers : List (Load base pointer) → Finset Register
  | [] => ∅
  | head :: tail => NativeWords.touched head.wiring ∪ clobbers tail

theorem clobbers_data (loads : List (Load base pointer)) : clobbers loads ⊆ dataRegisters := by
  induction loads with
  | nil => simp [clobbers]
  | cons load rest ih =>
    simp only [clobbers, Finset.union_subset_iff]
    refine ⟨?_, ih⟩
    intro reg touched
    simp only [NativeWords.touched, Finset.mem_insert, Finset.mem_singleton] at touched
    rcases touched with rfl | rfl
    · exact data_key _
    · decide

private theorem kept_of_distinct (loads : List (Load base pointer)) (r : Fin 16)
    (different : ∀ x ∈ loads, r ≠ x.destination) : key r ∉ clobbers loads := by
  induction loads with
  | nil => simp [clobbers]
  | cons head rest ih =>
    simp only [clobbers, Finset.mem_union, not_or]
    exact ⟨NativeWords.outside_scratch head.wiring r (different head List.mem_cons_self),
      ih (fun x present => different x (List.mem_cons_of_mem _ present))⟩

noncomputable abbrev handlers := X86IndexedAddress.handlers

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {codeBase : BitVec 48} {start : ℕ} {before : Native}
    (point : At image before codeBase start) (controls : Controls before) (loads : List (Load base pointer))
    (within : start + (emitted loads).length ≤ image.size) (placed : Code image start (emitted loads))
    (address : lookup before base.register = some pointer)
    (resident : ∀ move ∈ loads, Reads before move.cell.address move.value)
    (distinct : loads.Pairwise (fun x y => x.destination ≠ y.destination)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches loads.length).run before = .ok () after ∧
      X86StateFrame.Frame (clobbers loads) ∅ before after ∧
      (∀ move ∈ loads, lookup after move.destination = some move.value) ∧
      Nonempty (At image after codeBase (start + 7 * loads.length)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  induction loads generalizing start before with
  | nil =>
    exact ⟨before, X86FuelPrefix.fetches_zero before, X86StateFrame.Frame.refl _ _ _,
      fun _ h => (List.not_mem_nil h).elim, ⟨by simpa using point⟩⟩
  | cons head tail ih =>
    obtain ⟨code, remaining⟩ := NativeWords.code_append (show Code image start (head.bytes ++ emitted tail) from placed)
    rw [head.size] at remaining
    change start + (head.bytes ++ emitted tail).length ≤ image.size at within
    rw [List.length_append, head.size] at within
    let source : NativeWords.Source pointer := .copy _ head.cell
    obtain ⟨one, ran, first, actual, ⟨next⟩⟩ := source.fetch (handlers other extra) vector head.wiring head.value
      point controls address (resident head List.mem_cons_self) (show start + 7 ≤ image.size by omega) code
    have linked : NativeWords.handlers (handlers other extra) = handlers other extra := rfl
    rw [linked] at ran
    have retained := (first.lookup _ (NativeWords.outside_scratch head.wiring _ head.separate)).trans address
    have unique := List.pairwise_cons.mp distinct
    have headData : NativeWords.touched head.wiring ⊆ dataRegisters := by
      simpa only [clobbers, Finset.union_empty] using clobbers_data [head]
    change At image one codeBase (start + 7) at next
    obtain ⟨after, suffix, frame, values, endpoint⟩ := ih next
      (controls.transport first headData)
      (by omega) remaining retained (fun x present => (resident x (List.mem_cons_of_mem _ present)).preserved first (by simp))
      unique.2
    refine ⟨after, ?_, (first.trans frame).mono (Finset.Subset.refl _) (by simp), ?_, ?_⟩
    · simpa only [List.length_cons, Nat.add_comm] using X86FuelPrefix.fetches_then 1 tail.length before one after ran suffix
    · intro move present
      rcases List.mem_cons.mp present with same | otherLoad
      · subst move
        exact (frame.lookup head.destination (kept_of_distinct tail head.destination unique.1)).trans actual
      · exact values move otherLoad
    · simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      simpa only [Nat.add_assoc, Nat.add_comm 7] using endpoint

end Mettapedia.Machines.TIsa.StoreInstructions.NativeLoads
