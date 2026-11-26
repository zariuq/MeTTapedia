import Mettapedia.Machines.TIsa.StoreInstructions.NativeIndexedWord
import Mettapedia.Machines.TIsa.StoreInstructions.NativeOccurs
import Mettapedia.Machines.TIsa.StoreInstructions.PackedOccursPrefix

/-!
# The initialized prefix of a native occurrence-mark table

Scratch capacity is not evidence of an initialized bit. Only
marks already visited in allocation order are resident. Writing
the next qword leaves all earlier marks unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeMarkTable

open _root_.X86Registers (Register)
open X86PlacedMemory (Reads footprint)
open NativeArenaGeometry (Region)
open NativeOccurs (word)
open MemoryBinding (Native)

structure PrefixReady {capacity : ℕ} {A : Type*} (encode : A → Word)
    (table : Region capacity) (marks : Array A) (native : Native) : Prop where
  fits : marks.size ≤ capacity
  read : ∀ i : Fin marks.size,
    Reads native ((table.wordCell ⟨i.val, i.isLt.trans_le fits⟩).cell 0).address (encode marks[i])

abbrev Ready {capacity : ℕ} (table : Region capacity) (marks : Array Bool) (native : Native) : Prop :=
  PrefixReady word table marks native

variable {capacity : ℕ} {table : Region capacity}
variable {A : Type*} {encode : A → Word}

theorem PrefixReady.empty (encode : A → Word) (table : Region capacity) (native : Native) :
    PrefixReady encode table #[] native :=
  ⟨by simp, fun i => Fin.elim0 i⟩

theorem Ready.empty (table : Region capacity) (native : Native) : Ready table #[] native :=
  PrefixReady.empty word table native

theorem PrefixReady.at_word {marks : Array A} {native : Native} (ready : PrefixReady encode table marks native)
    (index : Word) {bit : A} (observed : marks[index.toNat]? = some bit) :
    ∃ inside : index.toNat < marks.size, Reads native
      ((table.wordCell ⟨index.toNat, inside.trans_le ready.fits⟩).cell 0).address (encode bit) := by
  obtain ⟨inside, selected⟩ := Array.getElem?_eq_some_iff.mp observed
  exact ⟨inside, selected ▸ ready.read ⟨index.toNat, inside⟩⟩

theorem PrefixReady.preserved {marks : Array A} {before after : Native} {regs : Finset Register}
    (resident : PrefixReady encode table marks before) (frame : X86StateFrame.Frame regs ∅ before after) :
    PrefixReady encode table marks after :=
  ⟨resident.fits, fun i => (resident.read i).preserved frame (by simp)⟩

theorem PrefixReady.kept {marks : Array A} {before after : Native} {regs : Finset Register}
    {bytes : Finset ℕ} (resident : PrefixReady encode table marks before)
    (frame : X86StateFrame.Frame regs bytes before after)
    (protect : ∀ i : Fin capacity, Disjoint (footprint ((table.wordCell i).cell 0).address) bytes) :
    PrefixReady encode table marks after :=
  ⟨resident.fits, fun i => (resident.read i).preserved frame (protect _)⟩

theorem PrefixReady.extend {marks : Array A} {before after : Native} {regs : Finset Register}
    (resident : PrefixReady encode table marks before) (room : marks.size < capacity) (bit : A)
    (frame : X86StateFrame.Frame regs (footprint ((table.wordCell ⟨marks.size, room⟩).cell 0).address) before after)
    (written : Reads after ((table.wordCell ⟨marks.size, room⟩).cell 0).address (encode bit)) :
    PrefixReady encode table (marks.push bit) after := by
  have fits : (marks.push bit).size ≤ capacity := by rw [Array.size_push]; omega
  refine ⟨fits, fun i => ?_⟩
  by_cases newest : i.val = marks.size
  · have same : (⟨i.val, i.isLt.trans_le fits⟩ : Fin capacity) = ⟨marks.size, room⟩ := Fin.ext newest
    have yes : (marks.push bit)[i] = bit := by
      change (marks.push bit)[i.val] = bit
      simp [Array.getElem_push, newest]
    rw [same, yes]
    exact written
  · have old : i.val < marks.size := by
      have bound := i.isLt
      simp only [Array.size_push] at bound
      omega
    let prior : Fin marks.size := ⟨i.val, old⟩
    have remains : (marks.push bit)[i] = marks[prior] := by
      change (marks.push bit)[i.val] = marks[i.val]
      simp [Array.getElem_push, old]
    rw [remains]
    exact (resident.read prior).preserved frame (table.wordCells_disjoint (fun eq => newest (congrArg Fin.val eq)))

def Within (table : Region capacity) (lo hi : ℕ) (writes : Finset ℕ) : Prop :=
  ∀ byte ∈ writes, ∃ index : Fin capacity, lo ≤ index.val ∧ index.val < hi ∧
    byte ∈ footprint ((table.wordCell index).cell 0).address

theorem Within.apart_interval {lo hi : ℕ} {writes : Finset ℕ} (within : Within table lo hi writes)
    (held : Finset ℕ)
    (protect : ∀ i : Fin capacity, lo ≤ i.val → i.val < hi → Disjoint held (footprint ((table.wordCell i).cell 0).address)) :
    Disjoint held writes := by
  apply Finset.disjoint_left.mpr
  intro byte exposed changed
  obtain ⟨i, lower, upper, present⟩ := within byte changed
  exact Finset.disjoint_left.mp (protect i lower upper) exposed present

theorem Within.apart {lo hi : ℕ} {writes : Finset ℕ} (within : Within table lo hi writes)
    (held : Finset ℕ) (protect : ∀ i : Fin capacity, Disjoint held (footprint ((table.wordCell i).cell 0).address)) :
    Disjoint held writes :=
  within.apart_interval held (fun i _ _ => protect i)

end Mettapedia.Machines.TIsa.StoreInstructions.NativeMarkTable
