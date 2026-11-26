import Mettapedia.Machines.TIsa.StoreInstructions.PackedEquations
import Mettapedia.Machines.TIsa.StoreInstructions.WordRegion
import Mettapedia.Machines.TIsa.StoreInstructions.NativeStores

/-!
# Appending and publishing one native equation node

Three qwords are written in the next free arena cell before
installing its handle. The stores take their values from runtime
registers. Older arena cells are not copied or overwritten.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeEquationAppend

open Mettapedia.Logic.LP
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Cell Encoding Controls CodeApart footprint Reads)
open X86PlacedScalar (Code)
open NativeStores (Native Write)
open PackedEquations (Arena Node CanAppend)
local instance : MemoryPrimitives := X86Memory.ordinary

variable {capacity : ℕ}

abbrev Bank (capacity : ℕ) := WordRegion.Region (3 * capacity)

def position (entry : Fin capacity) (field : Fin 3) : Fin (3 * capacity) :=
  ⟨3 * entry.val + field.val, by have := entry.isLt; have := field.isLt; omega⟩

def data (node : Node) (field : Fin 3) : Word :=
  match field.val with
  | 0 => node.older
  | 1 => node.left
  | _ => node.right

def location (bank : Bank capacity) (entry : Fin capacity) (field : Fin 3) : BitVec 48 :=
  (bank.cell (position entry field)).address

theorem separate (bank : Bank capacity) {entry other : Fin capacity} {field second : Fin 3}
    (different : entry ≠ other ∨ field ≠ second) :
    Disjoint (footprint (location bank entry field)) (footprint (location bank other second)) := by
  apply bank.separate_words
  intro same
  have coords := congrArg Fin.val same
  change 3 * entry.val + field.val = 3 * other.val + second.val at coords
  have x := field.isLt
  have y := second.isLt
  have slots : entry = other := Fin.ext (by omega)
  have columns : field = second := Fin.ext (by omega)
  exact different.elim (fun h => h slots) (fun h => h columns)

def Represents (bank : Bank capacity) (arena : Arena) (native : Native) : Prop :=
  arena.size ≤ capacity ∧
    ∀ (index : Fin capacity) (node : Node), arena[index.val]? = some node →
      ∀ field, Reads native (location bank index field) (data node field)

theorem Represents.preserved {bank : Bank capacity} {arena : Arena} {before after : Native}
    {regs : Finset Register} {written : Finset ℕ} (stable : Represents bank arena before)
    (frame : X86StateFrame.Frame regs written before after)
    (apart : ∀ index field, Disjoint (footprint (location bank index field)) written) :
    Represents bank arena after :=
  ⟨stable.1, fun index node selected field => (stable.2 index node selected field).preserved frame (apart index field)⟩

abbrev Sources := Fin 3 → Fin 16

def word (bank : Bank capacity) (entry : Fin capacity) (regs : Sources) (node : Node) (field : Fin 3) :
    Write bank.pointer :=
  ⟨regs field, BitVec.ofNat 32 (WordRegion.offset (position entry field)), bank.cell (position entry field), data node field⟩

def instructions (bank : Bank capacity) (entry : Fin capacity) (regs : Sources) (node : Node) :
    List (Write bank.pointer) :=
  (List.finRange 3).map (word bank entry regs node)

theorem width (bank : Bank capacity) (entry : Fin capacity) (regs : Sources) (node : Node) :
    (instructions bank entry regs node).length = 3 := by simp [instructions]

theorem separate_instructions (bank : Bank capacity) (entry : Fin capacity) (regs : Sources) (node : Node) :
    NativeStores.Separate (instructions bank entry regs node) := by
  rw [NativeStores.Separate, instructions, List.pairwise_map]
  exact (List.nodup_finRange 3).imp (fun different => separate bank (Or.inr different))

theorem keeps_old_cell (bank : Bank capacity) (entry : Fin capacity) (regs : Sources) (node : Node)
    {old : Fin capacity} (different : old ≠ entry) (field : Fin 3) :
    Disjoint (footprint (location bank old field)) (NativeStores.written (instructions bank entry regs node)) := by
  apply NativeStores.apart_written
  intro w member
  obtain ⟨column, _, rfl⟩ := List.mem_map.mp member
  exact separate bank (Or.inl different)

private theorem after_insert (bank : Bank capacity) (arena : Arena) (room : arena.size < capacity)
    (registers : Sources) (appended : Node) {before after : Native}
    (initial : Represents bank arena before)
    (frame : X86StateFrame.Frame {.rip}
      (NativeStores.written (instructions bank ⟨arena.size, room⟩ registers appended)) before after)
    (written : ∀ w ∈ instructions bank ⟨arena.size, room⟩ registers appended, Reads after w.cell.address w.value) :
    Represents bank (arena.push appended) after := by
  refine ⟨by simp; omega, ?_⟩
  intro index node selected field
  by_cases now : index.val = arena.size
  · rw [Array.getElem?_push, if_pos now] at selected
    obtain rfl := Option.some.inj selected
    obtain rfl : index = ⟨arena.size, room⟩ := Fin.ext now
    exact written (word bank ⟨arena.size, room⟩ registers appended field)
      (List.mem_map.mpr ⟨field, List.mem_finRange _, rfl⟩)
  · rw [Array.getElem?_push, if_neg now] at selected
    exact (initial.2 index node selected field).preserved frame
      (keeps_old_cell bank ⟨arena.size, room⟩ registers appended (fun h => now (congrArg Fin.val h)) field)

/-- The first three fetched stores form a private node. The fourth
publishes its handle. The appended arena still represents every
old node, and its new head denotes the pushed equation. -/
theorem fetched (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {codeBase : BitVec 48} {start : ℕ}
    {before : Native} (point : At image before codeBase start) (controls : Controls before)
    (bank : Bank capacity) (arena : Arena) (room : arena.size < capacity)
    (initial : Represents bank arena before) (node : Node) (fitHead : CanAppend arena node.older)
    (registers : Sources) (known : ∀ field, lookup before (registers field) = some (data node field))
    (encoding : Encoding) (bankKnown : lookup before encoding.base = some bank.pointer)
    (placed : NativeStores.Checked encoding image start (instructions bank ⟨arena.size, room⟩ registers node))
    (codeApart : CodeApart image codeBase (NativeStores.written (instructions bank ⟨arena.size, room⟩ registers node)))
    {root : Word} (publish : Write root) (rootEncoding : Encoding)
    (handle : publish.value = PackedEquations.next arena)
    (rootKnown : lookup before rootEncoding.base = some root)
    (valueKnown : lookup before publish.source = some publish.value)
    (commitFits : start + 3 * encoding.length + rootEncoding.length ≤ image.size)
    (commitCode : Code image (start + 3 * encoding.length) (publish.bytes rootEncoding))
    (commitApart : CodeApart image codeBase (footprint publish.cell.address))
    (rootSeparate : ∀ (index : Fin capacity) (field : Fin 3),
      Disjoint (footprint (location bank index field)) (footprint publish.cell.address))
    {T : Type*} (codes : PackedOccurrences.Codes T) (history : List (T × T))
    (older : PackedEquations.read codes arena node.older = some history)
    (equation : T × T) (left : codes.decode node.left = some equation.1) (right : codes.decode node.right = some equation.2) :
    letI : OtherOpcodeHandlers := other
    letI : VectorOpcodeHandlers := vector
    ∃ after,
      (X86FuelPrefix.fetches 4).run before = .ok () after ∧
      X86StateFrame.Frame {.rip} (NativeStores.written (instructions bank ⟨arena.size, room⟩ registers node) ∪
        footprint publish.cell.address) before after ∧
      Represents bank (arena.push node) after ∧
      Reads after publish.cell.address (PackedEquations.next arena) ∧
      PackedEquations.read codes (arena.push node) (PackedEquations.next arena) = some (equation :: history) ∧
      (∀ prior : Word, prior.toNat ≤ arena.size →
        PackedEquations.read codes (arena.push node) prior = PackedEquations.read codes arena prior) ∧
      Nonempty (At image after codeBase (start + 3 * encoding.length + rootEncoding.length)) := by
  let : OtherOpcodeHandlers := other
  let : VectorOpcodeHandlers := vector
  let issued := instructions bank ⟨arena.size, room⟩ registers node
  have operands : ∀ write ∈ issued, lookup before write.source = some write.value := by
    intro write member
    obtain ⟨field, _, rfl⟩ := List.mem_map.mp member
    exact known field
  obtain ⟨privateState, stored, privateFrame, newWords, ⟨atCommit⟩⟩ :=
    NativeStores.fetched other vector encoding issued point controls placed bankKnown operands
      (separate_instructions bank ⟨arena.size, room⟩ registers node) codeApart
  have saved := after_insert bank arena room registers node initial privateFrame newWords
  have count : issued.length = 3 := width _ _ _ _
  rw [count] at stored atCommit
  obtain ⟨after, wrote, rootFrame, rootWord, finish⟩ :=
    X86PlacedMemory.stores other vector atCommit (controls.transport privateFrame (by decide))
      rootEncoding publish.source publish.displacement root publish.value publish.cell
      ((privateFrame.lookup _ (NativeStores.keeps_word _)).trans rootKnown)
      ((privateFrame.lookup _ (NativeStores.keeps_word _)).trans valueKnown)
      commitFits commitCode commitApart
  exact ⟨after, X86FuelPrefix.fetches_then 3 1 before privateState after stored wrote,
    (privateFrame.trans rootFrame).mono (by simp) (Finset.Subset.refl _),
    saved.preserved rootFrame rootSeparate, handle ▸ rootWord, PackedEquations.appended_read codes fitHead older left right,
    PackedEquations.older_handles_unchanged codes arena node, finish⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeEquationAppend
