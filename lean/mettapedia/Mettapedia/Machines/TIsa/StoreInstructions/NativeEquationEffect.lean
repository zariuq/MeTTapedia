import Mettapedia.Machines.TIsa.StoreInstructions.NativeEquationInputs

/-!
# A fetched equation effect and the symbolic tell instruction

Operand loads, private node preparation and root publication
share one fetched trace. A symbolic tell makes exactly one
pending equation and returns the p1 success word. It makes no
assertion about whether the enlarged problem is solvable.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeEquationEffect

open Mettapedia.Logic.LP
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Encoding Controls CodeApart footprint Reads)
open X86PlacedScalar (Code)
open PackedEquations (Arena Node)
open NativeStores (Write)
open NativeEquationAppend (Bank Represents instructions)
open NativeEquationInputs (Operands registers)
open MemoryBinding (Native handlers)
local instance : MemoryPrimitives := X86Memory.ordinary

structure Destination (capacity : ℕ) (arena : Arena) where
  bank : Bank capacity
  room : arena.size < capacity
  encoding : Encoding
  rootPointer : Word
  rootEncoding : Encoding
  root : Write rootPointer
  handle : root.value = PackedEquations.next arena

variable {capacity : ℕ} {arena : Arena}

def Destination.moves (layout : Destination capacity arena) (node : Node) : List (Write layout.bank.pointer) :=
  instructions layout.bank ⟨arena.size, layout.room⟩ registers node

def Destination.width (layout : Destination capacity arena) : ℕ :=
  3 * layout.encoding.length + layout.rootEncoding.length

def Destination.writes (layout : Destination capacity arena) (node : Node) : Finset ℕ :=
  NativeStores.written (layout.moves node) ∪ footprint layout.root.cell.address

structure Destination.Placed (layout : Destination capacity arena) (node : Node)
    (image : NativeImage.View) (start : ℕ) : Prop where
  stores : NativeStores.Checked layout.encoding image start (layout.moves node)
  publishFits : start + 3 * layout.encoding.length + layout.rootEncoding.length ≤ image.size
  publish : Code image (start + 3 * layout.encoding.length) (layout.root.bytes layout.rootEncoding)

structure Destination.Geometry (layout : Destination capacity arena) (node : Node)
    (image : NativeImage.View) (base : BitVec 48) : Prop where
  code : CodeApart image base (layout.writes node)
  root : ∀ (index : Fin capacity) (field : Fin 3),
    Disjoint (footprint (NativeEquationAppend.location layout.bank index field)) (footprint layout.root.cell.address)

structure Destination.Ready (layout : Destination capacity arena) (before : Native) : Prop where
  arena : Represents layout.bank arena before
  bank : lookup before layout.encoding.base = some layout.bank.pointer
  root : lookup before layout.rootEncoding.base = some layout.rootPointer
  newHandle : lookup before layout.root.source = some layout.root.value
  keepBank : key layout.encoding.base ∉ NativeEquationInputs.clobbers
  keepRoot : key layout.rootEncoding.base ∉ NativeEquationInputs.clobbers
  keepHandle : key layout.root.source ∉ NativeEquationInputs.clobbers

theorem Destination.Ready.preserved {layout : Destination capacity arena} {before after : Native}
    {regs : Finset Register} {bytes : Finset ℕ} (ready : layout.Ready before)
    (frame : X86StateFrame.Frame regs bytes before after)
    (aside : ∀ (index : Fin capacity) (field : Fin 3),
      Disjoint (footprint (NativeEquationAppend.location layout.bank index field)) bytes)
    (bank : key layout.encoding.base ∉ regs) (root : key layout.rootEncoding.base ∉ regs)
    (handle : key layout.root.source ∉ regs) : layout.Ready after :=
  { ready with
    arena := ready.arena.preserved frame aside
    bank := (frame.lookup _ bank).trans ready.bank
    root := (frame.lookup _ root).trans ready.root
    newHandle := (frame.lookup _ handle).trans ready.newHandle }

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {codeBase : BitVec 48} {start : ℕ} {before : Native}
    (point : At image before codeBase start) (controls : Controls before) {level candidate : Word}
    (input : Operands level candidate) (loads : input.Checked image start)
    (node : Node) (fitHead : PackedEquations.CanAppend arena node.older)
    (operands : input.Ready before node) (levelRead : lookup before 6 = some level) (candidateRead : lookup before 7 = some candidate)
    (destination : Destination capacity arena) (prepared : destination.Ready before)
    (placed : destination.Placed node image (start + input.width))
    (geometry : destination.Geometry node image codeBase)
    {T : Type*} (codes : PackedOccurrences.Codes T) (history : List (T × T))
    (old : PackedEquations.read codes arena node.older = some history)
    (equation : T × T) (left : codes.decode node.left = some equation.1) (right : codes.decode node.right = some equation.2) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 7).run before = .ok () after ∧
      X86StateFrame.Frame NativeEquationInputs.clobbers (destination.writes node) before after ∧
      Represents destination.bank (arena.push node) after ∧
      Reads after destination.root.cell.address (PackedEquations.next arena) ∧
      PackedEquations.read codes (arena.push node) (PackedEquations.next arena) = some (equation :: history) ∧
      (∀ prior : Word, prior.toNat ≤ arena.size →
        PackedEquations.read codes (arena.push node) prior = PackedEquations.read codes arena prior) ∧
      Nonempty (At image after codeBase (start + input.width + destination.width)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨loaded, read, readFrame, values, ⟨atWrites⟩⟩ :=
    NativeEquationInputs.fetched other extra vector point controls input loads node operands levelRead candidateRead
  have retained := prepared.arena.preserved readFrame (by intro _ _; simp)
  obtain ⟨after, done, writeFrame, bank, root, found, oldHandles, reached⟩ :=
    NativeEquationAppend.fetched (handlers other extra) vector atWrites
      (controls.transport readFrame NativeEquationInputs.clobbers_data)
      destination.bank arena destination.room retained node fitHead registers values destination.encoding
      ((readFrame.lookup _ prepared.keepBank).trans prepared.bank) placed.stores
      (geometry.code.mono Finset.subset_union_left) destination.root destination.rootEncoding destination.handle
      ((readFrame.lookup _ prepared.keepRoot).trans prepared.root)
      ((readFrame.lookup _ prepared.keepHandle).trans prepared.newHandle)
      placed.publishFits placed.publish (geometry.code.mono Finset.subset_union_right) geometry.root
      codes history old equation left right
  refine ⟨after, X86FuelPrefix.fetches_then 3 4 before loaded after read done,
    (readFrame.trans writeFrame).mono (by decide) (by simp [Destination.writes, Destination.moves]),
    bank, root, found, oldHandles, ?_⟩
  simpa only [Destination.width, Nat.add_assoc] using reached

universe u q
variable {σ : LPSignature.{u,u,q,u}} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

theorem tell (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {codeBase : BitVec 48} {start : ℕ} {before : Native}
    (point : At image before codeBase start) (controls : Controls before) {slot candidate : Word}
    (input : Operands slot candidate) (loads : input.Checked image start)
    (node : Node) (fitHead : PackedEquations.CanAppend arena node.older)
    (operands : input.Ready before node) (slotRead : lookup before 6 = some slot) (candidateRead : lookup before 7 = some candidate)
    (destination : Destination capacity arena) (prepared : destination.Ready before)
    (placed : destination.Placed node image (start + input.width))
    (geometry : destination.Geometry node image codeBase)
    (levelRoot : destination.root.cell.address = input.previous.cell.address)
    (codes : PackedOccurrences.Codes (Term σ)) (knowledge : SymbolicExecution.Equations σ)
    (st : SymbolicExecution.Frame σ) (level : ℕ) (dst : P1Source.Reg) (lhs rhs : Term σ)
    (old : PackedEquations.read codes arena node.older = some (st.levels level).bindings.newer)
    (l : codes.decode node.left = some lhs) (r : codes.decode node.right = some rhs)
    (fits : start + input.width + destination.width + 6 ≤ image.size)
    (resultBytes : Code image (start + input.width + destination.width)
      (X86Immediate32.code (X86BoundedLoad.physical dst) 1)) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after abstract,
      (X86FuelPrefix.fetches 8).run before = .ok () after ∧
      executeInstructionWith (SymbolicExecution.profile knowledge).step st
        (.transform (.test (.perform (.tell lhs rhs)) level dst)) = .ok abstract ∧
      Represents destination.bank (arena.push node) after ∧
      Reads after input.previous.cell.address (PackedEquations.next arena) ∧
      PackedEquations.Symbolic.Represents codes (arena.push node) (PackedEquations.next arena)
        (abstract.levels level).bindings ∧
      lookup after (X86BoundedLoad.physical dst) = some (abstract.machine.registers dst) ∧
      X86StateFrame.Frame (NativeEquationInputs.clobbers ∪ X86Immediate32.writes (X86BoundedLoad.physical dst))
        (destination.writes node) before after ∧
      Nonempty (At image after codeBase (start + input.width + destination.width + 6)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨appended, wrote, affected, bank, newRoot, pushed, _, ⟨atResult⟩⟩ :=
    fetched other extra vector point controls input loads node fitHead operands slotRead candidateRead
      destination prepared placed geometry codes _ old (lhs, rhs) l r
  obtain ⟨after, ended, scalar, bit, reached⟩ := X86PlacedScalar.rex_immediate
    (X86FrameLoad.linkedHandlers other) extra vector atResult fits _ 1 resultBytes
  have saved := X86StateFrame.registerOnly scalar
  let work := (st.levels level).bindings.extend (lhs, rhs)
  let next := {st.levels level with bindings := work}
  let following := (st.setLevel level next).write dst 1
  refine ⟨after, following, X86FuelPrefix.fetches_then 7 1 before appended after wrote ended, rfl,
    bank.preserved saved (by intro _ _; simp), levelRoot ▸ newRoot.preserved saved (by simp), ?_, ?_,
    (affected.trans saved).mono (Finset.Subset.refl _) (by simp), reached⟩
  · have equals : following.levels level = next := by
      simp [following, StoreInstructions.State.setLevel, StoreInstructions.State.write]
    rw [equals]
    exact ⟨pushed, rfl⟩
  · simpa [following, StoreInstructions.State.setLevel, StoreInstructions.State.write, P1WordExecution.State.write] using bit

end Mettapedia.Machines.TIsa.StoreInstructions.NativeEquationEffect
