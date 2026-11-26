import Mettapedia.Machines.TIsa.StoreInstructions.NativeEquationAppend
import Mettapedia.Machines.TIsa.StoreInstructions.NativeRoleGate

/-!
# Fetching the operands of a native equation append

The parent handle is read from the published source level.
Either term can come from memory or be a literal term handle.
In particular, the right operand of MATCH can come from the
selected occurrence, without knowing its term when emitting
the instructions.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeEquationInputs

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code)
open X86PlacedMemory (Controls Reads)
open NativeRoleGate (WordAt)
open PackedEquations (Node)
open NativeWords (Wiring Source)
open MemoryBinding (Native handlers storeEncoding)
local instance : MemoryPrimitives := X86Memory.ordinary

def previousWire : Wiring := ⟨6, by decide, by decide, storeEncoding, 8, by decide, by decide⟩
def leftWire : Wiring := ⟨7, by decide, by decide, storeEncoding, 9, by decide, by decide⟩
def rightWire : Wiring := ⟨7, by decide, by decide, storeEncoding, 10, by decide, by decide⟩

def registers : NativeEquationAppend.Sources := fun field =>
  ⟨8 + field.val, by have := field.isLt; omega⟩

abbrev clobbers : Finset Register := {.r8, .r9, .r10, .rip}

theorem clobbers_data : clobbers ⊆ dataRegisters := by decide

structure Operands (level candidate : Word) where
  previous : WordAt level
  left : NativeWords.Source candidate
  right : NativeWords.Source candidate

variable {level candidate : Word}

def Operands.width (input : Operands level candidate) : ℕ :=
  7 + input.left.width + input.right.width

structure Operands.Checked (input : Operands level candidate) (image : NativeImage.View) (start : ℕ) : Prop where
  extent : start + input.width ≤ image.size
  loadPrevious : Code image start (input.previous.source.bytes previousWire)
  loadLeft : Code image (start + 7) (input.left.bytes leftWire)
  loadRight : Code image (start + 7 + input.left.width) (input.right.bytes rightWire)

structure Operands.Ready (input : Operands level candidate) (native : Native) (node : Node) : Prop where
  previous : Reads native input.previous.cell.address node.older
  left : input.left.Ready native node.left
  right : input.right.Ready native node.right

theorem fetched (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {base : BitVec 48} {start : ℕ} {before : Native}
    (point : At image before base start) (controls : Controls before)
    (input : Operands level candidate) (checked : input.Checked image start) (node : Node)
    (work : input.Ready before node)
    (levelRead : lookup before 6 = some level) (candidateRead : lookup before 7 = some candidate) :
    letI : OtherOpcodeHandlers := handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 3).run before = .ok () after ∧
      X86StateFrame.Frame clobbers ∅ before after ∧
      (∀ field, lookup after (registers field) = some (NativeEquationAppend.data node field)) ∧
      Nonempty (At image after base (start + input.width)) := by
  let : OtherOpcodeHandlers := handlers other extra
  let : VectorOpcodeHandlers := vector
  have extent : start + 7 + input.left.width + input.right.width ≤ image.size := by
    simpa only [Operands.width, Nat.add_assoc] using checked.extent
  obtain ⟨old, ranOld, oldFrame, head, ⟨atLeft⟩⟩ :=
    input.previous.source.fetch (handlers other extra) vector previousWire node.older point controls
      levelRead work.previous (by change start + 7 ≤ image.size; omega) checked.loadPrevious
  obtain ⟨left, ranLeft, leftFrame, first, ⟨atRight⟩⟩ :=
    input.left.fetch (handlers other extra) vector leftWire node.left atLeft
      (controls.transport oldFrame (by decide)) ((oldFrame.lookup 7 (by decide)).trans candidateRead)
      (input.left.ready_preserved work.left oldFrame (by simp))
      (by change start + 7 + input.left.width ≤ image.size; omega) checked.loadLeft
  have earlier := oldFrame.trans leftFrame
  have earlierRun := X86FuelPrefix.fetches_then 1 1 before old left ranOld ranLeft
  obtain ⟨after, ranRight, rightFrame, last, endpoint⟩ :=
    input.right.fetch (handlers other extra) vector rightWire node.right atRight
      (controls.transport earlier (by decide)) ((earlier.lookup 7 (by decide)).trans candidateRead)
      (input.right.ready_preserved work.right earlier (by simp)) extent checked.loadRight
  have carryHead := (rightFrame.lookup 8 (by decide)).trans ((leftFrame.lookup 8 (by decide)).trans head)
  have carryFirst := (rightFrame.lookup 9 (by decide)).trans first
  refine ⟨after, X86FuelPrefix.fetches_then 2 1 before left after earlierRun ranRight,
    (earlier.trans rightFrame).mono (by decide) (by simp), ?_, ?_⟩
  · intro f
    fin_cases f
    · exact carryHead
    · exact carryFirst
    · exact last
  · simpa only [WordAt.source, NativeWords.Source.width, Operands.width, Nat.add_assoc] using endpoint

end Mettapedia.Machines.TIsa.StoreInstructions.NativeEquationInputs
