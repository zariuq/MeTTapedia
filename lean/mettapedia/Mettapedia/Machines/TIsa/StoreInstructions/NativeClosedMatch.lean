import Mettapedia.Machines.TIsa.StoreInstructions.ClosedMatch
import Mettapedia.Machines.TIsa.StoreInstructions.MatchSlots

/-!
# Native selection of a closed matching occurrence

After the structural eligibility check and operand loading, a closed
premise is a comparison followed, on success alone, by selection of the
constructed next match. A failed comparison leaves all match levels
unchanged. Both paths return a p1 boolean and rejoin. This is not the
lowering of an open pattern that still has variables to bind.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeClosedMatch

open Mettapedia.Logic.LP
open Derivation (Role Match)
open Derivation.FirstOrderTerms (Bindings matcher)
open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedScalar (Code CompareBranch Jump)
open X86PlacedMemory (CodeApart Cell Controls Encoding footprint)
local instance : MemoryPrimitives := X86Memory.ordinary

structure Block (image : NativeImage.View) (start refused finish : ℕ)
    (lhs rhs result : Fin 16) (encoding : Encoding) (reference : Fin 16) (disp : BitVec 32) : Prop where
  compare : CompareBranch image start refused .equal lhs rhs
  storeInside : start + 9 + encoding.length ≤ image.size
  writeReference : Code image (start + 9) (encoding.bytes reference disp)
  yesInside : start + 9 + encoding.length + 6 ≤ image.size
  noInside : refused + 6 ≤ image.size
  yesFlag : Code image (start + 9 + encoding.length) (X86Immediate32.code result 1)
  noFlag : Code image refused (X86Immediate32.code result 0)
  yesJump : Jump image (start + 9 + encoding.length + 6) finish
  noJump : Jump image (refused + 6) finish

private theorem register_outside_compare (reg : Fin 16) : key reg ∉ ({.rflags, .rip} : Finset Register) := by
  revert reg
  decide +kernel

private theorem register_outside_jump (reg : Fin 16) : key reg ∉ ({.rip} : Finset Register) := by
  revert reg
  decide +kernel

private theorem sequence [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    {source middle final : X86RegisterRefinement.State} {first rest : ℕ}
    (ran : (X86FuelPrefix.fetches first).run source = .ok () middle)
    (continued : (X86FuelPrefix.fetches rest).run middle = .ok () final) :
    (X86FuelPrefix.fetches (first + rest)).run source = .ok () final := by
  rw [X86FuelPrefix.fetches_add, run_bind, ran]
  exact continued

private theorem materialize (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers)
    (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {native : X86RegisterRefinement.State} {base : BitVec 48}
    {start finish : ℕ} (point : At image native base start) (result : Fin 16) (value : BitVec 32)
    (fits : start + 6 ≤ image.size) (literal : Code image start (X86Immediate32.code result value))
    (jump : Jump image (start + 6) finish) :
    letI : OtherOpcodeHandlers := X86PlacedScalar.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run native = .ok () after ∧
      lookup after result = some (value.zeroExtend 64) ∧ after.mem = native.mem ∧
      Nonempty (At image after base finish) := by
  let : OtherOpcodeHandlers := X86PlacedScalar.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨literalEnd, moved, movFrame, installed, ⟨tail⟩⟩ :=
    X86PlacedScalar.rex_immediate other extra vector point fits result value literal
  obtain ⟨after, jumped, frame, next⟩ := X86PlacedScalar.jump other extra vector tail jump
  exact ⟨after, sequence moved jumped, (frame.lookup result (register_outside_jump result)).trans installed,
    frame.memory.trans movFrame.memory, next⟩

variable {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  {n : ℕ}

theorem lower_closed_match_x86 (codes : PackedOccurrences.Codes (GroundTerm σ))
    (st : StoreInstructions.State (GroundTerm σ) (Bindings σ))
    {memory : PackedOccurrences.Layout} (packed : PackedOccurrences.pack codes st.store = some memory)
    (directory : MatchSlots.Directory n (GroundTerm σ) (Bindings σ)) (nextLevel : Fin n)
    (role : Role) (pattern value : GroundTerm σ) (identity level : ℕ) (index dst : P1Source.Reg)
    (isNextLevel : nextLevel.val = level + 1)
    (allowed : role.allows (st.levels level) identity = true)
    (consistent : BindingsConsistent (st.levels level).bindings)
    (row : PackedOccurrences.at? codes memory (st.machine.registers index).toNat = some (identity, value))
    (left right handle : Word) (patternCode : codes.encode pattern = some left) (valueCode : codes.encode value = some right)
    (prepared : MatchSlots.decode matcher directory handle =
      some ((st.levels level).select role identity (st.levels level).bindings))
    (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {image : NativeImage.View} {native : X86RegisterRefinement.State} {base : BitVec 48}
    {start refused finish : ℕ} {lhs rhs reference : Fin 16} {encoding : Encoding} {disp : BitVec 32}
    (point : At image native base start)
    (code : Block image start refused finish lhs rhs (X86BoundedLoad.physical dst) encoding reference disp)
    (leftKnown : lookup native lhs = some left) (rightKnown : lookup native rhs = some right)
    (handleKnown : lookup native reference = some handle) (baseValue : Word)
    (baseKnown : lookup native encoding.base = some baseValue)
    (controls : Controls native) (cell : Cell baseValue disp) (located : cell.address = directory.addr nextLevel)
    (outsideCode : CodeApart image base (footprint cell.address))
    (levels : MatchSlots.Represents matcher directory native st.levels)
    (apart : MatchSlots.Apart directory nextLevel) :
    letI : OtherOpcodeHandlers := X86PlacedScalar.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after abstract,
      (X86FuelPrefix.fetches (if Comparison.equal.evaluate left right then 5 else 4)).run native = .ok () after ∧
      executeInstruction matcher st (.transform (.premise role pattern.toTerm level index dst)) = .ok abstract ∧
      lookup after (X86BoundedLoad.physical dst) = some (abstract.machine.registers dst) ∧
      MatchSlots.Represents matcher directory after abstract.levels ∧
      Nonempty (At image after base finish) := by
  let : OtherOpcodeHandlers := X86PlacedScalar.handlers other extra
  let : VectorOpcodeHandlers := vector
  obtain ⟨cmpState, compared, cmpFrame, ⟨onBranch⟩⟩ :=
    X86PlacedScalar.compare_branch other extra vector point .equal lhs rhs code.compare left right leftKnown rightKnown
  have beforeStore := MatchSlots.represents_memory matcher directory levels cmpFrame.memory
  have exactEffect := ClosedMatch.packed_attempt codes st packed role pattern value identity level index dst consistent
    row left right patternCode valueCode
  change (_ = if role.allows (st.levels level) identity && Comparison.equal.evaluate left right then _ else _) at exactEffect
  cases verdict : Comparison.equal.evaluate left right with
  | false =>
    have no : At image cmpState base refused := by simpa only [verdict, Bool.false_eq_true, if_false] using onBranch
    obtain ⟨after, ran, status, unchanged, done⟩ :=
      materialize other extra vector no (X86BoundedLoad.physical dst) 0 code.noInside code.noFlag code.noJump
    refine ⟨after, st.write dst 0, sequence compared ran, ?_, ?_, ?_, done⟩
    · simpa [verdict] using exactEffect
    · simpa [StoreInstructions.State.write, P1WordExecution.State.write] using status
    · exact MatchSlots.represents_memory matcher directory beforeStore unchanged
  | true =>
    have yes : At image cmpState base (start + 9) := by simpa only [verdict, Bool.true_eq, if_true] using onBranch
    have controls' := controls.transport (X86StateFrame.registerOnly cmpFrame) (by decide)
    have pointer' := (cmpFrame.lookup encoding.base (register_outside_compare encoding.base)).trans baseKnown
    have handle' := (cmpFrame.lookup reference (register_outside_compare reference)).trans handleKnown
    obtain ⟨installed, stored, frame, read, ⟨afterStore⟩⟩ :=
      X86PlacedMemory.stores (X86PlacedScalar.handlers other extra) vector yes controls' encoding reference disp
        baseValue handle cell pointer' handle' code.storeInside code.writeReference outsideCode
    have newLevels := MatchSlots.represents_update matcher directory beforeStore (located ▸ frame)
      (located ▸ read) prepared apart
    obtain ⟨after, ran, status, unchanged, done⟩ :=
      materialize other extra vector afterStore (X86BoundedLoad.physical dst) 1 code.yesInside code.yesFlag code.yesJump
    let selected := (st.levels level).select role identity (st.levels level).bindings
    refine ⟨after, (st.setLevel (level + 1) selected).write dst 1,
      sequence compared (sequence stored ran), ?_, ?_, ?_, done⟩
    · simpa [allowed, verdict, selected] using exactEffect
    · simpa [StoreInstructions.State.write, P1WordExecution.State.write] using status
    · have final := MatchSlots.represents_memory matcher directory newLevels unchanged
      simpa only [StoreInstructions.State.setLevel, StoreInstructions.State.write, isNextLevel, selected] using final

end Mettapedia.Machines.TIsa.StoreInstructions.NativeClosedMatch
