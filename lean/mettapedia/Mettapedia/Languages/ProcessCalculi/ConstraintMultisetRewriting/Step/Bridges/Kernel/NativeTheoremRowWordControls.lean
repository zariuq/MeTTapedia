import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeTheoremRowSource

/-!
# Consumed word-producer controls at the actual high-word load entry

The machine positive uses the unchanged public fixture. Other finite-cell
snapshots test refusal and literal range only; no altered CPU run is claimed.
Source projection remains conditional on exact readings and an independently
supplied actual field/image. No HOL29 admission or authority follows here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeTheoremRowWordControls

open Mettapedia.Machines.TIsa Cells CellEffects Control
open _root_.X86Registers X86RegisterRefinement X86Execution
open NativeTheoremRowWord

local instance : MemoryPrimitives := X86Memory.ordinary

noncomputable abbrev entry := X86MemoryFieldLoad.entryFixture
def high : Nat := 0x80000001000000ff

theorem actual_producer : (fromEntry? high entry).isSome = true := by decide +kernel

noncomputable def actualProjection : AtEntry high entry := (fromEntry? high entry).get actual_producer

theorem actual_word : actualProjection.word = (0x80000001000000ff#64) := by
  apply BitVec.eq_of_toNat_eq
  exact actualProjection.word_exact

theorem actual_native (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    Nonempty (Execution other extra vector entry actualProjection) := load_execution other extra vector entry actualProjection

/-- The actual admission is consumed, with the active AC profile retained. -/
theorem actual_native_ac (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    ∃ execution : Execution other extra vector entry actualProjection,
      X86MemoryView.readback entry.view.modes execution.after (.register 6) = some (0x80000001000000ff#64) ∧
      (execution.after.regs.get? .rflags).map Functions._get_rflagsbits_ac = some (1#1) := by
  obtain ⟨execution⟩ := actual_native other extra vector
  have word := execution.destination
  rw [actual_word] at word
  obtain ⟨controls,visible,flags,known,active⟩ := execution.profile
  refine ⟨execution,word,?_⟩
  rw [known]
  simpa only [Option.map_some,show entry.profile.ac = (1#1) from rfl] using congrArg some active

theorem overflow_refused : (fromEntry? (2 ^ 64) entry).isNone = true := by
  rw [fromEntry?,NativeTheoremRowWord.overflow_refused _ _ _ _ _ _ _ (by omega)]
  rfl

theorem truncated_literal_refused : (fromEntry? 255 entry).isNone = true := by decide +kernel

theorem missing_byte_refused :
    (projectHeadSecond? high entry.address (point entry) (next entry) (invalid entry)
      (entry.view.keys.erase (.byte 36879)) entry.values).isNone = true := by decide +kernel

theorem short_extent_refused :
    (projectHeadSecond? high entry.address (point entry) (next entry) (invalid entry)
      entry.view.keys (Function.update entry.values (.capabilityLength 0) (15#64))).isNone = true := by decide +kernel

theorem missing_mode_refused :
    (projectHeadSecond? high entry.address (point entry) (next entry) (invalid entry)
      (entry.view.keys.erase (.capabilityMode 0)) entry.values).isNone = true := by decide +kernel

theorem denied_mode_refused :
    (projectHeadSecond? high entry.address (point entry) (next entry) (invalid entry)
      entry.view.keys (Function.update entry.values (.capabilityMode 0) (0#64))).isNone = true := by decide +kernel

noncomputable def zeroCells : NativeKeyMemoryLoadAdmission.Key → Word
  | .byte _ => 0
  | key => entry.values key

/-- A finite-cell check, not a claim that the unchanged native memory is zero. -/
theorem zero_literal_accepted :
    (projectHeadSecond? 0 entry.address (point entry) (next entry) (invalid entry)
      entry.view.keys zeroCells).isSome = true := by decide +kernel

theorem overflowing_zero_refused :
    (projectHeadSecond? (2 ^ 64) entry.address (point entry) (next entry) (invalid entry)
      entry.view.keys zeroCells).isNone = true := by
  rw [NativeTheoremRowWord.overflow_refused _ _ _ _ _ _ _ (by omega)]
  rfl

theorem unchecked_words_alias : BitVec.ofNat 64 (2 ^ 64) = (0#64) := by decide

theorem exact_span : entry.address = 36872 ∧ entry.address = (entry.values (.register 1)).toNat + 8 ∧
    entry.values (.capabilityLength 0) = (16#64) := ⟨rfl,entry.addressEq,rfl⟩

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution TypeFamilySemantics NativeClauseData

universe w

/-- The SAME actual native positive composes with an independent source field.
The source-law readings and constructor-image licence are explicitly conditional. -/
theorem source_conditional {state : Registered.State} (profile : SourceProfileModels.ProfileFrame.{w} state)
    (ops : Operations) (head : NativeTheoremRowSource.HeadOperations)
    (readings : NativeTheoremRowSource.Readings ops head state)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (actualField : HOL.Ty.denote (profile.frame.model other assignment).Carrier (h12 ops))
    {context : HOL.Ctx AtomicTy} (first : HOL.Term Symbol context (h5 ops))
    (tail : HOL.Term Symbol context (h12 ops)) (rho : (profile.frame.model other assignment).Valuation context)
    (fieldImage : actualField = (profile.frame.model other assignment).denote
      (NativeTheoremRowSource.tableTerm ops first high tail) rho)
    (cpuOther : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers) :
    Nonempty (Execution cpuOther extra vector entry actualProjection) ∧
      (NativeTheoremRowSource.pairSignature ops).projectSecond (profile.frame.model other assignment)
        (NativeTheoremRowSource.sourceHead head ops (profile.frame.model other assignment) actualField) =
      (profile.frame.model other assignment).denote
        (NativeTheoremRowSource.numberTerm ops actualProjection.word.toNat) (SourceProducts.Signature.empty _) :=
  NativeTheoremRowSource.checked_head_second_image profile ops head readings other assignment actualField
    first high tail rho fieldImage cpuOther extra vector entry actualProjection

theorem empty_cache_refuses_source_laws (ops : Operations) (head : NativeTheoremRowSource.HeadOperations) :
    (NativeTheoremRowSource.read? ops head (Registered.empty SourceProfile.primitiveContext) 0 0).isNone = true := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeTheoremRowWordControls
