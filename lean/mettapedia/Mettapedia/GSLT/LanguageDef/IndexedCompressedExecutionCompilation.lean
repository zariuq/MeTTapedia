import Mettapedia.GSLT.LanguageDef.IndexedCompressedProgramPlanCompilation
import Mettapedia.GSLT.LanguageDef.PreparedIndexedValueTableCompilation

/-!
# Composed indexed compressed-execution refinement

The generated compressed-program plan, streaming decoder, split
prepared/saved table, and counter-bearing effect machine are separate
certified components.  This module closes their execution seam: a byte stream
accepted by the generated decoder has exactly the abstract instruction
semantics when executed by the complete physical machine, including decode
refusal, dynamic saved-value lookup, effect failure, final open-index refusal,
and the successful instruction counter.

The theorem remains polymorphic in prepared values, saved values, logical
state, and failures.  A proof checker, parser action machine, or process
scheduler supplies an effect algebra; none is named by this lowering.
-/

namespace Mettapedia.GSLT.LanguageDef.IndexedCompressedExecutionCompilation

open IndexedInstructionStreamCompilation
open IndexedEffectMachineCompilation
open IndexedEffectMachinePhysicalRefinement
open PreparedIndexedValueTableCompilation

def indexedValueToSum : IndexedValue Prepared Saved → Sum Prepared Saved
  | .prepared value => .inl value
  | .saved value => .inr value

/-- The effect machine's dynamic lookup is the same logical concatenated
index space as the independently proved immutable-prefix/saved-suffix table. -/
theorem lookupSplit_eq_sourceSplitLookup
    (prepared : List Prepared) (saved : List Saved) (index : UInt64) :
    (lookupSplit prepared saved index).map indexedValueToSum =
      sourceSplitLookup prepared saved index.toNat := by
  rw [← preparedSplitLookup_toArray prepared saved index.toNat]
  simp only [lookupSplit, preparedSplitLookup]
  by_cases inside : index.toNat < prepared.length
  · have arrayInside : index.toNat < prepared.toArray.size := by
      simpa using inside
    rw [if_pos arrayInside]
    simp [inside, indexedValueToSum]
  · have arrayOutside : ¬index.toNat < prepared.toArray.size := by
      simpa using inside
    rw [if_neg arrayOutside]
    have listOutside : prepared[index.toNat]? = none := by
      exact List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt inside)
    rw [listOutside]
    simp [indexedValueToSum, Function.comp_def]

/-- Complete physical execution refines the independently decoded abstract
instruction execution.  The premise is the executable decoder certificate;
capacity is the explicit finite-word side condition used by the native
counter. -/
theorem runPhysicalMachine_refines_of_compile
    (plan : Plan)
    (algebra : EffectAlgebra Prepared Saved State Failure)
    (state : PhysicalState State)
    (chunks : List (List UInt8))
    (instructions : List Instruction)
    (compiled : compile? plan chunks = .ok instructions)
    (capacity : CounterCapacity state.valueInstructionLen instructions) :
    runPhysicalMachine plan algebra state chunks =
      match executeInstructions algebra state.logical instructions with
      | .error failure =>
          .error (.execute (liftExecutionError failure))
      | .ok finalState => .ok
          { logical := finalState
            valueInstructionLen :=
              advanceCounters state.valueInstructionLen instructions } := by
  cases validEq : plan.valid with
  | false =>
      simp [compile?, validEq, bind, Except.bind, pure, Except.pure]
        at compiled
  | true =>
    cases decoded : runChunksFrom plan initialState chunks with
    | error failure =>
        simp [compile?, validEq, decoded, bind, Except.bind, pure,
          Except.pure] at compiled
    | ok result =>
        obtain ⟨decodedInstructions, finalDecoder⟩ := result
        cases phaseEq : finalDecoder.phase with
        | openIndex accumulator =>
            simp [compile?, validEq, decoded, phaseEq, bind, Except.bind,
              pure, Except.pure] at compiled
        | betweenUses =>
          have instructionEq : decodedInstructions = instructions := by
            simpa [compile?, validEq, decoded, phaseEq, bind, Except.bind,
              pure, Except.pure] using compiled
          subst instructions
          have decodedBytes :
              runBytesFrom plan initialState chunks.flatten =
                .ok (decodedInstructions, finalDecoder) := by
            rw [← runChunksFrom_eq_flatten]
            exact decoded
          simp only [runPhysicalMachine, validEq]
          rw [runPhysicalFusedBytesFrom_refines_abstract_of_decode
            plan algebra initialState state chunks.flatten decodedInstructions
            finalDecoder decodedBytes capacity]
          cases executed : executeInstructions algebra state.logical
              decodedInstructions <;>
              simp [phaseEq]
        | justCompletedUse =>
          have instructionEq : decodedInstructions = instructions := by
            simpa [compile?, validEq, decoded, phaseEq, bind, Except.bind,
              pure, Except.pure] using compiled
          subst instructions
          have decodedBytes :
              runBytesFrom plan initialState chunks.flatten =
                .ok (decodedInstructions, finalDecoder) := by
            rw [← runChunksFrom_eq_flatten]
            exact decoded
          simp only [runPhysicalMachine, validEq]
          rw [runPhysicalFusedBytesFrom_refines_abstract_of_decode
            plan algebra initialState state chunks.flatten decodedInstructions
            finalDecoder decodedBytes capacity]
          cases executed : executeInstructions algebra state.logical
              decodedInstructions <;>
              simp [phaseEq]

private def samplePlan : Plan :=
  { terminalLow := 65
    terminalHigh := 84
    continuationLow := 85
    continuationHigh := 89
    saveByte := 90
    unknownByte := 63
    terminalRadix := 20
    terminalDigitBias := 0
    continuationRadix := 5
    continuationDigitBias := 1 }

private def sampleState : StackState :=
  { prepared := [11, 22, 33], saved := [], stack := [] }

/-- A save extends the suffix, and the later index observes that exact saved
value through the same combined index space. -/
example : runPhysicalMachine samplePlan stackAlgebra
    ({ logical := sampleState } : PhysicalState StackState)
    [[65, 90, 68]] =
    .ok { logical := { sampleState with saved := [11], stack := [11, 11] }
          valueInstructionLen := 2 } := by
  decide

/-- A control byte inside an open numeric index remains a decode refusal and
cannot be reinterpreted as a proof effect. -/
example : runPhysicalMachine samplePlan stackAlgebra
    ({ logical := sampleState } : PhysicalState StackState)
    [[85, 90]] = .error (.decode .saveInsideIndex) := by
  decide

#print axioms runPhysicalMachine_refines_of_compile

end Mettapedia.GSLT.LanguageDef.IndexedCompressedExecutionCompilation
